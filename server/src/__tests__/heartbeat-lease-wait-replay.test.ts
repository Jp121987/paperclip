// Regression checks for a stage-handoff wake that arrives while a stopped
// run's SSH environment lease is still being cleaned up (BTR-165 / BTR-167).
//
// Each check drives the public heartbeat surface (wakeup, the pending-cleanup
// sweep and the scheduler tick) against a real embedded Postgres database.
// Faults are injected at the database boundary with triggers, so the checks
// do not depend on how the replay is written, only on what it delivers.
//
// Stakeholder: the reviewer who is next in a task's review stage. Their wake
// has no other sender, so a lost wake stalls the task silently.
import { randomUUID } from "node:crypto";
import { spawn, type ChildProcess } from "node:child_process";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { and, eq, sql } from "drizzle-orm";
import { afterAll, afterEach, beforeAll, beforeEach, describe, expect, it, vi } from "vitest";
import {
  agents,
  companies,
  createDb,
  environmentLeases,
  environments,
  heartbeatRunEvents,
  heartbeatRuns,
  issueComments,
  issues,
} from "@paperclipai/db";
import {
  getEmbeddedPostgresTestSupport,
  startEmbeddedPostgresTestDatabase,
} from "./helpers/embedded-postgres.js";

const mockTelemetryClient = vi.hoisted(() => ({
  track: vi.fn(),
  hashPrivateRef: vi.fn(() => "test-private-reference"),
}));
vi.mock("../telemetry.ts", () => ({ getTelemetryClient: () => mockTelemetryClient }));

vi.mock("../middleware/logger.js", () => ({
  logger: {
    child: vi.fn(function child() {
      return this;
    }),
    trace: vi.fn(),
    debug: vi.fn(),
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
    fatal: vi.fn(),
  },
  httpLogger: vi.fn(),
}));

// The successor run executes through a stub adapter; the checks care that it
// was admitted, not what a model did inside it. The stub review posts its
// comment (installed in beforeEach), as a real reviewer does, so no
// missing-comment follow-up run muddies the delivery count.
const mockAdapterExecute = vi.hoisted(() => vi.fn());
vi.mock("../adapters/index.ts", async () => {
  const actual = await vi.importActual<typeof import("../adapters/index.ts")>("../adapters/index.ts");
  return {
    ...actual,
    getServerAdapter: vi.fn(() => ({ supportsLocalAgentJwt: false, execute: mockAdapterExecute })),
  };
});

// Records every remote SSH operation. Cleanup of an SSH lease must not touch
// the remote host: the workspace path is shared by every lease on it.
const sshCalls = vi.hoisted(() => [] as string[]);
vi.mock("@paperclipai/adapter-utils/ssh", async () => {
  const actual = await vi.importActual<Record<string, unknown>>("@paperclipai/adapter-utils/ssh");
  return Object.fromEntries(Object.entries(actual).map(([name, value]) => [
    name,
    typeof value === "function" && /^[a-z]/.test(name)
      ? (...args: unknown[]) => {
          sshCalls.push(name);
          return (value as (...a: unknown[]) => unknown)(...args);
        }
      : value,
  ]));
});

import { heartbeatService, type HeartbeatEnvironmentRuntime } from "../services/heartbeat.ts";
import { environmentRuntimeService } from "../services/environment-runtime.ts";

const embeddedPostgresSupport = await getEmbeddedPostgresTestSupport();
const describeEmbeddedPostgres = embeddedPostgresSupport.supported ? describe : describe.skip;
if (!embeddedPostgresSupport.supported) {
  console.warn(
    `Skipping lease-wait replay tests on this host: ${embeddedPostgresSupport.reason ?? "unsupported environment"}`,
  );
}

type Db = ReturnType<typeof createDb>;
type Heartbeat = ReturnType<typeof heartbeatService>;

// How far wake records age between ticks: comfortably past any replay backoff.
const LATER_MS = 10 * 60_000;
const INJECTION_LOCK_KEY = 167_167;

describeEmbeddedPostgres("stage handoff wake parked behind a stopped run's SSH lease", () => {
  let db!: Db;
  let connectionString = "";
  let tempDb: Awaited<ReturnType<typeof startEmbeddedPostgresTestDatabase>> | null = null;
  let home = "";
  let previousHome: string | undefined;
  const extraDbs: Db[] = [];
  const children = new Set<ChildProcess>();

  beforeAll(async () => {
    tempDb = await startEmbeddedPostgresTestDatabase("paperclip-lease-wait-replay-");
    connectionString = tempDb.connectionString;
    db = createDb(connectionString);
    home = await fs.mkdtemp(path.join(os.tmpdir(), "paperclip-lease-wait-replay-home-"));
    previousHome = process.env.PAPERCLIP_HOME;
    process.env.PAPERCLIP_HOME = home;
    // Fault injection lives in the database, below every service write.
    // mode 'fail': the successor run insert raises, rolling back its transaction.
    // mode 'block': the successor run insert waits on an advisory lock the test holds.
    await db.execute(sql.raw(`
      create table if not exists test_fault_injection (
        mode text not null, agent_id uuid not null, issue_id text not null
      );
      create or replace function test_fault_on_run_insert() returns trigger language plpgsql as $$
      declare fault record;
      begin
        select * into fault from test_fault_injection
          where agent_id = new.agent_id and issue_id = new.context_snapshot->>'issueId' limit 1;
        if fault.mode = 'fail' then
          raise exception 'injected failure before the successor run committed';
        elsif fault.mode = 'block' then
          perform pg_advisory_xact_lock(${INJECTION_LOCK_KEY});
        end if;
        return new;
      end $$;
      drop trigger if exists test_fault_on_run_insert on heartbeat_runs;
      create trigger test_fault_on_run_insert before insert on heartbeat_runs
        for each row execute function test_fault_on_run_insert();
      -- A server process marked dead writes nothing more to delivery state.
      create table if not exists test_dead_servers (application_name text primary key);
      create or replace function test_dead_server_guard() returns trigger language plpgsql as $$
      begin
        if current_setting('test.bypass_faults', true) = 'on' then return coalesce(new, old); end if;
        if exists (select 1 from test_dead_servers where application_name = current_setting('application_name')) then
          raise exception 'server process is dead';
        end if;
        return coalesce(new, old);
      end $$;
      create trigger test_dead_server_guard before insert or update or delete on heartbeat_runs
        for each row execute function test_dead_server_guard();
      create trigger test_dead_server_guard before insert or update or delete on agent_wakeup_requests
        for each row execute function test_dead_server_guard();
    `));
  }, 60_000);

  beforeEach(() => {
    sshCalls.length = 0;
    mockAdapterExecute.mockClear();
    mockAdapterExecute.mockImplementation(async (input?: unknown) => {
      const { runId, agent, context } = input as { runId: string; agent: { id: string; companyId: string }; context: Record<string, unknown> };
      if (typeof context.issueId === "string") {
        await db.insert(issueComments).values({
          companyId: agent.companyId, issueId: context.issueId, authorAgentId: agent.id,
          authorType: "agent", createdByRunId: runId, body: "Reviewed.",
        });
      }
      return { exitCode: 0, signal: null, timedOut: false, errorMessage: null, summary: "Reviewed.", provider: "test", model: "test-model" };
    });
  });

  afterEach(async () => {
    for (const child of children) child.kill("SIGKILL");
    children.clear();
    await db.execute(sql`delete from test_fault_injection`);
    await db.execute(sql`delete from test_dead_servers`);
  });

  afterAll(async () => {
    for (const extra of extraDbs) await extra.$client.end({ timeout: 0 }).catch(() => undefined);
    await tempDb?.cleanup();
    if (previousHome === undefined) delete process.env.PAPERCLIP_HOME;
    else process.env.PAPERCLIP_HOME = previousHome;
    await fs.rm(home, { recursive: true, force: true });
  });

  // ---------------------------------------------------------------- fixtures

  /**
   * A task in review. The author's legacy conversation run was cancelled
   * (Stop requested) and still holds an SSH lease in pending_cleanup. The
   * reviewer is idle and assigned.
   */
  async function seedStoppedAuthorWithSshLease(input?: { authorProcessPid?: number }) {
    const companyId = randomUUID();
    const authorId = randomUUID();
    const reviewerId = randomUUID();
    const issueId = randomUUID();
    const stoppedRunId = randomUUID();
    const environmentId = randomUUID();
    const leaseId = randomUUID();
    const issuePrefix = `R${companyId.replace(/-/g, "").slice(0, 6).toUpperCase()}`;
    const stoppedAt = new Date(Date.now() - 60_000);

    await db.insert(companies).values({
      id: companyId, name: "Paperclip", issuePrefix,
      defaultResponsibleUserId: "responsible-user", requireBoardApprovalForNewAgents: false,
    });
    for (const [id, name] of [[authorId, "Author"], [reviewerId, "Reviewer"]] as const) {
      await db.insert(agents).values({
        // The stopped run's own adapter.invoke event marks it a conversation run;
        // the agents' current adapter is irrelevant to the hold.
        id, companyId, name, role: "engineer", status: "idle", adapterType: "process",
        adapterConfig: {}, runtimeConfig: {}, permissions: {},
      });
    }
    await db.insert(heartbeatRuns).values({
      id: stoppedRunId, companyId, agentId: authorId, invocationSource: "assignment", triggerDetail: "system",
      status: "cancelled", runtimeMode: "legacy", contextSnapshot: { issueId },
      resultJson: { executionCancellation: { state: "requested" } },
      processPid: input?.authorProcessPid ?? null,
      nextEventSeq: 2, startedAt: stoppedAt, finishedAt: stoppedAt, updatedAt: stoppedAt,
    });
    await db.insert(heartbeatRunEvents).values({
      companyId, agentId: authorId, runId: stoppedRunId, seq: 1, eventType: "adapter.invoke",
      payload: { adapterType: "codex_local" },
    });
    await db.insert(issues).values({
      id: issueId, companyId, title: "Review the handoff", status: "in_review", priority: "high",
      assigneeAgentId: reviewerId, responsibleUserId: "responsible-user",
      issueNumber: 1, identifier: `${issuePrefix}-1`,
    });
    await db.insert(environments).values({
      id: environmentId, name: `Build host ${environmentId}`, driver: "ssh", status: "active",
      config: {
        host: "ssh.example.test", port: 22, username: "ssh-user",
        remoteWorkspacePath: "/srv/paperclip/workspace",
        privateKey: null, knownHosts: null, strictHostKeyChecking: true,
      },
    });
    // The shape the SSH driver writes on acquire, left pending_cleanup by Stop.
    await db.insert(environmentLeases).values({
      id: leaseId, companyId, environmentId, issueId, heartbeatRunId: stoppedRunId,
      status: "pending_cleanup", leasePolicy: "ephemeral", provider: "ssh",
      providerLeaseId: "ssh://ssh-user@ssh.example.test:22/srv/paperclip/workspace",
      cleanupStatus: "failed",
      metadata: {
        driver: "ssh", host: "ssh.example.test", port: 22, username: "ssh-user",
        remoteWorkspacePath: "/srv/paperclip/workspace", remoteCwd: "/srv/paperclip/workspace",
      },
      acquiredAt: stoppedAt, lastUsedAt: stoppedAt, releasedAt: stoppedAt,
      createdAt: stoppedAt, updatedAt: stoppedAt,
    });
    return { companyId, authorId, reviewerId, issueId, stoppedRunId, environmentId, leaseId };
  }

  type Seed = Awaited<ReturnType<typeof seedStoppedAuthorWithSshLease>>;

  /** The wake the review stage sends to the next participant. */
  function sendReviewStageWake(heartbeat: Heartbeat, seed: Seed, guard?: { statuses: string[] }) {
    return heartbeat.wakeup(seed.reviewerId, {
      source: "assignment", triggerDetail: "system", reason: "execution_review_requested",
      payload: { issueId: seed.issueId, mutation: "update" },
      requestedByActorType: "agent", requestedByActorId: seed.authorId,
      contextSnapshot: {
        issueId: seed.issueId, taskId: seed.issueId,
        wakeReason: "execution_review_requested", source: "issue.execution_stage",
      },
      ...(guard ? { issueStateGuard: { statuses: guard.statuses, assigneeAgentId: seed.reviewerId } } : {}),
    });
  }

  /**
   * Runs that delivered the review handoff to the reviewer on this task: the
   * stakeholder-visible outcome. Unrelated system follow-ups (for example a
   * missing-comment nudge after the stub review) are not handoff deliveries.
   */
  async function reviewerRuns(seed: Seed) {
    return db.select({ id: heartbeatRuns.id, status: heartbeatRuns.status, error: heartbeatRuns.error, errorCode: heartbeatRuns.errorCode }).from(heartbeatRuns).where(and(
      eq(heartbeatRuns.companyId, seed.companyId), eq(heartbeatRuns.agentId, seed.reviewerId),
      sql`${heartbeatRuns.contextSnapshot}->>'issueId' = ${seed.issueId}`,
      sql`${heartbeatRuns.contextSnapshot}->>'wakeReason' = 'execution_review_requested'`,
    ));
  }

  async function waitForCompanyIdle(companyId: string, timeoutMs = 10_000) {
    const deadline = Date.now() + timeoutMs;
    for (;;) {
      const active = await db.select({ id: heartbeatRuns.id }).from(heartbeatRuns).where(and(
        eq(heartbeatRuns.companyId, companyId), sql`${heartbeatRuns.status} in ('queued', 'running')`,
      ));
      if (active.length === 0) return;
      if (Date.now() > deadline) throw new Error(`runs still active: ${active.map((r) => r.id).join(", ")}`);
      await new Promise((resolve) => setTimeout(resolve, 25));
    }
  }

  /**
   * Let time pass for this task's wake records, so the scheduler treats them
   * as due. Every timestamp on the company's wake records moves back by the
   * same amount; runs and leases keep real time. The test's own write skips
   * the injected faults.
   */
  async function letTimePass(seed: Seed) {
    const columns = await db.execute(sql`select column_name from information_schema.columns
      where table_name = 'agent_wakeup_requests' and data_type = 'timestamp with time zone'`) as unknown as Array<{ column_name: string }>;
    const assignments = columns.map(({ column_name: c }) => `"${c}" = "${c}" - interval '${LATER_MS} milliseconds'`);
    await db.transaction(async (tx) => {
      await tx.execute(sql`select set_config('test.bypass_faults', 'on', true)`);
      await tx.execute(sql.raw(`update agent_wakeup_requests set ${assignments.join(", ")}
        where company_id = '${seed.companyId}'`));
    });
  }

  /** A scheduler tick while a fault is injected. Like the production scheduler
   * loop, a failed tick is logged and the next tick carries on. */
  async function tickDuringFault(heartbeat: Heartbeat) {
    await heartbeat.resumeQueuedRuns().catch(() => undefined);
  }

  /** A second server process: its own connection pool, same database. */
  function secondServer(applicationName = `server-${randomUUID()}`) {
    const otherDb = createDb(connectionString, { applicationName });
    extraDbs.push(otherDb);
    return { db: otherDb, applicationName, heartbeat: heartbeatService(otherDb) };
  }

  async function injectFault(seed: Seed, mode: "fail" | "block") {
    await db.execute(sql`insert into test_fault_injection (mode, agent_id, issue_id)
      values (${mode}, ${seed.reviewerId}, ${seed.issueId})`);
  }

  async function clearFault() {
    await db.execute(sql`delete from test_fault_injection`);
  }

  /** Stop a lease hold the way production does: the pending-cleanup sweep. */
  async function releaseLeaseThroughCleanupSweep(heartbeat: Heartbeat, seed: Seed) {
    await heartbeat.sweepPendingCleanupLeases({ backoffMs: 0 });
    const [lease] = await db.select().from(environmentLeases).where(eq(environmentLeases.id, seed.leaseId));
    expect(lease?.status, "precondition: the sweep settled the SSH lease").not.toBe("pending_cleanup");
  }

  // ------------------------------------------------------------------ checks

  it("(1) admits exactly one reviewer run once cleanup releases the stopped run's SSH lease", async () => {
    // Actor: review stage. Start: author's cancelled run holds an SSH lease.
    // Action: handoff wake, then cleanup sweep, then scheduler ticks.
    // Expected: no run while held; exactly one run after release.
    // Defect caught: the wake is dropped as a diagnostic skip, or replayed twice.
    const seed = await seedStoppedAuthorWithSshLease();
    const heartbeat = heartbeatService(db);

    await sendReviewStageWake(heartbeat, seed);
    expect(await reviewerRuns(seed), "the lease still holds the task").toHaveLength(0);

    await releaseLeaseThroughCleanupSweep(heartbeat, seed);
    await letTimePass(seed);
    await heartbeat.resumeQueuedRuns();
    await waitForCompanyIdle(seed.companyId);
    await heartbeat.resumeQueuedRuns();
    await waitForCompanyIdle(seed.companyId);

    expect(await reviewerRuns(seed)).toHaveLength(1);
  });

  it("(2a) keeps the parked wake recoverable when the replay's enqueue fails before commit", async () => {
    // Actor: scheduler. Start: lease released; parked wake due for replay.
    // Action: the first replay's successor insert fails with a database error;
    // a later tick runs with the fault cleared.
    // Expected: exactly one reviewer run is eventually admitted.
    // Defect caught: the replay retires the parked wake before its successor
    // commits, so one failed insert loses the handoff forever (BTR-165 P1).
    const seed = await seedStoppedAuthorWithSshLease();
    const heartbeat = heartbeatService(db);
    await sendReviewStageWake(heartbeat, seed);
    await releaseLeaseThroughCleanupSweep(heartbeat, seed);

    await letTimePass(seed);
    await injectFault(seed, "fail");
    await tickDuringFault(heartbeat);
    expect(await reviewerRuns(seed), "precondition: the injected failure stopped the first replay").toHaveLength(0);
    await clearFault();

    await letTimePass(seed);
    await heartbeat.resumeQueuedRuns();
    await waitForCompanyIdle(seed.companyId);
    await heartbeat.resumeQueuedRuns();
    await waitForCompanyIdle(seed.companyId);

    expect(await reviewerRuns(seed)).toHaveLength(1);
  });

  it("(2b) delivers the parked wake once after the replaying server dies mid-enqueue", async () => {
    // Actor: server A replays, then dies; server B restarts scheduling.
    // Start: lease released; parked wake due.
    // Action: A's successor insert is held open, A's connections drop (process
    // death: its transaction rolls back and it writes nothing more); B ticks.
    // Expected: exactly one reviewer run.
    // Defect caught: a restart between claiming the parked wake and committing
    // its successor strands the handoff with no retry.
    const seed = await seedStoppedAuthorWithSshLease();
    await sendReviewStageWake(heartbeatService(db), seed);
    await releaseLeaseThroughCleanupSweep(heartbeatService(db), seed);

    // The test holds the lock the injected insert waits on, in its own transaction.
    let releaseHolder!: () => void;
    let holderReady!: () => void;
    const locked = new Promise<void>((resolve) => { holderReady = resolve; });
    const holding = db.transaction(async (tx) => {
      await tx.execute(sql`select pg_advisory_xact_lock(${INJECTION_LOCK_KEY})`);
      holderReady();
      await new Promise<void>((resolve) => { releaseHolder = resolve; });
    });
    try {
      await locked;
      await injectFault(seed, "block");
      const serverA = secondServer();
      await letTimePass(seed);
      const tickA = serverA.heartbeat.resumeQueuedRuns().catch(() => undefined);

      // Wait for A to be inside the successor insert, then kill A.
      const deadline = Date.now() + 10_000;
      for (;;) {
        const rows = await db.execute(sql`select count(*)::int as n from pg_locks
          where locktype = 'advisory' and objid = ${INJECTION_LOCK_KEY} and not granted`);
        if (Number((rows as unknown as Array<{ n: number }>)[0]?.n) > 0) break;
        if (Date.now() > deadline) throw new Error("the replay never reached the successor insert");
        await new Promise((resolve) => setTimeout(resolve, 25));
      }
      // Process death: nothing A would still do reaches the database, and its
      // open transaction rolls back when its connections drop.
      await db.execute(sql`insert into test_dead_servers values (${serverA.applicationName})`);
      await db.execute(sql`select pg_terminate_backend(pid) from pg_stat_activity
        where application_name = ${serverA.applicationName}`);
      await tickA;
    } finally {
      releaseHolder?.();
      await holding;
    }
    await clearFault();
    expect(await reviewerRuns(seed), "precondition: A died before its successor committed").toHaveLength(0);

    const serverB = heartbeatService(db);
    await letTimePass(seed);
    await serverB.resumeQueuedRuns();
    await waitForCompanyIdle(seed.companyId);
    await serverB.resumeQueuedRuns();
    await waitForCompanyIdle(seed.companyId);

    expect(await reviewerRuns(seed)).toHaveLength(1);
  });

  it("(3) does not start a second run when the successor committed but its receipt update failed", async () => {
    // Actor: scheduler. Start: lease released; parked wake due.
    // Action: the successor run commits, but every later write to the parked
    // receipt fails (lost acknowledgement). Retries run before and after the
    // successor finishes.
    // Expected: exactly one reviewer run throughout.
    // Defect caught: a retry that cannot see its own committed successor
    // replays the wake again and the reviewer runs twice.
    const seed = await seedStoppedAuthorWithSshLease();
    const heartbeat = heartbeatService(db);
    await sendReviewStageWake(heartbeat, seed);
    await releaseLeaseThroughCleanupSweep(heartbeat, seed);

    // Fault: once the reviewer's successor run has committed, a later
    // transaction can no longer write the wake record the handoff created.
    const [original] = await db.execute(sql`select id from agent_wakeup_requests
      where agent_id = ${seed.reviewerId} and payload->>'issueId' = ${seed.issueId}`) as unknown as Array<{ id: string }>;
    expect(original?.id, "precondition: the handoff left one wake record").toBeTruthy();
    await db.execute(sql.raw(`
      create or replace function test_fault_on_receipt_ack() returns trigger language plpgsql as $$
      begin
        if current_setting('test.bypass_faults', true) = 'on' then return new; end if;
        if old.id = '${original!.id}' and exists (select 1 from heartbeat_runs r
            where r.agent_id = old.agent_id and r.context_snapshot->>'issueId' = old.payload->>'issueId'
              and r.xmin <> (txid_current() % 4294967296)::text::xid) then
          raise exception 'injected acknowledgement failure';
        end if;
        return new;
      end $$;
      create trigger test_fault_on_receipt_ack before update on agent_wakeup_requests
        for each row execute function test_fault_on_receipt_ack();
    `));
    try {
      await letTimePass(seed);
      await tickDuringFault(heartbeat);
      // Retry while the successor may still be active.
      await tickDuringFault(secondServer().heartbeat);
      expect(await reviewerRuns(seed), "before the successor finishes").toHaveLength(1);

      await waitForCompanyIdle(seed.companyId);
      await letTimePass(seed);
      await tickDuringFault(heartbeat);
      await waitForCompanyIdle(seed.companyId);
    } finally {
      await db.execute(sql.raw(`drop trigger if exists test_fault_on_receipt_ack on agent_wakeup_requests`));
    }
    // With the fault gone, reconciliation may now record the link; it must
    // still not deliver the wake a second time.
    await letTimePass(seed);
    await heartbeat.resumeQueuedRuns();
    await waitForCompanyIdle(seed.companyId);

    const runs = await reviewerRuns(seed);
    expect(runs).toHaveLength(1);
    expect(runs[0]?.status, JSON.stringify(runs[0])).toBe("succeeded");
  });

  it("(4) two schedulers replaying the same parked wake at once start one reviewer run", async () => {
    // Actor: two server processes' scheduler ticks. Start: lease released.
    // Action: both ticks run concurrently.
    // Expected: exactly one reviewer run.
    // Defect caught: an unfenced replay double-starts the reviewer.
    const seed = await seedStoppedAuthorWithSshLease();
    const heartbeat = heartbeatService(db);
    await sendReviewStageWake(heartbeat, seed);
    await releaseLeaseThroughCleanupSweep(heartbeat, seed);

    await letTimePass(seed);
    const other = secondServer().heartbeat;
    await Promise.all([heartbeat.resumeQueuedRuns(), other.resumeQueuedRuns(), heartbeat.resumeQueuedRuns()]);
    await waitForCompanyIdle(seed.companyId);
    await Promise.all([heartbeat.resumeQueuedRuns(), other.resumeQueuedRuns()]);
    await waitForCompanyIdle(seed.companyId);

    expect(await reviewerRuns(seed)).toHaveLength(1);
  });

  it("(5a) does not start the reviewer while the stopped run's provider process is still alive", async () => {
    // Actor: review stage + scheduler. Start: the stopped author run's process
    // is still running, and its SSH lease is pending cleanup.
    // Action: handoff wake, cleanup sweep, scheduler ticks.
    // Expected: no reviewer run while the process lives.
    // Defect caught: lease replay treats a live-process hold as a lease hold
    // and two executions share the task.
    const child = spawn(process.execPath, ["-e", "setInterval(() => {}, 1000)"], { stdio: "ignore" });
    children.add(child);
    const seed = await seedStoppedAuthorWithSshLease({ authorProcessPid: child.pid! });
    const heartbeat = heartbeatService(db);

    await sendReviewStageWake(heartbeat, seed);
    await releaseLeaseThroughCleanupSweep(heartbeat, seed);
    await letTimePass(seed);
    await heartbeat.resumeQueuedRuns();
    await waitForCompanyIdle(seed.companyId);

    expect(await reviewerRuns(seed)).toHaveLength(0);
  });

  it("(5b) does not start the reviewer if the task left review while the wake was parked", async () => {
    // Actor: review stage + board. Start: lease held; wake guarded on
    // (assignee = reviewer, status in_review).
    // Action: the board marks the task done before cleanup; sweep; ticks.
    // Expected: no reviewer run.
    // Defect caught: replay drops the original issue-state guard.
    const seed = await seedStoppedAuthorWithSshLease();
    const heartbeat = heartbeatService(db);
    await sendReviewStageWake(heartbeat, seed, { statuses: ["in_review"] });

    await db.update(issues).set({ status: "done" }).where(eq(issues.id, seed.issueId));
    await releaseLeaseThroughCleanupSweep(heartbeat, seed);
    await letTimePass(seed);
    await heartbeat.resumeQueuedRuns();
    await waitForCompanyIdle(seed.companyId);

    expect(await reviewerRuns(seed)).toHaveLength(0);
  });

  it("(5c) does not start the reviewer if the task was reassigned while the wake was parked", async () => {
    const seed = await seedStoppedAuthorWithSshLease();
    const heartbeat = heartbeatService(db);
    await sendReviewStageWake(heartbeat, seed, { statuses: ["in_review"] });

    await db.update(issues).set({ assigneeAgentId: seed.authorId }).where(eq(issues.id, seed.issueId));
    await releaseLeaseThroughCleanupSweep(heartbeat, seed);
    await letTimePass(seed);
    await heartbeat.resumeQueuedRuns();
    await waitForCompanyIdle(seed.companyId);

    expect(await reviewerRuns(seed)).toHaveLength(0);
  });

  it("(6a) settles an SSH pending-cleanup lease without remote commands or a termination receipt", async () => {
    // Actor: cleanup sweep. Start: cancelled run's SSH lease pending_cleanup,
    // Stop requested but not proven.
    // Action: sweep.
    // Expected: lease leaves pending_cleanup; no SSH operation runs (the
    // shared remote workspace is untouched); the lease carries no remote
    // termination receipt and the stopped run's Stop is not marked proven.
    // Defect caught: SSH cleanup deletes the shared workspace, or forges proof
    // that a remote process was terminated.
    const seed = await seedStoppedAuthorWithSshLease();
    const heartbeat = heartbeatService(db);

    await heartbeat.sweepPendingCleanupLeases({ backoffMs: 0 });

    const [lease] = await db.select().from(environmentLeases).where(eq(environmentLeases.id, seed.leaseId));
    expect(lease?.status).not.toBe("pending_cleanup");
    expect(lease?.cleanupStatus).toBe("success");
    expect(lease?.metadata?.remoteExecutionTermination).toBeUndefined();
    expect(sshCalls).toEqual([]);
    const [stopped] = await db.select().from(heartbeatRuns).where(eq(heartbeatRuns.id, seed.stoppedRunId));
    const cancellation = (stopped?.resultJson as Record<string, any> | null)?.executionCancellation;
    expect(cancellation?.state).toBe("requested");
    expect(cancellation?.proof).toBeUndefined();
  });

  it("(6b) a superseded cleanup attempt cannot settle the SSH lease", async () => {
    // Actor: two cleanup attempts. Start: SSH lease pending_cleanup.
    // Action: while attempt 1 is in its teardown step, attempt 2 takes over
    // the lease; attempt 1 then finishes.
    // Expected: the lease stays pending_cleanup under attempt 2.
    // Defect caught: a stale attempt settles a lease another attempt owns.
    const seed = await seedStoppedAuthorWithSshLease();
    const real = environmentRuntimeService(db) as unknown as HeartbeatEnvironmentRuntime;
    const takeover: HeartbeatEnvironmentRuntime = Object.assign(Object.create(real), {
      async retryPendingSandboxTeardown(input: Parameters<HeartbeatEnvironmentRuntime["retryPendingSandboxTeardown"]>[0]) {
        await db.update(environmentLeases).set({
          metadata: sql`${environmentLeases.metadata} || '{"pendingCleanupAttemptId":"attempt-2"}'::jsonb`,
        }).where(eq(environmentLeases.id, seed.leaseId));
        return real.retryPendingSandboxTeardown(input);
      },
    });
    const heartbeat = heartbeatService(db, { environmentRuntime: takeover });

    await heartbeat.sweepPendingCleanupLeases({ backoffMs: 0 });

    const [lease] = await db.select().from(environmentLeases).where(eq(environmentLeases.id, seed.leaseId));
    expect(lease?.status).toBe("pending_cleanup");
    expect(lease?.metadata?.pendingCleanupAttemptId).toBe("attempt-2");
  });

  it("(6c) SSH destroy with a stale cleanup attempt leaves the lease to its current owner", async () => {
    const seed = await seedStoppedAuthorWithSshLease();
    await db.update(environmentLeases).set({
      metadata: sql`${environmentLeases.metadata} || '{"pendingCleanupAttemptId":"attempt-2"}'::jsonb`,
    }).where(eq(environmentLeases.id, seed.leaseId));
    const [environment] = await db.select().from(environments).where(eq(environments.id, seed.environmentId));
    const [current] = await db.select().from(environmentLeases).where(eq(environmentLeases.id, seed.leaseId));
    const staleSnapshot = { ...current!, metadata: { ...current!.metadata, pendingCleanupAttemptId: "attempt-1" } };

    await environmentRuntimeService(db).destroyRunLease({
      environment: environment!, lease: staleSnapshot, failureReason: "pending_cleanup_retry",
    } as Parameters<HeartbeatEnvironmentRuntime["destroyRunLease"]>[0]);

    const [lease] = await db.select().from(environmentLeases).where(eq(environmentLeases.id, seed.leaseId));
    expect(lease?.status).toBe("pending_cleanup");
    expect(sshCalls).toEqual([]);
  });
});
