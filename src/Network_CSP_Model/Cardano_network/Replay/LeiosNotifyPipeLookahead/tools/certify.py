#!/usr/bin/env python3
"""Propose Agda constructor proofs for selected controlled runtime schedules.

The planner is untrusted. A success requires Agda --safe to check every chunk,
the original wire-row equality, and its native realization. Failure to propose
a proof is inconclusive; this is not an exhaustive trace rejection procedure.
"""
import argparse
import ctypes
import hashlib
import json
import os
import signal
import time
import re
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
# The Agda library marker anchors all paths to the repository root.
ROOT = next(parent for parent in HERE.parents
            if (parent / "src/csp-ptree.agda-lib").is_file())
CASES = {"before-quit-flag", "terminate-at-capacity", "arrived-before-publication", "excessive"}
HEAP_LIMIT = "2G"
RSS_LIMIT_KIB = 3 * 1024 * 1024


def bounded_agda(arguments, log, stdin=None, timeout=900):
    """Only this task's child is stopped if the RSS/time budget is exceeded."""
    # Temporary modules live outside the repository's .agda-lib discovery path.
    argv = ["agda", "-l", "standard-library", "-l", "standard-library-classes",
            *map(str, arguments), "+RTS", f"-M{HEAP_LIMIT}", "-s", "-RTS"]
    started, peak, reason = time.monotonic(), 0, None
    parent_pid = os.getpid()

    def child_lifetime():
        # Linux parent-death cleanup also covers an externally interrupted runner.
        if ctypes.CDLL(None).prctl(1, signal.SIGKILL, 0, 0, 0) != 0:
            os._exit(125)
        if os.getppid() != parent_pid:
            os._exit(125)

    with log.open("w") as stream:
        process = subprocess.Popen(argv, cwd=ROOT / "src", stdout=stream, stderr=subprocess.STDOUT,
                                   stdin=subprocess.PIPE if stdin is not None else subprocess.DEVNULL,
                                   start_new_session=True, text=True, preexec_fn=child_lifetime)
        try:
            if stdin is not None:
                process.stdin.write(stdin)
                process.stdin.close()
            while process.poll() is None:
                try:
                    status = Path(f"/proc/{process.pid}/status").read_text()
                    rss = int(next(line for line in status.splitlines() if line.startswith("VmRSS:")).split()[1])
                    peak = max(peak, rss)
                except (OSError, StopIteration):
                    pass
                if peak > RSS_LIMIT_KIB:
                    reason = "RSS budget exceeded"
                elif time.monotonic() - started > timeout:
                    reason = "time budget exceeded"
                if reason:
                    os.killpg(process.pid, signal.SIGKILL)
                    break
                time.sleep(0.1)
            code = process.wait()
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
    if code and "Heap exhausted" in log.read_text():
        reason = "heap budget exceeded"
    stats = {"exit_code": code, "peak_sampled_rss_kib": peak, "seconds": round(time.monotonic() - started, 3),
             "heap_limit": HEAP_LIMIT, "rss_limit_kib": RSS_LIMIT_KIB, "budget_failure": reason}
    log.with_suffix(log.suffix + ".resources.json").write_text(json.dumps(stats, indent=2) + "\n")
    return stats


def seq(values, empty="[]"):
    values = list(values)
    return "(" + " ∷ ".join(values + [empty]) + ")" if values else empty


def compact(values):
    if not values:
        return "[]"
    if len(set(values)) == 1:
        return f"(replicate {len(values)} {values[0]})"
    head = values[0]
    n = next((i for i, x in enumerate(values) if x != head), len(values))
    return f"((replicate {n} {head}) ++ {compact(values[n:])})"


def boolean(value):
    return "true" if value else "false"


def notification(packet):
    kind, *numbers = packet.split(":")
    if kind == "Offer" and len(numbers) == 3:
        h, s, z = map(int, numbers)
        return f"(offer ({h} , {s}) {z})"
    if kind == "TxsOffer" and len(numbers) == 2:
        h, s = map(int, numbers)
        return f"(txsOffer ({h} , {s}))"
    raise ValueError(f"unsupported fixture notification: {packet}")


def reply(packet):
    return "S.canceled" if packet == "Canceled" else f"(S.normal {notification(packet)})"


def client_message(packet):
    return {"RequestNext": "D.request", "Quit": "D.quit"}[packet]


def server_message(packet):
    return "D.done" if packet == "Done" else f"(D.reply {reply(packet)})"


def event(row):
    actor, kind, packet = row
    constructor = {("client", "Send"): "clientSend", ("server", "Recv"): "serverRecv",
                   ("server", "Send"): "serverSend", ("client", "Recv"): "clientRecv"}[actor, kind]
    payload = client_message(packet) if (actor, kind) in [("client", "Send"), ("server", "Recv")] else server_message(packet)
    return f"(D.{constructor} {payload})"


def maybe(value, render):
    return "nothing" if value is None else f"(just {render(value)})"


class Planner:
    """State tracking chooses constructor terms; the kernel checks the tracking."""
    def __init__(self, case):
        self.case = case
        self.main, self.receiver, self.recv_packet = "poll", "idle", None
        self.jobs, self.results = [], []
        self.flight, self.arrived, self.stop_flag, self.returned = 0, 0, False, False
        self.reader, self.waiting, self.sender, self.chosen = "first", 0, "idle", None
        self.completed, self.quit_flag = 0, False
        self.cs, self.sc = [], []
        self.pc = self.ps = self.rc = self.rs = None
        self.free, self.queue = 0, []
        self.forecast, self.terminate = False, False
        self.steps, self.observed, self.commands = [], [], []
        self.checkpoint = None
        self.location = "initial"

    def state(self):
        main = f"(C.writingQuit {boolean(self.flight > 0)})" if self.main == "writingQuit" else "C." + self.main
        receiver = "C." + self.receiver
        if self.receiver in ["inspect", "handling"]:
            receiver = f"(C.{self.receiver} {reply(self.recv_packet)})"
        if self.receiver in ["publishFalse", "publishTrue"]:
            receiver = f"(C.publish {boolean(self.receiver == 'publishTrue')})"
        client = (f"(C.client {main} {receiver} {compact(['C.' + j for j in self.jobs])} "
                  f"{compact(['C.' + t for t in self.results])} {self.flight} (+ {self.arrived}) "
                  f"{boolean(self.stop_flag)} {'(just tt)' if self.returned else 'nothing'})")
        sender = f"(S.selected {reply(self.chosen)})" if self.sender == "selected" else "S." + self.sender
        server = f"(S.state S.{self.reader} {self.waiting} {sender} {self.completed} {boolean(self.quit_flag)})"
        driver = (f"(D.pair {client} {server} {compact(list(map(client_message, self.cs)))} "
                  f"{compact(list(map(server_message, self.sc)))} {maybe(self.pc, client_message)} "
                  f"{maybe(self.ps, server_message)} {maybe(self.rc, server_message)} {maybe(self.rs, client_message)})")
        return (f"(N.nodeDriver {driver} (Q.credits {self.free} {seq(map(notification, self.queue))}) "
                f"true {boolean(self.forecast)} {boolean(self.terminate)})")

    def step(self, proof, mutate, action=None):
        before = self.state()
        self.commands.append(self.command(proof, action))
        mutate()
        self.steps.append((before, self.state(), action, proof, self.location))

    def command(self, proof, action):
        if action is not None:
            return f"(Check.action {action})"
        main_rules = {"registerResponse", "setStopIdle", "setStopBusy", "registerMarker",
                      "optionalEmpty", "optionalResult", "blockingResult", "adjustArrival", "drainResult", "drained"}
        if "N.clientSchedule" in proof:
            rule = re.search(r"Client.schedule \(?C\.([A-Za-z]+)", proof).group(1)
            main_enabled = (self.main in {"issue", "stopPending", "registerQuit", "collectingMaybe", "adjustCollected"} or
                            self.main == "collectingWait" and bool(self.results) or
                            self.main == "draining" and (self.flight == 0 or bool(self.results)))
            return f"(Check.hidden (Check.client {0 if rule in main_rules else int(main_enabled)}))"
        if "Server.admitAccepted" in proof:
            return "(Check.hidden Check.accept)"
        if "Server.nextQueued" in proof:
            return "(Check.hidden Check.queued)"
        if "Server.schedule" in proof:
            rule = re.search(r"Server.schedule \(?S\.([A-Za-z]+)", proof).group(1)
            reader_enabled = (self.reader in {"register", "raising"} or self.reader == "signalQuit" and not self.quit_flag or
                              self.reader == "flushing" and (self.completed > 0 or
                                  self.waiting == 0 and self.sender == "idle" and self.quit_flag))
            index = int(reader_enabled) if rule in {"claim", "cancel", "retire"} else 0
            return f"(Check.hidden (Check.server {index}))"
        if "N.continueReady" in proof:
            return "(Check.hidden Check.continue)"
        if "N.terminateReady" in proof:
            return "(Check.hidden Check.terminate)"
        if "D.commitClient" in proof:
            op = "(Exec.writeClient D.request)" if "C.sentRequest" in proof else "(Exec.writeClient D.quit)"
        elif "D.commitServer" in proof:
            op = f"(Exec.writeServer {server_message('Done' if 'S.finish' in proof else self.chosen)})"
        elif "D.decodeClient" in proof:
            op = "Exec.readClient"
        elif "D.decodeServer" in proof:
            op = "Exec.readServer"
        else:
            raise ValueError(f"unsupported schedule operation: {proof}")
        return f"(Check.hidden (Check.transport {op}))"

    def set(self, **values):
        for name, value in values.items():
            setattr(self, name, value)

    def ctau(self, name, mutate, guard=False):
        rule = f"(C.{name} refl)" if guard else "C." + name
        self.step(f"N.internal (N.clientSchedule (Client.schedule {rule}))", mutate)

    def stau(self, name, mutate, guard=False):
        rule = f"(S.{name} refl)" if guard else "S." + name
        self.step(f"N.internal (N.serverSchedule (Server.schedule {rule} refl))", mutate)

    def transport(self, proof, mutate):
        self.step(f"N.internal (N.transport ({proof}) refl)", mutate)

    def start_receiver(self):
        if self.receiver == "idle" and self.jobs:
            job = self.jobs[0]
            if job == "responseJob":
                self.ctau("startResponse", lambda: self.set(receiver="awaiting", jobs=self.jobs[1:]), True)
            elif self.main == "draining":
                self.ctau("startMarker", lambda: self.set(receiver="publishTrue", jobs=self.jobs[1:]), True)
                self.ctau("publishMarker", lambda: self.set(receiver="idle", results=self.results + ["markerToken"]), True)

    def drain(self):
        self.start_receiver()
        while self.main == "draining":
            if self.results:
                self.ctau("drainResult", lambda: self.set(results=self.results[1:], flight=self.flight - 1))
            elif self.flight == 0:
                self.ctau("drained", lambda: self.set(main="awaitDone"))
                break
            else:
                break
            self.start_receiver()

    def arrival(self):
        if self.receiver == "bumpArrival":
            self.ctau("countArrival", lambda: self.set(receiver="publishFalse", arrived=self.arrived + 1), True)

    def publish(self):
        self.arrival()
        if self.receiver == "publishFalse":
            self.ctau("publishResponse", lambda: self.set(receiver="idle", results=self.results + ["responseToken"]), True)
            self.start_receiver()

    def prepare_client(self, packet):
        if self.pc is not None:
            if self.pc != packet:
                raise ValueError("pending client send differs")
            return
        if packet == "RequestNext":
            if self.main != "poll" or self.terminate or self.flight >= 1000:
                raise ValueError("fixture cannot issue another request")
            rule = "C.continueZero" if self.flight == 0 else "(C.continueBelow refl)"
            self.step(f"N.internal (N.continueReady (Client.continueAtDepth {rule}))",
                      lambda: self.set(main="issue" if self.flight == 0 else "collectingMaybe"))
            if self.main == "collectingMaybe":
                if self.results:
                    raise ValueError("fixture requires an uncollected result")
                self.ctau("optionalEmpty", lambda: self.set(main="issue"))
            self.ctau("registerResponse", lambda: self.set(main="writingRequest", jobs=self.jobs + ["responseJob"]))
            self.start_receiver()
            self.transport("D.commitClient C.sentRequest", lambda: self.set(pc=packet, cs=self.cs + [packet]))
        else:
            if self.main == "collectingWait":
                self.publish()
                self.ctau("blockingResult", lambda: self.set(main="adjustCollected", results=self.results[1:], flight=self.flight - 1))
                self.ctau("adjustArrival", lambda: self.set(main="poll", arrived=self.arrived - 1))
            if self.main != "poll" or not self.terminate:
                raise ValueError("fixture Quit does not follow a permitted stop decision")
            self.step("N.internal (N.terminateReady (Client.terminate C.stopRequested))",
                      lambda: self.set(main="stopPending", returned=True))
            if self.flight:
                self.ctau("setStopBusy", lambda: self.set(main="registerQuit", stop_flag=True))
                self.ctau("registerMarker", lambda: self.set(main="writingQuit", jobs=self.jobs + ["quitMarker"]))
                rule = "C.sentQuitBusy"
            else:
                self.ctau("setStopIdle", lambda: self.set(main="writingQuit", stop_flag=True))
                rule = "C.sentQuitIdle"
            self.transport(f"D.commitClient {rule}", lambda: self.set(pc=packet, cs=self.cs + [packet]))

    def flush(self):
        while self.reader == "flushing" and self.completed:
            self.stau("flush", lambda: self.set(completed=self.completed - 1))

    def select_normal(self):
        if self.sender == "idle":
            self.stau("claim", lambda: self.set(waiting=self.waiting - 1, sender="claimed"), True)
        if self.sender == "claimed":
            packet = self.queue[0]
            self.step("N.internal (N.serverSchedule (Server.nextQueued Q.dequeued (S.choose refl refl)))",
                      lambda: self.set(queue=self.queue[1:], sender="selected", chosen=packet))

    def prepare_server(self, packet):
        if self.ps is not None:
            if self.ps != packet:
                raise ValueError("pending server send differs")
            return
        if packet == "Done":
            self.flush()
            if self.reader != "doneReady":
                self.stau("drained", lambda: self.set(reader="doneReady"))
            rule = "S.finish"
        else:
            if self.sender != "selected":
                if packet == "Canceled":
                    if self.sender == "idle":
                        self.stau("claim", lambda: self.set(waiting=self.waiting - 1, sender="claimed"), True)
                    self.stau("cancel", lambda: self.set(sender="selected", chosen="Canceled"), True)
                else:
                    self.select_normal()
            if self.chosen != packet:
                raise ValueError("fixture reply differs from selected FIFO head")
            rule = "(S.send refl)"
        self.transport(f"D.commitServer {rule}", lambda: self.set(ps=packet, sc=self.sc + [packet]))

    def wire(self, row):
        actor, kind, packet = row
        action = f"(N.wire {event(row)})"
        self.observed.append(event(row))
        if (actor, kind) == ("client", "Send"):
            self.prepare_client(packet)
            rule = "C.sentRequest" if packet == "RequestNext" else "C.sentQuitBusy" if self.flight else "C.sentQuitIdle"
            def complete():
                self.pc = None
                if packet == "RequestNext":
                    self.main, self.flight = "poll", self.flight + 1
                else:
                    self.main = "draining" if self.flight else "awaitDone"
                    if self.flight:
                        self.flight += 1
            self.step(f"N.visible (N.clientRecord N.sent (D.clientSent {rule}))", complete, action)
            self.drain()
        elif (actor, kind) == ("server", "Recv"):
            if not self.cs:
                self.prepare_client(packet)
            if not self.cs or self.cs[0] != packet:
                raise ValueError("client-to-server FIFO mismatch")
            reading = "S.atFirst" if self.reader == "first" else "S.atNext"
            rule = f"(S.receive{'Request' if packet == 'RequestNext' else 'Quit'} {reading})"
            self.transport(f"D.decodeServer {rule}", lambda: self.set(cs=self.cs[1:], rs=packet))
            self.step(f"N.visible (N.serverRecord N.received (D.serverReceived {rule}))",
                      lambda: self.set(rs=None, reader="admit" if packet == "RequestNext" else "signalQuit"), action)
            if packet == "RequestNext":
                self.step("N.internal (N.serverSchedule (Server.admitAccepted (Q.admitted (λ ()))))",
                          lambda: self.set(reader="register", free=self.free + 1))
                self.stau("registered", lambda: self.set(reader="awaitNext", waiting=self.waiting + 1))
        elif (actor, kind) == ("server", "Send"):
            self.prepare_server(packet)
            rule = "S.finish" if packet == "Done" else "(S.send refl)"
            self.step(f"N.visible (N.serverRecord N.sent (D.serverSent {rule}))",
                      lambda: self.set(ps=None, reader="closed") if packet == "Done" else self.set(ps=None, sender="sent"), action)
            if packet != "Done":
                self.stau("retire", lambda: self.set(sender="idle", chosen=None, completed=self.completed + 1), True)
                self.flush()
        else:
            if not self.sc:
                self.prepare_server(packet)
            if not self.sc or self.sc[0] != packet:
                raise ValueError("server-to-client FIFO mismatch")
            self.drain()
            rule = "C.receivedDone" if packet == "Done" else "(C.receivedReply refl)"
            self.transport(f"D.decodeClient {rule}", lambda: self.set(sc=self.sc[1:], rc=packet))
            self.step(f"N.visible (N.clientRecord N.received (D.clientReceived {rule}))",
                      lambda: self.set(rc=None, main="closed") if packet == "Done" else self.set(rc=None, receiver="inspect", recv_packet=packet), action)
            if packet != "Done":
                if self.stop_flag:
                    self.ctau("discardReply", lambda: self.set(receiver="bumpArrival"), True)
                    self.publish()
                    self.drain()
                else:
                    self.ctau("keepReply", lambda: self.set(receiver="handling"), True)

    def consume(self, rows, require_closed=True):
        self.step("N.visible N.forecastInput", lambda: self.set(forecast=True), "(N.setForecast true)")
        for index, actor, kind, packet in rows:
            self.location = f"source TSV coordinate {index}: {actor}/{kind}/{packet}"
            if kind in {"Send", "Recv"}:
                self.wire((actor, kind, packet))
            elif kind == "Input" and actor == "controller" and packet == "Terminate":
                self.step("N.visible N.terminateInput", lambda: self.set(terminate=True), "(N.setTerminate true)")
            elif kind == "Input" and actor == "environment":
                self.step("N.visible (N.applicationInput (Server.applicationOffer refl Q.enqueued))",
                          lambda: self.set(free=self.free - 1, queue=self.queue + [packet]), f"(N.eligible {notification(packet)})")
            elif kind == "Hook" and packet == "SelectedNormalBeforeCommit":
                self.select_normal()
            elif kind == "Hook" and packet == "QuitEffectCompleted":
                self.stau("setQuit", lambda: self.set(reader="flushing", quit_flag=True))
                self.flush()
            elif kind == "Handler":
                self.step("N.visible (N.normalHandler (Client.handled (C.delivered refl)))",
                          lambda: self.set(receiver="bumpArrival"), f"(N.handledNormal {notification(packet)})")
            elif kind == "Hook" and packet in {"ArrivedBeforePublication", "BlockingCollectSelected"}:
                self.arrival()
                if packet == "BlockingCollectSelected":
                    self.step("N.internal (N.continueReady (Client.continueAtDepth (C.continueFull refl refl)))",
                              lambda: self.set(main="collectingWait"))
            elif kind == "Hook" and packet == "StopPendingPublication":
                if (self.main, self.receiver, self.arrived, self.terminate) != ("collectingWait", "publishFalse", 1, True):
                    raise ValueError("publication checkpoint was not reached")
                self.location += " (held publication checkpoint)"
                self.checkpoint = (len(self.steps), len(self.observed))
        if require_closed and (self.main != "closed" or self.reader != "closed" or
                               any([self.pc, self.ps, self.rc, self.rs, self.cs, self.sc, self.jobs, self.results])):
            raise ValueError("fixture did not finish with empty transport/jobs and both endpoints closed")


HEADER = """{-# OPTIONS --guardedness #-}
-- Generated constructor certificate; validated by Agda --safe, not trusted Python.
module MODULE where
open import Data.Bool using (true; false)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; replicate; concat; map)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Data.String using (String; intersperse)
open import Data.Fin using () renaming (zero to fzero)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyPipeLookahead.RuntimeInstance
"""


def balanced(values, combine):
    values = list(values)
    if len(values) == 1:
        return values[0]
    mid = len(values) // 2
    return combine(balanced(values[:mid], combine), balanced(values[mid:], combine))


def joined(start, end):
    if end == start + 1:
        return f"P{start:04}.part"
    middle = (start + end) // 2
    values = []
    for prefix in ["actions", "rows"]:
        for a, b in [(start, middle), (middle, end)]:
            values.append(balanced((f"{prefix}{i}" for i in range(a, b)), lambda x, y: f"({x} ++ {y})"))
    return (f"(Assembly.combine state{start} state{middle} state{end} " + " ".join(values) +
            f" {joined(start, middle)} {joined(middle, end)})")


def emit_project(planner, module, out, chunk_size=512):
    bounds = set(range(0, len(planner.steps), chunk_size)) | {len(planner.steps)}
    if planner.checkpoint:
        bounds.add(planner.checkpoint[0])
    bounds = sorted(bounds)
    chunks = [planner.steps[a:b] for a, b in zip(bounds, bounds[1:])]
    folder = out / module
    folder.mkdir(parents=True, exist_ok=True)
    states = [HEADER.replace("MODULE", module + ".States")]
    for i, state in enumerate([chunk[0][0] for chunk in chunks] + [planner.state()]):
        states += ["-- Exact control, buffers and accounting at this boundary.", f"state{i} : N.State", f"state{i} = {state}\n"]
    (folder / "States.agda").write_text("\n".join(states))
    n = len(chunks)
    data = [HEADER.replace("MODULE", module + ".Data"), f"open import {module}.States public\n"]
    cursor = 0
    for i, chunk in enumerate(chunks):
        start, end = bounds[i:i + 2]
        count = sum(1 for step in chunk if step[2] is not None and step[2].startswith("(N.wire "))
        rows = planner.observed[cursor:cursor + count]
        cursor += count
        part = [HEADER.replace("MODULE", f"{module}.Part{i:04}"), f"open import {module}.States\n",
                "-- Independently transcribed original rows assigned to this chronological chunk.",
                f"rows{i} : List D.Event", f"rows{i} = {seq(rows)}\n", "abstract",
                "  -- Data-only hints are checked here, and remain opaque to later assembly.",
                f"  instructions{i} : List Check.Instruction", f"  instructions{i} = {seq(planner.commands[start:end])}\n",
                "  -- Erase hidden hints while retaining all visible inputs and records.",
                f"  actions{i} : List N.Action", f"  actions{i} = Check.actions instructions{i}\n",
                "  -- Reflexivity checks actual evaluation at the original node rules.",
                f"  checked : Check.evaluate state{i} instructions{i} ≡ just state{i + 1}", "  checked = refl\n",
                "  -- Independently supplied raw rows match this checked chunk exactly.",
                f"  matches : N.wireRows actions{i} ≡ rows{i}", "  matches = refl\n",
                "  -- Export evidence rather than a new unchecked transition assumption.",
                f"  part : Assembly.Certificate state{i} actions{i} rows{i} state{i + 1}",
                f"  part = Assembly.certificate (Check.sound {{s = state{i}}} {{instructions = instructions{i}}} {{t = state{i + 1}}} checked) matches\n"]
        (folder / f"Part{i:04}.agda").write_text("\n".join(part))
        data += [f"open import {module}.Part{i:04} public using (actions{i}; rows{i})"]
    if cursor != len(planner.observed):
        raise ValueError("wire partition lost input records")
    data += ["\n-- Preserve chronological concatenation of the abstract checked action lists.", "actions : List N.Action",
             "actions = " + balanced((f"actions{i}" for i in range(n)), lambda x, y: f"({x} ++ {y})") + "\n",
             "-- The original rows remain transparent for independent output comparison.", "recorded : List D.Event",
             "recorded = " + balanced((f"rows{i}" for i in range(n)), lambda x, y: f"({x} ++ {y})") + "\n"]
    (folder / "Data.agda").write_text("\n".join(data))
    root = [HEADER.replace("MODULE", module), f"open import {module}.Data\n"]
    root += [f"import {module}.Part{i:04} as P{i:04}" for i in range(n)]
    root += ["\nabstract", "  -- Generic proved concatenation assembles the original order.",
             f"  bundle : Assembly.Certificate N.initial actions recorded state{n}", "  bundle = " + joined(0, n) + "\n",
             "-- The fresh source execution is obtained from checked chunk evidence.",
             f"source : N.Run N.initial actions state{n}", "source = Assembly.Certificate.execution bundle\n",
             "-- No original row is omitted, duplicated or reordered.",
             "wire-order : N.wireRows actions ≡ recorded", "wire-order = Assembly.Certificate.matching bundle\n",
             "-- Equality transport realizes exactly the original rows in the native paired tree.",
             f"native : B.N.tree D.initial Native.Traces.⟹∖√⟨ map B.N.encode recorded ⟩ B.N.tree (N.driverState state{n})",
             f"native = subst (λ rows → B.N.tree D.initial Native.Traces.⟹∖√⟨ map B.N.encode rows ⟩ B.N.tree (N.driverState state{n})) {{x = N.wireRows actions}} {{y = recorded}} wire-order (B.realize {{s = N.initial}} {{actions = actions}} {{t = state{n}}} source)\n",
             "-- Normalization binds the independent raw-row transcription to its capture.",
             "rendered : String", 'rendered = intersperse "\\n" (map Export.row recorded)\n']
    if planner.checkpoint:
        boundary = bounds.index(planner.checkpoint[0])
        prefix = balanced((f"actions{i}" for i in range(boundary)), lambda x, y: f"({x} ++ {y})")
        prows = balanced((f"rows{i}" for i in range(boundary)), lambda x, y: f"({x} ++ {y})")
        root += ["abstract", "  -- The held-publication checkpoint has an inhabited fresh prefix.",
                 f"  held : Assembly.Certificate N.initial {prefix} {prows} state{boundary}", f"  held = {joined(0, boundary)}\n",
                 "-- The full-pipe Collect decision has already been made.",
                 f"held-main : C.main (D.clientState (N.driverState state{boundary})) ≡ C.collectingWait", "held-main = refl\n",
                 "-- The receiver has not yet published its result.",
                 f"held-receiver : C.receiver (D.clientState (N.driverState state{boundary})) ≡ C.publish false", "held-receiver = refl\n",
                 "-- Its arrived count is already visible.",
                 f"held-arrived : C.arrived (D.clientState (N.driverState state{boundary})) ≡ (+ 1)", "held-arrived = refl\n",
                 "-- Termination has been requested at this same reachable state.",
                 f"held-stop : N.terminateRequested state{boundary} ≡ true", "held-stop = refl\n"]
    target = out / (module + ".agda")
    target.write_text("\n".join(root))
    return target


class ServerPlanner(Planner):
    """The adversarial writer is not represented as an honest paired client."""
    def state(self):
        peer = f"(S.state S.{self.reader} {self.waiting} S.idle 0 false)"
        return f"(Server.node {peer} (Q.credits {self.free} []))"

    def command(self, proof, action):
        return None

    def consume(self, rows):
        for index, actor, kind, packet in rows:
            self.location = f"source TSV coordinate {index}: {actor}/{kind}/{packet}"
            if kind not in {"Send", "Recv"}:
                continue
            if (actor, kind, packet) != ("server", "Recv", "RequestNext"):
                raise ValueError("adversarial fixture contains an unsupported wire row")
            self.observed.append(event((actor, kind, packet)))
            reading = "S.atFirst" if self.reader == "first" else "S.atNext"
            self.step(f"Server.visible (Server.peerRecord Server.request (S.receiveRequest {reading}))",
                      lambda: self.set(reader="admit"), "(Server.wire S.recvRequest)")
            if self.free < 1000:
                self.step("Server.internal (Server.admitAccepted (Q.admitted (λ ())))",
                          lambda: self.set(reader="register", free=self.free + 1))
                self.step("Server.internal (Server.schedule S.registered refl)",
                          lambda: self.set(reader="awaitNext", waiting=self.waiting + 1))
            else:
                self.step("Server.internal (Server.admitExcessive (Q.excessive refl))", lambda: self.set(reader="raising"))
                self.step("Server.internal (Server.schedule S.abort refl)", lambda: self.set(reader="failed"))
        if (self.reader, self.free, self.waiting, len(self.observed)) != ("failed", 1000, 1000, 1001):
            raise ValueError("fixture did not reach the original guarded admission failure")


def emit_server_project(planner, module, out, chunk_size=64):
    chunks = [planner.steps[i:i + chunk_size] for i in range(0, len(planner.steps), chunk_size)]
    folder = out / module
    folder.mkdir(parents=True, exist_ok=True)
    base_header = HEADER.split("import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverBridge", 1)[0]
    data = [base_header.replace("MODULE", module + ".Data")]
    n = len(chunks)
    for i, state in enumerate([chunk[0][0] for chunk in chunks] + [planner.state()]):
        data += ["-- Actual local policy control and credit accounting.", f"state{i} : Server.State", f"state{i} = {state}\n"]
    for i, chunk in enumerate(chunks):
        actions = [step[2] for step in chunk if step[2] is not None]
        data += ["-- Original server wire records for this chunk.", f"actions{i} : List Server.Action", f"actions{i} = {seq(actions)}\n"]
        part = [base_header.replace("MODULE", f"{module}.Part{i:04}"), f"open import {module}.Data\n", "abstract",
                "  -- The original request/admission/abort constructors check this local run.",
                f"  part : Server.Run state{i} actions{i} state{i + 1}", "  part ="]
        for _, _, _, proof, location in chunk:
            part += [f"    -- {location}", f"    {proof} $"]
        part += ["    Server.stop\n"]
        (folder / f"Part{i:04}.agda").write_text("\n".join(part))
    data += ["-- Original records remain ordered and retain their exact multiplicity.", "actions : List Server.Action",
             "actions = " + balanced((f"actions{i}" for i in range(n)), lambda x, y: f"({x} ++ {y})") + "\n",
             "-- Independent raw-record transcription, without a fabricated client peer.", "recorded : List D.Event",
             "recorded = " + balanced([seq(planner.observed[i:i + 64]) for i in range(0, len(planner.observed), 64)], lambda x, y: f"({x} ++ {y})") + "\n"]
    (folder / "Data.agda").write_text("\n".join(data))
    root = [base_header.replace("MODULE", module), f"open import {module}.Data\n",
            "open import Data.Product using (proj₁; proj₂)", "open import Data.List using (mapMaybe)",
            "open import Relation.Binary.PropositionalEquality using (trans; cong)",
            "open import Process_Trees using (ExtI)", "open import Cardano_network.LeiosNotifyP exactParams using (LNPEv)",
            "import Cardano_network.LeiosNotifyPipeLookahead.DriverProjections Notification ⊤ as Projection",
            "import Cardano_network.LeiosNotifyPipeLookahead exactParams as LocalNative",
            "import Cardano_network.LeiosNotifyPipeLookahead.ServerEvents exactParams as Events",
            "import Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerBridge exactParams as LocalBridge",

            "import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv} as Traces",
            "module Tree = LocalNative.Machine S.nodeNext fzero hi", "module LocalProof = LocalBridge.For S.nodeNext fzero hi"]
    root += [f"import {module}.Part{i:04} as P{i:04}" for i in range(n)]
    root += ["-- A fresh actual node server accepts 1000 credits and fails on request 1001.",
             f"source : Server.Run Server.initial actions state{n}",
             "source = " + balanced((f"P{i:04}.part" for i in range(n)), lambda x, y: f"(Assembly.append-server {x} {y})") + "\n",
             "-- The generic core trace is derived only after validating node accounting.", "core : List S.Action", "core = proj₁ (Assembly.server-source source)\n",
             "-- The policy certificate supplies its complete generic source execution.",
             f"core-source : S.Run S.nodeNext S.initial core (Server.peer state{n})", "core-source = proj₁ (proj₂ (Assembly.server-source source))\n",
             "-- Raw server records match the actual policy actions exactly.",
             "wire-order : mapMaybe Projection.serverWire (Assembly.server-records actions) ≡ recorded", "wire-order = refl\n",
             "-- Readiness erasure preserves every raw server record of the native realization.",
             "native-wire-order : mapMaybe Projection.serverWire (S.wireActions core) ≡ recorded",
             "native-wire-order = trans (cong (mapMaybe Projection.serverWire) (proj₂ (proj₂ (Assembly.server-source source)))) wire-order\n",
             "-- The checked core execution is realized by the native server PTree.",
             f"native : Tree.tree S.initial Traces.⟹∖√⟨ map (Events.encode fzero hi) core ⟩ Tree.tree (Server.peer state{n})", "native = LocalProof.realize core-source\n",
             "-- Normalization exports only the independently transcribed raw records.", "rendered : String", 'rendered = intersperse "\\n" (map Export.row recorded)\n']
    target = out / (module + ".agda")
    target.write_text("\n".join(root))
    return target


def parse(path, case):
    rows, counts, passed = [], {}, set()
    kinds = {"Send", "Recv", "Input", "Hook", "Callback", "Handler", "Release", "Outcome", "FinalCredit"}
    for number, line in enumerate(path.read_text().splitlines(), 1):
        fields = line.split("\t")
        if len(fields) == 2 and fields[1] == "PASS":
            if fields[0] in passed:
                raise ValueError(f"duplicate PASS at line {number}")
            passed.add(fields[0])
            continue
        if len(fields) != 6:
            raise ValueError(f"malformed harness row at line {number}")
        name, index, actor, kind, packet, _ = fields
        if int(index) != counts.get(name, 0) or kind not in kinds:
            raise ValueError(f"invalid coordinate/record kind at line {number}")
        if actor not in {"client", "server", "controller", "environment"}:
            raise ValueError(f"unknown actor at line {number}")
        counts[name] = int(index) + 1
        if name == case:
            rows.append((int(index), actor, kind, packet))
    if not rows or case not in passed:
        raise ValueError("case has no complete harness record")
    return rows


def normalize(target, out):
    path = json.dumps(str(target))
    commands = (f"IOTCM {path} None Direct (Cmd_load {path} [])\n"
                f'IOTCM {path} None Direct (Cmd_compute_toplevel DefaultCompute "rendered")\n')
    log = out / "normalization.jsonl"
    stats = bounded_agda(["--safe", "--interaction-json", "-i", ROOT / "src", "-i", out], log,
                         stdin=commands, timeout=300)
    normal, checked = [], False
    for line in log.read_text().splitlines():
        line = line.removeprefix("JSON> ").strip()
        if line.startswith("{"):
            response = json.loads(line)
            if response.get("kind") == "Status":
                checked = response["status"].get("checked", False)
            info = response.get("info", {})
            if info.get("kind") == "NormalForm" and info.get("computeMode") == "DefaultCompute":
                normal.append(json.loads(info["expr"]))
    if stats["exit_code"] or not checked or len(normal) != 1:
        raise ValueError("missing checked Agda normal form")
    return normal[0]


def checked_case(raw, case, out):
    out.mkdir(parents=True, exist_ok=True)
    rows = parse(raw, case)
    planner = ServerPlanner(case) if case == "excessive" else Planner(case)
    planner.consume(rows)
    final = next((packet for _, actor, kind, packet in rows if (actor, kind) == ("controller", "FinalCredit")), None)
    if final != str(planner.free):
        raise ValueError("reported final credit differs from the proposed certified state")
    module = "Runtime_" + case.replace("-", "_")
    target = emit_server_project(planner, module, out) if case == "excessive" else emit_project(planner, module, out)
    stats = bounded_agda(["--safe", "-i", ROOT / "src", "-i", out, target], out / "check.log")
    if stats["exit_code"]:
        raise ValueError(f"Agda did not accept supplied schedule; see {out / 'check.log'}")
    rendered = normalize(target, out)
    expected = "\n".join("\t".join((actor, kind, packet)) for _, actor, kind, packet in rows if kind in {"Send", "Recv"})
    if rendered != expected:
        raise ValueError("checked certificate rows differ from original unsorted wire capture")
    (out / "model.tsv").write_text(rendered + "\n")
    hashes = {str(p.relative_to(out)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.rglob("*.agda"))}
    (out / "source-hashes.json").write_text(json.dumps(hashes, indent=2) + "\n")
    return {"case": case, "wire_rows": len(planner.observed), "instructions": len(planner.steps),
            "scope": "server-only" if case == "excessive" else "paired-node-policy",
            "publication_checkpoint": bool(planner.checkpoint), "final_credit": planner.free,
            "module": module, "directory": str(out),
            "resources": stats,
            "proof_sources_sha256": hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest()}


def diagnose(raw, out):
    global HEAP_LIMIT, RSS_LIMIT_KIB
    report = {"heap_limit": HEAP_LIMIT, "rss_limit_kib": RSS_LIMIT_KIB, "stages": []}
    for label, path in [("checker-guards", "RuntimeCheckTests.agda"), ("shared-instance", "RuntimeInstance.agda")]:
        target = ROOT / "src/Cardano_network/Replay/LeiosNotifyPipeLookahead" / path
        stats = bounded_agda(["--safe", target], out / (label + ".log"))
        report["stages"].append({"stage": label, **stats})
        (out / "diagnosis.json").write_text(json.dumps(report, indent=2) + "\n")
        print(f"{label}: exit={stats['exit_code']}, sampled peak RSS={stats['peak_sampled_rss_kib'] / 1024:.1f} MiB", flush=True)
        if stats["exit_code"]:
            raise ValueError("bounded prerequisite check failed; no larger check started")
    rows = parse(raw, "terminate-at-capacity")
    for count in [32, 128, 512]:
        prefix, wires = [], 0
        for row in rows:
            prefix.append(row)
            if row[2] in {"Send", "Recv"}:
                wires += 1
            if wires == count:
                break
        directory = out / f"prefix-{count}"
        directory.mkdir(parents=True, exist_ok=True)
        planner = Planner("terminate-at-capacity")
        planner.consume(prefix, require_closed=False)
        target = emit_project(planner, f"Prefix{count}", directory)
        stats = bounded_agda(["--safe", "-i", ROOT / "src", "-i", directory, target], directory / "check.log")
        report["stages"].append({"stage": f"original-prefix-{count}", "wire_rows": count, **stats})
        (out / "diagnosis.json").write_text(json.dumps(report, indent=2) + "\n")
        print(f"prefix-{count}: exit={stats['exit_code']}, sampled peak RSS={stats['peak_sampled_rss_kib'] / 1024:.1f} MiB", flush=True)
        if stats["exit_code"]:
            raise ValueError("bounded prefix check failed; no larger check started")
    original_heap, original_rss = HEAP_LIMIT, RSS_LIMIT_KIB
    try:
        target = ROOT / "src/Cardano_network/Replay/LeiosNotifyPipeLookahead/RuntimeCheckTests.agda"
        RSS_LIMIT_KIB = 32 * 1024
        stats = bounded_agda(["--safe", target], out / "rss-guard-control.log")
        if stats["budget_failure"] != "RSS budget exceeded":
            raise ValueError("RSS watchdog control did not stop its own child")
        report["stages"].append({"stage": "rss-guard-control", "expected_budget_failure": True, **stats})
        RSS_LIMIT_KIB, HEAP_LIMIT = original_rss, "32M"
        stats = bounded_agda(["--safe", target], out / "heap-guard-control.log")
        if stats["budget_failure"] != "heap budget exceeded":
            raise ValueError("heap guard control did not produce the expected bounded failure")
        report["stages"].append({"stage": "heap-guard-control", "expected_budget_failure": True, **stats})
    finally:
        HEAP_LIMIT, RSS_LIMIT_KIB = original_heap, original_rss
    (out / "diagnosis.json").write_text(json.dumps(report, indent=2) + "\n")
    print("RSS watchdog and heap-cap controls stopped their own children as expected", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("raw", type=Path, nargs="?")
    parser.add_argument("--captures", type=Path, help="certify all new cases in N*.tsv captures")
    parser.add_argument("--diagnose", action="store_true", help="profile bounded prerequisites and original prefixes")
    parser.add_argument("--case", choices=sorted(CASES))
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.out.resolve().is_relative_to(ROOT):
        parser.error("generated artifacts must stay outside the repository")
    args.out.mkdir(parents=True, exist_ok=True)
    if args.diagnose:
        if not args.raw:
            parser.error("diagnosis needs a raw captured TSV")
        diagnose(args.raw, args.out)
        return
    if not args.captures:
        if not args.raw or not args.case:
            parser.error("supply RAW --case CASE, or --captures DIR")
        result = checked_case(args.raw, args.case, args.out)
        (args.out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps(result), flush=True)
        return
    cache, checks = {}, []
    for raw in sorted(args.captures.glob("N*.tsv")):
        for case in sorted(CASES):
            rows = parse(raw, case)
            wire = [row[1:] for row in rows if row[2] in {"Send", "Recv"}]
            proposed = ServerPlanner(case) if case == "excessive" else Planner(case)
            proposed.consume(rows)
            reported = [packet for _, actor, kind, packet in rows if (actor, kind) == ("controller", "FinalCredit")]
            if reported != [str(proposed.free)]:
                raise ValueError("capture credit metadata differs from proposed final state")
            # Exact tuple equality, not a truncated hash, authorizes certificate reuse.
            key = (case, tuple(wire), tuple(proposed.commands), proposed.checkpoint)
            reused = key in cache
            if not reused:
                cache[key] = checked_case(raw, case, args.out / f"{case}_{len(cache):04}")
            checks.append({"capture": raw.name, "capture_sha256": hashlib.sha256(raw.read_bytes()).hexdigest(),
                           "reused_identical_schedule_certificate": reused, "certificate": cache[key]})
            (args.out / "progress.json").write_text(json.dumps(checks, indent=2) + "\n")
            print(f"{raw.name}/{case}: Agda accepted exact {'server-only' if case == 'excessive' else 'paired'} history"
                  + (" (identical supplied schedule and wire history)" if reused else ""), flush=True)
    if not checks:
        raise ValueError("no captures found")
    sources = [Path(__file__), ROOT / "src/Cardano_network/Replay/LeiosNotifyPipeLookahead/RuntimeCheck.agda",
               ROOT / "src/Cardano_network/Replay/LeiosNotifyPipeLookahead/RuntimeCertificates.agda"]
    sources += [ROOT / "src/Cardano_network/Replay/LeiosNotifyPipeLookahead/RuntimeInstance.agda",
                ROOT / "src/Cardano_network/Replay/LeiosNotifyPipeLookahead/RuntimeCheckTests.agda"]
    report = {"baseline_commit": "e8565021", "agda": subprocess.check_output(["agda", "--version"], text=True).strip(),
              "source_hashes": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
              "certified_captures": len(checks), "unique_certificates": len(cache), "checks": checks,
              "scope": "supplied finite schedule witnesses; no exhaustive rejection or implementation refinement"}
    (args.out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
