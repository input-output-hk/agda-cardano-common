{-# OPTIONS --safe #-}

-- One-request-at-a-time production-policy runs retain arbitrarily many server completion tokens.
module Cardano_network.LeiosNotifyPipeLookahead.SequentialCompletion
  (Notification : Set) (message : Notification) where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; length; mapMaybe)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; +-assoc; +-comm)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.ClientAccounting Notification ⊤ as ClientWork
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as N
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverProperties Notification as Projection
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.CompletionDriver Notification ⊤ as Count
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Notification ⊤ as Operations
import Cardano_network.LeiosNotifyPipeLookahead.DriverProjections Notification ⊤ as Endpoint
import Cardano_network.LeiosNotifyPipeLookahead.CompletionAccounting Notification as Source
import Cardano_network.LeiosNotifyPipeLookahead.ServerConservation Notification as Requests

-- The empty client/queues coexist with n retained server completions before the next request.
ready : S.Reader → ℕ → N.State
ready r n = N.nodeDriver (D.pair C.initial (S.state r 0 S.idle n false)
  [] [] nothing nothing nothing nothing) Q.initial true true false

-- Each successful round contains exactly one eligible input and its successful normal handler.
round-actions : List N.Action
round-actions = N.wire (D.clientSend D.request) ∷ N.wire (D.serverRecv D.request) ∷
  N.eligible message ∷ N.wire (D.serverSend (D.reply (S.normal message))) ∷
  N.wire (D.clientRecv (D.reply (S.normal message))) ∷ N.handledNormal message ∷ []

-- The actual fixed-depth client waits for collection before starting the next chosen round.
round : ∀ {r} → S.Reading r → (n : ℕ) → N.Run (ready r n) round-actions (ready S.awaitNext (suc n))
round canRead n =
  N.internal (N.continueReady (Client.continueAtDepth C.continueZero)) $
  N.internal (N.clientSchedule (Client.schedule C.registerResponse)) $
  N.internal (N.clientSchedule (Client.schedule (C.startResponse refl))) $
  N.internal (N.transport (D.commitClient C.sentRequest) refl) $
  N.visible (N.clientRecord N.sent (D.clientSent C.sentRequest)) $
  N.internal (N.transport (D.decodeServer (S.receiveRequest canRead)) refl) $
  N.visible (N.serverRecord N.received (D.serverReceived (S.receiveRequest canRead))) $
  N.internal (N.serverSchedule (Server.admitAccepted (Q.admitted (λ ())))) $
  N.internal (N.serverSchedule (Server.schedule S.registered refl)) $
  N.visible (N.applicationInput (Server.applicationOffer refl Q.enqueued)) $
  N.internal (N.serverSchedule (Server.schedule (S.claim refl) refl)) $
  N.internal (N.serverSchedule (Server.nextQueued Q.dequeued (S.choose refl refl))) $
  N.internal (N.transport (D.commitServer (S.send refl)) refl) $
  N.visible (N.serverRecord N.sent (D.serverSent (S.send refl))) $
  N.internal (N.serverSchedule (Server.schedule (S.retire refl) refl)) $
  N.internal (N.transport (D.decodeClient (C.receivedReply refl)) refl) $
  N.visible (N.clientRecord N.received (D.clientReceived (C.receivedReply refl))) $
  N.internal (N.clientSchedule (Client.schedule (C.keepReply refl))) $
  N.visible (N.normalHandler (Client.handled (C.delivered refl))) $
  N.internal (N.clientSchedule (Client.schedule (C.countArrival refl))) $
  N.internal (N.clientSchedule (Client.schedule (C.publishResponse refl))) $
  N.internal (N.continueReady (Client.continueAtDepth (C.continueBelow refl))) $
  N.internal (N.clientSchedule (Client.schedule C.optionalResult)) $
  N.internal (N.clientSchedule (Client.schedule C.adjustArrival)) N.stop

-- Concatenation preserves every actual node input, callback, transport and trace operation.
append : ∀ {s actions t more u} → N.Run s actions t → N.Run t more u → N.Run s (actions ++ more) u
append N.stop suffix = suffix
append (N.internal pr run) suffix = N.internal pr (append run suffix)
append (N.visible pr run) suffix = N.visible pr (append run suffix)

-- Fresh first Await differs from the later lookahead Await, even at zero completions.
reader : ℕ → S.Reader
reader zero = S.first
reader (suc n) = S.awaitNext

-- Both ordinary reader phases admit the next chosen one-request round.
reading : ∀ n → S.Reading (reader n)
reading zero = S.atFirst
reading (suc n) = S.atNext

-- Preserve the exact repeated round input/record order without inventing a batch operation.
history : ℕ → List N.Action
history zero = []
history (suc n) = history n ++ round-actions

-- Every finite number of sequential rounds reaches the corresponding completion count.
rounds : ∀ n → N.Run (ready S.first 0) (history n) (ready (reader n) n)
rounds zero = N.stop
rounds (suc n) = append (rounds n) (round (reading n) n)

-- The only initial environment change is successful forecast availability.
begin : N.Run N.initial (N.setForecast true ∷ []) (ready S.first 0)
begin = N.visible N.forecastInput N.stop

-- The entire family is freshly reachable in the combined production-policy model.
prefix : ∀ n → N.Run N.initial ((N.setForecast true ∷ []) ++ history n) (ready (reader n) n)
prefix n = append begin (rounds n)

-- This small boolean classifies concrete occupancy zero or one, leaving history unbounded.
at-most-one : ℕ → Bool
at-most-one zero = true
at-most-one (suc zero) = true
at-most-one (suc (suc n)) = false

-- A true check is a constructive natural-number bound, not a sampled runtime assertion.
one-bound : ∀ n → at-most-one n ≡ true → n ≤ 1
one-bound zero pr = z≤n
one-bound (suc zero) pr = s≤s z≤n
one-bound (suc (suc n)) ()

-- Check client work/depth, owed/waiting server work, credits and actual queue occupancies.
small : N.State → Bool
small state = at-most-one (C.inFlight (D.clientState raw)) ∧
  (at-most-one (ClientWork.work (D.clientState raw)) ∧
  (at-most-one (S.owed (D.serverState raw)) ∧
  (at-most-one (S.waiting (D.serverState raw)) ∧
  (at-most-one (Q.free (N.queueState state)) ∧
  (at-most-one (length (Q.queued (N.queueState state))) ∧
  (at-most-one (length (D.clientToServer raw)) ∧ at-most-one (length (D.serverToClient raw))))))))
  where
  -- The raw driver is the same component carried by the node policy.
  raw : D.State
  raw = N.driverState state

-- This proposition covers every actual intermediate source state as well as the final target.
AllSmall : ∀ {s actions t} → N.Run s actions t → Set
AllSmall {s} N.stop = small s ≡ true
AllSmall {s} (N.internal pr run) = (small s ≡ true) × AllSmall run
AllSmall {s} (N.visible pr run) = (small s ≡ true) × AllSmall run

-- A definitional computation gate can validate a fixed round without hand-listing its states.
gate : ∀ {s actions t} → N.Run s actions t → Bool
gate {s} N.stop = small s
gate {s} (N.internal pr run) = small s ∧ gate run
gate {s} (N.visible pr run) = small s ∧ gate run

-- A true conjunction certifies its first concrete condition.
and-left : ∀ a b → a ∧ b ≡ true → a ≡ true
and-left true b pr = refl
and-left false b ()

-- A true conjunction certifies its second concrete condition.
and-right : ∀ a b → a ∧ b ≡ true → b ≡ true
and-right true b pr = pr
and-right false b ()

-- Natural-number bounds expose the meaning of all eight boolean occupancy checks.
record Bounds (state : N.State) : Set where
  field
    in-flight : C.inFlight (D.clientState (N.driverState state)) ≤ 1
    client-work : ClientWork.work (D.clientState (N.driverState state)) ≤ 1
    owed : S.owed (D.serverState (N.driverState state)) ≤ 1
    waiting : S.waiting (D.serverState (N.driverState state)) ≤ 1
    free : Q.free (N.queueState state) ≤ 1
    queued : length (Q.queued (N.queueState state)) ≤ 1
    commands : length (D.clientToServer (N.driverState state)) ≤ 1
    responses : length (D.serverToClient (N.driverState state)) ≤ 1

-- A true conjunction exposes all eight checks without relying on boolean-function injectivity.
split-eight : ∀ a b c d e f g h → (a ∧ (b ∧ (c ∧ (d ∧ (e ∧ (f ∧ (g ∧ h))))))) ≡ true →
  (a ≡ true × b ≡ true × c ≡ true × d ≡ true × e ≡ true × f ≡ true × g ≡ true × h ≡ true)
split-eight a b c d e f g h yes =
  and-left a (b ∧ (c ∧ (d ∧ (e ∧ (f ∧ (g ∧ (h))))))) (yes) ,
  and-left b (c ∧ (d ∧ (e ∧ (f ∧ (g ∧ (h)))))) (and-right a (b ∧ (c ∧ (d ∧ (e ∧ (f ∧ (g ∧ (h))))))) (yes)) ,
  and-left c (d ∧ (e ∧ (f ∧ (g ∧ (h))))) (and-right b (c ∧ (d ∧ (e ∧ (f ∧ (g ∧ (h)))))) (and-right a (b ∧ (c ∧ (d ∧ (e ∧ (f ∧ (g ∧ (h))))))) (yes))) ,
  and-left d (e ∧ (f ∧ (g ∧ (h)))) (and-right c (d ∧ (e ∧ (f ∧ (g ∧ (h))))) (and-right b (c ∧ (d ∧ (e ∧ (f ∧ (g ∧ (h)))))) (and-right a (b ∧ (c ∧ (d ∧ (e ∧ (f ∧ (g ∧ (h))))))) (yes)))) ,
  and-left e (f ∧ (g ∧ (h))) (and-right d (e ∧ (f ∧ (g ∧ (h)))) (and-right c (d ∧ (e ∧ (f ∧ (g ∧ (h))))) (and-right b (c ∧ (d ∧ (e ∧ (f ∧ (g ∧ (h)))))) (and-right a (b ∧ (c ∧ (d ∧ (e ∧ (f ∧ (g ∧ (h))))))) (yes))))) ,
  and-left f (g ∧ (h)) (and-right e (f ∧ (g ∧ (h))) (and-right d (e ∧ (f ∧ (g ∧ (h)))) (and-right c (d ∧ (e ∧ (f ∧ (g ∧ (h))))) (and-right b (c ∧ (d ∧ (e ∧ (f ∧ (g ∧ (h)))))) (and-right a (b ∧ (c ∧ (d ∧ (e ∧ (f ∧ (g ∧ (h))))))) (yes)))))) ,
  and-left g (h) (and-right f (g ∧ (h)) (and-right e (f ∧ (g ∧ (h))) (and-right d (e ∧ (f ∧ (g ∧ (h)))) (and-right c (d ∧ (e ∧ (f ∧ (g ∧ (h))))) (and-right b (c ∧ (d ∧ (e ∧ (f ∧ (g ∧ (h)))))) (and-right a (b ∧ (c ∧ (d ∧ (e ∧ (f ∧ (g ∧ (h))))))) (yes))))))) ,
  and-right g (h) (and-right f (g ∧ (h)) (and-right e (f ∧ (g ∧ (h))) (and-right d (e ∧ (f ∧ (g ∧ (h)))) (and-right c (d ∧ (e ∧ (f ∧ (g ∧ (h))))) (and-right b (c ∧ (d ∧ (e ∧ (f ∧ (g ∧ (h)))))) (and-right a (b ∧ (c ∧ (d ∧ (e ∧ (f ∧ (g ∧ (h))))))) (yes)))))))

-- Every true small-state certificate supplies the corresponding eight actual inequalities.
bounds : ∀ {state} → small state ≡ true → Bounds state
bounds {state} yes with split-eight
  (at-most-one (C.inFlight (D.clientState (N.driverState state))))
  (at-most-one (ClientWork.work (D.clientState (N.driverState state))))
  (at-most-one (S.owed (D.serverState (N.driverState state))))
  (at-most-one (S.waiting (D.serverState (N.driverState state))))
  (at-most-one (Q.free (N.queueState state)))
  (at-most-one (length (Q.queued (N.queueState state))))
  (at-most-one (length (D.clientToServer (N.driverState state))))
  (at-most-one (length (D.serverToClient (N.driverState state)))) yes
... | p0 , p1 , p2 , p3 , p4 , p5 , p6 , p7 = record
  { in-flight = one-bound (C.inFlight (D.clientState (N.driverState state))) p0
  ; client-work = one-bound (ClientWork.work (D.clientState (N.driverState state))) p1
  ; owed = one-bound (S.owed (D.serverState (N.driverState state))) p2
  ; waiting = one-bound (S.waiting (D.serverState (N.driverState state))) p3
  ; free = one-bound (Q.free (N.queueState state)) p4
  ; queued = one-bound (length (Q.queued (N.queueState state))) p5
  ; commands = one-bound (length (D.clientToServer (N.driverState state))) p6
  ; responses = one-bound (length (D.serverToClient (N.driverState state))) p7
  }

-- This all-state statement uses actual natural inequalities rather than only the computation gate.
AllBounds : ∀ {s actions t} → N.Run s actions t → Set
AllBounds {s} N.stop = Bounds s
AllBounds {s} (N.internal pr run) = Bounds s × AllBounds run
AllBounds {s} (N.visible pr run) = Bounds s × AllBounds run

-- Every boolean prefix certificate gives the corresponding full all-state resource certificate.
to-bounds : ∀ {s actions t} (run : N.Run s actions t) → AllSmall run → AllBounds run
to-bounds N.stop pr = bounds pr
to-bounds (N.internal pr run) (now , rest) = bounds now , to-bounds run rest
to-bounds (N.visible pr run) (now , rest) = bounds now , to-bounds run rest

-- Computed gate success gives an actual all-intermediate-state certificate.
certify : ∀ {s actions t} (run : N.Run s actions t) → gate run ≡ true → AllSmall run
certify {s} N.stop pr = pr
certify {s} (N.internal pr run) yes = and-left (small s) (gate run) yes , certify run (and-right (small s) (gate run) yes)
certify {s} (N.visible pr run) yes = and-left (small s) (gate run) yes , certify run (and-right (small s) (gate run) yes)

-- Certified small paths concatenate without omitting their shared boundary state.
append-small : ∀ {s actions t more u} (run : N.Run s actions t) (suffix : N.Run t more u) →
  AllSmall run → AllSmall suffix → AllSmall (append run suffix)
append-small N.stop suffix first second = second
append-small (N.internal pr run) suffix (small-now , rest) second = small-now , append-small run suffix rest second
append-small (N.visible pr run) suffix (small-now , rest) second = small-now , append-small run suffix rest second

-- Each ordinary round remains small independently of its unbounded completed counter.
round-small : ∀ {r} (canRead : S.Reading r) n → AllSmall (round canRead n)
round-small S.atFirst n = certify (round S.atFirst n) refl
round-small S.atNext n = certify (round S.atNext n) refl

-- Every finite normal sequential history is small at every intermediate state.
rounds-small : ∀ n → AllSmall (rounds n)
rounds-small zero = refl
rounds-small (suc n) = append-small (rounds n) (round (reading n) n) (rounds-small n) (round-small (reading n) n)

-- Initial readiness and all repeated rounds retain the same occupancy-one certificate.
prefix-small : ∀ n → AllSmall (prefix n)
prefix-small n = append-small begin (rounds n) (certify begin refl) (rounds-small n)

-- All eight resources stay at most one at every intermediate state of every fresh prefix.
prefix-bounds : ∀ n → AllBounds (prefix n)
prefix-bounds n = to-bounds (prefix n) (prefix-small n)

-- The projected server actually receives n requests and performs no normal-operation flushes.
server-history : ∀ n → Σ[ actions ∈ List S.Action ]
  Σ[ run ∈ S.Run S.nodeNext S.initial actions (D.serverState (N.driverState (ready (reader n) n))) ]
  (Requests.requests actions ≡ n × Source.flushes run ≡ 0 ×
   mapMaybe Endpoint.serverWire actions ≡ Endpoint.serverRows (N.wireRows ((N.setForecast true ∷ []) ++ history n)))
server-history zero = [] , S.stop , refl , refl , refl
server-history (suc n) with Endpoint.For.server S.nodeNext (Projection.driver (prefix (suc n)))
... | actions , run , same = actions , run , Source.ready-history run , Source.before-no-flushes run (λ ()) , same

-- At final ordinary quiescence the client has drained and no wire reply remains owed.
ready-idle : ∀ n → C.inFlight (D.clientState (N.driverState (ready (reader n) n))) ≡ 0
ready-idle n = refl

-- The server similarly owes no response despite retaining n completion tokens.
ready-owed : ∀ n → S.owed (D.serverState (N.driverState (ready (reader n) n))) ≡ 0
ready-owed zero = refl
ready-owed (suc n) = refl

-- Both ordinary reader phases retain exactly the chosen number of future flush units.
ready-work : ∀ {r} → S.Reading r → ∀ n → Count.work (N.driverState (ready r n)) ≡ n
ready-work S.atFirst n = refl
ready-work S.atNext n = refl

-- Before Done, shutdown flushes accumulated tokens with an otherwise empty idle pipeline.
flushing : ℕ → N.State
flushing n = N.nodeDriver
  (D.pair (C.client C.awaitDone C.idle [] [] 0 (+ 0) true (just tt))
    (S.state S.flushing 0 S.idle n true) [] [] nothing nothing nothing nothing)
  Q.initial true true true

-- The final state retains the unit return with all peer, packet and hook work cleared.
closed : N.State
closed = N.nodeDriver
  (D.pair (C.client C.closed C.idle [] [] 0 (+ 0) true (just tt))
    (S.state S.closed 0 S.idle 0 true) [] [] nothing nothing nothing nothing)
  Q.initial true true true

-- The actual policy performs one source flush per token before completing Done.
drain : ∀ n → N.Run (flushing n)
  (N.wire (D.serverSend D.done) ∷ N.wire (D.clientRecv D.done) ∷ []) closed
drain zero =
  N.internal (N.serverSchedule (Server.schedule S.drained refl)) $
  N.internal (N.transport (D.commitServer S.finish) refl) $
  N.visible (N.serverRecord N.sent (D.serverSent S.finish)) $
  N.internal (N.transport (D.decodeClient C.receivedDone) refl) $
  N.visible (N.clientRecord N.received (D.clientReceived C.receivedDone)) N.stop
drain (suc n) = N.internal (N.serverSchedule (Server.schedule S.flush refl)) (drain n)

-- The termination input is separate from the already available forecast.
shutdown-actions : List N.Action
shutdown-actions = N.setTerminate true ∷ N.wire (D.clientSend D.quit) ∷ N.wire (D.serverRecv D.quit) ∷
  N.wire (D.serverSend D.done) ∷ N.wire (D.clientRecv D.done) ∷ []

-- An ordinary quiescent state shuts down without issuing a new RequestNext.
shutdown : ∀ {r} → S.Reading r → (n : ℕ) → N.Run (ready r n) shutdown-actions closed
shutdown canRead n =
  N.visible N.terminateInput $
  N.internal (N.terminateReady (Client.terminate C.stopRequested)) $
  N.internal (N.clientSchedule (Client.schedule C.setStopIdle)) $
  N.internal (N.transport (D.commitClient C.sentQuitIdle) refl) $
  N.visible (N.clientRecord N.sent (D.clientSent C.sentQuitIdle)) $
  N.internal (N.transport (D.decodeServer (S.receiveQuit canRead)) refl) $
  N.visible (N.serverRecord N.received (D.serverReceived (S.receiveQuit canRead))) $
  N.internal (N.serverSchedule (Server.schedule S.setQuit refl)) (drain n)

-- Count actual paired flushes in this family, retaining the node policy projection.
drain-count : ∀ n → Count.flushes (Projection.driver (drain n)) ≡ n
drain-count zero = refl
drain-count (suc n) = cong suc (drain-count n)

-- Even at zero outstanding client/server replies, shutdown performs exactly n flushes.
shutdown-count : ∀ {r} (canRead : S.Reading r) n → Count.flushes (Projection.driver (shutdown canRead n)) ≡ n
shutdown-count canRead n = drain-count n

-- The chosen flush-only tail has n flushes and five fixed transport/control operations.
drain-steps : ∀ n → Operations.steps (Projection.driver (drain n)) ≡ n Data.Nat.+ 5
drain-steps zero = refl
drain-steps (suc n) = cong suc (drain-steps n)

-- The full selected shutdown adds twelve paired operations independently of the completed history.
shutdown-steps : ∀ {r} (canRead : S.Reading r) n →
  Operations.steps (Projection.driver (shutdown canRead n)) ≡ n Data.Nat.+ 12
shutdown-steps canRead n = trans (cong (7 Data.Nat.+_) (drain-steps n))
  (trans (sym (+-assoc 7 n 5)) (trans (cong (Data.Nat._+ 5) (+-comm 7 n)) (+-assoc n 7 5)))

-- A full prefix followed by shutdown has an actual fresh policy execution to the closed state.
full : ∀ n → N.Run N.initial (((N.setForecast true ∷ []) ++ history n) ++ shutdown-actions) closed
full n = append (prefix n) (shutdown (reading n) n)

-- A prefix certificate also supplies success of its pure computation gate.
to-gate : ∀ {s actions t} (run : N.Run s actions t) → AllSmall run → gate run ≡ true
to-gate N.stop pr = pr
to-gate (N.internal pr run) (now , rest) = trans (cong (_∧ gate run) now) (to-gate run rest)
to-gate (N.visible pr run) (now , rest) = trans (cong (_∧ gate run) now) (to-gate run rest)

-- The flush tail preserves occupancy bounds independently of its decreasing completed count.
drain-small : ∀ n → AllSmall (drain n)
drain-small zero = certify (drain zero) refl
drain-small (suc n) = refl , drain-small n

-- All ordinary Quit/control operations in front of that tail also satisfy the gate.
shutdown-gate : ∀ {r} (canRead : S.Reading r) n → gate (shutdown canRead n) ≡ gate (drain n)
shutdown-gate S.atFirst n = refl
shutdown-gate S.atNext n = refl

-- No occupancy burst is hidden in shutdown after the small normal prefix.
shutdown-small : ∀ {r} (canRead : S.Reading r) n → AllSmall (shutdown canRead n)
shutdown-small canRead n = certify (shutdown canRead n)
  (trans (shutdown-gate canRead n) (to-gate (drain n) (drain-small n)))

-- Every state of the full arbitrary-length normal-plus-shutdown family has all eight bounds.
full-bounds : ∀ n → AllBounds (full n)
full-bounds n = to-bounds (full n)
  (append-small (prefix n) (shutdown (reading n) n) (prefix-small n) (shutdown-small (reading n) n))

-- Every future successful close, even with more requests, requires at least n paired operations.
any-close-lower-bound : ∀ n {actions target} (run : N.Run (ready (reader n) n) actions target) →
  D.serverState (N.driverState target) ≡ S.state S.closed 0 S.idle 0 true →
  n ≤ Operations.steps (Projection.driver run)
any-close-lower-bound n run done = Count.completed-closing-lower-bound (Projection.driver run) done

-- No constant completed-token bound follows even from occupancy at most one at every prefix.
unbounded-completions : ∀ bound →
  AllSmall (prefix (suc bound)) ×
  C.inFlight (D.clientState (N.driverState (ready S.awaitNext (suc bound)))) ≡ 0 ×
  S.owed (D.serverState (N.driverState (ready S.awaitNext (suc bound)))) ≡ 0 ×
  bound < S.completed (D.serverState (N.driverState (ready S.awaitNext (suc bound))))
unbounded-completions bound = prefix-small (suc bound) , refl , refl , ≤-refl
