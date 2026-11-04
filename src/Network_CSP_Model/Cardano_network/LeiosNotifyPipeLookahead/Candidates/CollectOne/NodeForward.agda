{-# OPTIONS --safe #-}

-- Every finite candidate paired-policy history has an exact baseline history with ghost completions.
module Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.NodeForward
  (Notification : Set) where

open import Data.Bool using (true)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as B
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as BD
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000 as BS
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as BN
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Notification as C
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.DriverModel Notification ⊤ as CD
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.NodeModel Notification 1000 as CS
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.NodeDriverModel Notification as CN
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Forward Notification as F

-- Exactly the server state changes; all packet queues, hook values and client control are retained.
driver : ℕ → CD.State → BD.State
driver extra (CD.pair c s cs sc pc ps rc rs) = BD.pair c (F.lift extra s) cs sc pc ps rc rs

-- Credit/eligible FIFO state, client failure and environment snapshots also remain identical.
lift : ℕ → CN.State → BN.State
lift extra (CN.nodeDriver raw q live forecast stop) = BN.nodeDriver (driver extra raw) q live forecast stop

-- The terminal ghost invariant from the local simulation is all that the lift requires.
Good : CD.State → ℕ → Set
Good raw extra = F.Good (C.reader (CD.serverState raw)) extra

-- Join baseline histories in this proof module without changing any baseline source file.
append : ∀ {s t u actions more} → BN.Run s actions t → BN.Run t more u → BN.Run s (actions ++ more) u
append BN.stop suffix = suffix
append (BN.internal pr run) suffix = BN.internal pr (append run suffix)
append (BN.visible pr run) suffix = BN.visible pr (append run suffix)

-- Propositional state identity supplies a stuttering baseline schedule.
stay : ∀ {s t} → s ≡ t → BN.Run s [] t
stay refl = BN.stop

-- A source action is retained exactly, including reply selection and the selected payload.
peer-step : ∀ {s a t} → C.Step C.nodeNext s a t → (extra : ℕ) → F.Good (C.reader s) extra →
  F.Good (C.reader t) extra × B.Step B.nodeNext (F.lift extra s) a (F.lift extra t)
peer-step (C.receiveRequest reading) extra _ = tt , B.receiveRequest (F.reading reading)
peer-step (C.receiveQuit reading) extra _ = tt , B.receiveQuit (F.reading reading)
peer-step (C.choose {r = r} live allowed) extra good = good ,
  B.choose (trans (sym (F.active-reader r)) live) allowed
peer-step (C.send {r = r} live) extra good = good ,
  B.send (trans (sym (F.active-reader r)) live)
peer-step C.finish .0 refl = refl , B.finish

-- Physical trace-hook completion retains the same actor, record and exact packet value.
driver-step : ∀ {s row t} → CD.Step C.nodeNext s row t → (extra : ℕ) → Good s extra →
  Good t extra × BD.Step B.nodeNext (driver extra s) row (driver extra t)
driver-step (CD.clientSent pr) extra good = good , BD.clientSent pr
driver-step (CD.clientReceived pr) extra good = good , BD.clientReceived pr
driver-step (CD.serverSent pr) extra good with peer-step pr extra good
... | next , step = next , BD.serverSent step
driver-step (CD.serverReceived pr) extra good with peer-step pr extra good
... | next , step = next , BD.serverReceived step

-- Only the four physical transport operations are admitted through the node transport rule.
transport : ∀ {s t live} (pr : CD.Tau C.nodeNext s t) → CN.transportAllowed live pr ≡ true →
  (extra : ℕ) → Good s extra → Good t extra ×
  (Σ[ step ∈ BD.Tau B.nodeNext (driver extra s) (driver extra t) ] BN.transportAllowed live step ≡ true)
transport (CD.clientInternal _) ()
transport (CD.serverInternal _) ()
transport (CD.clientCallback _ _) ()
transport (CD.serverCallback _) ()
transport (CD.commitClient pr) allowed extra good = good , BD.commitClient pr , allowed
transport (CD.decodeClient pr) allowed extra good = good , BD.decodeClient pr , allowed
transport (CD.commitServer pr) allowed extra good with peer-step pr extra good
... | next , step = good , BD.commitServer step , refl
transport (CD.decodeServer pr) allowed extra good with peer-step pr extra good
... | next , step = good , BD.decodeServer step , refl

-- Baseline extra tokens are flushed under the same paired context before reader handoff.
drain-extra : ∀ {c cs sc pc ps rc rs q live forecast stop} extra → BN.Run
  (BN.nodeDriver (BD.pair c (B.state B.flushing 0 B.idle extra true) cs sc pc ps rc rs) q live forecast stop)
  [] (BN.nodeDriver (BD.pair c (B.state B.doneReady 0 B.idle 0 true) cs sc pc ps rc rs) q live forecast stop)
drain-extra zero = BN.internal (BN.serverSchedule (BS.schedule B.drained refl)) BN.stop
drain-extra (suc extra) = BN.internal (BN.serverSchedule (BS.schedule B.flush refl)) (drain-extra extra)

-- Node server callbacks retain credit guards and consume exactly the same eligible FIFO head.
server-tau : ∀ {raw q live forecast stop s′ q′}
  (pr : CS.Tau (CS.node (CD.serverState raw) q) (CS.node s′ q′)) →
  (extra : ℕ) → Good raw extra → Σ[ more ∈ ℕ ]
  (Good (CN.withServer raw s′) more × BN.Run (lift extra (CN.nodeDriver raw q live forecast stop)) []
    (lift more (CN.nodeDriver (CN.withServer raw s′) q′ live forecast stop)))
server-tau {raw = CD.pair _ _ _ _ _ _ _ _} (CS.admitAccepted pr) extra _ =
  extra , tt , BN.internal (BN.serverSchedule (BS.admitAccepted pr)) BN.stop
server-tau {raw = CD.pair _ _ _ _ _ _ _ _} (CS.admitExcessive pr) extra _ =
  extra , tt , BN.internal (BN.serverSchedule (BS.admitExcessive pr)) BN.stop
server-tau {raw = CD.pair _ _ _ _ _ _ _ _} (CS.nextQueued queue pr) extra good with peer-step pr extra good
... | next , step = extra , next , BN.internal (BN.serverSchedule (BS.nextQueued queue step)) BN.stop
server-tau (CS.schedule C.admitted ())
server-tau (CS.schedule C.excessive ())
server-tau {raw = CD.pair _ _ _ _ _ _ _ _} (CS.schedule (C.inspectZero _) _) extra _ = extra , tt , BN.stop
server-tau {raw = CD.pair _ _ _ _ _ _ _ _} (CS.schedule (C.inspectPositive _) _) extra _ = extra , tt , BN.stop
server-tau {raw = CD.pair c _ cs sc pc ps rc rs} {q = q} {live = live} {forecast = forecast} {stop = stop}
  (CS.schedule C.pollHit _) extra _ = suc extra , tt , stay
    (Relation.Binary.PropositionalEquality.cong
      (λ s → BN.nodeDriver (BD.pair c s cs sc pc ps rc rs) q live forecast stop) (sym F.hit-state))
server-tau {raw = CD.pair _ _ _ _ _ _ _ _} (CS.schedule (C.pollMiss _) _) extra _ = extra , tt , BN.stop
server-tau {raw = CD.pair _ _ _ _ _ _ _ _} (CS.schedule C.registered _) extra _ =
  extra , tt , BN.internal (BN.serverSchedule (BS.schedule B.registered refl)) BN.stop
server-tau {raw = CD.pair _ _ _ _ _ _ _ _} (CS.schedule C.setQuit _) extra _ =
  extra , tt , BN.internal (BN.serverSchedule (BS.schedule B.setQuit refl)) BN.stop
server-tau {raw = CD.pair _ _ _ _ _ _ _ _} (CS.schedule (C.claim {r = r} live) _) extra good =
  extra , good , BN.internal (BN.serverSchedule (BS.schedule
    (B.claim (trans (sym (F.active-reader r)) live)) refl)) BN.stop
server-tau {raw = CD.pair _ _ _ _ _ _ _ _} (CS.schedule (C.cancel {r = r} live) _) extra good =
  extra , good , BN.internal (BN.serverSchedule (BS.schedule
    (B.cancel (trans (sym (F.active-reader r)) live)) refl)) BN.stop
server-tau {raw = CD.pair _ _ _ _ _ _ _ _} (CS.schedule (C.retire {r = r} live) _) extra good =
  extra , good , BN.internal (BN.serverSchedule (BS.schedule
    (B.retire (trans (sym (F.active-reader r)) live)) refl)) BN.stop
server-tau {raw = CD.pair _ _ _ _ _ _ _ _} (CS.schedule C.flush _) extra _ =
  extra , tt , BN.internal (BN.serverSchedule (BS.schedule B.flush refl)) BN.stop
server-tau {raw = CD.pair _ _ _ _ _ _ _ _} (CS.schedule C.drained _) extra _ = 0 , refl , drain-extra extra
server-tau {raw = CD.pair _ _ _ _ _ _ _ _} (CS.schedule C.abort _) extra _ =
  extra , tt , BN.internal (BN.serverSchedule (BS.schedule B.abort refl)) BN.stop

-- Each node scheduling/transport operation has a finite baseline realization with unchanged inputs.
tau : ∀ {s t} → CN.Tau s t → (extra : ℕ) → Good (CN.driverState s) extra →
  Σ[ more ∈ ℕ ] (Good (CN.driverState t) more × BN.Run (lift extra s) [] (lift more t))
tau (CN.clientSchedule {raw = CD.pair _ _ _ _ _ _ _ _} pr) extra good =
  extra , good , BN.internal (BN.clientSchedule pr) BN.stop
tau (CN.continueReady {raw = CD.pair _ _ _ _ _ _ _ _} pr) extra good =
  extra , good , BN.internal (BN.continueReady pr) BN.stop
tau (CN.terminateReady {raw = CD.pair _ _ _ _ _ _ _ _} pr) extra good =
  extra , good , BN.internal (BN.terminateReady pr) BN.stop
tau (CN.serverSchedule pr) extra good = server-tau pr extra good
tau (CN.transport pr allowed) extra good with transport pr allowed extra good
... | next , step , allowed′ = extra , next , BN.internal (BN.transport step allowed′) BN.stop

-- Every explicit policy input and physical wire record is retained in its original order.
step : ∀ {s a t} → CN.Step s a t → (extra : ℕ) → Good (CN.driverState s) extra →
  Good (CN.driverState t) extra × BN.Run (lift extra s) (a ∷ []) (lift extra t)
step (CN.clientRecord row pr) extra good with driver-step pr extra good
... | next , traceStep = next , BN.visible (BN.clientRecord row traceStep) BN.stop
step (CN.serverRecord row pr) extra good with driver-step pr extra good
... | next , traceStep = next , BN.visible (BN.serverRecord row traceStep) BN.stop
step CN.forecastInput extra good = good , BN.visible BN.forecastInput BN.stop
step CN.terminateInput extra good = good , BN.visible BN.terminateInput BN.stop
step (CN.applicationInput {raw = CD.pair _ (C.state r _ _ _ _) _ _ _ _ _ _}
  (CS.applicationOffer live pr)) extra good = good , BN.visible
    (BN.applicationInput (BS.applicationOffer (trans (sym (F.active-reader r)) live) pr)) BN.stop
step (CN.normalHandler {raw = CD.pair _ _ _ _ _ _ _ _} pr) extra good =
  good , BN.visible (BN.normalHandler pr) BN.stop
step (CN.canceledHandlerExit pr) extra good = good , BN.visible (BN.canceledHandlerExit pr) BN.stop

-- Structural induction preserves exact complete paired-policy action lists from any related state.
run : ∀ {s actions t} → CN.Run s actions t → (extra : ℕ) → Good (CN.driverState s) extra →
  Σ[ more ∈ ℕ ] (Good (CN.driverState t) more × BN.Run (lift extra s) actions (lift more t))
run CN.stop extra good = extra , good , BN.stop
run (CN.internal pr rest) extra good with tau pr extra good
... | more , next , prefix with run rest more next
...   | final , last , suffix = final , last , append prefix suffix
run (CN.visible pr rest) extra good with step pr extra good
... | next , prefix with run rest extra next
...   | final , last , suffix = final , last , append prefix suffix

-- Fresh candidate node histories need no external resource or simulation premise.
from-initial : ∀ {actions t} → CN.Run CN.initial actions t →
  Σ[ extra ∈ ℕ ] (Good (CN.driverState t) extra × BN.Run BN.initial actions (lift extra t))
from-initial execution = run execution 0 tt
