{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Smoke test (imported by nothing): the iteration lemma `MAccR-iter` of
-- `CSP.Laws.DivFree.Loop` discharged on ONE real `iter` peer — the
-- KeepAlive server `KAserverStClient l d = iter (serverStep l d) stClient`.
--   round guards : `Guarded-react` + `NoRetBy-mono` (menu states),
--                  `NoRetBy-Ret` (`stDone` returns `inj₂`, not a loop-back)
--   body states  : `MAccR-react` (inverting the receive menu), `MAccR-Output`,
--                  `MAccR-⟶₀`, `MAccR-Ret`
-- No `postulate`, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.NetworkVerification.PeerTauAccSmoke (p : Params) where

open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl; subst)
open import Class.DecEq using (_≟_)

open import Process_Trees using (ExtI)
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.KeepAlive p
open import CSP.Operators KAEv-≟ using (∅ES)
open import Semantics.LTS {E = KAEv} {I = ExtI KAEv} using (_─[_]─►_; ev; sVis)
open import Semantics.DivergenceFree {E = KAEv} {I = ExtI KAEv} using (τ-AccReach)
open import CSP.Laws.DivFree.ModAcc KAEv-≟ using (MAccR; MAccR→τ-AccReach)
open import CSP.Laws.DivFree.Reach KAEv-≟ using (MAccR-Ret)
open import CSP.Laws.DivFree.Loop KAEv-≟
  using (NoRetBy; Looping; NoRetBy-mono; NoRetBy-Ret; Guarded-react;
         MAccR-react; MAccR-Output; MAccR-⟶₀; MAccR-iter)

-- every continuation of the server's receive menu is τ-accessible everywhere
recvR : ∀ {l d x t′} → serverStep l d stClient ─[ ev x ]─► t′ → MAccR ∅ES t′
recvR {l} {d} (sVis {at = _ , receiveKA l′ d′} {a = _ , _ , _ , keepAlive (MsgKeepAlive c)} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl =
  subst (MAccR ∅ES) (just-injective br) (MAccR-Output (apiKAev l d recvKACookie) c (MAccR-Ret _))
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
recvR {l} {d} (sVis {at = _ , receiveKA l′ d′} {a = _ , _ , _ , keepAlive MsgKADone} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (MAccR ∅ES) (just-injective br) (MAccR-⟶₀ (doneKA l d) (MAccR-Ret _))
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
recvR (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , keepAlive (MsgKeepAliveResponse _)} refl ())
recvR (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , blockFetch _}   refl ())
recvR (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , chainSync _}    refl ())
recvR (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , txSubmission _} refl ())
recvR (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , leiosNotify _}  refl ())
recvR (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , leiosFetch _}   refl ())
recvR (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
recvR (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , leiosFetchP _}  refl ())
recvR (sVis {at = _ , sendKA _ _}    refl ())
recvR (sVis {at = _ , apiKAev _ _ _} refl ())
recvR (sVis {at = _ , doneKA _ _}    refl ())

-- every body state is τ-accessible at every reachable state
bodyR : ∀ {l d} st → MAccR ∅ES (serverStep l d st)
bodyR {l} {d} stClient = MAccR-react refl λ {at} {a} eq → recvR {l} {d} (sVis {at = at} {a = a} refl eq)
bodyR (stServer c) = MAccR-Output _ _ (MAccR-Ret _)
bodyR stDone       = MAccR-Ret _

-- no round start loops back before a visible event (`stDone` returns `inj₂`)
bodyG : ∀ {l d} st → NoRetBy Looping ∅ES (serverStep l d st)
bodyG stClient     = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
bodyG (stServer c) = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
bodyG stDone       = NoRetBy-Ret λ ()

-- THE SMOKE THEOREM: the real KeepAlive server peer is τ-accessible at every reachable state
server-τ-AccReach : ∀ l d → τ-AccReach (KAserverStClient l d)
server-τ-AccReach l d = MAccR→τ-AccReach (MAccR-iter {k = serverStep l d} bodyG bodyR stClient)
