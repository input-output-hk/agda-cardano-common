{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the TxSubmission2 mini-protocol peers.
--
-- Mirrors the other peer modules.  Role mapping (Ouroboros naming):
-- `clientStep` = the SUBMITTER (has txs: auto-sends MsgInit, is notified of
-- requests, replies, decides Done); `serverStep` = the REQUESTER (pulls
-- tx-ids / txs).  Wire events `sendTS`/`receiveTS` negotiate `Payload`;
-- api/done are peer-local.  Productive via `iter` (no NON_TERMINATING).
--
-- Protocol: submitter MsgInit ⇒ requester pulls (RequestTxIds Blocking/
-- NonBlocking or RequestTxs) ⇒ submitter replies; submitter MsgDone from the
-- blocking-txids state ends it.  "Pipelined" api tags = the NonBlocking
-- variant (no actual concurrency; sequential).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.TxSubmission (p : Params) where

open import Level renaming (zero to lzero)
import Data.Unit.Polymorphic as Poly
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI

open import Process_Trees

open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.Net  p

open Params p

------------------------------------------------------------------------
-- Step 1: the per-protocol event type `TSEv`.
------------------------------------------------------------------------

-- the TxSubmission2 peer alphabet
data TSEv : Set → Set where
  sendTS    : Conn N2N_TxSubmission → TSEv Payload   -- peer→net (→ input)
  receiveTS : Conn N2N_TxSubmission → TSEv Payload   -- net→peer (→ output)
  apiTSev   : (c : Conn N2N_TxSubmission) (m : ApiTSTag) → TSEv (ApiTSCar m)  -- peer-local
  doneTS    : Conn N2N_TxSubmission → TSEv ⊤          -- peer-local: Done

------------------------------------------------------------------------
-- Step 2: decidable equality on `AnyTypes TSEv`.
------------------------------------------------------------------------

-- decidable equality on existential-wrapped TxSubmission events
TSEv-≟ : (x y : AnyTypes TSEv) → Dec (x ≡ y)
TSEv-≟ = go
  where
  go : (x y : AnyTypes TSEv) → Dec (x ≡ y)
  go (_ , sendTS c₁)     (_ , sendTS c₂)     with c₁ ≟ c₂
  ... | yes refl = yes refl
  ... | no ¬p    = no λ where refl → ¬p refl
  go (_ , receiveTS c₁)  (_ , receiveTS c₂)  with c₁ ≟ c₂
  ... | yes refl = yes refl
  ... | no ¬p    = no λ where refl → ¬p refl
  go (_ , apiTSev c₁ m₁) (_ , apiTSev c₂ m₂) with c₁ ≟ c₂ | m₁ ≟ m₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , doneTS c₁)     (_ , doneTS c₂)     with c₁ ≟ c₂
  ... | yes refl = yes refl
  ... | no ¬p    = no λ where refl → ¬p refl
  go (_ , sendTS _)    (_ , receiveTS _) = no λ ()
  go (_ , sendTS _)    (_ , apiTSev _ _) = no λ ()
  go (_ , sendTS _)    (_ , doneTS _)    = no λ ()
  go (_ , receiveTS _) (_ , sendTS _)    = no λ ()
  go (_ , receiveTS _) (_ , apiTSev _ _) = no λ ()
  go (_ , receiveTS _) (_ , doneTS _)    = no λ ()
  go (_ , apiTSev _ _) (_ , sendTS _)    = no λ ()
  go (_ , apiTSev _ _) (_ , receiveTS _) = no λ ()
  go (_ , apiTSev _ _) (_ , doneTS _)    = no λ ()
  go (_ , doneTS _)    (_ , sendTS _)    = no λ ()
  go (_ , doneTS _)    (_ , receiveTS _) = no λ ()
  go (_ , doneTS _)    (_ , apiTSev _ _) = no λ ()

------------------------------------------------------------------------
-- Step 3: return type + carrier DecEq instances.
------------------------------------------------------------------------

-- the peers return the unit on √
Rr : Set
Rr = Poly.⊤ {lzero}

instance
  -- trivial decidable equality on the unit return type
  DecEq-Rr : DecEq Rr
  DecEq-Rr = record { _≟_ = λ _ _ → yes refl }

  -- `!`-output carriers needing DecEq (DecEq-× is not an instance; the ℕ/List
  -- instances are not re-exported through Data's using-import).
  DecEq-ℕ' : DecEq ℕ
  DecEq-ℕ' = DecEqI.DecEq-ℕ
  DecEq-ListTxid : DecEq (List Txid)
  DecEq-ListTxid = DecEqI.DecEq-List
  DecEq-ℕ×ℕ : DecEq (ℕ × ℕ)
  DecEq-ℕ×ℕ = DecEqI.DecEq-×
  DecEq-BS×ℕ×ℕ : DecEq (BlockingStyle × ℕ × ℕ)
  DecEq-BS×ℕ×ℕ = DecEqI.DecEq-×

import CSP.Operators {E = TSEv} as TSOps
open TSOps TSEv-≟

------------------------------------------------------------------------
-- Step 4: unified peer state (both peers walk the same FSM; agency differs).
------------------------------------------------------------------------

-- TxSubmission2 peer state
data TSState : Set where
  stInit             : TSState   -- before MsgInit (submitter sends / requester awaits)
  stIdle             : TSState   -- requester pulls / submitter awaits a request
  stTxIdsBlocking    : TSState   -- blocking RequestTxIds outstanding
  stTxIdsNonBlocking : TSState   -- non-blocking (pipelined) RequestTxIds outstanding
  stTxs              : TSState   -- RequestTxs outstanding
  stDone             : TSState   -- terminal (√)

instance
  -- decidable equality on the unified TxSubmission state
  DecEq-TSState : DecEq TSState
  DecEq-TSState ._≟_ = go
    where
    go : (x y : TSState) → Dec (x ≡ y)
    go stInit             stInit             = yes refl
    go stIdle             stIdle             = yes refl
    go stTxIdsBlocking    stTxIdsBlocking    = yes refl
    go stTxIdsNonBlocking stTxIdsNonBlocking = yes refl
    go stTxs              stTxs              = yes refl
    go stDone             stDone             = yes refl
    go stInit             stIdle             = no λ ()
    go stInit             stTxIdsBlocking    = no λ ()
    go stInit             stTxIdsNonBlocking = no λ ()
    go stInit             stTxs              = no λ ()
    go stInit             stDone             = no λ ()
    go stIdle             stInit             = no λ ()
    go stIdle             stTxIdsBlocking    = no λ ()
    go stIdle             stTxIdsNonBlocking = no λ ()
    go stIdle             stTxs              = no λ ()
    go stIdle             stDone             = no λ ()
    go stTxIdsBlocking    stInit             = no λ ()
    go stTxIdsBlocking    stIdle             = no λ ()
    go stTxIdsBlocking    stTxIdsNonBlocking = no λ ()
    go stTxIdsBlocking    stTxs              = no λ ()
    go stTxIdsBlocking    stDone             = no λ ()
    go stTxIdsNonBlocking stInit             = no λ ()
    go stTxIdsNonBlocking stIdle             = no λ ()
    go stTxIdsNonBlocking stTxIdsBlocking    = no λ ()
    go stTxIdsNonBlocking stTxs              = no λ ()
    go stTxIdsNonBlocking stDone             = no λ ()
    go stTxs              stInit             = no λ ()
    go stTxs              stIdle             = no λ ()
    go stTxs              stTxIdsBlocking    = no λ ()
    go stTxs              stTxIdsNonBlocking = no λ ()
    go stTxs              stDone             = no λ ()
    go stDone             stInit             = no λ ()
    go stDone             stIdle             = no λ ()
    go stDone             stTxIdsBlocking    = no λ ()
    go stDone             stTxIdsNonBlocking = no λ ()
    go stDone             stTxs              = no λ ()

------------------------------------------------------------------------
-- Step 5: the client (submitter / replier) peer.
------------------------------------------------------------------------

-- one submitter step (the body of the `iter` loop)
clientStep : Conn N2N_TxSubmission → TSState → PTree TSEv (ExtI TSEv) (TSState ⊎ Rr)
clientStep c stInit =
  -- auto-send the protocol Init, then hand agency to the requester
  sendTS c ! (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) ⟶
    Ret (inj₁ stIdle)
clientStep c stIdle = pchoice v
  where
  v : (at : AnyTypes TSEv)
    → ContinueType at (Maybe (PTree TSEv (ExtI TSEv) (TSState ⊎ Rr)))
  v (_ , receiveTS c′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking a r)) with c′ ≟ c
  ... | yes refl = just (Output ⦃ DecEq-BS×ℕ×ℕ ⦄ (apiTSev c recvTSRequestTxIds) (Blocking , a , r) (Ret (inj₁ stTxIdsBlocking)))
  ... | no _     = nothing
  v (_ , receiveTS c′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) with c′ ≟ c
  ... | yes refl = just (Output ⦃ DecEq-BS×ℕ×ℕ ⦄ (apiTSev c recvTSRequestTxIds) (NonBlocking , a , r) (Ret (inj₁ stTxIdsNonBlocking)))
  ... | no _     = nothing
  v (_ , receiveTS c′) (_ , _ , _ , txSubmission (MsgTSRequestTxs txids)) with c′ ≟ c
  ... | yes refl = just (Output ⦃ DecEq-ListTxid ⦄ (apiTSev c recvTSRequestTxs) txids (Ret (inj₁ stTxs)))
  ... | no _     = nothing
  v (_ , receiveTS _) _ = nothing
  v (_ , sendTS _)    _ = nothing
  v (_ , apiTSev _ _) _ = nothing
  v (_ , doneTS _)    _ = nothing
clientStep c stTxIdsBlocking = pchoice v
  where
  v : (at : AnyTypes TSEv)
    → ContinueType at (Maybe (PTree TSEv (ExtI TSEv) (TSState ⊎ Rr)))
  v (_ , apiTSev c′ sendTSReplyTxIds) txids with c′ ≟ c
  ... | yes refl = just
        (sendTS c ! (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds txids)) ⟶
           Ret (inj₁ stIdle))
  ... | no _     = nothing
  v (_ , apiTSev c′ sendTSDone) _ with c′ ≟ c
  ... | yes refl = just
        (sendTS c ! (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) ⟶
           (doneTS c ⟶₀ Ret (inj₁ stDone)))
  ... | no _     = nothing
  v (_ , apiTSev _ _) _ = nothing
  v (_ , sendTS _)    _ = nothing
  v (_ , receiveTS _) _ = nothing
  v (_ , doneTS _)    _ = nothing
clientStep c stTxIdsNonBlocking = pchoice v
  where
  v : (at : AnyTypes TSEv)
    → ContinueType at (Maybe (PTree TSEv (ExtI TSEv) (TSState ⊎ Rr)))
  v (_ , apiTSev c′ sendTSReplyTxIds) txids with c′ ≟ c
  ... | yes refl = just
        (sendTS c ! (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds txids)) ⟶
           Ret (inj₁ stIdle))
  ... | no _     = nothing
  v (_ , apiTSev _ _) _ = nothing
  v (_ , sendTS _)    _ = nothing
  v (_ , receiveTS _) _ = nothing
  v (_ , doneTS _)    _ = nothing
clientStep c stTxs = pchoice v
  where
  v : (at : AnyTypes TSEv)
    → ContinueType at (Maybe (PTree TSEv (ExtI TSEv) (TSState ⊎ Rr)))
  v (_ , apiTSev c′ sendTSReplyTxs) txs with c′ ≟ c
  ... | yes refl = just
        (sendTS c ! (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) ⟶
           Ret (inj₁ stIdle))
  ... | no _     = nothing
  v (_ , apiTSev _ _) _ = nothing
  v (_ , sendTS _)    _ = nothing
  v (_ , receiveTS _) _ = nothing
  v (_ , doneTS _)    _ = nothing
-- StDone: successful termination (√)
clientStep _ stDone = Ret (inj₂ _)

-- the submitter peer: loop the step from the init state
TSclientStClient : Conn N2N_TxSubmission → PTree TSEv (ExtI TSEv) Rr
TSclientStClient c = iter (clientStep c) stInit

------------------------------------------------------------------------
-- Step 6: the server (requester) peer — application-driven pulls.
------------------------------------------------------------------------

-- one requester step (the body of the `iter` loop)
serverStep : Conn N2N_TxSubmission → TSState → PTree TSEv (ExtI TSEv) (TSState ⊎ Rr)
serverStep c stInit = pchoice v
  where
  v : (at : AnyTypes TSEv)
    → ContinueType at (Maybe (PTree TSEv (ExtI TSEv) (TSState ⊎ Rr)))
  v (_ , receiveTS c′) (_ , _ , _ , txSubmission MsgTSInit) with c′ ≟ c
  ... | yes refl = just (Ret (inj₁ stIdle))
  ... | no _     = nothing
  v (_ , receiveTS _) _ = nothing
  v (_ , sendTS _)    _ = nothing
  v (_ , apiTSev _ _) _ = nothing
  v (_ , doneTS _)    _ = nothing
serverStep c stIdle = pchoice v
  where
  v : (at : AnyTypes TSEv)
    → ContinueType at (Maybe (PTree TSEv (ExtI TSEv) (TSState ⊎ Rr)))
  v (_ , apiTSev c′ sendTSRequestTxIdsBlocking) (a , r) with c′ ≟ c
  ... | yes refl = just
        (sendTS c ! (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) ⟶
           Ret (inj₁ stTxIdsBlocking))
  ... | no _     = nothing
  v (_ , apiTSev c′ sendTSRequestTxIdsPipelined) (a , r) with c′ ≟ c
  ... | yes refl = just
        (sendTS c ! (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) ⟶
           Ret (inj₁ stTxIdsNonBlocking))
  ... | no _     = nothing
  v (_ , apiTSev c′ sendTSRequestTxsPipelined) txids with c′ ≟ c
  ... | yes refl = just
        (sendTS c ! (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs txids)) ⟶
           Ret (inj₁ stTxs))
  ... | no _     = nothing
  v (_ , apiTSev _ _) _ = nothing
  v (_ , sendTS _)    _ = nothing
  v (_ , receiveTS _) _ = nothing
  v (_ , doneTS _)    _ = nothing
serverStep c stTxIdsBlocking = pchoice v
  where
  v : (at : AnyTypes TSEv)
    → ContinueType at (Maybe (PTree TSEv (ExtI TSEv) (TSState ⊎ Rr)))
  v (_ , receiveTS c′) (_ , _ , _ , txSubmission (MsgTSReplyTxIds txids)) with c′ ≟ c
  ... | yes refl = just (Ret (inj₁ stIdle))
  ... | no _     = nothing
  v (_ , receiveTS c′) (_ , _ , _ , txSubmission MsgTSDone) with c′ ≟ c
  ... | yes refl = just (doneTS c ⟶₀ Ret (inj₁ stDone))
  ... | no _     = nothing
  v (_ , receiveTS _) _ = nothing
  v (_ , sendTS _)    _ = nothing
  v (_ , apiTSev _ _) _ = nothing
  v (_ , doneTS _)    _ = nothing
serverStep c stTxIdsNonBlocking = pchoice v
  where
  v : (at : AnyTypes TSEv)
    → ContinueType at (Maybe (PTree TSEv (ExtI TSEv) (TSState ⊎ Rr)))
  v (_ , receiveTS c′) (_ , _ , _ , txSubmission (MsgTSReplyTxIds txids)) with c′ ≟ c
  ... | yes refl = just (Ret (inj₁ stIdle))
  ... | no _     = nothing
  v (_ , receiveTS _) _ = nothing
  v (_ , sendTS _)    _ = nothing
  v (_ , apiTSev _ _) _ = nothing
  v (_ , doneTS _)    _ = nothing
serverStep c stTxs = pchoice v
  where
  v : (at : AnyTypes TSEv)
    → ContinueType at (Maybe (PTree TSEv (ExtI TSEv) (TSState ⊎ Rr)))
  v (_ , receiveTS c′) (_ , _ , _ , txSubmission (MsgTSReplyTxs txs)) with c′ ≟ c
  ... | yes refl = just (Ret (inj₁ stIdle))
  ... | no _     = nothing
  v (_ , receiveTS _) _ = nothing
  v (_ , sendTS _)    _ = nothing
  v (_ , apiTSev _ _) _ = nothing
  v (_ , doneTS _)    _ = nothing
-- StDone: successful termination (√)
serverStep _ stDone = Ret (inj₂ _)

-- the requester peer: loop the step from the init state
TSserverStClient : Conn N2N_TxSubmission → PTree TSEv (ExtI TSEv) Rr
TSserverStClient c = iter (serverStep c) stInit

------------------------------------------------------------------------
-- Step 7: network-fragment injection into `Net` (documentation stub).
------------------------------------------------------------------------

-- intended Net images of the TxSubmission wire events (api/done: none)
ιTSNet : ∀ {A} → TSEv A → Maybe (Net Payload A)
ιTSNet (sendTS c)    = just (input  N2N_TxSubmission c)
ιTSNet (receiveTS c) = just (output N2N_TxSubmission c)
ιTSNet (apiTSev _ _) = nothing
ιTSNet (doneTS _)    = nothing
