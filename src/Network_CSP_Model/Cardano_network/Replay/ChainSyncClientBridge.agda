{-# OPTIONS --guardedness #-}

-- Exact control-trace correspondence for the original pipelined PTree.
-- Payloads, API events, collection and semantic termination are unobserved.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.ChainSyncClientBridge (p : Params) where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.List using (List; []; _∷_; _∷ʳ_; length; map)
open import Data.List.Properties using (map-id)
open import Data.List.Relation.Unary.All using (universal)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (id)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Process_Trees using (PTree; ExtI)
open import Cardano_network.Base
open import Cardano_network.Data p
open import Cardano_network.Net p
open Params p
open import Cardano_network.ChainSync p using (CSEv; sendCS; receiveCS; CSEv-≟; Rr)
import Cardano_network.ChainSyncPipe p as P
open P using (send; step)
open import Cardano_network.Replay.ChainSyncClientParts p hiding (forward; backward; found; notFound)
open import CSP.Operators CSEv-≟ using (Ret)
open import Semantics.LTS {E = CSEv} {I = ExtI CSEv} using (Event; evLabel; _─[_]─►_; ev; evl; τ)
open import Semantics.Deadlock {E = CSEv} {I = ExtI CSEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Cardano_network.Replay.LeiosFetchServerForward using (module Fire)
open Fire CSEv-≟ using (out-fire)
import Semantics.Replay.Bridge {E = CSEv} {I = ExtI CSEv} as Br
open import Semantics.Replay using (Replay)
open import Cardano_network.Replay.ChainSyncSession
import Cardano_network.Replay.ChainSyncStepView as V
open import Cardano_network.Replay.ChainSyncServerBridge p using (kind; cls; Obs) public
import Cardano_network.Replay.ChainSyncClientParts p as Parts
open import Cardano_network.Replay.PipelineBounds using (wire-bound)

-- Translate the phase without changing AwaitReply's meaning.
ph : P.Phase → Phase
ph P.canAwait = canAwait
ph P.mustReply = mustReply

-- Completed-but-uncollected results are unobservable on the wire.
ctl : P.State → St
ctl (P.pending n q c) = pending n (ph q)
ctl P.intersect = intersect

module _ (k : ℕ) (l : Link) (d : Dir) where
  open Spec k client

  -- Retain the actual pipeline iteration around every residual.
  It′ : P.Body → Proc
  It′ = It k l d

  -- Include pending wire sends and every application-delivery residual.
  data Rel : Proc → St → Set₁ where
    head : ∀ s → Rel (It′ (step k l d s)) (ctl s)
    backR : ∀ s → Rel (It′ (Ret (inj₁ s))) (ctl s)
    sendR : ∀ {m s a} → Step s (Send , kind m) (ctl a) →
      Rel (It′ (send l d m (inj₁ a))) s
    doneR : Rel (It′ (send l d MsgCSDone (inj₂ _))) initial
    forwardR : ∀ s h t → Rel (It′ (Parts.forward k l d h t s)) (ctl s)
    backwardR : ∀ s pt t → Rel (It′ (Parts.backward k l d pt t s)) (ctl s)
    foundR : ∀ pt t → Rel (It′ (Parts.found k l d pt t)) initial
    notFoundR : ∀ t → Rel (It′ (Parts.notFound k l d t)) initial
    endR : Rel (It′ (Ret (inj₂ _))) closed

  -- Silent collection and iteration preserve the projected state.
  sim-τ : ∀ {T T′ s} → Rel T s → T ─[ τ ]─► T′ →
    Σ[ s′ ∈ St ] (s ⇒⟨ [] ⟩ s′ × Rel T′ s′)
  sim-τ (head (P.pending n q c)) st with collect-inv k l d st
  ... | c′ , refl , refl = _ , done , backR (P.pending n q c′)
  sim-τ (head P.intersect) st = ⊥-elim (intersect-noτ k l d st)
  sim-τ (backR s) st with back-inv k l d st
  ... | refl = _ , done , head s
  sim-τ (sendR _) st = ⊥-elim (noτ k l d refl st)
  sim-τ doneR st = ⊥-elim (noτ k l d refl st)
  sim-τ (forwardR _ _ _) st = ⊥-elim (noτ k l d refl st)
  sim-τ (backwardR _ _ _) st = ⊥-elim (noτ k l d refl st)
  sim-τ (foundR _ _) st = ⊥-elim (noτ k l d refl st)
  sim-τ (notFoundR _) st = ⊥-elim (noτ k l d refl st)
  sim-τ endR st = ⊥-elim (end-noτ k l d st)

  -- Observe precisely the wire event, retaining all response-phase guards.
  sim-ev : ∀ {T T′ s e} → Rel T s → T ─[ ev (evl e) ]─► T′ →
    Σ[ es ∈ List E ] Σ[ s′ ∈ St ] (Obs (e ∷ []) es × s ⇒⟨ es ⟩ s′ × Rel T′ s′)
  sim-ev (head s) st with head-inv k l d st
  ... | _ , hReq refl lt , refl = [] , _ , refl , done , sendR (V.issue-ok (wire-bound lt))
  ... | _ , hFind pts refl , refl = [] , _ , refl , done , sendR refl
  ... | _ , hDone refl , refl = [] , _ , refl , done , doneR
  ... | _ , hAwait refl , refl = (Recv , awaitReply) ∷ [] , _ , refl , vis refl done , backR _
  ... | _ , hForwardCan h t refl , refl = (Recv , rollForward) ∷ [] , _ , refl , vis refl done , forwardR _ h t
  ... | _ , hForwardMust h t refl , refl = (Recv , rollForward) ∷ [] , _ , refl , vis refl done , forwardR _ h t
  ... | _ , hBackwardCan pt t refl , refl = (Recv , rollBackward) ∷ [] , _ , refl , vis refl done , backwardR _ pt t
  ... | _ , hBackwardMust pt t refl , refl = (Recv , rollBackward) ∷ [] , _ , refl , vis refl done , backwardR _ pt t
  ... | _ , hFound pt t refl , refl = (Recv , intersectFound) ∷ [] , _ , refl , vis refl done , foundR pt t
  ... | _ , hNotFound t refl , refl = (Recv , intersectNotFound) ∷ [] , _ , refl , vis refl done , notFoundR t
  sim-ev (sendR {m} pr) st with out-inv k l d st
  ... | refl , refl = (Send , kind m) ∷ [] , _ , refl , vis pr done , backR _
  sim-ev doneR st with out-inv k l d st
  ... | refl , refl = (Send , doneK) ∷ [] , _ , refl , vis refl done , endR
  sim-ev (forwardR s h t) st with out-inv k l d st
  ... | refl , refl = [] , _ , refl , done , backR s
  sim-ev (backwardR s pt t) st with out-inv k l d st
  ... | refl , refl = [] , _ , refl , done , backR s
  sim-ev (foundR pt t) st with out-inv k l d st
  ... | refl , refl = [] , _ , refl , done , backR P.initial
  sim-ev (notFoundR t) st with out-inv k l d st
  ... | refl , refl = [] , _ , refl , done , backR P.initial
  sim-ev (backR _) st = ⊥-elim (ret-noev k l d st)
  sim-ev endR st = ⊥-elim (ret-noev k l d st)

  -- The original pipelined peer is simulated by the replay model.
  simulation : Br.Sim model cls id Rel
  simulation = record { sim-τ = sim-τ ; sim-ev = sim-ev }

  -- Every projected finite PTree trace is accepted by replay.
  sound : ∀ {t M es} → P.client k l d ⟹∖√⟨ t ⟩ M → Obs t es → HasTrace initial es
  sound {es = es} run o with Br.sound model cls id simulation (head P.initial) run
  ... | es′ , s′ , o′ , r , _ = s′ , subst (λ xs → initial ⇒⟨ xs ⟩ s′)
    (trans (sym (map-id es′)) (trans (sym o′) (trans o (map-id es)))) r

  -- Collect results immediately in canonical completeness witnesses.
  data RelC : Proc → St → Set₁ where
    cCan : ∀ n → RelC (It′ (step k l d (P.pending n P.canAwait 0))) (pending n canAwait)
    cMust : ∀ n → RelC (It′ (step k l d (P.pending n P.mustReply 0))) (pending n mustReply)
    cIntersect : RelC (It′ (step k l d P.intersect)) intersect
    cEnd : RelC (It′ (Ret (inj₂ _))) closed

  -- One block suffices to construct every erased response payload.
  module _ (b₀ : Block) where
    -- There are no silent replay transitions.
    co-τ : ∀ {T s s′} → RelC T s → Replay._-τ→_ model s s′ →
      Σ[ T′ ∈ Proc ] Σ[ t ∈ List Event ] (T ⟹∖√⟨ t ⟩ T′ × Obs t [] × RelC T′ s′)
    co-τ _ ()

    -- Construct one event using the inductive view of the actual checker.
    co-view : ∀ {T s s′ e} → RelC T s → V.View k s e s′ →
      Σ[ T′ ∈ Proc ] Σ[ t ∈ List Event ] (T ⟹∖√⟨ t ⟩ T′ × Obs t (e ∷ []) × RelC T′ s′)
    co-view (cCan n) (V.request lt) = _ , _ ,
      ∖√-ev (fire k l d (fire-Req k l d {u = tt} (subst (_< k) (sym (+-identityʳ n)) lt)))
      (∖√-ev (fire k l d out-fire) (∖√-τ (back k l d) ∖√-refl)) , refl , cCan (suc n)
    co-view (cMust n) (V.request lt) = _ , _ ,
      ∖√-ev (fire k l d (fire-Req k l d {u = tt} (subst (_< k) (sym (+-identityʳ n)) lt)))
      (∖√-ev (fire k l d out-fire) (∖√-τ (back k l d) ∖√-refl)) , refl , cMust (suc n)
    co-view (cCan zero) V.find = _ , _ ,
      ∖√-ev (fire k l d (fire-Find k l d []))
      (∖√-ev (fire k l d out-fire) (∖√-τ (back k l d) ∖√-refl)) , refl , cIntersect
    co-view (cCan zero) V.close = _ , _ ,
      ∖√-ev (fire k l d (fire-Done k l d {u = tt}))
      (∖√-ev (fire k l d out-fire) ∖√-refl) , refl , cEnd
    co-view (cCan (suc n)) V.await = _ , _ ,
      ∖√-ev (fire k l d (fire-Await k l d))
      (∖√-τ (back k l d) ∖√-refl) , refl , cMust (suc n)
    co-view (cCan (suc n)) V.forward = _ , _ ,
      ∖√-ev (fire k l d (fire-ForwardCan k l d (header b₀) (tip b₀)))
      (∖√-ev (fire k l d out-fire)
      (∖√-τ (back k l d) (∖√-τ (collect-fire k l d)
      (∖√-τ (back k l d) ∖√-refl)))) , refl , cCan n
    co-view (cCan (suc n)) V.backward = _ , _ ,
      ∖√-ev (fire k l d (fire-BackwardCan k l d (point b₀) (tip b₀)))
      (∖√-ev (fire k l d out-fire)
      (∖√-τ (back k l d) (∖√-τ (collect-fire k l d)
      (∖√-τ (back k l d) ∖√-refl)))) , refl , cCan n
    co-view (cMust (suc n)) V.forward = _ , _ ,
      ∖√-ev (fire k l d (fire-ForwardMust k l d (header b₀) (tip b₀)))
      (∖√-ev (fire k l d out-fire)
      (∖√-τ (back k l d) (∖√-τ (collect-fire k l d)
      (∖√-τ (back k l d) ∖√-refl)))) , refl , cCan n
    co-view (cMust (suc n)) V.backward = _ , _ ,
      ∖√-ev (fire k l d (fire-BackwardMust k l d (point b₀) (tip b₀)))
      (∖√-ev (fire k l d out-fire)
      (∖√-τ (back k l d) (∖√-τ (collect-fire k l d)
      (∖√-τ (back k l d) ∖√-refl)))) , refl , cCan n
    co-view cIntersect V.found = _ , _ ,
      ∖√-ev (fire k l d (fire-Found k l d (point b₀) (tip b₀)))
      (∖√-ev (fire k l d out-fire) (∖√-τ (back k l d) ∖√-refl)) , refl , cCan 0
    co-view cIntersect V.notFound = _ , _ ,
      ∖√-ev (fire k l d (fire-NotFound k l d (tip b₀)))
      (∖√-ev (fire k l d out-fire) (∖√-τ (back k l d) ∖√-refl)) , refl , cCan 0
    co-view cEnd ()

    -- Invert a replay step before constructing its concrete witness.
    co-ev : ∀ {T s s′ e} → RelC T s → ⊤ → Step s e s′ →
      Σ[ T′ ∈ Proc ] Σ[ t ∈ List Event ] (T ⟹∖√⟨ t ⟩ T′ × Obs t (e ∷ []) × RelC T′ s′)
    co-ev r _ pr = co-view r (V.view pr)

    -- The original pipeline co-simulates the complete control language.
    cosimulation : Br.CoSim model cls id RelC (λ _ → ⊤)
    cosimulation = record { co-τ = co-τ ; co-ev = co-ev }

    -- Every accepted trace has a finite run in the original client.
    complete : ∀ {es} → HasTrace initial es →
      ∃[ t ] ∃[ M ] (P.client k l d ⟹∖√⟨ t ⟩ M × Obs t es)
    complete {es} (_ , r) with Br.complete model cls id cosimulation
      (cCan 0) (universal (λ _ → tt) es) r
    ... | M , t , run , o , _ = t , M , run , o

    -- Bidirectional correspondence for every depth, including zero.
    bridge : ∀ {es} → HasTrace initial es ⇔
      (∃[ t ] ∃[ M ] (P.client k l d ⟹∖√⟨ t ⟩ M × Obs t es))
    bridge = mk⇔ complete (λ { (t , M , run , o) → sound run o })
