{-# OPTIONS --guardedness #-}

-- Exact control-trace correspondence for the original pipelined PTree.
-- Payloads, API events, collection and semantic termination are unobserved.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.BlockFetchClientBridge (p : Params) where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; +-identityʳ)
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
open import Cardano_network.BlockFetch p using (BFEv; sendBF; receiveBF; BFEv-≟; Rr)
import Cardano_network.BlockFetchPipe p as P
open P using (pending; ranges; phase; completed; occupancy; send; step)
open import Cardano_network.Replay.BlockFetchClientParts p
open import CSP.Operators BFEv-≟ using (Ret)
open import Semantics.LTS {E = BFEv} {I = ExtI BFEv} using (Event; evLabel; _─[_]─►_; ev; evl; τ)
open import Semantics.Deadlock {E = BFEv} {I = ExtI BFEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Cardano_network.Replay.LeiosFetchServerForward using (module Fire)
open Fire BFEv-≟ using (out-fire)
import Semantics.Replay.Bridge {E = BFEv} {I = ExtI BFEv} as Br
open import Semantics.Replay using (Replay)
open import Cardano_network.Replay.BlockFetchClientSession

-- Erase message contents, retaining all protocol-control distinctions.
kind : MessageBlockFetch → Kind
kind (MsgRequestRange _) = request
kind MsgStartBatch = startBatch
kind MsgNoBlocks = noBlocks
kind (MsgBlock _) = block
kind MsgBatchDone = batchDone
kind MsgClientDone = clientDone

-- Observe wire messages; unlogged application events are erased.
cls : Event → Maybe E
cls (evLabel _ (sendBF _ _) (_ , _ , _ , blockFetch m)) = just (Send , kind m)
cls (evLabel _ (receiveBF _ _) (_ , _ , _ , blockFetch m)) = just (Recv , kind m)
cls _ = nothing

-- Exact equality of projected wire-control traces, with no payload claim.
Obs : List Event → List E → Set
Obs = Br.Obs cls id

-- Translate the PTree response phase without changing its meaning.
ph : P.Phase → Phase
ph P.waiting = waiting
ph P.streaming = streaming

-- Completed responses are hidden; only unanswered ranges remain observable.
ctl : P.State → St
ctl (pending rs q c) = openS (length rs) (ph q)

-- Appending one range increments the outstanding response count.
snoc-length : ∀ (rs : List ChainRange) r → length (rs ∷ʳ r) ≡ suc (length rs)
snoc-length [] r = refl
snoc-length (_ ∷ rs) r = cong suc (snoc-length rs r)

-- Forgetting completed results cannot increase the outstanding count.
left≤sum : ∀ n c → n ≤ n + c
left≤sum zero c = z≤n
left≤sum (suc n) c = s≤s (left≤sum n c)

-- The PTree's stronger occupancy guard implies the wire-level guard.
wire-bound : ∀ {n c k} → n + c < k → n < k
wire-bound {n} {c} lt = ≤-trans (s≤s (left≤sum n c)) lt

module _ (k : ℕ) (l : Link) (d : Dir) where
  open Spec k

  -- Specialise the original iteration wrapper to this session.
  It′ : P.Body → Proc
  It′ = It k l d

  -- Include every reachable residual, not just the loop heads.
  data Rel : Proc → St → Set₁ where
    head : ∀ s → Rel (It′ (step k l d s)) (ctl s)
    backR : ∀ s → Rel (It′ (Ret (inj₁ s))) (ctl s)
    reqR : ∀ s r → occupancy s < k →
      Rel (It′ (send l d (MsgRequestRange r)
        (inj₁ (pending (ranges s ∷ʳ r) (phase s) (completed s))))) (ctl s)
    doneR : Rel (It′ (send l d MsgClientDone (inj₂ _))) initial
    delR : ∀ s b → Rel (It′ (deliver k l d b s)) (ctl s)
    endR : Rel (It′ (Ret (inj₂ _))) closed

  -- Collection and loop-back preserve the wire abstraction.
  sim-τ : ∀ {T T′ s} → Rel T s → T ─[ τ ]─► T′ →
    Σ[ s′ ∈ St ] (s ⇒⟨ [] ⟩ s′ × Rel T′ s′)
  sim-τ (head (pending rs q c)) st with collect-inv k l d st
  ... | c′ , refl , refl = _ , done , backR (pending rs q c′)
  sim-τ (backR s) st with back-inv k l d st
  ... | refl = _ , done , head s
  sim-τ (reqR _ _ _) st = ⊥-elim (noτ k l d refl st)
  sim-τ doneR st = ⊥-elim (noτ k l d refl st)
  sim-τ (delR _ _) st = ⊥-elim (noτ k l d refl st)
  sim-τ endR st = ⊥-elim (end-noτ k l d st)

  -- Each wire step advances the control model; API handoffs do not.
  sim-ev : ∀ {T T′ s e} → Rel T s → T ─[ ev (evl e) ]─► T′ →
    Σ[ es ∈ List E ] Σ[ s′ ∈ St ] (Obs (e ∷ []) es × s ⇒⟨ es ⟩ s′ × Rel T′ s′)
  sim-ev (head s) st with head-inv k l d st
  ... | _ , hReq r lt , refl = [] , _ , refl , done , reqR s r lt
  ... | _ , hDone refl , refl = [] , _ , refl , done , doneR
  ... | _ , hStart refl , refl = (Recv , startBatch) ∷ [] , _ , refl , vis start done , backR _
  ... | _ , hNone refl , refl = (Recv , noBlocks) ∷ [] , _ , refl , vis none done , backR _
  ... | _ , hBlock b refl , refl = (Recv , block) ∷ [] , _ , refl , vis body done , delR _ b
  ... | _ , hEnd refl , refl = (Recv , batchDone) ∷ [] , _ , refl , vis end done , backR _
  sim-ev (reqR (pending rs q c) r lt) st with out-inv k l d st
  ... | refl , refl = (Send , request) ∷ [] , _ , refl ,
    vis (subst (λ n → Step k (openS (length rs) (ph q)) (Send , request) (openS n (ph q)))
      (sym (snoc-length rs r)) (issue (wire-bound lt))) done , backR _
  sim-ev doneR st with out-inv k l d st
  ... | refl , refl = (Send , clientDone) ∷ [] , _ , refl , vis close done , endR
  sim-ev (delR s b) st with out-inv k l d st
  ... | refl , refl = [] , _ , refl , done , backR s
  sim-ev (backR _) st = ⊥-elim (ret-noev k l d st)
  sim-ev endR st = ⊥-elim (ret-noev k l d st)

  -- The checker model simulates every reachable client PTree residual.
  simulation : Br.Sim model cls id Rel
  simulation = record { sim-τ = sim-τ ; sim-ev = sim-ev }

  -- Every observed client trace belongs to the certified control language.
  sound : ∀ {t M es} → P.client k l d ⟹∖√⟨ t ⟩ M → Obs t es → HasTrace initial es
  sound {es = es} run o with Br.sound model cls id simulation (head P.initial) run
  ... | es′ , s′ , o′ , r , _ = s′ , subst (λ xs → initial ⇒⟨ xs ⟩ s′)
    (trans (sym (map-id es′)) (trans (sym o′) (trans o (map-id es)))) r

  -- An indexed queue makes the response count explicit during inversion.
  data Queue : List ChainRange → ℕ → Set where
    emptyQ : Queue [] 0
    consQ : ∀ {rs n} r → Queue rs n → Queue (r ∷ rs) (suc n)

  -- The indexed count agrees with the original list length.
  queue-length : ∀ {rs n} → Queue rs n → length rs ≡ n
  queue-length emptyQ = refl
  queue-length (consQ r qs) = cong suc (queue-length qs)

  -- Appending preserves the index correspondence.
  queue-snoc : ∀ {rs n} → Queue rs n → ∀ r → Queue (rs ∷ʳ r) (suc n)
  queue-snoc emptyQ r = consQ r emptyQ
  queue-snoc (consQ h qs) r = consQ h (queue-snoc qs r)

  -- Canonical completeness collects each response immediately, leaving c=0.
  data RelC : Proc → St → Set₁ where
    cWait : ∀ {rs n} → Queue rs n → RelC (It′ (step k l d (pending rs P.waiting 0))) (openS n waiting)
    cStream : ∀ {rs n} → Queue rs n → RelC (It′ (step k l d (pending rs P.streaming 0))) (openS n streaming)
    cEnd : RelC (It′ (Ret (inj₂ _))) closed

  -- Select the phase-specific relation constructor.
  cHead : ∀ {rs n} → Queue rs n → ∀ q → RelC (It′ (step k l d (pending rs q 0))) (openS n (ph q))
  cHead qs P.waiting = cWait qs
  cHead qs P.streaming = cStream qs

  -- Completeness needs an inhabited block carrier to realise erased payloads.
  module _ (b₀ : Block) where
    -- A canonical range witnesses RequestRange at the control abstraction.
    range₀ : ChainRange
    range₀ = chainRange (point b₀) (point b₀)

    -- The replay abstraction has no silent transitions.
    co-τ : ∀ {T s s′} → RelC T s → Replay._-τ→_ model s s′ →
      Σ[ T′ ∈ Proc ] Σ[ t ∈ List Event ] (T ⟹∖√⟨ t ⟩ T′ × Obs t [] × RelC T′ s′)
    co-τ _ ()

    -- A request extends the canonical queue while preserving its phase.
    co-issue : ∀ {rs n} (qs : Queue rs n) q → n < k →
      Σ[ T′ ∈ Proc ] Σ[ t ∈ List Event ]
        (It′ (step k l d (pending rs q 0)) ⟹∖√⟨ t ⟩ T′ ×
        Obs t ((Send , request) ∷ []) × RelC T′ (openS (suc n) (ph q)))
    co-issue {rs} qs q lt = _ , _ ,
      ∖√-ev (fire k l d (fire-req k l d range₀ (subst (_< k) (sym (trans (+-identityʳ (length rs)) (queue-length qs))) lt)))
      (∖√-ev (fire k l d out-fire) (∖√-τ (back k l d) ∖√-refl)) , refl ,
      cHead (queue-snoc qs range₀) q

    -- Realise each accepted wire event in the original client.
    co-ev : ∀ {T s s′ e} → RelC T s → ⊤ → Step k s e s′ →
      Σ[ T′ ∈ Proc ] Σ[ t ∈ List Event ] (T ⟹∖√⟨ t ⟩ T′ × Obs t (e ∷ []) × RelC T′ s′)
    co-ev (cWait qs) _ (issue lt) = co-issue qs P.waiting lt
    co-ev (cStream qs) _ (issue lt) = co-issue qs P.streaming lt
    co-ev (cWait emptyQ) _ close = _ , _ ,
      ∖√-ev (fire k l d (fire-done k l d {u = tt}))
      (∖√-ev (fire k l d out-fire) ∖√-refl) , refl , cEnd
    co-ev (cWait (consQ r qs)) _ start = _ , _ ,
      ∖√-ev (fire k l d (fire-start k l d))
      (∖√-τ (back k l d) ∖√-refl) , refl , cStream (consQ r qs)
    co-ev (cWait (consQ r qs)) _ none = _ , _ ,
      ∖√-ev (fire k l d (fire-none k l d))
      (∖√-τ (back k l d)
      (∖√-τ (collect-fire k l d)
      (∖√-τ (back k l d) ∖√-refl))) , refl , cWait qs
    co-ev (cStream (consQ r qs)) _ body = _ , _ ,
      ∖√-ev (fire k l d (fire-block k l d b₀))
      (∖√-ev (fire k l d out-fire)
      (∖√-τ (back k l d) ∖√-refl)) , refl , cStream (consQ r qs)
    co-ev (cStream (consQ r qs)) _ end = _ , _ ,
      ∖√-ev (fire k l d (fire-end k l d))
      (∖√-τ (back k l d)
      (∖√-τ (collect-fire k l d)
      (∖√-τ (back k l d) ∖√-refl))) , refl , cWait qs
    co-ev cEnd _ ()

    -- No event premise is needed after choosing an inhabited payload carrier.
    cosimulation : Br.CoSim model cls id RelC (λ _ → ⊤)
    cosimulation = record { co-τ = co-τ ; co-ev = co-ev }

    -- Every accepted control trace has a finite original PTree execution.
    complete : ∀ {es} → HasTrace initial es →
      ∃[ t ] ∃[ M ] (P.client k l d ⟹∖√⟨ t ⟩ M × Obs t es)
    complete {es} (_ , r) with Br.complete model cls id cosimulation
      (cWait emptyQ) (universal (λ _ → tt) es) r
    ... | M , t , run , o , _ = t , M , run , o

    -- Bidirectional correspondence at every pipeline depth and endpoint.
    bridge : ∀ {es} → HasTrace initial es ⇔
      (∃[ t ] ∃[ M ] (P.client k l d ⟹∖√⟨ t ⟩ M × Obs t es))
    bridge = mk⇔ complete (λ { (t , M , run , o) → sound run o })
