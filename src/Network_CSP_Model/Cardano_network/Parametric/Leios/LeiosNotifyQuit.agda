{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- LeiosNotify GRACEFUL SHUTDOWN (ouroboros-consensus PR 2344, cardano-blueprint PR 67
-- state table), verified on the ported peers themselves (`LeiosNotifyP.clientStepP` /
-- `serverStepP`, not a copy).
--
-- THE SYSTEM.  For one link `l` the real client runs at `(l , lo)` and the real server
-- at `(l , hi)` — the direction index only keeps the two peers' channel names apart.
-- The peers follow the table literally and strictly alternate (no pipelining, no
-- lookahead), so they are composed DIRECTLY, without buffers: the server is renamed
-- (`srv`: its `receiveLNP l hi` becomes `sendLNP l lo`, its `sendLNP l hi` becomes
-- `receiveLNP l lo`, api / done unchanged), so each send rendezvouses with the matching
-- receive, and the pair synchronises on the wire:
--     sys = client [| wire |] srv
-- The api / done events are left OPEN to the environment.  The wire is visible: every
-- wire event of `sys` is one LeiosNotify message, named as the client end sees it.
--
-- THE METHOD.  Each component tree is ABSTRACTED by a small labelled transition system
-- (`Abs`: every concrete step is an abstract step; `AbsI`: every abstract step is a
-- concrete step); the abstraction is closed under `Par⊤` (`Prod`), so the composite is
-- abstracted by the product.  An inductive invariant `J` over the product's phases (9
-- joint states) is closed under every abstract step.
--
-- THE RESULTS (§7, §8), all ∀ `Params`, ∀ link `l`:
--   (T) TABLE CONFORMANCE.  `LNPSpec` is the blueprint table as ONE process over the
--       protocol messages (StIdle offers RequestNext / Quit, StBusy the four replies and
--       MsgCanceled, StQuit MsgDone then √).  `sys-conforms`: every √-free trace of `sys`,
--       with api / done projected away (`wire`), is a trace of `LNPSpec`, and if `sys` can
--       terminate there so can `LNPSpec` — trace refinement of the projected pair by the
--       table.  Per peer, the same holds for the client alone (`client-conforms`) and the
--       server alone (`server-conforms`): neither ever offers a message outside its table
--       state.
--   (a) `sys-deadlockFree`, `sys-divergenceFree` (api / done left to the environment).
--   (b) `blk-afterQuit`: with ALL the server's api sends blocked (`blk`, including
--       `lnpSendCanceled`), once the client's quit command `lnpSendDone` has occurred, the
--       rest is deadlock-free, divergence-free and has at most 3 visible events — so every
--       run from there is finite and ends in √.
--   (c) THE NON-PIPELINED STALL.  `blk-stall` / `blk-deadlock`: after "RequestNext
--       commanded and sent", `blk` is STUCK — the client (StBusy, no agency) cannot quit.
--       `blkC-cancelThenQuit`: with only `lnpSendCanceled` allowed to the server (`blkC`),
--       the same prefix continues through MsgCanceled, the quit and MsgDone to √.
--   (d) the earlier negative control on the pre-PR-2344 peers is REMOVED: without
--       pipelining both protocols stall identically when the server never answers; the
--       only difference is MsgCanceled, whose escape is exactly (c).
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.LeiosNotifyQuit (p : Params) where

open import Data.Bool using (Bool; true; false; T; not; _∧_; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-≤-trans; ≤ᵇ⇒≤; +-monoˡ-<; +-monoʳ-<)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Unit as U
open import Data.Unit.Polymorphic using (tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (T?)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI

open import Process_Trees
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.Data p
open import Cardano_network.LeiosNotifyP p
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLNP p
  using ( snd; iV
        ; CIdleV; ciNext; ciQuit; cIdleV; CBusyV; cbCan; cbAnn; cbOff; cbTxs; cbVote; cBusyV
        ; CQuitV; cqDone; cQuitV
        ; SIdleV; siNext; siQuit; sIdleV; SBusyV; sbCan; sbAnn; sbOff; sbTxs; sbVote; sBusyV
        ; SQuitV; sqDone; sQuitV )
open Params p using (time₀; length₀; EBHash; LSlot; Size; VoteBlob)

open import CSP.Operators LNPEv-≟
  using (Ret; Output; Output-cont; pchoice; iter; iter-bind; iterV; iterT
        ; Par; Par⊤; Skip; EventSet; ∅ES; viewV; ∅t)
open EventSet
open import CSP.Rename {E₁ = LNPEv} {E₂ = LNPEv} (λ e → e) (λ e → just e) (λ _ → refl)
  using (renameInv; ConcEvent₁)
import CSP.Laws.Traces.TraceLawsRename {E = LNPEv} as TR
open import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv}
open import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv}
  using (IsStuck; DeadlockFree; HasDeadlock; _⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.DivergenceFree {E = LNPEv} {I = ExtI LNPEv} using (DivergenceFree)
open import CSP.Laws.Traces.TraceLawsParallelElim LNPEv-≟
  using (τL; τR; evSync; evL; evR; evBoth; Par-τ-elim; Par-ev-elim; Par-force-ret-inv; viewV-ev)
open import CSP.Laws.Traces.TraceLawsParallel LNPEv-≟ using (Par-τ-L; Par-τ-R; Par-sync; Par-soloL; Par-soloR)
open import CSP.Laws.DivFree.Loop LNPEv-≟ using (itτ; itBack; iter-τ-elim; iter-ev-elim)
open import CSP.Laws.DivFree.Count LNPEv-≟ using (out-cont)

------------------------------------------------------------------------
-- §0  Generic step lemmas (no Leios content)
------------------------------------------------------------------------

-- the process trees of this module
Tree : Set₁
Tree = PTree LNPEv (ExtI LNPEv) Rr

-- a decision of `x ≟ x` is `yes refl`
≟-refl : ∀ {A : Set} ⦃ _ : DecEq A ⦄ (x : A) → (x ≟ x) ≡ yes refl
≟-refl x with x ≟ x
... | yes refl = refl
... | no ¬p    = ⊥-elim (¬p refl)

-- the visible-offer map of a tree (used to STATE an offer of a `pchoice` menu)
vOf : ∀ {R : Set} → PTree LNPEv (ExtI LNPEv) R → (at : AnyTypes LNPEv) → ContinueType at (Maybe (PTree LNPEv (ExtI LNPEv) R))
vOf t with PTree.force t
... | react v _ = v
... | _         = λ _ _ → nothing

-- a menu's offer is a visible step
pchS : ∀ {R : Set} {v} {at : AnyTypes LNPEv} {a : proj₁ at} {t′ : PTree LNPEv (ExtI LNPEv) R}
     → v at a ≡ just t′ → pchoice v ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► t′
pchS eq = sVis refl eq

-- an output fires its own event
outS : ∀ {R : Set} {A : Set} ⦃ _ : DecEq A ⦄ (e : LNPEv A) (v : A) (P : PTree LNPEv (ExtI LNPEv) R)
     → Output e v P ─[ ev (evl (evLabel A e v)) ]─► P
outS {A = A} e v P = sVis refl oc
  where
  -- the matching output branch fires
  oc : Output-cont e v P (A , e) v ≡ just P
  oc with LNPEv-≟ (A , e) (A , e)
  ... | no ¬p    = ⊥-elim (¬p refl)
  ... | yes refl with v ≟ v
  ...   | yes _  = refl
  ...   | no ¬p  = ⊥-elim (¬p refl)

-- an output's only visible step is its own event, into its continuation
outI : ∀ {R : Set} {A : Set} ⦃ _ : DecEq A ⦄ {e : LNPEv A} {v : A} {P t′ : PTree LNPEv (ExtI LNPEv) R} {x}
     → Output e v P ─[ ev (evl x) ]─► t′ → x ≡ evLabel A e v × t′ ≡ P
outI {e = e} {v} {P} (sVis refl br) = out-cont e v P br

-- a menu, an output or a prefix makes no τ
pchNoτ : ∀ {R : Set} {v} {t′ : PTree LNPEv (ExtI LNPEv) R} → pchoice v ─[ τ ]─► t′ → ⊥
pchNoτ (sSil ())
pchNoτ (sTau refl ())

-- (an output)
outNoτ : ∀ {R : Set} {A : Set} ⦃ _ : DecEq A ⦄ {e : LNPEv A} {v : A} {P t′ : PTree LNPEv (ExtI LNPEv) R}
       → Output e v P ─[ τ ]─► t′ → ⊥
outNoτ (sSil ())
outNoτ (sTau refl ())

-- a visible step of the body lifts through `iter-bind`
iterE : ∀ {A : Set} {k : A → PTree LNPEv (ExtI LNPEv) (A ⊎ Rr)} {T T′ : PTree LNPEv (ExtI LNPEv) (A ⊎ Rr)} {x}
      → T ─[ ev (evl x) ]─► T′ → iter-bind T k ─[ ev (evl x) ]─► iter-bind T′ k
iterE {k = k} {T} {T′} (sVis {v = v} {τc = τc} {at = at} {a = a} eqT br) = sVis eqF eqB
  where
  -- the bound node is the body's react node, re-wrapped
  eqF : PTree.force (iter-bind T k) ≡ react (iterV k (react v τc)) (iterT k (react v τc))
  eqF rewrite eqT = refl
  -- … whose offer is the body's offer, re-wrapped
  eqB : iterV k (react v τc) at a ≡ just (iter-bind T′ k)
  eqB rewrite br = refl

-- the steps of an `iter-bind` over a body that makes no τ and does not return:
-- every τ is impossible, every visible step is the body's
module IterNoτ {A : Set} {k : A → PTree LNPEv (ExtI LNPEv) (A ⊎ Rr)} {T : PTree LNPEv (ExtI LNPEv) (A ⊎ Rr)}
               (noτ : ∀ {T′} → T ─[ τ ]─► T′ → ⊥) (noRet : ∀ {r} → PTree.force T ≡ ret r → ⊥) where

  -- no τ
  τ✗ : ∀ {t′} → iter-bind T k ─[ τ ]─► t′ → ⊥
  τ✗ st with iter-τ-elim T k st
  ... | itτ _ st′ _    = noτ st′
  ... | itBack _ eq _  = noRet eq

  -- no return
  ret✗ : ∀ {r} → PTree.force (iter-bind T k) ≡ ret r → ⊥
  ret✗ eq with PTree.force T
  ... | ret (inj₁ _) = case eq of λ ()
  ... | ret (inj₂ r) = noRet refl
  ... | sil _        = case eq of λ ()
  ... | react _ _    = case eq of λ ()

-- a `Par⊤` of two returned operands has returned
Par-ret : ∀ {A : EventSet} {P Q : Tree} → PTree.force P ≡ ret tt → PTree.force Q ≡ ret tt
        → PTree.force (Par⊤ A P Q) ≡ ret tt
Par-ret eP eQ rewrite eP | eQ = refl

------------------------------------------------------------------------
-- §1  Abstract labels and abstractions (for one link `l`)
------------------------------------------------------------------------

-- everything below is for one link `l`
module _ (l : Link) where

  -- the abstract labels: a wire send / receive, an api event, a peer-local done,
  -- at link `l` and the given direction
  data Lab : Set where
    wS wR : Dir → Payload → Lab
    ap    : Dir → (m : ApiLPTag) → ApiLPCar m → Lab
    dn    : Dir → Lab

  -- the concrete event of an abstract label
  ⌜_⌝ : Lab → Event
  ⌜ wS d x ⌝   = evLabel _ (sendLNP l d) x
  ⌜ wR d x ⌝   = evLabel _ (receiveLNP l d) x
  ⌜ ap d m v ⌝ = evLabel _ (apiLPev l d m) v
  ⌜ dn d ⌝     = evLabel _ (doneLNP l d) U.tt

  -- reading an event back as a label (link ignored)
  decode : Event → Maybe Lab
  decode (evLabel _ (sendLNP _ d) x)    = just (wS d x)
  decode (evLabel _ (receiveLNP _ d) x) = just (wR d x)
  decode (evLabel _ (apiLPev _ d m) v)  = just (ap d m v)
  decode (evLabel _ (doneLNP _ d) _)    = just (dn d)

  -- decoding inverts `⌜_⌝`
  decode-⌜⌝ : ∀ ω → decode ⌜ ω ⌝ ≡ just ω
  decode-⌜⌝ (wS _ _)   = refl
  decode-⌜⌝ (wR _ _)   = refl
  decode-⌜⌝ (ap _ _ _) = refl
  decode-⌜⌝ (dn _)     = refl

  -- `⌜_⌝` is injective
  ⌜⌝-inj : ∀ {ω ω′} → ⌜ ω ⌝ ≡ ⌜ ω′ ⌝ → ω ≡ ω′
  ⌜⌝-inj {ω} {ω′} eq = just-injective (trans (sym (decode-⌜⌝ ω)) (trans (cong decode eq) (decode-⌜⌝ ω′)))

  -- an abstract step label: τ or a visible label (√ is `Fin`)
  data ALbl : Set where
    τ′  : ALbl
    ev′ : Lab → ALbl

  -- an event lies in an event set
  InEv : EventSet → Event → Set
  InEv W e = W .mem (Event.A e , Event.e e) (Event.a e)

  -- an abstract label lies in an event set
  InE : EventSet → Lab → Set
  InE W ω = InEv W ⌜ ω ⌝

  -- an ABSTRACTION of a family of trees: a position predicate `Pos σ t`, abstract
  -- steps, final states, an alphabet, a τ-measure, and the three ELIM facts (every
  -- concrete step / return of a positioned tree is an abstract one)
  record Abs (S : Set) : Set₂ where
    field
      Pos   : S → Tree → Set₁
      Stp   : S → ALbl → S → Set
      Fin   : S → Set
      Alpha : Lab → Set
      alpha : ∀ {σ ω σ′} → Stp σ (ev′ ω) σ′ → Alpha ω
      μ     : S → ℕ
      μτ    : ∀ {σ σ′} → Stp σ τ′ σ′ → μ σ′ < μ σ
      elimτ : ∀ {σ t t′} → Pos σ t → t ─[ τ ]─► t′ → Σ[ σ′ ∈ S ] (Stp σ τ′ σ′ × Pos σ′ t′)
      elimE : ∀ {σ t t′ e} → Pos σ t → t ─[ ev (evl e) ]─► t′
            → Σ[ ω ∈ Lab ] Σ[ σ′ ∈ S ] (e ≡ ⌜ ω ⌝ × Stp σ (ev′ ω) σ′ × Pos σ′ t′)
      elimR : ∀ {σ t r} → Pos σ t → PTree.force t ≡ ret r → Fin σ

  -- … and its INTRO facts (every abstract step / final state is a concrete one)
  record AbsI {S : Set} (A : Abs S) : Set₂ where
    open Abs A
    field
      introτ : ∀ {σ σ′ t} → Pos σ t → Stp σ τ′ σ′ → Σ[ t′ ∈ Tree ] (t ─[ τ ]─► t′ × Pos σ′ t′)
      introE : ∀ {σ σ′ t ω} → Pos σ t → Stp σ (ev′ ω) σ′
             → Σ[ t′ ∈ Tree ] (t ─[ ev (evl ⌜ ω ⌝) ]─► t′ × Pos σ′ t′)
      introR : ∀ {σ t} → Pos σ t → Fin σ → PTree.force t ≡ ret tt

  ------------------------------------------------------------------------
  -- §2  What an abstraction gives
  ------------------------------------------------------------------------

  -- the elim side
  module Gen {S : Set} (A : Abs S) where
    open Abs A

    -- an abstract run, recording the concrete visible events
    data ARun : S → List Event → S → Set₁ where
      r0 : ∀ {σ} → ARun σ [] σ
      rτ : ∀ {σ σ′ σ″ s} → Stp σ τ′ σ′ → ARun σ′ s σ″ → ARun σ s σ″
      rE : ∀ {σ σ′ σ″ s ω} → Stp σ (ev′ ω) σ′ → ARun σ′ s σ″ → ARun σ (⌜ ω ⌝ ∷ s) σ″

    -- every √-free run of a positioned tree is an abstract run
    runE : ∀ {σ t s t′} → Pos σ t → t ⟹∖√⟨ s ⟩ t′ → Σ[ σ′ ∈ S ] (ARun σ s σ′ × Pos σ′ t′)
    runE p ∖√-refl = _ , r0 , p
    runE p (∖√-τ st r) with elimτ p st
    ... | _ , a , p₁ with runE p₁ r
    ...   | σ′ , ar , p′ = σ′ , rτ a ar , p′
    runE p (∖√-ev st r) with elimE p st
    ... | ω , _ , refl , a , p₁ with runE p₁ r
    ...   | σ′ , ar , p′ = σ′ , rE a ar , p′

    -- a positioned tree with no abstract step that has not terminated is stuck
    stuckE : ∀ {σ t} → Pos σ t → (∀ {ℓ σ′} → Stp σ ℓ σ′ → ⊥) → (Fin σ → ⊥) → IsStuck t
    stuckE p ns nf {τ} st with elimτ p st
    ... | _ , a , _ = ns a
    stuckE p ns nf {ev (evl e)} st with elimE p st
    ... | _ , _ , _ , a , _ = ns a
    stuckE p ns nf {ev (√ r)} (sRet eq) = nf (elimR p eq)

    -- a positioned tree does not diverge (the τ-measure decreases)
    noDiv : ∀ {σ t} → Pos σ t → Diverges t → ⊥
    noDiv {σ} p d = go (suc (μ σ)) ≤-refl p d
      where
      -- by induction on a bound of the measure
      go : ∀ n {σ t} → μ σ < n → Pos σ t → Diverges t → ⊥
      go zero      () _ _
      go (suc n) (s≤s lt) p d with elimτ p (Diverges.step d)
      ... | _ , a , p′ = go n (<-≤-trans (μτ a) lt) p′ (Diverges.rest d)

    -- every tree reachable from a positioned one is divergence-free
    divFree : ∀ {σ t} → Pos σ t → DivergenceFree t
    divFree p r d with runE p r
    ... | _ , _ , p′ = noDiv p′ d

  -- the intro side
  module GenI {S : Set} {A : Abs S} (I : AbsI A) where
    open Abs A
    open AbsI I
    open Gen A

    -- an abstract run of a positioned tree is a concrete √-free run
    runI : ∀ {σ s σ′ t} → ARun σ s σ′ → Pos σ t → Σ[ t′ ∈ Tree ] (t ⟹∖√⟨ s ⟩ t′ × Pos σ′ t′)
    runI r0 p = _ , ∖√-refl , p
    runI (rτ a ar) p with introτ p a
    ... | _ , st , p₁ with runI ar p₁
    ...   | t′ , r , p′ = t′ , ∖√-τ st r , p′
    runI (rE a ar) p with introE p a
    ... | _ , st , p₁ with runI ar p₁
    ...   | t′ , r , p′ = t′ , ∖√-ev st r , p′

    -- a positioned tree with an abstract step, or terminated, is not stuck
    notStuck : ∀ {σ t} → Pos σ t → (Fin σ ⊎ Σ[ ℓ ∈ ALbl ] Σ[ σ′ ∈ S ] Stp σ ℓ σ′) → IsStuck t → ⊥
    notStuck p (inj₁ f)               stk = stk (sRet (introR p f))
    notStuck p (inj₂ (τ′ , _ , a))    stk = stk (proj₁ (proj₂ (introτ p a)))
    notStuck p (inj₂ (ev′ _ , _ , a)) stk = stk (proj₁ (proj₂ (introE p a)))

  ------------------------------------------------------------------------
  -- §3  Abstractions compose under `Par⊤`
  ------------------------------------------------------------------------

  -- the product of two abstractions, synchronised on `W` (operand alphabets meet only in `W`)
  module Prod {S₁ S₂ : Set} (A₁ : Abs S₁) (A₂ : Abs S₂) (W : EventSet)
              (disj : ∀ {ω} → Abs.Alpha A₁ ω → Abs.Alpha A₂ ω → ¬ InE W ω → ⊥) where
    open Abs A₁ renaming (Pos to Pos₁; Stp to Stp₁; Fin to Fin₁; Alpha to Alpha₁; alpha to alpha₁
                         ; μ to μ₁; μτ to μτ₁; elimτ to elimτ₁; elimE to elimE₁; elimR to elimR₁)
    open Abs A₂ renaming (Pos to Pos₂; Stp to Stp₂; Fin to Fin₂; Alpha to Alpha₂; alpha to alpha₂
                         ; μ to μ₂; μτ to μτ₂; elimτ to elimτ₂; elimE to elimE₂; elimR to elimR₂)

    -- the steps of the product: either side's τ, a synchronised step on `W`, a solo step off `W`
    data PStp : S₁ × S₂ → ALbl → S₁ × S₂ → Set where
      pτL : ∀ {σ₁ σ₁′ σ₂} → Stp₁ σ₁ τ′ σ₁′ → PStp (σ₁ , σ₂) τ′ (σ₁′ , σ₂)
      pτR : ∀ {σ₁ σ₂ σ₂′} → Stp₂ σ₂ τ′ σ₂′ → PStp (σ₁ , σ₂) τ′ (σ₁ , σ₂′)
      psy : ∀ {σ₁ σ₁′ σ₂ σ₂′ ω} → InE W ω → Stp₁ σ₁ (ev′ ω) σ₁′ → Stp₂ σ₂ (ev′ ω) σ₂′
          → PStp (σ₁ , σ₂) (ev′ ω) (σ₁′ , σ₂′)
      psL : ∀ {σ₁ σ₁′ σ₂ ω} → ¬ InE W ω → Stp₁ σ₁ (ev′ ω) σ₁′ → PStp (σ₁ , σ₂) (ev′ ω) (σ₁′ , σ₂)
      psR : ∀ {σ₁ σ₂ σ₂′ ω} → ¬ InE W ω → Stp₂ σ₂ (ev′ ω) σ₂′ → PStp (σ₁ , σ₂) (ev′ ω) (σ₁ , σ₂′)

    -- a product position: the tree is the `Par⊤` of two positioned operands
    PPos : S₁ × S₂ → Tree → Set₁
    PPos (σ₁ , σ₂) t = Σ[ t₁ ∈ Tree ] Σ[ t₂ ∈ Tree ] (t ≡ Par⊤ W t₁ t₂ × Pos₁ σ₁ t₁ × Pos₂ σ₂ t₂)

    -- the right operand does not offer a left-alphabet label off `W`
    noOffer : ∀ {σ₂ t₂ ω} → Pos₂ σ₂ t₂ → Alpha₁ ω → ¬ InE W ω
            → viewV (PTree.force t₂) (Event.A ⌜ ω ⌝ , Event.e ⌜ ω ⌝) (Event.a ⌜ ω ⌝) ≡ nothing
    noOffer {t₂ = t₂} {ω} p₂ al ¬w with viewV (PTree.force t₂) (Event.A ⌜ ω ⌝ , Event.e ⌜ ω ⌝) (Event.a ⌜ ω ⌝) in eq
    ... | nothing = refl
    ... | just _ with elimE₂ p₂ (viewV-ev {P = t₂} refl eq)
    ...   | ω′ , _ , e′ , a′ , _ with ⌜⌝-inj e′
    ...     | refl = ⊥-elim (disj al (alpha₂ a′) ¬w)

    -- (symmetric)
    noOfferL : ∀ {σ₁ t₁ ω} → Pos₁ σ₁ t₁ → Alpha₂ ω → ¬ InE W ω
             → viewV (PTree.force t₁) (Event.A ⌜ ω ⌝ , Event.e ⌜ ω ⌝) (Event.a ⌜ ω ⌝) ≡ nothing
    noOfferL {t₁ = t₁} {ω} p₁ al ¬w with viewV (PTree.force t₁) (Event.A ⌜ ω ⌝ , Event.e ⌜ ω ⌝) (Event.a ⌜ ω ⌝) in eq
    ... | nothing = refl
    ... | just _ with elimE₁ p₁ (viewV-ev {P = t₁} refl eq)
    ...   | ω′ , _ , e′ , a′ , _ with ⌜⌝-inj e′
    ...     | refl = ⊥-elim (disj (alpha₁ a′) al ¬w)

    -- the product abstraction
    ParA : Abs (S₁ × S₂)
    ParA .Abs.Pos = PPos
    ParA .Abs.Stp = PStp
    ParA .Abs.Fin (σ₁ , σ₂) = Fin₁ σ₁ × Fin₂ σ₂
    ParA .Abs.Alpha ω = Alpha₁ ω ⊎ Alpha₂ ω
    ParA .Abs.alpha (psy _ a _) = inj₁ (alpha₁ a)
    ParA .Abs.alpha (psL _ a)   = inj₁ (alpha₁ a)
    ParA .Abs.alpha (psR _ a)   = inj₂ (alpha₂ a)
    ParA .Abs.μ (σ₁ , σ₂) = μ₁ σ₁ + μ₂ σ₂
    ParA .Abs.μτ {_ , σ₂} (pτL a) = +-monoˡ-< (μ₂ σ₂) (μτ₁ a)
    ParA .Abs.μτ {σ₁ , _} (pτR a) = +-monoʳ-< (μ₁ σ₁) (μτ₂ a)
    ParA .Abs.elimτ (t₁ , t₂ , refl , p₁ , p₂) st with Par-τ-elim W (λ _ _ → tt) t₁ t₂ st
    ... | τL t₁′ st₁ refl with elimτ₁ p₁ st₁
    ...   | _ , a , p₁′ = _ , pτL a , (t₁′ , t₂ , refl , p₁′ , p₂)
    ParA .Abs.elimτ (t₁ , t₂ , refl , p₁ , p₂) st | τR t₂′ st₂ refl with elimτ₂ p₂ st₂
    ...   | _ , a , p₂′ = _ , pτR a , (t₁ , t₂′ , refl , p₁ , p₂′)
    ParA .Abs.elimE (t₁ , t₂ , refl , p₁ , p₂) st with Par-ev-elim W (λ _ _ → tt) t₁ t₂ st
    ... | evSync m st₁ st₂ with elimE₁ p₁ st₁ | elimE₂ p₂ st₂
    ...   | ω₁ , _ , e₁ , a₁ , p₁′ | ω₂ , _ , e₂ , a₂ , p₂′ with ⌜⌝-inj (trans (sym e₁) e₂)
    ...     | refl = ω₁ , _ , e₁ , psy (subst (InEv W) e₁ m) a₁ a₂ , (_ , _ , refl , p₁′ , p₂′)
    ParA .Abs.elimE (t₁ , t₂ , refl , p₁ , p₂) st | evL ¬m st₁ with elimE₁ p₁ st₁
    ...   | ω₁ , _ , e₁ , a₁ , p₁′ = ω₁ , _ , e₁ , psL (λ i → ¬m (subst (InEv W) (sym e₁) i)) a₁ , (_ , _ , refl , p₁′ , p₂)
    ParA .Abs.elimE (t₁ , t₂ , refl , p₁ , p₂) st | evR ¬m st₂ with elimE₂ p₂ st₂
    ...   | ω₂ , _ , e₂ , a₂ , p₂′ = ω₂ , _ , e₂ , psR (λ i → ¬m (subst (InEv W) (sym e₂) i)) a₂ , (_ , _ , refl , p₁ , p₂′)
    ParA .Abs.elimE (t₁ , t₂ , refl , p₁ , p₂) st | evBoth ¬m st₁ st₂ with elimE₁ p₁ st₁ | elimE₂ p₂ st₂
    ...   | ω₁ , _ , e₁ , a₁ , _ | ω₂ , _ , e₂ , a₂ , _ with ⌜⌝-inj (trans (sym e₁) e₂)
    ...     | refl = ⊥-elim (disj (alpha₁ a₁) (alpha₂ a₂) (λ i → ¬m (subst (InEv W) (sym e₁) i)))
    ParA .Abs.elimR (t₁ , t₂ , refl , p₁ , p₂) eq with Par-force-ret-inv W (λ _ _ → tt) eq
    ... | _ , _ , f₁ , f₂ , _ = elimR₁ p₁ f₁ , elimR₂ p₂ f₂

    -- the product's intro facts, from the operands'
    ParI : AbsI A₁ → AbsI A₂ → AbsI ParA
    ParI I₁ I₂ .AbsI.introτ (t₁ , t₂ , refl , p₁ , p₂) (pτL a) with AbsI.introτ I₁ p₁ a
    ... | t₁′ , st , p₁′ = _ , Par-τ-L W (λ _ _ → tt) t₁ t₂ st , (t₁′ , t₂ , refl , p₁′ , p₂)
    ParI I₁ I₂ .AbsI.introτ (t₁ , t₂ , refl , p₁ , p₂) (pτR a) with AbsI.introτ I₂ p₂ a
    ... | t₂′ , st , p₂′ = _ , Par-τ-R W (λ _ _ → tt) t₁ t₂ st , (t₁ , t₂′ , refl , p₁ , p₂′)
    ParI I₁ I₂ .AbsI.introE (t₁ , t₂ , refl , p₁ , p₂) (psy m a₁ a₂) with AbsI.introE I₁ p₁ a₁ | AbsI.introE I₂ p₂ a₂
    ... | t₁′ , st₁ , p₁′ | t₂′ , st₂ , p₂′ = _ , Par-sync W (λ _ _ → tt) t₁ t₂ m st₁ st₂ , (t₁′ , t₂′ , refl , p₁′ , p₂′)
    ParI I₁ I₂ .AbsI.introE (t₁ , t₂ , refl , p₁ , p₂) (psL ¬m a₁) with AbsI.introE I₁ p₁ a₁
    ... | t₁′ , st₁ , p₁′ = _ , Par-soloL W (λ _ _ → tt) t₁ t₂ ¬m st₁ (noOffer p₂ (alpha₁ a₁) ¬m) , (t₁′ , t₂ , refl , p₁′ , p₂)
    ParI I₁ I₂ .AbsI.introE (t₁ , t₂ , refl , p₁ , p₂) (psR ¬m a₂) with AbsI.introE I₂ p₂ a₂
    ... | t₂′ , st₂ , p₂′ = _ , Par-soloR W (λ _ _ → tt) t₁ t₂ ¬m st₂ (noOfferL p₁ (alpha₂ a₂) ¬m) , (t₁ , t₂′ , refl , p₁ , p₂′)
    ParI I₁ I₂ .AbsI.introR (t₁ , t₂ , refl , p₁ , p₂) (f₁ , f₂) = Par-ret {W} (AbsI.introR I₁ p₁ f₁) (AbsI.introR I₂ p₂ f₂)

  ------------------------------------------------------------------------
  -- §3b  The server's renaming: its wire events, named from the client end
  ------------------------------------------------------------------------

  -- the other direction of the link
  flipD : Dir → Dir
  flipD lo = hi
  flipD hi = lo

  -- the renaming on concrete events: a send becomes the receive at the other end of the
  -- link and vice versa; api / done are unchanged (an involution)
  sw : (bt : AnyTypes LNPEv) → proj₁ bt → ConcEvent₁
  sw (_ , sendLNP l′ d)    x = (_ , receiveLNP l′ (flipD d)) , x
  sw (_ , receiveLNP l′ d) x = (_ , sendLNP l′ (flipD d)) , x
  sw (_ , apiLPev l′ d m)  v = (_ , apiLPev l′ d m) , v
  sw (_ , doneLNP l′ d)    u = (_ , doneLNP l′ d) , u

  -- the renaming's preimage map: every target event has exactly one source
  sinv : (bt : AnyTypes LNPEv) → proj₁ bt → Maybe ConcEvent₁
  sinv bt b = just (sw bt b)

  -- a renamed tree
  R : Tree → Tree
  R t = renameInv t sinv

  -- a concrete event, as an `Event`
  toE : ConcEvent₁ → Event
  toE (at , a) = evLabel (proj₁ at) (proj₂ at) a

  -- the renaming on `Event`s
  swE : Event → Event
  swE (evLabel A e a) = toE (sw (A , e) a)

  -- the renaming is an involution
  sw-sw : ∀ bt b → sw (proj₁ (sw bt b)) (proj₂ (sw bt b)) ≡ (bt , b)
  sw-sw (_ , sendLNP _ lo)    _ = refl
  sw-sw (_ , sendLNP _ hi)    _ = refl
  sw-sw (_ , receiveLNP _ lo) _ = refl
  sw-sw (_ , receiveLNP _ hi) _ = refl
  sw-sw (_ , apiLPev _ _ _)   _ = refl
  sw-sw (_ , doneLNP _ _)     _ = refl

  -- the SOURCE label (what the unrenamed server does) of a renamed label
  sl : Lab → Lab
  sl (wS d x)   = wR (flipD d) x
  sl (wR d x)   = wS (flipD d) x
  sl (ap d m v) = ap d m v
  sl (dn d)     = dn d

  -- renaming the source event of a label gives the label's event
  swE-sl : ∀ ω → swE ⌜ sl ω ⌝ ≡ ⌜ ω ⌝
  swE-sl (wS lo _)  = refl
  swE-sl (wS hi _)  = refl
  swE-sl (wR lo _)  = refl
  swE-sl (wR hi _)  = refl
  swE-sl (ap _ _ _) = refl
  swE-sl (dn _)     = refl

  -- a visible step of a renamed tree is the renaming of a visible step of its source
  renEv : ∀ {t₀ W : Tree} {e} → R t₀ ─[ ev (evl e) ]─► W
        → Σ[ e₀ ∈ Event ] Σ[ P₁ ∈ Tree ] (t₀ ─[ ev (evl e₀) ]─► P₁ × e ≡ swE e₀ × W ≡ R P₁)
  renEv {t₀} st with TR.ren-ev-inv {inv = sinv} {P = t₀} st
  ... | inj₁ (at , a , bt , b , P₁ , st₀ , eqi , refl , refl) =
        evLabel (proj₁ at) (proj₂ at) a , P₁ , st₀
      , cong toE (trans (sym (sw-sw bt b)) (cong (λ c → sw (proj₁ c) (proj₂ c)) (just-injective eqi)))
      , refl
  ... | inj₂ (_ , () , _ , _)

  -- a source step on a label's source event lifts to the renamed tree, on the label's event
  rF : ∀ ω {t₀ t₁ : Tree} → t₀ ─[ ev (evl ⌜ sl ω ⌝) ]─► t₁ → R t₀ ─[ ev (evl ⌜ ω ⌝) ]─► R t₁
  rF (wS d x) st =
    TR.ren-ev-fwd {inv = sinv} {at = _ , receiveLNP l (flipD d)} {a = x} {bt = _ , sendLNP l d} {b = x} st refl
  rF (wR d x) st =
    TR.ren-ev-fwd {inv = sinv} {at = _ , sendLNP l (flipD d)} {a = x} {bt = _ , receiveLNP l d} {b = x} st refl
  rF (ap d m v) st =
    TR.ren-ev-fwd {inv = sinv} {at = _ , apiLPev l d m} {a = v} {bt = _ , apiLPev l d m} {b = v} st refl
  rF (dn d) st =
    TR.ren-ev-fwd {inv = sinv} {at = _ , doneLNP l d} {a = U.tt} {bt = _ , doneLNP l d} {b = U.tt} st refl

  ------------------------------------------------------------------------
  -- §4  The components and their abstractions
  ------------------------------------------------------------------------

  -- a payload as the peers build it
  pay : Mode → MessageLeiosNotifyP → Payload
  pay md m = time₀ , md , length₀ , leiosNotifyP m

  -- 1 for a pending loop-back τ, 0 otherwise (the τ-measure of every component)
  fl : Bool → ℕ
  fl true  = 1
  fl false = 0

  -- a pending loop-back τ removes itself
  fl< : fl false < fl true
  fl< = s≤s z≤n

  ---------------------------------------------------------------- the client

  -- a reply the client delivers to its api
  data Dlv : Set where
    dAnn : Header → Dlv
    dOff : EBHash × LSlot → Size → Dlv
    dTxs : EBHash × LSlot → Dlv
    dVot : List VoteBlob → Dlv

  -- the client's delivery continuation (exactly `clientStepP`'s)
  dlvT : Dlv → PTree LNPEv (ExtI LNPEv) (LNPState ⊎ Rr)
  dlvT (dAnn h)    = apiLPev l lo lnpRecvBlockAnnouncement ! h ⟶ Ret (inj₁ stIdle)
  dlvT (dOff q sz) = Output ⦃ DecEq-Offer ⦄ (apiLPev l lo lnpRecvBlockOffer) (q , sz) (Ret (inj₁ stIdle))
  dlvT (dTxs q)    = Output ⦃ DecEq-EBPoint ⦄ (apiLPev l lo lnpRecvBlockTxsOffer) q (Ret (inj₁ stIdle))
  dlvT (dVot vs)   = Output ⦃ iV ⦄ (apiLPev l lo lnpRecvVotes) vs (Ret (inj₁ stIdle))

  -- the client's phases: the three table menus (StIdle / StBusy / StQuit), the two
  -- committed sends, a delivery, the end
  data CS : Set where
    cI cB cQ cR cS cE : CS
    cD : Dlv → CS

  -- the client's loop body, at `(l , lo)`
  kc : LNPState → PTree LNPEv (ExtI LNPEv) (LNPState ⊎ Rr)
  kc = clientStepP l lo

  -- where a client tree is (the flag marks a pending loop-back τ)
  data CPos : CS × Bool → Tree → Set₁ where
    cpI  : CPos (cI , false) (iter kc stIdle)
    cpB  : CPos (cB , false) (iter kc stBusy)
    cpQ  : CPos (cQ , false) (iter kc stQuit)
    cpI′ : CPos (cI , true) (iter-bind (Ret (inj₁ stIdle)) kc)
    cpB′ : CPos (cB , true) (iter-bind (Ret (inj₁ stBusy)) kc)
    cpQ′ : CPos (cQ , true) (iter-bind (Ret (inj₁ stQuit)) kc)
    cpR  : CPos (cR , false) (iter-bind (snd l lo FromInitiator MsgLNPRequestNext stBusy) kc)
    cpS  : CPos (cS , false) (iter-bind (snd l lo FromInitiator MsgLNPQuit stQuit) kc)
    cpD  : ∀ dv → CPos (cD dv , false) (iter-bind (dlvT dv) kc)
    cpE  : CPos (cE , false) (iter-bind (Ret (inj₂ tt)) kc)

  -- the client's abstract steps (one constructor per table transition / api event)
  data CStp : CS × Bool → ALbl → CS × Bool → Set where
    cτI : CStp (cI , true) τ′ (cI , false)
    cτB : CStp (cB , true) τ′ (cB , false)
    cτQ : CStp (cQ , true) τ′ (cQ , false)
    cRN : ∀ u → CStp (cI , false) (ev′ (ap lo lnpSendRequestNext u)) (cR , false)
    cQi : ∀ u → CStp (cI , false) (ev′ (ap lo lnpSendDone u)) (cS , false)
    cSR : CStp (cR , false) (ev′ (wS lo (pay FromInitiator MsgLNPRequestNext))) (cB , true)
    cSQ : CStp (cS , false) (ev′ (wS lo (pay FromInitiator MsgLNPQuit))) (cQ , true)
    cRA : ∀ {tm md ln} h    → CStp (cB , false) (ev′ (wR lo (tm , md , ln , leiosNotifyP (MsgLNPBlockAnnouncement h)))) (cD (dAnn h) , false)
    cRO : ∀ {tm md ln} q sz → CStp (cB , false) (ev′ (wR lo (tm , md , ln , leiosNotifyP (MsgLNPBlockOffer q sz)))) (cD (dOff q sz) , false)
    cRT : ∀ {tm md ln} q    → CStp (cB , false) (ev′ (wR lo (tm , md , ln , leiosNotifyP (MsgLNPBlockTxsOffer q)))) (cD (dTxs q) , false)
    cRV : ∀ {tm md ln} vs   → CStp (cB , false) (ev′ (wR lo (tm , md , ln , leiosNotifyP (MsgLNPVotes vs)))) (cD (dVot vs) , false)
    cRC : ∀ {tm md ln}      → CStp (cB , false) (ev′ (wR lo (tm , md , ln , leiosNotifyP MsgLNPCanceled))) (cI , true)
    cDA : ∀ h    → CStp (cD (dAnn h) , false) (ev′ (ap lo lnpRecvBlockAnnouncement h)) (cI , true)
    cDO : ∀ q sz → CStp (cD (dOff q sz) , false) (ev′ (ap lo lnpRecvBlockOffer (q , sz))) (cI , true)
    cDT : ∀ q    → CStp (cD (dTxs q) , false) (ev′ (ap lo lnpRecvBlockTxsOffer q)) (cI , true)
    cDV : ∀ vs   → CStp (cD (dVot vs) , false) (ev′ (ap lo lnpRecvVotes vs)) (cI , true)
    cDn : ∀ {tm md ln}      → CStp (cQ , false) (ev′ (wR lo (tm , md , ln , leiosNotifyP MsgLNPDone))) (cE , false)

  -- the client has terminated
  CFin : CS × Bool → Set
  CFin (cE , _) = U.⊤
  CFin _        = ⊥

  -- the client's alphabet: its wire cell and its api, at direction `lo`
  data CAl : Lab → Set where
    caS : ∀ x   → CAl (wS lo x)
    caR : ∀ x   → CAl (wR lo x)
    caA : ∀ m v → CAl (ap lo m v)

  -- the client's steps stay in its alphabet
  cAlpha : ∀ {σ ω σ′} → CStp σ (ev′ ω) σ′ → CAl ω
  cAlpha (cRN _)   = caA _ _
  cAlpha (cQi _)   = caA _ _
  cAlpha cSR       = caS _
  cAlpha cSQ       = caS _
  cAlpha (cRA _)   = caR _
  cAlpha (cRO _ _) = caR _
  cAlpha (cRT _)   = caR _
  cAlpha (cRV _)   = caR _
  cAlpha cRC       = caR _
  cAlpha (cDA _)   = caA _ _
  cAlpha (cDO _ _) = caA _ _
  cAlpha (cDT _)   = caA _ _
  cAlpha (cDV _)   = caA _ _
  cAlpha cDn       = caR _

  -- the client's τ-measure decreases
  cμτ : ∀ {σ σ′} → CStp σ τ′ σ′ → fl (proj₂ σ′) < fl (proj₂ σ)
  cμτ cτI = fl<
  cμτ cτB = fl<
  cμτ cτQ = fl<

  -- the client makes a τ only at a loop-back
  cElimτ : ∀ {σ t t′} → CPos σ t → t ─[ τ ]─► t′ → Σ[ σ′ ∈ _ ] (CStp σ τ′ σ′ × CPos σ′ t′)
  cElimτ cpI st = ⊥-elim (IterNoτ.τ✗ pchNoτ (λ ()) st)
  cElimτ cpB st = ⊥-elim (IterNoτ.τ✗ pchNoτ (λ ()) st)
  cElimτ cpQ st = ⊥-elim (IterNoτ.τ✗ pchNoτ (λ ()) st)
  cElimτ cpI′ (sSil refl) = _ , cτI , cpI
  cElimτ cpB′ (sSil refl) = _ , cτB , cpB
  cElimτ cpQ′ (sSil refl) = _ , cτQ , cpQ
  cElimτ cpI′ (sTau () _)
  cElimτ cpB′ (sTau () _)
  cElimτ cpQ′ (sTau () _)
  cElimτ cpR st = ⊥-elim (IterNoτ.τ✗ outNoτ (λ ()) st)
  cElimτ cpS st = ⊥-elim (IterNoτ.τ✗ outNoτ (λ ()) st)
  cElimτ (cpD (dAnn _))   st = ⊥-elim (IterNoτ.τ✗ outNoτ (λ ()) st)
  cElimτ (cpD (dOff _ _)) st = ⊥-elim (IterNoτ.τ✗ (outNoτ ⦃ DecEq-Offer ⦄) (λ ()) st)
  cElimτ (cpD (dTxs _))   st = ⊥-elim (IterNoτ.τ✗ (outNoτ ⦃ DecEq-EBPoint ⦄) (λ ()) st)
  cElimτ (cpD (dVot _))   st = ⊥-elim (IterNoτ.τ✗ (outNoτ ⦃ iV ⦄) (λ ()) st)
  cElimτ cpE (sSil ())
  cElimτ cpE (sTau () _)

  -- every visible client step is an abstract one
  cElimE : ∀ {σ t t′ e} → CPos σ t → t ─[ ev (evl e) ]─► t′
         → Σ[ ω ∈ Lab ] Σ[ σ′ ∈ _ ] (e ≡ ⌜ ω ⌝ × CStp σ (ev′ ω) σ′ × CPos σ′ t′)
  cElimE cpI st with iter-ev-elim (kc stIdle) kc st
  ... | _ , st′ , refl with cIdleV st′
  ...   | ciNext u = _ , _ , refl , cRN u , cpR
  ...   | ciQuit u = _ , _ , refl , cQi u , cpS
  cElimE cpB st with iter-ev-elim (kc stBusy) kc st
  ... | _ , st′ , refl with cBusyV st′
  ...   | cbCan      = _ , _ , refl , cRC , cpI′
  ...   | cbAnn h    = _ , _ , refl , cRA h , cpD (dAnn h)
  ...   | cbOff q sz = _ , _ , refl , cRO q sz , cpD (dOff q sz)
  ...   | cbTxs q    = _ , _ , refl , cRT q , cpD (dTxs q)
  ...   | cbVote vs  = _ , _ , refl , cRV vs , cpD (dVot vs)
  cElimE cpQ st with iter-ev-elim (kc stQuit) kc st
  ... | _ , st′ , refl with cQuitV st′
  ...   | cqDone = _ , _ , refl , cDn , cpE
  cElimE cpI′ (sVis () _)
  cElimE cpB′ (sVis () _)
  cElimE cpQ′ (sVis () _)
  cElimE cpR st with iter-ev-elim (snd l lo FromInitiator MsgLNPRequestNext stBusy) kc st
  ... | _ , st′ , refl with outI st′
  ...   | refl , refl = _ , _ , refl , cSR , cpB′
  cElimE cpS st with iter-ev-elim (snd l lo FromInitiator MsgLNPQuit stQuit) kc st
  ... | _ , st′ , refl with outI st′
  ...   | refl , refl = _ , _ , refl , cSQ , cpQ′
  cElimE (cpD (dAnn h)) st with iter-ev-elim (dlvT (dAnn h)) kc st
  ... | _ , st′ , refl with outI st′
  ...   | refl , refl = _ , _ , refl , cDA h , cpI′
  cElimE (cpD (dOff q sz)) st with iter-ev-elim (dlvT (dOff q sz)) kc st
  ... | _ , st′ , refl with outI ⦃ DecEq-Offer ⦄ st′
  ...   | refl , refl = _ , _ , refl , cDO q sz , cpI′
  cElimE (cpD (dTxs q)) st with iter-ev-elim (dlvT (dTxs q)) kc st
  ... | _ , st′ , refl with outI ⦃ DecEq-EBPoint ⦄ st′
  ...   | refl , refl = _ , _ , refl , cDT q , cpI′
  cElimE (cpD (dVot vs)) st with iter-ev-elim (dlvT (dVot vs)) kc st
  ... | _ , st′ , refl with outI ⦃ iV ⦄ st′
  ...   | refl , refl = _ , _ , refl , cDV vs , cpI′
  cElimE cpE (sVis () _)

  -- a client tree returns only at the end
  cElimR : ∀ {σ t r} → CPos σ t → PTree.force t ≡ ret r → CFin σ
  cElimR cpE  _ = U.tt
  cElimR cpI  ()
  cElimR cpB  ()
  cElimR cpQ  ()
  cElimR cpI′ ()
  cElimR cpB′ ()
  cElimR cpQ′ ()
  cElimR cpR  ()
  cElimR cpS  ()
  cElimR (cpD (dAnn _))   ()
  cElimR (cpD (dOff _ _)) ()
  cElimR (cpD (dTxs _))   ()
  cElimR (cpD (dVot _))   ()

  -- the client abstraction
  CA : Abs (CS × Bool)
  CA = record { Pos = CPos ; Stp = CStp ; Fin = CFin ; Alpha = CAl ; alpha = cAlpha
              ; μ = λ σ → fl (proj₂ σ) ; μτ = cμτ
              ; elimτ = cElimτ ; elimE = cElimE ; elimR = cElimR }

  -- a client menu offer is a step of the client loop
  cOff : ∀ st {at a t′} → vOf (kc st) at a ≡ just t′
       → iter kc st ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► iter-bind t′ kc
  cOff stIdle eq = iterE (pchS eq)
  cOff stBusy eq = iterE (pchS eq)
  cOff stQuit eq = iterE (pchS eq)

  -- every abstract client τ is a concrete one
  cIntroτ : ∀ {σ σ′ t} → CPos σ t → CStp σ τ′ σ′ → Σ[ t′ ∈ Tree ] (t ─[ τ ]─► t′ × CPos σ′ t′)
  cIntroτ cpI′ cτI = _ , sSil refl , cpI
  cIntroτ cpB′ cτB = _ , sSil refl , cpB
  cIntroτ cpQ′ cτQ = _ , sSil refl , cpQ

  -- every abstract visible client step is a concrete one
  cIntroE : ∀ {σ σ′ t ω} → CPos σ t → CStp σ (ev′ ω) σ′
          → Σ[ t′ ∈ Tree ] (t ─[ ev (evl ⌜ ω ⌝) ]─► t′ × CPos σ′ t′)
  cIntroE cpI (cRN u) = _ , cOff stIdle e , cpR
    where
    -- the idle menu offers RequestNext
    e : vOf (kc stIdle) (_ , apiLPev l lo lnpSendRequestNext) u ≡ just (snd l lo FromInitiator MsgLNPRequestNext stBusy)
    e rewrite ≟-refl l = refl
  cIntroE cpI (cQi u) = _ , cOff stIdle e , cpS
    where
    -- the idle menu offers the quit
    e : vOf (kc stIdle) (_ , apiLPev l lo lnpSendDone) u ≡ just (snd l lo FromInitiator MsgLNPQuit stQuit)
    e rewrite ≟-refl l = refl
  cIntroE cpB (cRA {tm} {md} {ln} h) = _ , cOff stBusy e , cpD (dAnn h)
    where
    -- the busy menu accepts an announcement
    e : vOf (kc stBusy) (_ , receiveLNP l lo) (tm , md , ln , leiosNotifyP (MsgLNPBlockAnnouncement h)) ≡ just (dlvT (dAnn h))
    e rewrite ≟-refl l = refl
  cIntroE cpB (cRO {tm} {md} {ln} q sz) = _ , cOff stBusy e , cpD (dOff q sz)
    where
    -- the busy menu accepts an offer
    e : vOf (kc stBusy) (_ , receiveLNP l lo) (tm , md , ln , leiosNotifyP (MsgLNPBlockOffer q sz)) ≡ just (dlvT (dOff q sz))
    e rewrite ≟-refl l = refl
  cIntroE cpB (cRT {tm} {md} {ln} q) = _ , cOff stBusy e , cpD (dTxs q)
    where
    -- the busy menu accepts a txs offer
    e : vOf (kc stBusy) (_ , receiveLNP l lo) (tm , md , ln , leiosNotifyP (MsgLNPBlockTxsOffer q)) ≡ just (dlvT (dTxs q))
    e rewrite ≟-refl l = refl
  cIntroE cpB (cRV {tm} {md} {ln} vs) = _ , cOff stBusy e , cpD (dVot vs)
    where
    -- the busy menu accepts votes
    e : vOf (kc stBusy) (_ , receiveLNP l lo) (tm , md , ln , leiosNotifyP (MsgLNPVotes vs)) ≡ just (dlvT (dVot vs))
    e rewrite ≟-refl l = refl
  cIntroE cpB (cRC {tm} {md} {ln}) = _ , cOff stBusy e , cpI′
    where
    -- the busy menu accepts MsgCanceled
    e : vOf (kc stBusy) (_ , receiveLNP l lo) (tm , md , ln , leiosNotifyP MsgLNPCanceled) ≡ just (Ret (inj₁ stIdle))
    e rewrite ≟-refl l = refl
  cIntroE cpQ (cDn {tm} {md} {ln}) = _ , cOff stQuit e , cpE
    where
    -- the quit menu accepts MsgDone
    e : vOf (kc stQuit) (_ , receiveLNP l lo) (tm , md , ln , leiosNotifyP MsgLNPDone) ≡ just (Ret (inj₂ tt))
    e rewrite ≟-refl l = refl
  cIntroE cpR cSR = _ , iterE (outS (sendLNP l lo) _ _) , cpB′
  cIntroE cpS cSQ = _ , iterE (outS (sendLNP l lo) _ _) , cpQ′
  cIntroE (cpD (dAnn h))    (cDA _)   = _ , iterE (outS (apiLPev l lo lnpRecvBlockAnnouncement) _ _) , cpI′
  cIntroE (cpD (dOff q sz)) (cDO _ _) = _ , iterE (outS ⦃ DecEq-Offer ⦄ (apiLPev l lo lnpRecvBlockOffer) _ _) , cpI′
  cIntroE (cpD (dTxs q))    (cDT _)   = _ , iterE (outS ⦃ DecEq-EBPoint ⦄ (apiLPev l lo lnpRecvBlockTxsOffer) _ _) , cpI′
  cIntroE (cpD (dVot vs))   (cDV _)   = _ , iterE (outS ⦃ iV ⦄ (apiLPev l lo lnpRecvVotes) _ _) , cpI′

  -- the terminated client has returned
  cIntroR : ∀ {σ t} → CPos σ t → CFin σ → PTree.force t ≡ ret tt
  cIntroR cpE _ = refl

  -- the client's intro facts
  CI : AbsI CA
  CI = record { introτ = cIntroτ ; introE = cIntroE ; introR = cIntroR }

  ---------------------------------------------------------------- the server

  -- what the server sends from StBusy: a notification, or the cancel
  data Rep : Set where
    rA : Header → Rep
    rO : EBHash × LSlot → Size → Rep
    rT : EBHash × LSlot → Rep
    rV : List VoteBlob → Rep
    rC : Rep

  -- its message
  repM : Rep → MessageLeiosNotifyP
  repM (rA h)    = MsgLNPBlockAnnouncement h
  repM (rO q sz) = MsgLNPBlockOffer q sz
  repM (rT q)    = MsgLNPBlockTxsOffer q
  repM (rV vs)   = MsgLNPVotes vs
  repM rC        = MsgLNPCanceled

  -- the server's phases: the three table menus, the committed reply / Done sends, the end
  data SS : Set where
    sI sB sQ sD sE : SS
    sN : Rep → SS

  -- the server's loop body, at `(l , hi)`
  ks : LNPState → PTree LNPEv (ExtI LNPEv) (LNPState ⊎ Rr)
  ks = serverStepP l hi

  -- where an (unrenamed) server tree is
  data SPos₀ : SS × Bool → Tree → Set₁ where
    spI  : SPos₀ (sI , false) (iter ks stIdle)
    spB  : SPos₀ (sB , false) (iter ks stBusy)
    spQ  : SPos₀ (sQ , false) (iter ks stQuit)
    spI′ : SPos₀ (sI , true) (iter-bind (Ret (inj₁ stIdle)) ks)
    spB′ : SPos₀ (sB , true) (iter-bind (Ret (inj₁ stBusy)) ks)
    spQ′ : SPos₀ (sQ , true) (iter-bind (Ret (inj₁ stQuit)) ks)
    spN  : ∀ r → SPos₀ (sN r , false) (iter-bind (snd l hi FromResponder (repM r) stIdle) ks)
    spD  : SPos₀ (sD , false) (iter-bind (sendLNP l hi ! pay FromResponder MsgLNPDone ⟶ Ret (inj₂ tt)) ks)
    spE  : SPos₀ (sE , false) (iter-bind (Ret (inj₂ tt)) ks)

  -- the server's abstract steps, labelled as the RENAMED server shows them (the client end
  -- of the link): its receives are `wS lo`, its sends `wR lo`
  data SStp : SS × Bool → ALbl → SS × Bool → Set where
    sτI : SStp (sI , true) τ′ (sI , false)
    sτB : SStp (sB , true) τ′ (sB , false)
    sτQ : SStp (sQ , true) τ′ (sQ , false)
    sRN : ∀ {tm md ln} → SStp (sI , false) (ev′ (wS lo (tm , md , ln , leiosNotifyP MsgLNPRequestNext))) (sB , true)
    sQi : ∀ {tm md ln} → SStp (sI , false) (ev′ (wS lo (tm , md , ln , leiosNotifyP MsgLNPQuit))) (sQ , true)
    sAA : ∀ h    → SStp (sB , false) (ev′ (ap hi lnpSendBlockAnnouncement h)) (sN (rA h) , false)
    sAO : ∀ q sz → SStp (sB , false) (ev′ (ap hi lnpSendBlockOffer (q , sz))) (sN (rO q sz) , false)
    sAT : ∀ q    → SStp (sB , false) (ev′ (ap hi lnpSendBlockTxsOffer q)) (sN (rT q) , false)
    sAV : ∀ vs   → SStp (sB , false) (ev′ (ap hi lnpSendVotes vs)) (sN (rV vs) , false)
    sAC : ∀ u    → SStp (sB , false) (ev′ (ap hi lnpSendCanceled u)) (sN rC , false)
    sNA : ∀ h    → SStp (sN (rA h) , false) (ev′ (wR lo (pay FromResponder (MsgLNPBlockAnnouncement h)))) (sI , true)
    sNO : ∀ q sz → SStp (sN (rO q sz) , false) (ev′ (wR lo (pay FromResponder (MsgLNPBlockOffer q sz)))) (sI , true)
    sNT : ∀ q    → SStp (sN (rT q) , false) (ev′ (wR lo (pay FromResponder (MsgLNPBlockTxsOffer q)))) (sI , true)
    sNV : ∀ vs   → SStp (sN (rV vs) , false) (ev′ (wR lo (pay FromResponder (MsgLNPVotes vs)))) (sI , true)
    sNC :          SStp (sN rC , false) (ev′ (wR lo (pay FromResponder MsgLNPCanceled))) (sI , true)
    sDn : SStp (sQ , false) (ev′ (dn hi)) (sD , false)
    sDS : SStp (sD , false) (ev′ (wR lo (pay FromResponder MsgLNPDone))) (sE , false)

  -- the server has terminated
  SFin : SS × Bool → Set
  SFin (sE , _) = U.⊤
  SFin _        = ⊥

  -- the renamed server's alphabet: the client end's wire cell, its api and done at `hi`
  data SAl : Lab → Set where
    saS : ∀ x   → SAl (wS lo x)
    saR : ∀ x   → SAl (wR lo x)
    saA : ∀ m v → SAl (ap hi m v)
    saD :         SAl (dn hi)

  -- the server's steps stay in its alphabet
  sAlpha : ∀ {σ ω σ′} → SStp σ (ev′ ω) σ′ → SAl ω
  sAlpha sRN       = saS _
  sAlpha sQi       = saS _
  sAlpha (sAA _)   = saA _ _
  sAlpha (sAO _ _) = saA _ _
  sAlpha (sAT _)   = saA _ _
  sAlpha (sAV _)   = saA _ _
  sAlpha (sAC _)   = saA _ _
  sAlpha (sNA _)   = saR _
  sAlpha (sNO _ _) = saR _
  sAlpha (sNT _)   = saR _
  sAlpha (sNV _)   = saR _
  sAlpha sNC       = saR _
  sAlpha sDn       = saD
  sAlpha sDS       = saR _

  -- the server's τ-measure decreases
  sμτ : ∀ {σ σ′} → SStp σ τ′ σ′ → fl (proj₂ σ′) < fl (proj₂ σ)
  sμτ sτI = fl<
  sμτ sτB = fl<
  sμτ sτQ = fl<

  -- the (unrenamed) server makes a τ only at a loop-back
  sElimτ₀ : ∀ {σ t t′} → SPos₀ σ t → t ─[ τ ]─► t′ → Σ[ σ′ ∈ _ ] (SStp σ τ′ σ′ × SPos₀ σ′ t′)
  sElimτ₀ spI st = ⊥-elim (IterNoτ.τ✗ pchNoτ (λ ()) st)
  sElimτ₀ spB st = ⊥-elim (IterNoτ.τ✗ pchNoτ (λ ()) st)
  sElimτ₀ spQ st = ⊥-elim (IterNoτ.τ✗ pchNoτ (λ ()) st)
  sElimτ₀ spI′ (sSil refl) = _ , sτI , spI
  sElimτ₀ spB′ (sSil refl) = _ , sτB , spB
  sElimτ₀ spQ′ (sSil refl) = _ , sτQ , spQ
  sElimτ₀ spI′ (sTau () _)
  sElimτ₀ spB′ (sTau () _)
  sElimτ₀ spQ′ (sTau () _)
  sElimτ₀ (spN _) st = ⊥-elim (IterNoτ.τ✗ outNoτ (λ ()) st)
  sElimτ₀ spD st = ⊥-elim (IterNoτ.τ✗ outNoτ (λ ()) st)
  sElimτ₀ spE (sSil ())
  sElimτ₀ spE (sTau () _)

  -- every visible (unrenamed) server step is an abstract one, on the label's source event
  sElimE₀ : ∀ {σ t t′ e} → SPos₀ σ t → t ─[ ev (evl e) ]─► t′
          → Σ[ ω ∈ Lab ] Σ[ σ′ ∈ _ ] (e ≡ ⌜ sl ω ⌝ × SStp σ (ev′ ω) σ′ × SPos₀ σ′ t′)
  sElimE₀ spI st with iter-ev-elim (ks stIdle) ks st
  ... | _ , st′ , refl with sIdleV st′
  ...   | siNext = wS lo _ , _ , refl , sRN , spB′
  ...   | siQuit = wS lo _ , _ , refl , sQi , spQ′
  sElimE₀ spB st with iter-ev-elim (ks stBusy) ks st
  ... | _ , st′ , refl with sBusyV st′
  ...   | sbCan u    = ap hi lnpSendCanceled u , _ , refl , sAC u , spN rC
  ...   | sbAnn h    = ap hi lnpSendBlockAnnouncement h , _ , refl , sAA h , spN (rA h)
  ...   | sbOff q sz = ap hi lnpSendBlockOffer (q , sz) , _ , refl , sAO q sz , spN (rO q sz)
  ...   | sbTxs q    = ap hi lnpSendBlockTxsOffer q , _ , refl , sAT q , spN (rT q)
  ...   | sbVote vs  = ap hi lnpSendVotes vs , _ , refl , sAV vs , spN (rV vs)
  sElimE₀ spQ st with iter-ev-elim (ks stQuit) ks st
  ... | _ , st′ , refl with sQuitV st′
  ...   | sqDone _ = dn hi , _ , refl , sDn , spD
  sElimE₀ spI′ (sVis () _)
  sElimE₀ spB′ (sVis () _)
  sElimE₀ spQ′ (sVis () _)
  sElimE₀ (spN r) st with iter-ev-elim (snd l hi FromResponder (repM r) stIdle) ks st
  ... | _ , st′ , refl with outI st′
  sElimE₀ (spN (rA h))    st | _ , _ , refl | refl , refl = wR lo _ , _ , refl , sNA h , spI′
  sElimE₀ (spN (rO q sz)) st | _ , _ , refl | refl , refl = wR lo _ , _ , refl , sNO q sz , spI′
  sElimE₀ (spN (rT q))    st | _ , _ , refl | refl , refl = wR lo _ , _ , refl , sNT q , spI′
  sElimE₀ (spN (rV vs))   st | _ , _ , refl | refl , refl = wR lo _ , _ , refl , sNV vs , spI′
  sElimE₀ (spN rC)        st | _ , _ , refl | refl , refl = wR lo _ , _ , refl , sNC , spI′
  sElimE₀ spD st with iter-ev-elim (sendLNP l hi ! pay FromResponder MsgLNPDone ⟶ Ret (inj₂ tt)) ks st
  ... | _ , st′ , refl with outI st′
  ...   | refl , refl = wR lo _ , _ , refl , sDS , spE
  sElimE₀ spE (sVis () _)

  -- an (unrenamed) server tree returns only at the end
  sElimR₀ : ∀ {σ t r} → SPos₀ σ t → PTree.force t ≡ ret r → SFin σ
  sElimR₀ spE  _ = U.tt
  sElimR₀ spI  ()
  sElimR₀ spB  ()
  sElimR₀ spQ  ()
  sElimR₀ spI′ ()
  sElimR₀ spB′ ()
  sElimR₀ spQ′ ()
  sElimR₀ (spN _) ()
  sElimR₀ spD  ()

  -- a server menu offer is a step of the server loop
  sOff : ∀ st {at a t′} → vOf (ks st) at a ≡ just t′
       → iter ks st ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► iter-bind t′ ks
  sOff stIdle eq = iterE (pchS eq)
  sOff stBusy eq = iterE (pchS eq)
  sOff stQuit eq = iterE (pchS eq)

  -- every abstract server τ is a concrete (unrenamed) one
  sIntroτ₀ : ∀ {σ σ′ t} → SPos₀ σ t → SStp σ τ′ σ′ → Σ[ t′ ∈ Tree ] (t ─[ τ ]─► t′ × SPos₀ σ′ t′)
  sIntroτ₀ spI′ sτI = _ , sSil refl , spI
  sIntroτ₀ spB′ sτB = _ , sSil refl , spB
  sIntroτ₀ spQ′ sτQ = _ , sSil refl , spQ

  -- every abstract visible server step is a concrete (unrenamed) one, on the source event
  sIntroE₀ : ∀ {σ σ′ t ω} → SPos₀ σ t → SStp σ (ev′ ω) σ′
           → Σ[ t′ ∈ Tree ] (t ─[ ev (evl ⌜ sl ω ⌝) ]─► t′ × SPos₀ σ′ t′)
  sIntroE₀ spI (sRN {tm} {md} {ln}) = _ , sOff stIdle e , spB′
    where
    -- the idle menu accepts RequestNext
    e : vOf (ks stIdle) (_ , receiveLNP l hi) (tm , md , ln , leiosNotifyP MsgLNPRequestNext) ≡ just (Ret (inj₁ stBusy))
    e rewrite ≟-refl l = refl
  sIntroE₀ spI (sQi {tm} {md} {ln}) = _ , sOff stIdle e , spQ′
    where
    -- the idle menu accepts the quit
    e : vOf (ks stIdle) (_ , receiveLNP l hi) (tm , md , ln , leiosNotifyP MsgLNPQuit) ≡ just (Ret (inj₁ stQuit))
    e rewrite ≟-refl l = refl
  sIntroE₀ spB (sAA h) = _ , sOff stBusy e , spN (rA h)
    where
    -- the busy menu takes an announcement command
    e : vOf (ks stBusy) (_ , apiLPev l hi lnpSendBlockAnnouncement) h ≡ just (snd l hi FromResponder (MsgLNPBlockAnnouncement h) stIdle)
    e rewrite ≟-refl l = refl
  sIntroE₀ spB (sAO q sz) = _ , sOff stBusy e , spN (rO q sz)
    where
    -- the busy menu takes an offer command
    e : vOf (ks stBusy) (_ , apiLPev l hi lnpSendBlockOffer) (q , sz) ≡ just (snd l hi FromResponder (MsgLNPBlockOffer q sz) stIdle)
    e rewrite ≟-refl l = refl
  sIntroE₀ spB (sAT q) = _ , sOff stBusy e , spN (rT q)
    where
    -- the busy menu takes a txs-offer command
    e : vOf (ks stBusy) (_ , apiLPev l hi lnpSendBlockTxsOffer) q ≡ just (snd l hi FromResponder (MsgLNPBlockTxsOffer q) stIdle)
    e rewrite ≟-refl l = refl
  sIntroE₀ spB (sAV vs) = _ , sOff stBusy e , spN (rV vs)
    where
    -- the busy menu takes a votes command
    e : vOf (ks stBusy) (_ , apiLPev l hi lnpSendVotes) vs ≡ just (snd l hi FromResponder (MsgLNPVotes vs) stIdle)
    e rewrite ≟-refl l = refl
  sIntroE₀ spB (sAC u) = _ , sOff stBusy e , spN rC
    where
    -- the busy menu takes the cancel command
    e : vOf (ks stBusy) (_ , apiLPev l hi lnpSendCanceled) u ≡ just (snd l hi FromResponder MsgLNPCanceled stIdle)
    e rewrite ≟-refl l = refl
  sIntroE₀ spQ sDn = _ , sOff stQuit e , spD
    where
    -- the quit menu offers the peer-local done
    e : vOf (ks stQuit) (_ , doneLNP l hi) U.tt ≡ just (sendLNP l hi ! pay FromResponder MsgLNPDone ⟶ Ret (inj₂ tt))
    e rewrite ≟-refl l = refl
  sIntroE₀ (spN (rA h))    (sNA _)   = _ , iterE (outS (sendLNP l hi) _ _) , spI′
  sIntroE₀ (spN (rO q sz)) (sNO _ _) = _ , iterE (outS (sendLNP l hi) _ _) , spI′
  sIntroE₀ (spN (rT q))    (sNT _)   = _ , iterE (outS (sendLNP l hi) _ _) , spI′
  sIntroE₀ (spN (rV vs))   (sNV _)   = _ , iterE (outS (sendLNP l hi) _ _) , spI′
  sIntroE₀ (spN rC)        sNC       = _ , iterE (outS (sendLNP l hi) _ _) , spI′
  sIntroE₀ spD sDS = _ , iterE (outS (sendLNP l hi) _ _) , spE

  -- the terminated (unrenamed) server has returned
  sIntroR₀ : ∀ {σ t} → SPos₀ σ t → SFin σ → PTree.force t ≡ ret tt
  sIntroR₀ spE _ = refl

  -- where a RENAMED server tree is: the renaming of a positioned server tree
  SPos : SS × Bool → Tree → Set₁
  SPos σ t = Σ[ t₀ ∈ Tree ] (t ≡ R t₀ × SPos₀ σ t₀)

  -- the renamed server makes a τ only at a loop-back
  sElimτ : ∀ {σ t t′} → SPos σ t → t ─[ τ ]─► t′ → Σ[ σ′ ∈ _ ] (SStp σ τ′ σ′ × SPos σ′ t′)
  sElimτ (t₀ , refl , p) st with TR.ren-τ-inv {inv = sinv} {P = t₀} st
  ... | P₁ , st₀ , refl with sElimτ₀ p st₀
  ...   | σ′ , a , p′ = σ′ , a , (P₁ , refl , p′)

  -- every visible renamed-server step is an abstract one
  sElimE : ∀ {σ t t′ e} → SPos σ t → t ─[ ev (evl e) ]─► t′
         → Σ[ ω ∈ Lab ] Σ[ σ′ ∈ _ ] (e ≡ ⌜ ω ⌝ × SStp σ (ev′ ω) σ′ × SPos σ′ t′)
  sElimE (t₀ , refl , p) st with renEv st
  ... | e₀ , P₁ , st₀ , refl , refl with sElimE₀ p st₀
  ...   | ω , σ′ , refl , a , p′ = ω , σ′ , swE-sl ω , a , (P₁ , refl , p′)

  -- the renamed server returns only at the end
  sElimR : ∀ {σ t r} → SPos σ t → PTree.force t ≡ ret r → SFin σ
  sElimR (t₀ , refl , p) eq = sElimR₀ p (TR.force-ren-ret-inv {inv = sinv} {P = t₀} eq)

  -- the (renamed) server abstraction
  SA : Abs (SS × Bool)
  SA = record { Pos = SPos ; Stp = SStp ; Fin = SFin ; Alpha = SAl ; alpha = sAlpha
              ; μ = λ σ → fl (proj₂ σ) ; μτ = sμτ
              ; elimτ = sElimτ ; elimE = sElimE ; elimR = sElimR }

  -- every abstract server τ is a concrete renamed one
  sIntroτ : ∀ {σ σ′ t} → SPos σ t → SStp σ τ′ σ′ → Σ[ t′ ∈ Tree ] (t ─[ τ ]─► t′ × SPos σ′ t′)
  sIntroτ (t₀ , refl , p) a with sIntroτ₀ p a
  ... | t₁ , st , p′ = R t₁ , TR.ren-τ-fwd {inv = sinv} st , (t₁ , refl , p′)

  -- every abstract visible server step is a concrete renamed one
  sIntroE : ∀ {σ σ′ t ω} → SPos σ t → SStp σ (ev′ ω) σ′
          → Σ[ t′ ∈ Tree ] (t ─[ ev (evl ⌜ ω ⌝) ]─► t′ × SPos σ′ t′)
  sIntroE {ω = ω} (t₀ , refl , p) a with sIntroE₀ p a
  ... | t₁ , st , p′ = R t₁ , rF ω st , (t₁ , refl , p′)

  -- the terminated renamed server has returned
  sIntroR : ∀ {σ t} → SPos σ t → SFin σ → PTree.force t ≡ ret tt
  sIntroR (t₀ , refl , p) f = TR.force-ren-ret {inv = sinv} {P = t₀} (sIntroR₀ p f)

  -- the server's intro facts
  SI : AbsI SA
  SI = record { introτ = sIntroτ ; introE = sIntroE ; introR = sIntroR }

  ---------------------------------------------------------------- `Skip`

  -- `Skip` makes no τ
  skτ : ∀ {t t′ : Tree} → t ≡ Skip → t ─[ τ ]─► t′ → Σ[ σ′ ∈ U.⊤ ] (⊥ × t′ ≡ Skip)
  skτ refl (sSil ())
  skτ refl (sTau () _)

  -- `Skip` makes no visible step
  skE : ∀ {t t′ : Tree} {e} → t ≡ Skip → t ─[ ev (evl e) ]─► t′
      → Σ[ ω ∈ Lab ] Σ[ σ′ ∈ U.⊤ ] (e ≡ ⌜ ω ⌝ × ⊥ × t′ ≡ Skip)
  skE refl (sVis () _)

  -- the abstraction of `Skip`: one terminated state, no step, empty alphabet
  SkA : Abs U.⊤
  SkA = record { Pos = λ _ t → t ≡ Skip ; Stp = λ _ _ _ → ⊥ ; Fin = λ _ → U.⊤ ; Alpha = λ _ → ⊥
               ; alpha = λ () ; μ = λ _ → 0 ; μτ = λ ()
               ; elimτ = skτ ; elimE = skE ; elimR = λ _ _ → U.tt }

  -- … and its intro facts
  SkI : AbsI SkA
  SkI = record { introτ = λ _ () ; introE = λ _ () ; introR = λ { refl _ → refl } }

  ------------------------------------------------------------------------
  -- §5  The system
  ------------------------------------------------------------------------

  -- whether an event is a wire event
  wireEv : ∀ {A} → LNPEv A → Bool
  wireEv (sendLNP _ _)    = true
  wireEv (receiveLNP _ _) = true
  wireEv _                = false

  -- the wire events: the client and the renamed server synchronise on these
  wireES : EventSet
  wireES = record { mem = λ at _ → T (wireEv (proj₂ at)) ; dec = λ at _ → T? (wireEv (proj₂ at)) }

  -- the server's api sends: the four notifications AND the cancel
  srvCmd : ApiLPTag → Bool
  srvCmd lnpSendBlockAnnouncement = true
  srvCmd lnpSendBlockOffer        = true
  srvCmd lnpSendBlockTxsOffer     = true
  srvCmd lnpSendVotes             = true
  srvCmd lnpSendCanceled          = true
  srvCmd _                        = false

  -- the server's four notification sends (NOT the cancel)
  srvCmdN : ApiLPTag → Bool
  srvCmdN lnpSendBlockAnnouncement = true
  srvCmdN lnpSendBlockOffer        = true
  srvCmdN lnpSendBlockTxsOffer     = true
  srvCmdN lnpSendVotes             = true
  srvCmdN _                        = false

  -- whether an event is one of the server's (direction `hi`) api sends selected by `f`
  srvEv : (ApiLPTag → Bool) → ∀ {A} → LNPEv A → Bool
  srvEv f (apiLPev _ hi m) = f m
  srvEv _ _                = false

  -- all the server's api sends, as an event set (blocked in `blk`)
  srvApi : EventSet
  srvApi = record { mem = λ at _ → T (srvEv srvCmd (proj₂ at)) ; dec = λ at _ → T? (srvEv srvCmd (proj₂ at)) }

  -- the server's notification sends, as an event set (blocked in `blkC`)
  srvApiN : EventSet
  srvApiN = record { mem = λ at _ → T (srvEv srvCmdN (proj₂ at)) ; dec = λ at _ → T? (srvEv srvCmdN (proj₂ at)) }

  -- the peers' alphabets meet only on the wire
  disjCS : ∀ {ω} → CAl ω → SAl ω → ¬ InE wireES ω → ⊥
  disjCS (caS _)   (saS _) ¬w = ¬w U.tt
  disjCS (caR _)   (saR _) ¬w = ¬w U.tt
  disjCS (caA _ _) ()

  -- `Skip` shares nothing
  disjSk : ∀ {W ω} {X : Set} → X → ⊥ → ¬ InE W ω → ⊥
  disjSk _ ()

  -- the pair (client and renamed server, synchronised on the wire)
  module P1 = Prod CA SA wireES disjCS
  -- the pair with every server api send blocked
  module P4 = Prod P1.ParA SkA srvApi (λ {ω} → disjSk {srvApi} {ω})
  -- the pair with the server's notification sends blocked (the cancel allowed)
  module P5 = Prod P1.ParA SkA srvApiN (λ {ω} → disjSk {srvApiN} {ω})

  -- the system's abstract states
  SysS : Set
  SysS = (CS × Bool) × (SS × Bool)

  -- the system's abstraction and intro facts
  SysA : Abs SysS
  SysA = P1.ParA

  -- (intro)
  SysI : AbsI SysA
  SysI = P1.ParI CI SI

  -- the blocked system's abstraction and intro facts
  BlkA : Abs (SysS × U.⊤)
  BlkA = P4.ParA

  -- (intro)
  BlkI : AbsI BlkA
  BlkI = P4.ParI SysI SkI

  -- the cancel-only system's abstraction and intro facts
  BlkCA : Abs (SysS × U.⊤)
  BlkCA = P5.ParA

  -- (intro)
  BlkCI : AbsI BlkCA
  BlkCI = P5.ParI SysI SkI

  -- THE RENAMED SERVER: the real server at `(l , hi)`, its wire named from the client end
  srv : Tree
  srv = R (LNPserverStClient l hi)

  -- THE SYSTEM: the real client at `(l , lo)` and the renamed real server, in rendezvous
  sys : Tree
  sys = Par⊤ wireES (LNPclientStClient l lo) srv

  -- THE BLOCKED SYSTEM: every server api send (incl. `lnpSendCanceled`) is refused
  blk : Tree
  blk = Par⊤ srvApi sys Skip

  -- THE CANCEL-ONLY SYSTEM: the server's notification sends are refused, the cancel is not
  blkC : Tree
  blkC = Par⊤ srvApiN sys Skip

  -- the initial abstract state
  σ₀ : SysS
  σ₀ = (cI , false) , (sI , false)

  -- the renamed server starts there
  srv₀ : SPos (sI , false) srv
  srv₀ = _ , refl , spI

  -- the system starts there
  sys₀ : Abs.Pos SysA σ₀ sys
  sys₀ = _ , _ , refl , cpI , srv₀

  -- … and so do the blocked systems
  blk₀ : Abs.Pos BlkA (σ₀ , U.tt) blk
  blk₀ = _ , _ , refl , sys₀ , refl

  -- (cancel-only)
  blkC₀ : Abs.Pos BlkCA (σ₀ , U.tt) blkC
  blkC₀ = _ , _ , refl , sys₀ , refl

  ------------------------------------------------------------------------
  -- §6  The table as a process, and conformance
  ------------------------------------------------------------------------

  -- the table's states (End is the loop's √)
  data TSt : Set where
    tIdle tBusy tQuit : TSt

  -- one table step, LITERALLY the blueprint's rows, over the protocol messages as the
  -- client end `(l , lo)` sees them (Initiator messages sent, Responder messages received;
  -- any time / mode / length): StIdle --RequestNext--> StBusy, StIdle --Quit--> StQuit;
  -- StBusy --{Announcement, Offer, TxsOffer, Votes, Canceled}--> StIdle; StQuit --Done--> End
  specStep : TSt → PTree LNPEv (ExtI LNPEv) (TSt ⊎ Rr)
  specStep tIdle = pchoice v
    where
    -- the StIdle rows' offers
    v : (at : AnyTypes LNPEv) → ContinueType at (Maybe (PTree LNPEv (ExtI LNPEv) (TSt ⊎ Rr)))
    v (_ , sendLNP l′ d′) (_ , _ , _ , leiosNotifyP MsgLNPRequestNext) with l′ ≟ l | d′ ≟ lo
    ... | yes refl | yes refl = just (Ret (inj₁ tBusy))
    ... | _        | _        = nothing
    v (_ , sendLNP l′ d′) (_ , _ , _ , leiosNotifyP MsgLNPQuit) with l′ ≟ l | d′ ≟ lo
    ... | yes refl | yes refl = just (Ret (inj₁ tQuit))
    ... | _        | _        = nothing
    v _ _ = nothing
  specStep tBusy = pchoice v
    where
    -- the StBusy rows' offers
    v : (at : AnyTypes LNPEv) → ContinueType at (Maybe (PTree LNPEv (ExtI LNPEv) (TSt ⊎ Rr)))
    v (_ , receiveLNP l′ d′) (_ , _ , _ , leiosNotifyP (MsgLNPBlockAnnouncement _)) with l′ ≟ l | d′ ≟ lo
    ... | yes refl | yes refl = just (Ret (inj₁ tIdle))
    ... | _        | _        = nothing
    v (_ , receiveLNP l′ d′) (_ , _ , _ , leiosNotifyP (MsgLNPBlockOffer _ _)) with l′ ≟ l | d′ ≟ lo
    ... | yes refl | yes refl = just (Ret (inj₁ tIdle))
    ... | _        | _        = nothing
    v (_ , receiveLNP l′ d′) (_ , _ , _ , leiosNotifyP (MsgLNPBlockTxsOffer _)) with l′ ≟ l | d′ ≟ lo
    ... | yes refl | yes refl = just (Ret (inj₁ tIdle))
    ... | _        | _        = nothing
    v (_ , receiveLNP l′ d′) (_ , _ , _ , leiosNotifyP (MsgLNPVotes _)) with l′ ≟ l | d′ ≟ lo
    ... | yes refl | yes refl = just (Ret (inj₁ tIdle))
    ... | _        | _        = nothing
    v (_ , receiveLNP l′ d′) (_ , _ , _ , leiosNotifyP MsgLNPCanceled) with l′ ≟ l | d′ ≟ lo
    ... | yes refl | yes refl = just (Ret (inj₁ tIdle))
    ... | _        | _        = nothing
    v _ _ = nothing
  specStep tQuit = pchoice v
    where
    -- the StQuit row's offer
    v : (at : AnyTypes LNPEv) → ContinueType at (Maybe (PTree LNPEv (ExtI LNPEv) (TSt ⊎ Rr)))
    v (_ , receiveLNP l′ d′) (_ , _ , _ , leiosNotifyP MsgLNPDone) with l′ ≟ l | d′ ≟ lo
    ... | yes refl | yes refl = just (Ret (inj₂ tt))
    ... | _        | _        = nothing
    v _ _ = nothing

  -- THE TABLE: loop the table step from StIdle
  LNPSpec : Tree
  LNPSpec = iter specStep tIdle

  -- the table's End (it has terminated)
  specEnd : Tree
  specEnd = iter-bind (Ret (inj₂ tt)) specStep

  -- a table step, then its loop-back, prefixed to a run of the next state
  spGo : ∀ a {b} {at : AnyTypes LNPEv} {x} → vOf (specStep a) at x ≡ just (Ret (inj₁ b))
       → ∀ {s r} → iter specStep b ⟹∖√⟨ s ⟩ r → iter specStep a ⟹∖√⟨ evLabel (proj₁ at) (proj₂ at) x ∷ s ⟩ r
  spGo tIdle eq rest = ∖√-ev (iterE (pchS eq)) (∖√-τ (sSil refl) rest)
  spGo tBusy eq rest = ∖√-ev (iterE (pchS eq)) (∖√-τ (sSil refl) rest)
  spGo tQuit eq rest = ∖√-ev (iterE (pchS eq)) (∖√-τ (sSil refl) rest)

  -- the table's last step (MsgDone from StQuit to End), prefixed to a run of the End
  spEnd : ∀ {at : AnyTypes LNPEv} {x} → vOf (specStep tQuit) at x ≡ just (Ret (inj₂ tt))
        → ∀ {s r} → specEnd ⟹∖√⟨ s ⟩ r → iter specStep tQuit ⟹∖√⟨ evLabel (proj₁ at) (proj₂ at) x ∷ s ⟩ r
  spEnd eq rest = ∖√-ev (iterE (pchS eq)) rest

  -- row StIdle --RequestNext--> StBusy
  tReq : ∀ {tm md ln} → vOf (specStep tIdle) (_ , sendLNP l lo) (tm , md , ln , leiosNotifyP MsgLNPRequestNext) ≡ just (Ret (inj₁ tBusy))
  tReq rewrite ≟-refl l = refl

  -- row StIdle --Quit--> StQuit
  tQt : ∀ {tm md ln} → vOf (specStep tIdle) (_ , sendLNP l lo) (tm , md , ln , leiosNotifyP MsgLNPQuit) ≡ just (Ret (inj₁ tQuit))
  tQt rewrite ≟-refl l = refl

  -- row StBusy --Announcement--> StIdle
  tAnn : ∀ {tm md ln} h → vOf (specStep tBusy) (_ , receiveLNP l lo) (tm , md , ln , leiosNotifyP (MsgLNPBlockAnnouncement h)) ≡ just (Ret (inj₁ tIdle))
  tAnn _ rewrite ≟-refl l = refl

  -- row StBusy --Offer--> StIdle
  tOff : ∀ {tm md ln} q sz → vOf (specStep tBusy) (_ , receiveLNP l lo) (tm , md , ln , leiosNotifyP (MsgLNPBlockOffer q sz)) ≡ just (Ret (inj₁ tIdle))
  tOff _ _ rewrite ≟-refl l = refl

  -- row StBusy --TxsOffer--> StIdle
  tTxs : ∀ {tm md ln} q → vOf (specStep tBusy) (_ , receiveLNP l lo) (tm , md , ln , leiosNotifyP (MsgLNPBlockTxsOffer q)) ≡ just (Ret (inj₁ tIdle))
  tTxs _ rewrite ≟-refl l = refl

  -- row StBusy --Votes--> StIdle
  tVot : ∀ {tm md ln} vs → vOf (specStep tBusy) (_ , receiveLNP l lo) (tm , md , ln , leiosNotifyP (MsgLNPVotes vs)) ≡ just (Ret (inj₁ tIdle))
  tVot _ rewrite ≟-refl l = refl

  -- row StBusy --Canceled--> StIdle
  tCan : ∀ {tm md ln} → vOf (specStep tBusy) (_ , receiveLNP l lo) (tm , md , ln , leiosNotifyP MsgLNPCanceled) ≡ just (Ret (inj₁ tIdle))
  tCan rewrite ≟-refl l = refl

  -- row StQuit --Done--> End
  tDone : ∀ {tm md ln} → vOf (specStep tQuit) (_ , receiveLNP l lo) (tm , md , ln , leiosNotifyP MsgLNPDone) ≡ just (Ret (inj₂ tt))
  tDone rewrite ≟-refl l = refl

  -- whether an event is a wire event
  isWE : Event → Bool
  isWE (evLabel _ e _) = wireEv e

  -- keep an event, or drop it
  keepE : Bool → Event → List Event → List Event
  keepE true  e s = e ∷ s
  keepE false _ s = s

  -- THE PROJECTION: a trace's wire events (its protocol messages), api / done dropped
  wire : List Event → List Event
  wire []      = []
  wire (e ∷ s) = keepE (isWE e) e (wire s)

  -- whether an abstract label is a wire label
  isW : Lab → Bool
  isW (wS _ _) = true
  isW (wR _ _) = true
  isW _        = false

  -- what the table owes for a step on a label: a wire label is one table step, else none
  WMv : Bool → Lab → Tree → Tree → Set₁
  WMv true  ω a b = ∀ {s r} → b ⟹∖√⟨ s ⟩ r → a ⟹∖√⟨ ⌜ ω ⌝ ∷ s ⟩ r
  WMv false _ a b = b ≡ a

  -- what the table owes for an abstract step (a τ: nothing)
  SpecMv : ALbl → Tree → Tree → Set₁
  SpecMv τ′      a b = b ≡ a
  SpecMv (ev′ ω) a b = WMv (isW ω) ω a b

  -- one step of the simulation on the projected trace
  stepW : ∀ ω {a b r s} → WMv (isW ω) ω a b → b ⟹∖√⟨ wire s ⟩ r → a ⟹∖√⟨ wire (⌜ ω ⌝ ∷ s) ⟩ r
  stepW (wS _ _)   m    rest = m rest
  stepW (wR _ _)   m    rest = m rest
  stepW (ap _ _ _) refl rest = rest
  stepW (dn _)     refl rest = rest

  -- (generic) an abstraction whose steps the table simulates CONFORMS to the table: every
  -- √-free trace, projected, is a table trace, and termination is table termination
  module Conf {S : Set} (A : Abs S) (φ : S → Tree)
              (mv : ∀ {σ ℓ σ′} → Abs.Stp A σ ℓ σ′ → SpecMv ℓ (φ σ) (φ σ′))
              (fin : ∀ {σ} → Abs.Fin A σ → PTree.force (φ σ) ≡ ret tt) where
    open Abs A using (Pos; elimR)
    open Gen A using (ARun; r0; rτ; rE; runE)

    -- an abstract run is simulated by the table on its projection
    simRun : ∀ {σ s σ′} → ARun σ s σ′ → φ σ ⟹∖√⟨ wire s ⟩ φ σ′
    simRun r0                = ∖√-refl
    simRun {s = s} {σ′ = σ″} (rτ a ar) = subst (λ t → t ⟹∖√⟨ wire s ⟩ φ σ″) (mv a) (simRun ar)
    simRun (rE {s = s} {ω = ω} a ar) = stepW ω {s = s} (mv a) (simRun ar)

    -- conformance of a positioned tree
    conforms : ∀ {σ t} → Pos σ t → ∀ {s W} → t ⟹∖√⟨ s ⟩ W
             → Σ[ W′ ∈ Tree ] (φ σ ⟹∖√⟨ wire s ⟩ W′ × (PTree.force W ≡ ret tt → PTree.force W′ ≡ ret tt))
    conforms p r with runE p r
    ... | σ′ , ar , p′ = φ σ′ , simRun ar , λ eq → fin (elimR p′ eq)

  -- the table state of a client phase
  φc : CS × Bool → Tree
  φc (cI , _)   = iter specStep tIdle
  φc (cR , _)   = iter specStep tIdle
  φc (cS , _)   = iter specStep tIdle
  φc (cD _ , _) = iter specStep tIdle
  φc (cB , _)   = iter specStep tBusy
  φc (cQ , _)   = iter specStep tQuit
  φc (cE , _)   = specEnd

  -- every client step is a table row (wire) or no table step (api / τ)
  cMv : ∀ {σ ℓ σ′} → CStp σ ℓ σ′ → SpecMv ℓ (φc σ) (φc σ′)
  cMv cτI        = refl
  cMv cτB        = refl
  cMv cτQ        = refl
  cMv (cRN _)    = refl
  cMv (cQi _)    = refl
  cMv cSR        = spGo tIdle (tReq {time₀} {FromInitiator} {length₀})
  cMv cSQ        = spGo tIdle (tQt {time₀} {FromInitiator} {length₀})
  cMv (cRA {tm} {md} {ln} h)    = spGo tBusy (tAnn {tm} {md} {ln} h)
  cMv (cRO {tm} {md} {ln} q sz) = spGo tBusy (tOff {tm} {md} {ln} q sz)
  cMv (cRT {tm} {md} {ln} q)    = spGo tBusy (tTxs {tm} {md} {ln} q)
  cMv (cRV {tm} {md} {ln} vs)   = spGo tBusy (tVot {tm} {md} {ln} vs)
  cMv (cRC {tm} {md} {ln})      = spGo tBusy (tCan {tm} {md} {ln})
  cMv (cDA _)    = refl
  cMv (cDO _ _)  = refl
  cMv (cDT _)    = refl
  cMv (cDV _)    = refl
  cMv (cDn {tm} {md} {ln})      = spEnd (tDone {tm} {md} {ln})

  -- the client ends exactly when the table does
  cFin : ∀ {σ} → CFin σ → PTree.force (φc σ) ≡ ret tt
  cFin {cE , _} _ = refl
  cFin {cI , _}   ()
  cFin {cB , _}   ()
  cFin {cQ , _}   ()
  cFin {cR , _}   ()
  cFin {cS , _}   ()
  cFin {cD _ , _} ()

  -- the table state of a server phase
  φs : SS × Bool → Tree
  φs (sI , _)   = iter specStep tIdle
  φs (sB , _)   = iter specStep tBusy
  φs (sN _ , _) = iter specStep tBusy
  φs (sQ , _)   = iter specStep tQuit
  φs (sD , _)   = iter specStep tQuit
  φs (sE , _)   = specEnd

  -- every server step is a table row (wire) or no table step (api / done / τ)
  sMv : ∀ {σ ℓ σ′} → SStp σ ℓ σ′ → SpecMv ℓ (φs σ) (φs σ′)
  sMv sτI        = refl
  sMv sτB        = refl
  sMv sτQ        = refl
  sMv (sRN {tm} {md} {ln})      = spGo tIdle (tReq {tm} {md} {ln})
  sMv (sQi {tm} {md} {ln})      = spGo tIdle (tQt {tm} {md} {ln})
  sMv (sAA _)    = refl
  sMv (sAO _ _)  = refl
  sMv (sAT _)    = refl
  sMv (sAV _)    = refl
  sMv (sAC _)    = refl
  sMv (sNA h)    = spGo tBusy (tAnn {time₀} {FromResponder} {length₀} h)
  sMv (sNO q sz) = spGo tBusy (tOff {time₀} {FromResponder} {length₀} q sz)
  sMv (sNT q)    = spGo tBusy (tTxs {time₀} {FromResponder} {length₀} q)
  sMv (sNV vs)   = spGo tBusy (tVot {time₀} {FromResponder} {length₀} vs)
  sMv sNC        = spGo tBusy (tCan {time₀} {FromResponder} {length₀})
  sMv sDn        = refl
  sMv sDS        = spEnd (tDone {time₀} {FromResponder} {length₀})

  -- the server ends exactly when the table does
  sFin : ∀ {σ} → SFin σ → PTree.force (φs σ) ≡ ret tt
  sFin {sE , _} _ = refl
  sFin {sI , _}   ()
  sFin {sB , _}   ()
  sFin {sQ , _}   ()
  sFin {sD , _}   ()
  sFin {sN _ , _} ()

  -- an off-wire label owes the table nothing
  offW : ∀ {ω} {t : Tree} → ¬ InE wireES ω → SpecMv (ev′ ω) t t
  offW {wS _ _}   ¬w = ⊥-elim (¬w U.tt)
  offW {wR _ _}   ¬w = ⊥-elim (¬w U.tt)
  offW {ap _ _ _} _  = refl
  offW {dn _}     _  = refl

  -- the table state of a system state: the client's
  φ : SysS → Tree
  φ (σc , _) = φc σc

  -- every system step is simulated through its client part (a synchronised wire step is
  -- the client's; a server-only step is off the wire)
  pMv : ∀ {σ ℓ σ′} → Abs.Stp SysA σ ℓ σ′ → SpecMv ℓ (φ σ) (φ σ′)
  pMv (P1.pτL a)     = cMv a
  pMv (P1.pτR _)     = refl
  pMv (P1.psy _ a _) = cMv a
  pMv (P1.psL _ a)   = cMv a
  pMv (P1.psR ¬w _)  = offW ¬w

  -- the system ends only when the client does
  pFin : ∀ {σ} → Abs.Fin SysA σ → PTree.force (φ σ) ≡ ret tt
  pFin (f , _) = cFin f

  -- the client's simulation by the table
  module CC = Conf CA φc cMv cFin
  -- the server's simulation by the table
  module SC = Conf SA φs sMv sFin
  -- the pair's simulation by the table
  module PC = Conf SysA φ pMv pFin

  ---------------------------------------------------------------- (T)

  -- (T) THE CLIENT ALONE CONFORMS TO THE TABLE: whatever the environment does, the client's
  -- wire trace is a trace of `LNPSpec` (it never offers a message outside its table state),
  -- and it terminates only where the table does
  client-conforms : ∀ {s W} → LNPclientStClient l lo ⟹∖√⟨ s ⟩ W
                  → Σ[ W′ ∈ Tree ] (LNPSpec ⟹∖√⟨ wire s ⟩ W′ × (PTree.force W ≡ ret tt → PTree.force W′ ≡ ret tt))
  client-conforms = CC.conforms cpI

  -- (T) THE SERVER ALONE CONFORMS TO THE TABLE (its wire named from the client end)
  server-conforms : ∀ {s W} → srv ⟹∖√⟨ s ⟩ W
                  → Σ[ W′ ∈ Tree ] (LNPSpec ⟹∖√⟨ wire s ⟩ W′ × (PTree.force W ≡ ret tt → PTree.force W′ ≡ ret tt))
  server-conforms = SC.conforms srv₀

  -- (T) TABLE CONFORMANCE OF THE PAIR: every √-free trace of `sys`, with api / done
  -- projected away, is a trace of `LNPSpec`, and where `sys` can terminate so can
  -- `LNPSpec` — i.e. `LNPSpec ⊑T (sys with api / done projected away)`
  sys-conforms : ∀ {s W} → sys ⟹∖√⟨ s ⟩ W
               → Σ[ W′ ∈ Tree ] (LNPSpec ⟹∖√⟨ wire s ⟩ W′ × (PTree.force W ≡ ret tt → PTree.force W′ ≡ ret tt))
  sys-conforms = PC.conforms sys₀

  ------------------------------------------------------------------------
  -- §7  The joint invariant
  ------------------------------------------------------------------------

  -- the 9 reachable joint phases (client, server), loop-back flags aside.
  -- `j…`: before the quit command; `q…`: after it
  data J : CS → SS → Set where
    j1 : J cI sI
    j2 : J cR sI
    j3 : J cB sB
    j4 : ∀ r → J cB (sN r)
    j5 : ∀ dv → J (cD dv) sI
    q1 : J cS sI
    q2 : J cQ sQ
    q3 : J cQ sD
    q4 : J cE sE

  -- the invariant on a system state
  JJ : SysS → Set
  JJ ((c , _) , (s , _)) = J c s

  -- after the quit command
  postJ : ∀ {c s} → J c s → Bool
  postJ q1 = true
  postJ q2 = true
  postJ q3 = true
  postJ q4 = true
  postJ _  = false

  -- after the quit command: the most visible events still possible
  rankJ : ∀ {c s} → J c s → ℕ
  rankJ q1 = 3
  rankJ q2 = 2
  rankJ q3 = 1
  rankJ _  = 0

  -- the client's quit command
  isQuitApi : Lab → Bool
  isQuitApi (ap lo lnpSendDone _) = true
  isQuitApi _                     = false

  -- side fact of a visible step: after the quit command the rank strictly drops, staying after it
  rkOK : ∀ {c s c′ s′} → J c s → J c′ s′ → Bool
  rkOK j j′ = not (postJ j) ∨ (postJ j′ ∧ (suc (rankJ j′) ≤ᵇ rankJ j))

  -- side fact of a visible step: the quit command leads after it
  qOK : ∀ {c′ s′} → Lab → J c′ s′ → Bool
  qOK ω j′ = not (isQuitApi ω) ∨ postJ j′

  -- the side facts of any step (a τ changes no phase)
  Side : ∀ {c s c′ s′} → ALbl → J c s → J c′ s′ → Set
  Side τ′      j j′ = (rankJ j′ ≡ rankJ j) × (postJ j′ ≡ postJ j)
  Side (ev′ ω) j j′ = T (rkOK j j′) × T (qOK ω j′)

  -- a client api step
  capi : ∀ {c fc c′ fc′ s ω} → ¬ InE wireES ω → CStp (c , fc) (ev′ ω) (c′ , fc′)
       → (j : J c s) → Σ[ j′ ∈ J c′ s ] Side (ev′ ω) j j′
  capi _ (cRN _)   j1     = j2 , _
  capi _ (cQi _)   j1     = q1 , _
  capi _ (cDA _)   (j5 _) = j1 , _
  capi _ (cDO _ _) (j5 _) = j1 , _
  capi _ (cDT _)   (j5 _) = j1 , _
  capi _ (cDV _)   (j5 _) = j1 , _
  capi ¬w cSR       _ = ⊥-elim (¬w U.tt)
  capi ¬w cSQ       _ = ⊥-elim (¬w U.tt)
  capi ¬w (cRA _)   _ = ⊥-elim (¬w U.tt)
  capi ¬w (cRO _ _) _ = ⊥-elim (¬w U.tt)
  capi ¬w (cRT _)   _ = ⊥-elim (¬w U.tt)
  capi ¬w (cRV _)   _ = ⊥-elim (¬w U.tt)
  capi ¬w cRC       _ = ⊥-elim (¬w U.tt)
  capi ¬w cDn       _ = ⊥-elim (¬w U.tt)

  -- a server api / done step
  sapi : ∀ {c s fs s′ fs′ ω} → ¬ InE wireES ω → SStp (s , fs) (ev′ ω) (s′ , fs′)
       → (j : J c s) → Σ[ j′ ∈ J c s′ ] Side (ev′ ω) j j′
  sapi _ (sAA _)   j3 = j4 _ , _
  sapi _ (sAO _ _) j3 = j4 _ , _
  sapi _ (sAT _)   j3 = j4 _ , _
  sapi _ (sAV _)   j3 = j4 _ , _
  sapi _ (sAC _)   j3 = j4 _ , _
  sapi _ sDn       q2 = q3 , _
  sapi ¬w sRN       _ = ⊥-elim (¬w U.tt)
  sapi ¬w sQi       _ = ⊥-elim (¬w U.tt)
  sapi ¬w (sNA _)   _ = ⊥-elim (¬w U.tt)
  sapi ¬w (sNO _ _) _ = ⊥-elim (¬w U.tt)
  sapi ¬w (sNT _)   _ = ⊥-elim (¬w U.tt)
  sapi ¬w (sNV _)   _ = ⊥-elim (¬w U.tt)
  sapi ¬w sNC       _ = ⊥-elim (¬w U.tt)
  sapi ¬w sDS       _ = ⊥-elim (¬w U.tt)

  -- a rendezvous: a client wire step and the server's matching one
  sync : ∀ {c fc c′ fc′ s fs s′ fs′ ω} → CStp (c , fc) (ev′ ω) (c′ , fc′) → SStp (s , fs) (ev′ ω) (s′ , fs′)
       → (j : J c s) → Σ[ j′ ∈ J c′ s′ ] Side (ev′ ω) j j′
  sync cSR        sRN       j2     = j3 , _
  sync cSQ        sQi       q1     = q2 , _
  sync (cRA h)    (sNA _)   (j4 _) = j5 (dAnn h) , _
  sync (cRO q sz) (sNO _ _) (j4 _) = j5 (dOff q sz) , _
  sync (cRT q)    (sNT _)   (j4 _) = j5 (dTxs q) , _
  sync (cRV vs)   (sNV _)   (j4 _) = j5 (dVot vs) , _
  sync cRC        sNC       (j4 _) = j1 , _
  sync cDn        sDS       q3     = q4 , _
  sync (cRN _)   ()
  sync (cQi _)   ()
  sync (cDA _)   ()
  sync (cDO _ _) ()
  sync (cDT _)   ()
  sync (cDV _)   ()

  -- THE INVARIANT IS INDUCTIVE: every system step keeps it, with the side facts
  J-step : ∀ {σ ℓ σ′} (j : JJ σ) → Abs.Stp SysA σ ℓ σ′ → Σ[ j′ ∈ JJ σ′ ] Side ℓ j j′
  J-step j (P1.pτL cτI)   = j , refl , refl
  J-step j (P1.pτL cτB)   = j , refl , refl
  J-step j (P1.pτL cτQ)   = j , refl , refl
  J-step j (P1.pτR sτI)   = j , refl , refl
  J-step j (P1.pτR sτB)   = j , refl , refl
  J-step j (P1.pτR sτQ)   = j , refl , refl
  J-step j (P1.psL ¬w a)  = capi ¬w a j
  J-step j (P1.psR ¬w a)  = sapi ¬w a j
  J-step j (P1.psy _ a b) = sync a b j

  ------------------------------------------------------------------------
  -- §8  Progress, and the theorems (a)–(c)
  ------------------------------------------------------------------------

  -- a step that the full blocking set does not touch (a τ, or a label off `srvApi`)
  OffSrv : ALbl → Set
  OffSrv τ′      = U.⊤
  OffSrv (ev′ ω) = ¬ InE srvApi ω

  -- what progress gives at phase `j`: the end, or a step, which avoids `srvApi` once the
  -- quit command is behind
  Prog : ∀ {c s} → J c s → SysS → Set
  Prog j σ = Abs.Fin SysA σ ⊎ Σ[ ℓ ∈ ALbl ] Σ[ σ′ ∈ SysS ] (Abs.Stp SysA σ ℓ σ′ × (T (postJ j) → OffSrv ℓ))

  -- a client loop-back is pending, or none is
  cτ? : ∀ {c f t} → CPos (c , f) t → f ≡ false ⊎ Σ[ σ′ ∈ CS × Bool ] CStp (c , f) τ′ σ′
  cτ? cpI′     = inj₂ (_ , cτI)
  cτ? cpB′     = inj₂ (_ , cτB)
  cτ? cpQ′     = inj₂ (_ , cτQ)
  cτ? cpI      = inj₁ refl
  cτ? cpB      = inj₁ refl
  cτ? cpQ      = inj₁ refl
  cτ? cpR      = inj₁ refl
  cτ? cpS      = inj₁ refl
  cτ? (cpD _)  = inj₁ refl
  cτ? cpE      = inj₁ refl

  -- (the server)
  sτ? : ∀ {s f t} → SPos₀ (s , f) t → f ≡ false ⊎ Σ[ σ′ ∈ SS × Bool ] SStp (s , f) τ′ σ′
  sτ? spI′     = inj₂ (_ , sτI)
  sτ? spB′     = inj₂ (_ , sτB)
  sτ? spQ′     = inj₂ (_ , sτQ)
  sτ? spI      = inj₁ refl
  sτ? spB      = inj₁ refl
  sτ? spQ      = inj₁ refl
  sτ? (spN _)  = inj₁ refl
  sτ? spD      = inj₁ refl
  sτ? spE      = inj₁ refl

  -- PROGRESS with no loop-back pending: every joint phase has a step or has terminated;
  -- after the quit command the step is never a server api send.  At `j3` the only step is
  -- a server api send (here the cancel, whose carrier is ⊤)
  progJ : ∀ {c s} (j : J c s) → Prog j ((c , false) , (s , false))
  progJ j1             = inj₂ (_ , _ , P1.psL (λ ()) (cRN U.tt) , λ ())
  progJ j2             = inj₂ (_ , _ , P1.psy U.tt cSR sRN , λ ())
  progJ j3             = inj₂ (_ , _ , P1.psR (λ ()) (sAC U.tt) , λ ())
  progJ (j4 (rA h))    = inj₂ (_ , _ , P1.psy U.tt (cRA h) (sNA h) , λ ())
  progJ (j4 (rO q sz)) = inj₂ (_ , _ , P1.psy U.tt (cRO q sz) (sNO q sz) , λ ())
  progJ (j4 (rT q))    = inj₂ (_ , _ , P1.psy U.tt (cRT q) (sNT q) , λ ())
  progJ (j4 (rV vs))   = inj₂ (_ , _ , P1.psy U.tt (cRV vs) (sNV vs) , λ ())
  progJ (j4 rC)        = inj₂ (_ , _ , P1.psy U.tt cRC sNC , λ ())
  progJ (j5 (dAnn h))    = inj₂ (_ , _ , P1.psL (λ ()) (cDA h) , λ ())
  progJ (j5 (dOff q sz)) = inj₂ (_ , _ , P1.psL (λ ()) (cDO q sz) , λ ())
  progJ (j5 (dTxs q))    = inj₂ (_ , _ , P1.psL (λ ()) (cDT q) , λ ())
  progJ (j5 (dVot vs))   = inj₂ (_ , _ , P1.psL (λ ()) (cDV vs) , λ ())
  progJ q1             = inj₂ (_ , _ , P1.psy U.tt cSQ sQi , λ _ ())
  progJ q2             = inj₂ (_ , _ , P1.psR (λ ()) sDn , λ _ ())
  progJ q3             = inj₂ (_ , _ , P1.psy U.tt cDn sDS , λ _ ())
  progJ q4             = inj₁ (U.tt , U.tt)

  -- PROGRESS at every positioned state: a pending loop-back τ, or the phase's witness
  prog : ∀ {σ t} (j : JJ σ) → Abs.Pos SysA σ t → Prog j σ
  prog j (_ , _ , _ , pc , (_ , _ , ps)) with cτ? pc | sτ? ps
  ... | inj₂ (_ , a) | _            = inj₂ (τ′ , _ , P1.pτL a , λ _ → U.tt)
  ... | inj₁ refl    | inj₂ (_ , a) = inj₂ (τ′ , _ , P1.pτR a , λ _ → U.tt)
  ... | inj₁ refl    | inj₁ refl    = progJ j

  -- forgetting the blocking side condition
  progS : ∀ {σ t} → JJ σ → Abs.Pos SysA σ t
        → Abs.Fin SysA σ ⊎ Σ[ ℓ ∈ ALbl ] Σ[ σ′ ∈ SysS ] Abs.Stp SysA σ ℓ σ′
  progS j p with prog j p
  ... | inj₁ f                = inj₁ f
  ... | inj₂ (ℓ , σ′ , a , _) = inj₂ (ℓ , σ′ , a)

  -- a step of the blocked system is a system step
  unblk : ∀ {σ u ℓ σ′ u′} → Abs.Stp BlkA (σ , u) ℓ (σ′ , u′) → Abs.Stp SysA σ ℓ σ′
  unblk (P4.pτL a)   = a
  unblk (P4.psL _ a) = a
  unblk (P4.pτR ())
  unblk (P4.psy _ _ ())
  unblk (P4.psR _ ())

  -- progress of the blocked system once the quit command is behind: the witness never
  -- needs a blocked server send
  progB : ∀ {σ t} (j : JJ (proj₁ σ)) → T (postJ j) → Abs.Pos BlkA σ t
        → Abs.Fin BlkA σ ⊎ Σ[ ℓ ∈ ALbl ] Σ[ σ′ ∈ SysS × U.⊤ ] Abs.Stp BlkA σ ℓ σ′
  progB j post (_ , _ , refl , p , refl) with prog j p
  ... | inj₁ f                     = inj₁ (f , U.tt)
  ... | inj₂ (τ′ , _ , a , _)      = inj₂ (τ′ , _ , P4.pτL a)
  ... | inj₂ (ev′ _ , _ , a , off) = inj₂ (ev′ _ , _ , P4.psL (off post) a)

  -- boolean helpers
  ∧-l : ∀ {a b} → T (a ∧ b) → T a
  ∧-l {true} _ = U.tt

  -- (right conjunct)
  ∧-r : ∀ {a b} → T (a ∧ b) → T b
  ∧-r {true} t = t

  -- an implication read off `not a ∨ b`
  ⇒ : ∀ {a b} → T (not a ∨ b) → T a → T b
  ⇒ {true} t _ = t

  -- the client's quit command (its api trigger `lnpSendDone` at `(l , lo)`)
  QuitApi : Event → Set₁
  QuitApi e = e ≡ ⌜ ap lo lnpSendDone U.tt ⌝

  -- an abstract quit command label is one
  quitApi-T : ∀ ω → QuitApi ⌜ ω ⌝ → T (isQuitApi ω)
  quitApi-T ω eq with ⌜⌝-inj {ω} {ap lo lnpSendDone U.tt} eq
  ... | refl = U.tt

  -- every rank is at most 3
  rank≤3 : ∀ {c s} (j : J c s) → rankJ j ≤ 3
  rank≤3 j = ≤ᵇ⇒≤ (rankJ j) 3 (r3 j)
    where
    -- by computation
    r3 : ∀ {c s} (j : J c s) → T (rankJ j ≤ᵇ 3)
    r3 j1     = U.tt
    r3 j2     = U.tt
    r3 j3     = U.tt
    r3 (j4 _) = U.tt
    r3 (j5 _) = U.tt
    r3 q1     = U.tt
    r3 q2     = U.tt
    r3 q3     = U.tt
    r3 q4     = U.tt

  -- the invariant along any run of a system (`π` reads the system state off a state)
  module Walk {S : Set} (A : Abs S) (π : S → SysS)
              (un : ∀ {σ ℓ σ′} → Abs.Stp A σ ℓ σ′ → Abs.Stp SysA (π σ) ℓ (π σ′)) where
    open Abs A using (Pos; Fin; Stp)
    open Gen A using (ARun; r0; rτ; rE; runE)

    -- the invariant holds along a run, and the post-quit phase is entered by the quit
    -- command and never left
    walk : ∀ {σ s σ′} → ARun σ s σ′ → (j : JJ (π σ))
         → Σ[ j′ ∈ JJ (π σ′) ] ((Any QuitApi s ⊎ T (postJ j)) → T (postJ j′))
    walk r0 j = j , λ { (inj₁ ()) ; (inj₂ p) → p }
    walk (rτ a ar) j with J-step j (un a)
    ... | j₁ , _ , post≡ with walk ar j₁
    ...   | j′ , f = j′ , λ { (inj₁ q) → f (inj₁ q) ; (inj₂ p) → f (inj₂ (subst T (sym post≡) p)) }
    walk (rE {ω = ω} a ar) j with J-step j (un a)
    ... | j₁ , side with walk ar j₁
    ...   | j′ , f = j′ , g
      where
      -- the quit command here, later, or already behind
      g : (Any QuitApi (⌜ ω ⌝ ∷ _) ⊎ T (postJ j)) → T (postJ j′)
      g (inj₁ (here q))  = f (inj₂ (⇒ {isQuitApi ω} (proj₂ side) (quitApi-T ω q)))
      g (inj₁ (there q)) = f (inj₁ q)
      g (inj₂ p)         = f (inj₂ (∧-l {postJ j₁} (⇒ {postJ j} (proj₁ side) p)))

    -- after the quit command, a run has at most `rankJ` visible events
    bound : ∀ {σ s σ′} → ARun σ s σ′ → (j : JJ (π σ)) → T (postJ j) → length s ≤ rankJ j
    bound r0 _ _ = z≤n
    bound (rτ a ar) j p with J-step j (un a)
    ... | j₁ , rk≡ , post≡ = subst (_ ≤_) rk≡ (bound ar j₁ (subst T (sym post≡) p))
    bound (rE {ω = ω} a ar) j p with J-step j (un a)
    ... | j₁ , side with ⇒ {postJ j} (proj₁ side) p
    ...   | d = ≤-trans (s≤s (bound ar j₁ (∧-l {postJ j₁} d))) (≤ᵇ⇒≤ (suc (rankJ j₁)) (rankJ j) (∧-r {postJ j₁} d))

    -- (generic) a positioned start satisfying the invariant, with progress, is deadlock-free
    dlFree : (I : AbsI A)
           → (∀ {σ t} → JJ (π σ) → Pos σ t → Fin σ ⊎ Σ[ ℓ ∈ ALbl ] Σ[ σ′ ∈ S ] Stp σ ℓ σ′)
           → ∀ {σ t} → Pos σ t → JJ (π σ) → DeadlockFree t
    dlFree I pr p j r stk with runE p r
    ... | _ , ar , p′ = GenI.notStuck I p′ (pr (proj₁ (walk ar j)) p′) stk

    -- (generic) once the quit is commanded, with progress after it: what remains is
    -- deadlock-free, divergence-free, and has at most 3 visible events
    afterQuit : (I : AbsI A)
              → (∀ {σ t} (j : JJ (π σ)) → T (postJ j) → Pos σ t → Fin σ ⊎ Σ[ ℓ ∈ ALbl ] Σ[ σ′ ∈ S ] Stp σ ℓ σ′)
              → ∀ {σ t} → Pos σ t → JJ (π σ) → ∀ {s W} → t ⟹∖√⟨ s ⟩ W → Any QuitApi s
              → DeadlockFree W × DivergenceFree W × (∀ {s′ W′} → W ⟹∖√⟨ s′ ⟩ W′ → length s′ ≤ 3)
    afterQuit I pr p j {W = W} r q with runE p r
    ... | _ , ar , p₁ with walk ar j
    ...   | j₁ , post = dl , Gen.divFree A p₁ , bd
      where
      -- the quit command is behind
      post₁ : T (postJ j₁)
      post₁ = post (inj₁ q)
      -- no deadlock from here
      dl : DeadlockFree W
      dl r′ stk with runE p₁ r′
      ... | _ , ar′ , p₂ with walk ar′ j₁
      ...   | j₂ , post′ = GenI.notStuck I p₂ (pr j₂ (post′ (inj₂ post₁)) p₂) stk
      -- at most 3 more visible events
      bd : ∀ {s′ W′} → W ⟹∖√⟨ s′ ⟩ W′ → length s′ ≤ 3
      bd r′ with runE p₁ r′
      ... | _ , ar′ , _ = ≤-trans (bound ar′ j₁ post₁) (rank≤3 j₁)

  -- the walk of the system
  module WS = Walk SysA (λ σ → σ) (λ a → a)
  -- the walk of the blocked system
  module WB = Walk BlkA proj₁ unblk

  ---------------------------------------------------------------- (a)

  -- (a) THE PAIR NEVER GETS STUCK BEFORE √: every √-free-reachable state has a move
  -- (api / done events left to the environment)
  sys-deadlockFree : DeadlockFree sys
  sys-deadlockFree = WS.dlFree SysI progS sys₀ j1

  -- (a) … and never diverges
  sys-divergenceFree : DivergenceFree sys
  sys-divergenceFree = Gen.divFree SysA sys₀

  ---------------------------------------------------------------- (b)

  -- (b) QUIT FROM StIdle ALWAYS COMPLETES.  With every server api send blocked (incl. the
  -- cancel), once the client's quit command `lnpSendDone` has occurred in a trace, the rest
  -- never gets stuck before √, never diverges, and has at most 3 visible events (MsgQuit,
  -- the server's done, MsgDone).  So every run from there is finite and ends in √.
  blk-afterQuit : ∀ {s W} → blk ⟹∖√⟨ s ⟩ W → Any QuitApi s
                → DeadlockFree W × DivergenceFree W × (∀ {s′ W′} → W ⟹∖√⟨ s′ ⟩ W′ → length s′ ≤ 3)
  blk-afterQuit = WB.afterQuit BlkI progB blk₀ j1

  ---------------------------------------------------------------- (c)

  -- the trace: the client commands RequestNext and sends it (the server receives it)
  trRN : List Event
  trRN = ⌜ ap lo lnpSendRequestNext U.tt ⌝ ∷ ⌜ wS lo (pay FromInitiator MsgLNPRequestNext) ⌝ ∷ []

  -- the stall: client in StBusy, server in StBusy, nothing pending
  σX : SysS × U.⊤
  σX = ((cB , false) , (sB , false)) , U.tt

  -- the abstract run into it (two visible events, then the two loop-backs)
  stRun : Gen.ARun BlkA (σ₀ , U.tt) trRN σX
  stRun = rE (P4.psL (λ ()) (P1.psL (λ ()) (cRN U.tt)))
        (rE (P4.psL (λ ()) (P1.psy U.tt cSR sRN))
        (rτ (P4.pτL (P1.pτL cτB))
        (rτ (P4.pτL (P1.pτR sτB))
         r0)))
    where open Gen BlkA using (rE; rτ; r0)

  -- in the stall there is no abstract step at all: the client (no agency) only receives,
  -- the server's only moves are its blocked api sends
  noStepX : ∀ {ℓ σ′} → Abs.Stp BlkA σX ℓ σ′ → ⊥
  noStepX (P4.pτL (P1.pτL ()))
  noStepX (P4.pτL (P1.pτR ()))
  noStepX (P4.pτR ())
  noStepX (P4.psy _ _ ())
  noStepX (P4.psR _ ())
  noStepX (P4.psL _ (P1.psL ¬w (cRA _)))   = ¬w U.tt
  noStepX (P4.psL _ (P1.psL ¬w (cRO _ _))) = ¬w U.tt
  noStepX (P4.psL _ (P1.psL ¬w (cRT _)))   = ¬w U.tt
  noStepX (P4.psL _ (P1.psL ¬w (cRV _)))   = ¬w U.tt
  noStepX (P4.psL _ (P1.psL ¬w cRC))       = ¬w U.tt
  noStepX (P4.psL ¬s (P1.psR _ (sAA _)))   = ¬s U.tt
  noStepX (P4.psL ¬s (P1.psR _ (sAO _ _))) = ¬s U.tt
  noStepX (P4.psL ¬s (P1.psR _ (sAT _)))   = ¬s U.tt
  noStepX (P4.psL ¬s (P1.psR _ (sAV _)))   = ¬s U.tt
  noStepX (P4.psL ¬s (P1.psR _ (sAC _)))   = ¬s U.tt
  noStepX (P4.psL _ (P1.psy _ (cRA _) ()))
  noStepX (P4.psL _ (P1.psy _ (cRO _ _) ()))
  noStepX (P4.psL _ (P1.psy _ (cRT _) ()))
  noStepX (P4.psL _ (P1.psy _ (cRV _) ()))
  noStepX (P4.psL _ (P1.psy _ cRC ()))

  -- (c) THE NON-PIPELINED STALL.  With every server api send blocked (incl. the cancel),
  -- "RequestNext commanded and sent" leads to a STUCK state: the client is in StBusy, has
  -- no agency and waits for a reply or MsgCanceled that never comes — in particular it
  -- cannot quit (no `lnpSendDone`, nor anything else, is ever offered again)
  blk-stall : Σ[ W ∈ Tree ] (blk ⟹∖√⟨ trRN ⟩ W × IsStuck W)
  blk-stall with GenI.runI BlkI stRun blk₀
  ... | W , r , p = W , r , Gen.stuckE BlkA p noStepX (λ { ((() , _) , _) })

  -- (c) … so the blocked pair is not deadlock-free
  blk-deadlock : HasDeadlock blk
  blk-deadlock = trRN , proj₁ blk-stall , proj₁ (proj₂ blk-stall) , proj₂ (proj₂ blk-stall)

  -- the escape: after the stall prefix, the server cancels, the client quits, the server
  -- reports done and sends MsgDone
  trC : List Event
  trC = trRN ++ ⌜ ap hi lnpSendCanceled U.tt ⌝ ∷ ⌜ wR lo (pay FromResponder MsgLNPCanceled) ⌝
               ∷ ⌜ ap lo lnpSendDone U.tt ⌝ ∷ ⌜ wS lo (pay FromInitiator MsgLNPQuit) ⌝
               ∷ ⌜ dn hi ⌝ ∷ ⌜ wR lo (pay FromResponder MsgLNPDone) ⌝ ∷ []

  -- the abstract run of the cancel-only system along it, to the terminated state
  cRun : Gen.ARun BlkCA (σ₀ , U.tt) trC (((cE , false) , (sE , false)) , U.tt)
  cRun = rE (P5.psL (λ ()) (P1.psL (λ ()) (cRN U.tt)))
       (rE (P5.psL (λ ()) (P1.psy U.tt cSR sRN))
       (rτ (P5.pτL (P1.pτL cτB))
       (rτ (P5.pτL (P1.pτR sτB))
       (rE (P5.psL (λ ()) (P1.psR (λ ()) (sAC U.tt)))
       (rE (P5.psL (λ ()) (P1.psy U.tt cRC sNC))
       (rτ (P5.pτL (P1.pτL cτI))
       (rτ (P5.pτL (P1.pτR sτI))
       (rE (P5.psL (λ ()) (P1.psL (λ ()) (cQi U.tt)))
       (rE (P5.psL (λ ()) (P1.psy U.tt cSQ sQi))
       (rτ (P5.pτL (P1.pτL cτQ))
       (rτ (P5.pτL (P1.pτR sτQ))
       (rE (P5.psL (λ ()) (P1.psR (λ ()) sDn))
       (rE (P5.psL (λ ()) (P1.psy U.tt cDn sDS))
        r0)))))))))))))
    where open Gen BlkCA using (rE; rτ; r0)

  -- (c) THE ESCAPE: with only the cancel allowed to the server (its notification sends
  -- blocked), the stall prefix continues through MsgCanceled, the client's quit and
  -- MsgDone to a terminated state (√)
  blkC-cancelThenQuit : Σ[ W ∈ Tree ] (blkC ⟹∖√⟨ trC ⟩ W × PTree.force W ≡ ret tt)
  blkC-cancelThenQuit with GenI.runI BlkCI cRun blkC₀
  ... | W , r , p = W , r , AbsI.introR BlkCI p ((U.tt , U.tt) , U.tt)
