{-# OPTIONS --guardedness #-}

-- FAILURE-SIMULATION congruence for the BINARY ALPHABETISED PARALLEL `_⟦ A ∥ B ⟧_`
-- (= `αpar A B _,_`), under a DIVERGENCE-FREEDOM side condition on the SPEC operands:
--
--   αpar-fsim-df : (A B : EventSet)
--                → τ-AccReach P₂ → τ-AccReach Q₂
--                → FSim R P₁ P₂ → FSim S Q₁ Q₂
--                → FSim (R × S) (P₁ ⟦ A ∥ B ⟧ Q₁) (P₂ ⟦ A ∥ B ⟧ Q₂)
--
-- ORIENTATION: in `FSim R t₁ t₂` the FIRST argument is the IMPLEMENTATION and the
-- SECOND the SPECIFICATION (`fsim→⊑FD : FSim R Q P → P ⊑FD Q`), so the side condition
-- constrains the SPEC operands ONLY — the implementation operands stay completely
-- unconstrained, which is what makes the law usable for refinement (`αpar-mono-⊑FD-fsim-df`
-- below: a divergence-free spec composite refines to an arbitrary impl composite).
--
-- WHY A SIDE CONDITION IS NECESSARY (not a proof artefact).  `CSP.Laws.FSim.
-- AlphaParCounterexample` PROVES the unconditional two-sided law FALSE (`¬αpar-fsim`)
-- AND the one-sided variant that fixes one operand FALSE in both orientations
-- (`¬αpar-fsim-R`; the witness has `P₁ = P₂` literally, and `αpar` inspects BOTH heads,
-- so the mirror image refutes the other orientation too).  The mechanism is `αpar`'s
-- SIL-HEADED-OPERAND PRIORITY: a `sil` head on either side pre-empts the composite
-- entirely, so a `sil`-headed spec operand MASKS the other operand's visible offers.
-- Finitely many masking τ's are absorbed by `WSimF`'s weak matching, but the masking
-- becomes PERMANENT exactly when the spec operand's leading `sil` chain is infinite
-- (spec operand = `div`), and `FSim` does relate a `react`-headed divergence to `div`.
-- A bare `NoSil` invariant cannot repair this: `NoSil` is not preserved by τ-stepping,
-- so it cannot be carried coinductively — it collapses into divergence-freedom.
--
-- WHICH side condition, and why `τ-AccReach` rather than `τ-Acc`.  The proof DRAINS the
-- leading `sil`s of each spec operand at every matched step (see `αdrain`), so it needs
-- τ-accessibility not merely at the two roots but at every spec-operand state the
-- corecursion reaches — that is, closed under τ-steps AND under visible (non-√) steps.
-- `τ-AccReach` (`Semantics.DivergenceFree`) is exactly that closure, and `τ-Acc` alone
-- is NOT enough (it says nothing after a visible step).  `τ-AccReach` is used only
-- through the four one-line closure lemmas below and `∖√-refl` at the root.
--
-- THE PROOF, field by field.
--
--   fwd  : invert an IMPL composite step (`αpar-vis-step-inv` / `αpar-τ-step-inv` /
--          `αpar-√-step-inv`), then, before lifting anything to the spec side, DRAIN
--          both spec operands to non-`sil` heads with `αdrain`: the drain is FORCED and
--          UNIQUE (a `sil` node has exactly one τ-successor) and BOUNDED by the
--          inductive `τ-Acc`, so it is a well-founded induction, NOT a König step.  The
--          simulation is carried across the drain by `Semantics.FailureSim.
--          fsim-sil-factor`, one `sil` node at a time.  At the drained pair every
--          `NoSil` premise of `CSP.Laws.AlphaParallelLift` is available, so
--          `αpar-flush` (the drain itself, as ONE composite silent run),
--          `αpar-wsolo-L`/`-R`, `αpar-wsync`, `αpar-τ*-L`/`-R` and `αpar-w√` all apply.
--          The `sync` case additionally drains the two run ENDPOINTS (which is what
--          `αpar-wsync` requires there) and absorbs those drains into the weak step's
--          trailing runs.  The `√` case needs NO drain: `αpar-w√`'s flush endpoints are
--          `ret`-headed.
--
--   stab : NO side condition, and a transcription of `CSP.Laws.FSim.ParCong`'s: classify
--          the stable impl composite with the constructive `αpar-stable-normal` into
--          stable|stable, ret|stable or stable|ret, settle each spec operand (a stable
--          one by its own `FSim.stab`, a terminated one by its `FSim.fwd` match of the
--          impl's `√`, whose weak run exhibits a τ*-run into a `ret`-headed state), glue
--          the two spec runs with the `αpar-flush` corollaries (whose endpoint `NoSil`s
--          a stable / `ret` endpoint discharges), and compose the offer inclusions with
--          `αpar-offer-mono`.
--
--   div→ : the side condition makes the hypothesis REFUTABLE, which is the cheapest
--          honest discharge: the certified König step `αpar-Diverges→` splits the impl
--          composite's livelock into an impl OPERAND livelock, that operand's own
--          `FSim.div→` transfers it to the corresponding SPEC operand, and `τ-Acc→¬Div`
--          refutes it there.  (Re-LIFTING a spec-operand divergence into the spec
--          composite would need `NoSil` on the OTHER spec operand — i.e. the very same
--          side condition — so no phrasing of `div→` escapes it: while `Q₂` is
--          `sil`-headed the composite cannot perform any step of `P₂`, and deciding
--          whether `Q₂`'s `sil` chain is finite is exactly what `τ-Acc` provides.)
--
-- POSTULATES.  This module declares NONE.  It INHERITS exactly one, through `div→`: the
-- pre-existing `CSP.Laws.FD.AlphaParallelDivergence.αpar-Diverges→` König interface,
-- certified sound from the single `dne` of `CSP.Laws.ClassicalFromLEM` (Derivation 11),
-- used here exactly as `ParCong.Par-fsim-div→` uses `Par-Diverges→`.  `fwd` and `stab`
-- are fully constructive.  No NON_TERMINATING, no sized type, no hole.
--
-- SHAPE.  The operator is the `_,_`-merge instance `_⟦ A ∥ B ⟧_` (the only shape
-- `CSP.Laws.AlphaParallelLift` states its lemmas for), so the composite carrier is
-- `R × S` and there is no `merge` argument; the two operand carriers may live at
-- DIFFERENT levels (unlike `ParCong`, whose `Par-stable-normal` pins them to one).

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees

module CSP.Laws.FSim.AlphaParCong {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS        {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.WeakBisim  {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.Refusals   {E = E} {I = ExtI E} using (Offers)
open import Semantics.DRBisim    {E = E} {I = ExtI E} using (Diverges)
open import Semantics.Deadlock   {E = E} {I = ExtI E}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.DivergenceFree {E = E} {I = ExtI E}
  using (τ-Acc; acc; τ-AccReach; τ-Acc→¬Div)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_⊑FD_)
open import Semantics.FailureSim {E = E} {I = ExtI E}
  using (FSim; fsim-refl; fsim-sil-factor; fsim→⊑FD)
open import CSP.Laws.AlphaParallel E-≟
  using ( αVisR; vSync; vSoloL; vSoloR; v√
        ; αpar-vis-step-inv; αpar-√-step-inv; αpar-τ-step-inv )
open import CSP.Laws.AlphaParallelLift E-≟
  using ( NoSil; noSil-ret; noSil-react; noSil-stable; √-source
        ; αpar-τ*-L; αpar-τ*-R; αpar-flush
        ; αpar-flush-stable; αpar-flush-retL; αpar-flush-retR
        ; αpar-wsolo-L; αpar-wsolo-R; αpar-wsync; αpar-w√
        ; αpar-stable; αpar-stable-termL; αpar-stable-termR
        ; αpar-stable-normal; αpar-offer-mono; ret-offer-incl )
open import CSP.Laws.FD.AlphaParallelDivergence E-≟ using (αpar-Diverges→)

-------------------------------------------------------------------------------------
-- §1.  `τ-AccReach` closure: the side condition survives every spec-side move the
-- proof makes (one τ, a whole silent run, one visible non-√ event, a weak event).
-- Each is one line: `⟹∖√` is built by PREPENDING the step to the given run.
-------------------------------------------------------------------------------------

-- closed under a single τ-step
arτ : ∀ {ℓr} {R : Set ℓr} {t u : PTree E (ExtI E) R}
    → τ-AccReach t → t ─[ τ ]─► u → τ-AccReach u
arτ ar st run = ar (∖√-τ st run)

-- closed under a whole silent run (iterate `arτ`)
arτ* : ∀ {ℓr} {R : Set ℓr} {t u : PTree E (ExtI E) R}
     → τ-AccReach t → t ─[τ*]─► u → τ-AccReach u
arτ* ar τ*-refl           = ar
arτ* ar (τ*-step st rest) = arτ* (arτ ar st) rest

-- closed under a single VISIBLE (non-√) step
arev : ∀ {ℓr} {R : Set ℓr} {t u : PTree E (ExtI E) R} {e : Event}
     → τ-AccReach t → t ─[ ev (evl e) ]─► u → τ-AccReach u
arev ar st run = ar (∖√-ev st run)

-- … hence under a WEAK visible (non-√) step (τ* · e · τ*)
arwev : ∀ {ℓr} {R : Set ℓr} {t u : PTree E (ExtI E) R} {e : Event}
      → τ-AccReach t → t ═[ ev (evl e) ]═► u → τ-AccReach u
arwev ar (wev pre stp post) = arτ* (arev (arτ* ar pre) stp) post

-------------------------------------------------------------------------------------
-- §2.  THE DRAIN — the engine of the whole proof.  A spec operand's leading `sil`s are
-- consumed until its head is `ret` or `react`, i.e. until `NoSil` holds; the drain run
-- is returned (so it can be lifted into the composite by `αpar-flush`) together with
-- the simulation re-established at the drained state.
--
-- It is a WELL-FOUNDED INDUCTION, not a König step: the `sil` node has exactly ONE
-- τ-successor, so no choice is made, and the inductive `τ-Acc` bounds the chain.
-- `fsim-sil-factor` (Semantics.FailureSim) is what moves the simulation one node down.
-------------------------------------------------------------------------------------

-- drain a spec state's leading `sil`s, carrying the simulation along
αdrain : ∀ {ℓr} {R : Set ℓr} {t T : PTree E (ExtI E) R}
       → τ-Acc T → FSim R t T
       → Σ[ T′ ∈ PTree E (ExtI E) R ]
           ((T ─[τ*]─► T′) × NoSil T′ × FSim R t T′)
αdrain {T = T} (acc f) sim with T .force in eqT
... | ret r      = T , τ*-refl , noSil-ret   {t = T} eqT , sim
... | react v τc = T , τ*-refl , noSil-react {t = T} eqT , sim
... | sil T0 with αdrain (f (sSil eqT)) (fsim-sil-factor eqT sim)
...   | T′ , run , ns , sim′ = T′ , τ*-step (sSil eqT) run , ns , sim′

-------------------------------------------------------------------------------------
-- §3.  Weak-step surgery: the two gluings the drains need.
-------------------------------------------------------------------------------------

-- absorb a trailing silent run into a weak visible step
wev-then-τ* : ∀ {ℓr} {R : Set ℓr} {t u w : PTree E (ExtI E) R} {l : Event√ R}
            → t ═[ ev l ]═► u → u ─[τ*]─► w → t ═[ ev l ]═► w
wev-then-τ* (wev pre stp post) run = wev pre stp (τ*-trans post run)

-- absorb a leading silent run into a weak visible step
τ*-then-wev : ∀ {ℓr} {R : Set ℓr} {t u w : PTree E (ExtI E) R} {l : Event√ R}
            → t ─[τ*]─► u → u ═[ ev l ]═► w → t ═[ ev l ]═► w
τ*-then-wev run (wev pre stp post) = wev (τ*-trans run pre) stp post

-------------------------------------------------------------------------------------
-- §4.  What one matched impl step leaves behind.  A weak spec-COMPOSITE step (label
-- `l`) out of `C` into a composite of two DRAINED spec operands, plus the two
-- reachability certificates and the two operand simulations re-established there —
-- exactly the arguments the corecursive `αpar-fsim-df` call needs.  Packaging them in
-- one Σ keeps the corecursive call syntactically thin (and hence visibly guarded).
-------------------------------------------------------------------------------------

-- the payload of a matched step
MatchData : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (A B : EventSet)
          → PTree E (ExtI E) R → PTree E (ExtI E) S
          → PTree E (ExtI E) (R × S) → Label (R × S)
          → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr ⊔ ℓs)
MatchData {R = R} {S = S} A B P₁ Q₁ C l =
  Σ[ Pd ∈ PTree E (ExtI E) R ] Σ[ Qd ∈ PTree E (ExtI E) S ]
    ( (C ═[ l ]═► (Pd ⟦ A ∥ B ⟧ Qd))
    × τ-AccReach Pd × τ-AccReach Qd
    × FSim R P₁ Pd × FSim S Q₁ Qd )

-------------------------------------------------------------------------------------
-- §5.  The four matching lemmas (one per impl-composite step shape that has an operand
-- residual).  All four begin with the SAME two drains, whose runs become the composite
-- weak step's leading silent run via `αpar-flush`.
-------------------------------------------------------------------------------------

-- SYNC: both impl operands fire a shared (`A∩B`) event.  Both spec operands match it
-- weakly; the two run ENDPOINTS are then drained as well (that is what `αpar-wsync`
-- requires) and those drains are absorbed into the trailing runs.
match-sync : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (A B : EventSet)
             {P₁ P₁′ P₂ : PTree E (ExtI E) R} {Q₁ Q₁′ Q₂ : PTree E (ExtI E) S}
             {X : Set ℓ} {f : E X} {a : X}
           → A .mem (X , f) a → B .mem (X , f) a
           → τ-AccReach P₂ → τ-AccReach Q₂
           → FSim R P₁ P₂ → FSim S Q₁ Q₂
           → P₁ ─[ ev (evl (evLabel X f a)) ]─► P₁′
           → Q₁ ─[ ev (evl (evLabel X f a)) ]─► Q₁′
           → MatchData A B P₁′ Q₁′ (P₂ ⟦ A ∥ B ⟧ Q₂) (ev (evl (evLabel X f a)))
match-sync A B {P₂ = P₂} {Q₂ = Q₂} mA mB arP arQ pp qq P₁ev Q₁ev
  with αdrain (arP ∖√-refl) pp | αdrain (arQ ∖√-refl) qq
... | Pd , runP , nsPd , pp′ | Qd , runQ , nsQd , qq′
      with pp′ .FSim.fwd .WSimF.on-ev P₁ev | qq′ .FSim.fwd .WSimF.on-ev Q₁ev
...     | P₂′ , wP , relP | Q₂′ , wQ , relQ
          with αdrain (arwev (arτ* arP runP) wP ∖√-refl) relP
             | αdrain (arwev (arτ* arQ runQ) wQ ∖√-refl) relQ
...         | Pd² , runP² , nsPd² , relP′ | Qd² , runQ² , nsQd² , relQ′ =
              Pd² , Qd²
            , τ*-then-wev (αpar-flush A B P₂ Q₂ runP runQ nsPd nsQd)
                (αpar-wsync A B Pd Qd mA mB nsPd² nsQd²
                  (wev-then-τ* wP runP²) (wev-then-τ* wQ runQ²))
            , arτ* (arwev (arτ* arP runP) wP) runP²
            , arτ* (arwev (arτ* arQ runQ) wQ) runQ²
            , relP′ , relQ′

-- SOLO-L: an `A∖B` event of the LEFT impl operand.  The right spec operand stands
-- still at its DRAINED state, which is precisely the `NoSil Q` premise of the lift.
match-soloL : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (A B : EventSet)
              {P₁ P₁′ P₂ : PTree E (ExtI E) R} {Q₁ Q₂ : PTree E (ExtI E) S}
              {X : Set ℓ} {f : E X} {a : X}
            → A .mem (X , f) a → ¬ B .mem (X , f) a
            → τ-AccReach P₂ → τ-AccReach Q₂
            → FSim R P₁ P₂ → FSim S Q₁ Q₂
            → P₁ ─[ ev (evl (evLabel X f a)) ]─► P₁′
            → MatchData A B P₁′ Q₁ (P₂ ⟦ A ∥ B ⟧ Q₂) (ev (evl (evLabel X f a)))
match-soloL A B {P₂ = P₂} {Q₂ = Q₂} mA ¬mB arP arQ pp qq P₁ev
  with αdrain (arP ∖√-refl) pp | αdrain (arQ ∖√-refl) qq
... | Pd , runP , nsPd , pp′ | Qd , runQ , nsQd , qq′
      with pp′ .FSim.fwd .WSimF.on-ev P₁ev
...     | P₂′ , wP , relP =
          P₂′ , Qd
        , τ*-then-wev (αpar-flush A B P₂ Q₂ runP runQ nsPd nsQd)
            (αpar-wsolo-L A B Pd Qd mA ¬mB nsQd wP)
        , arwev (arτ* arP runP) wP
        , arτ* arQ runQ
        , relP , qq′

-- SOLO-R: mirror of `match-soloL` (a `B∖A` event of the RIGHT impl operand)
match-soloR : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (A B : EventSet)
              {P₁ P₂ : PTree E (ExtI E) R} {Q₁ Q₁′ Q₂ : PTree E (ExtI E) S}
              {X : Set ℓ} {f : E X} {a : X}
            → ¬ A .mem (X , f) a → B .mem (X , f) a
            → τ-AccReach P₂ → τ-AccReach Q₂
            → FSim R P₁ P₂ → FSim S Q₁ Q₂
            → Q₁ ─[ ev (evl (evLabel X f a)) ]─► Q₁′
            → MatchData A B P₁ Q₁′ (P₂ ⟦ A ∥ B ⟧ Q₂) (ev (evl (evLabel X f a)))
match-soloR A B {P₂ = P₂} {Q₂ = Q₂} ¬mA mB arP arQ pp qq Q₁ev
  with αdrain (arP ∖√-refl) pp | αdrain (arQ ∖√-refl) qq
... | Pd , runP , nsPd , pp′ | Qd , runQ , nsQd , qq′
      with qq′ .FSim.fwd .WSimF.on-ev Q₁ev
...     | Q₂′ , wQ , relQ =
          Pd , Q₂′
        , τ*-then-wev (αpar-flush A B P₂ Q₂ runP runQ nsPd nsQd)
            (αpar-wsolo-R A B Pd Qd ¬mA mB nsPd wQ)
        , arτ* arP runP
        , arwev (arτ* arQ runQ) wQ
        , pp′ , relQ

-- τ-L: a τ of the LEFT impl operand.  The spec's matching silent run is lifted by
-- `αpar-τ*-L` (right operand standing still at its drained, hence `NoSil`, state) and
-- appended to the drain flush.
match-τL : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (A B : EventSet)
           {P₁ P₁′ P₂ : PTree E (ExtI E) R} {Q₁ Q₂ : PTree E (ExtI E) S}
         → τ-AccReach P₂ → τ-AccReach Q₂
         → FSim R P₁ P₂ → FSim S Q₁ Q₂ → P₁ ─[ τ ]─► P₁′
         → MatchData A B P₁′ Q₁ (P₂ ⟦ A ∥ B ⟧ Q₂) τ
match-τL A B {P₂ = P₂} {Q₂ = Q₂} arP arQ pp qq P₁τ
  with αdrain (arP ∖√-refl) pp | αdrain (arQ ∖√-refl) qq
... | Pd , runP , nsPd , pp′ | Qd , runQ , nsQd , qq′
      with pp′ .FSim.fwd .WSimF.on-tau P₁τ
...     | P₂′ , wτ run , relP =
          P₂′ , Qd
        , wτ (τ*-trans (αpar-flush A B P₂ Q₂ runP runQ nsPd nsQd)
                       (αpar-τ*-L A B Pd Qd nsQd run))
        , arτ* (arτ* arP runP) run
        , arτ* arQ runQ
        , relP , qq′

-- τ-R: mirror of `match-τL` (a τ of the RIGHT impl operand)
match-τR : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (A B : EventSet)
           {P₁ P₂ : PTree E (ExtI E) R} {Q₁ Q₁′ Q₂ : PTree E (ExtI E) S}
         → τ-AccReach P₂ → τ-AccReach Q₂
         → FSim R P₁ P₂ → FSim S Q₁ Q₂ → Q₁ ─[ τ ]─► Q₁′
         → MatchData A B P₁ Q₁′ (P₂ ⟦ A ∥ B ⟧ Q₂) τ
match-τR A B {P₂ = P₂} {Q₂ = Q₂} arP arQ pp qq Q₁τ
  with αdrain (arP ∖√-refl) pp | αdrain (arQ ∖√-refl) qq
... | Pd , runP , nsPd , pp′ | Qd , runQ , nsQd , qq′
      with qq′ .FSim.fwd .WSimF.on-tau Q₁τ
...     | Q₂′ , wτ run , relQ =
          Pd , Q₂′
        , wτ (τ*-trans (αpar-flush A B P₂ Q₂ runP runQ nsPd nsQd)
                       (αpar-τ*-R A B Pd Qd nsPd run))
        , arτ* arP runP
        , arτ* (arτ* arQ runQ) run
        , pp′ , relQ

-------------------------------------------------------------------------------------
-- §6.  THE `stab` FIELD — no side condition, no drain (the `αpar-flush` corollaries
-- accept stable and `ret` endpoints).  One named lemma per `αNormal` leaf, exactly as
-- `CSP.Laws.FSim.ParCong` does.
-------------------------------------------------------------------------------------

-- BOTH impl operands stable: settle both spec operands with their own `FSim.stab`
αpar-fsim-stab-both : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (A B : EventSet)
                      {P₁ P₂ : PTree E (ExtI E) R} {Q₁ Q₂ : PTree E (ExtI E) S}
                    → FSim R P₁ P₂ → FSim S Q₁ Q₂
                    → isStable P₁ → isStable Q₁
                    → Σ[ M ∈ PTree E (ExtI E) (R × S) ]
                        ( (P₂ ⟦ A ∥ B ⟧ Q₂) ─[τ*]─► M × isStable M
                        × (∀ e → Offers M e → Offers (P₁ ⟦ A ∥ B ⟧ Q₁) e) )
αpar-fsim-stab-both A B {P₁} {P₂} {Q₁} {Q₂} pp qq stP stQ
  with pp .FSim.stab stP | qq .FSim.stab stQ
... | P₂* , rP , stP* , inclP | Q₂* , rQ , stQ* , inclQ =
      (P₂* ⟦ A ∥ B ⟧ Q₂*)
    , αpar-flush-stable A B P₂ Q₂ rP rQ stP* stQ*
    , αpar-stable A B P₂* Q₂* stP* stQ*
    , αpar-offer-mono A B P₁ P₂* Q₁ Q₂*
        (noSil-stable {t = P₁} stP) (noSil-stable {t = Q₁} stQ)
        (αpar-stable A B P₂* Q₂* stP* stQ*) inclP inclQ

-- LEFT impl operand TERMINATED, right stable: the spec's left operand is settled by
-- matching the impl's `√` step (the weak match exhibits a τ*-run into a `ret r` state),
-- the spec's right operand by its own `FSim.stab`
αpar-fsim-stab-termL : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (A B : EventSet)
                       {P₁ P₂ : PTree E (ExtI E) R} {Q₁ Q₂ : PTree E (ExtI E) S}
                       {r : R}
                     → FSim R P₁ P₂ → FSim S Q₁ Q₂
                     → P₁ .force ≡ ret r → isStable Q₁
                     → Σ[ M ∈ PTree E (ExtI E) (R × S) ]
                         ( (P₂ ⟦ A ∥ B ⟧ Q₂) ─[τ*]─► M × isStable M
                         × (∀ e → Offers M e → Offers (P₁ ⟦ A ∥ B ⟧ Q₁) e) )
αpar-fsim-stab-termL A B {P₁} {P₂} {Q₁} {Q₂} pp qq eqP stQ
  with pp .FSim.fwd .WSimF.on-ev (sRet eqP) | qq .FSim.stab stQ
... | _ , wev {p′ = P₂ₛ} p→pₛ pₛev _ , _ | Q₂* , rQ , stQ* , inclQ =
      (P₂ₛ ⟦ A ∥ B ⟧ Q₂*)
    , αpar-flush-retL A B P₂ Q₂ p→pₛ rQ (√-source pₛev) stQ*
    , αpar-stable-termL A B P₂ₛ Q₂* (√-source pₛev) stQ*
    , αpar-offer-mono A B P₁ P₂ₛ Q₁ Q₂*
        (noSil-ret {t = P₁} eqP) (noSil-stable {t = Q₁} stQ)
        (αpar-stable-termL A B P₂ₛ Q₂* (√-source pₛev) stQ*)
        (ret-offer-incl (√-source pₛev) eqP) inclQ

-- LEFT impl operand stable, RIGHT terminated (mirror of `αpar-fsim-stab-termL`)
αpar-fsim-stab-termR : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (A B : EventSet)
                       {P₁ P₂ : PTree E (ExtI E) R} {Q₁ Q₂ : PTree E (ExtI E) S}
                       {s : S}
                     → FSim R P₁ P₂ → FSim S Q₁ Q₂
                     → isStable P₁ → Q₁ .force ≡ ret s
                     → Σ[ M ∈ PTree E (ExtI E) (R × S) ]
                         ( (P₂ ⟦ A ∥ B ⟧ Q₂) ─[τ*]─► M × isStable M
                         × (∀ e → Offers M e → Offers (P₁ ⟦ A ∥ B ⟧ Q₁) e) )
αpar-fsim-stab-termR A B {P₁} {P₂} {Q₁} {Q₂} pp qq stP eqQ
  with pp .FSim.stab stP | qq .FSim.fwd .WSimF.on-ev (sRet eqQ)
... | P₂* , rP , stP* , inclP | _ , wev {p′ = Q₂ₛ} q→qₛ qₛev _ , _ =
      (P₂* ⟦ A ∥ B ⟧ Q₂ₛ)
    , αpar-flush-retR A B P₂ Q₂ rP q→qₛ stP* (√-source qₛev)
    , αpar-stable-termR A B P₂* Q₂ₛ stP* (√-source qₛev)
    , αpar-offer-mono A B P₁ P₂* Q₁ Q₂ₛ
        (noSil-stable {t = P₁} stP) (noSil-ret {t = Q₁} eqQ)
        (αpar-stable-termR A B P₂* Q₂ₛ stP* (√-source qₛev))
        inclP (ret-offer-incl (√-source qₛev) eqQ)

-- the `stab` field itself: classify the stable impl composite (constructive
-- `αpar-stable-normal`) and apply the matching leaf lemma
αpar-fsim-stab : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (A B : EventSet)
                 {P₁ P₂ : PTree E (ExtI E) R} {Q₁ Q₂ : PTree E (ExtI E) S}
               → FSim R P₁ P₂ → FSim S Q₁ Q₂
               → isStable (P₁ ⟦ A ∥ B ⟧ Q₁)
               → Σ[ M ∈ PTree E (ExtI E) (R × S) ]
                   ( (P₂ ⟦ A ∥ B ⟧ Q₂) ─[τ*]─► M × isStable M
                   × (∀ e → Offers M e → Offers (P₁ ⟦ A ∥ B ⟧ Q₁) e) )
αpar-fsim-stab A B {P₁} {P₂} {Q₁} {Q₂} pp qq st
  with αpar-stable-normal A B P₁ Q₁ st
... | inj₁ (stP , stQ)            = αpar-fsim-stab-both  A B pp qq stP stQ
... | inj₂ (inj₁ (r , eqP , stQ)) = αpar-fsim-stab-termL A B pp qq eqP stQ
... | inj₂ (inj₂ (stP , s , eqQ)) = αpar-fsim-stab-termR A B pp qq stP eqQ

-------------------------------------------------------------------------------------
-- §7.  THE `div→` FIELD: the certified König step splits the impl composite's livelock
-- into an impl OPERAND livelock, the operand `FSim.div→` transfers it to the spec
-- operand, and the side condition refutes it there.
-------------------------------------------------------------------------------------

-- divergence transfer (vacuously: a divergence-free spec forces a divergence-free impl)
αpar-fsim-div→ : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (A B : EventSet)
                 {P₁ P₂ : PTree E (ExtI E) R} {Q₁ Q₂ : PTree E (ExtI E) S}
               → τ-Acc P₂ → τ-Acc Q₂
               → FSim R P₁ P₂ → FSim S Q₁ Q₂
               → Diverges (P₁ ⟦ A ∥ B ⟧ Q₁) → Diverges (P₂ ⟦ A ∥ B ⟧ Q₂)
αpar-fsim-div→ A B acP acQ pp qq d with αpar-Diverges→ A B d
... | inj₁ dP = ⊥-elim (τ-Acc→¬Div acP (pp .FSim.div→ dP))
... | inj₂ dQ = ⊥-elim (τ-Acc→¬Div acQ (qq .FSim.div→ dQ))

-------------------------------------------------------------------------------------
-- §8.  THE CONGRUENCE.  Forward declarations (no old-style `mutual`): the corecursive
-- `αpar-fsim-df` residuals sit under the `WSimF` Σ-results of `f-sim-αpar`, which is
-- the guardedness discipline of `ParCong.f-sim-Par`.  Every composite is passed as an
-- ARGUMENT to a lift lemma and is never `with`-forced here, so no composite is driven
-- to weak head normal form in this module.
-------------------------------------------------------------------------------------

-- HEADLINE: `_⟦ A ∥ B ⟧_` is an FSim congruence provided the two SPEC operands are
-- divergence-free at every reachable state (the impl operands are unconstrained)
αpar-fsim-df : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (A B : EventSet)
               {P₁ P₂ : PTree E (ExtI E) R} {Q₁ Q₂ : PTree E (ExtI E) S}
             → τ-AccReach P₂ → τ-AccReach Q₂
             → FSim R P₁ P₂ → FSim S Q₁ Q₂
             → FSim (R × S) (P₁ ⟦ A ∥ B ⟧ Q₁) (P₂ ⟦ A ∥ B ⟧ Q₂)

-- the forward half: invert one impl composite step, match it with the corresponding
-- `match-…` lemma, and hand the payload to the corecursion
f-sim-αpar : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (A B : EventSet)
             {P₁ P₂ : PTree E (ExtI E) R} {Q₁ Q₂ : PTree E (ExtI E) S}
           → τ-AccReach P₂ → τ-AccReach Q₂
           → FSim R P₁ P₂ → FSim S Q₁ Q₂
           → WSimF (FSim (R × S)) (P₁ ⟦ A ∥ B ⟧ Q₁) (P₂ ⟦ A ∥ B ⟧ Q₂)

-- visible steps of the impl composite: routed by alphabet membership
f-sim-αpar A B arP arQ pp qq .WSimF.on-ev (sVis feq br)
  with αpar-vis-step-inv feq br
... | vSync mA mB P₁ev Q₁ev
      with match-sync A B mA mB arP arQ pp qq P₁ev Q₁ev
...     | Pd , Qd , run , arPd , arQd , relP , relQ =
          (Pd ⟦ A ∥ B ⟧ Qd) , run , αpar-fsim-df A B arPd arQd relP relQ
f-sim-αpar A B arP arQ pp qq .WSimF.on-ev (sVis feq br)
    | vSoloL mA ¬mB P₁ev
      with match-soloL A B mA ¬mB arP arQ pp qq P₁ev
...     | Pd , Qd , run , arPd , arQd , relP , relQ =
          (Pd ⟦ A ∥ B ⟧ Qd) , run , αpar-fsim-df A B arPd arQd relP relQ
f-sim-αpar A B arP arQ pp qq .WSimF.on-ev (sVis feq br)
    | vSoloR ¬mA mB Q₁ev
      with match-soloR A B ¬mA mB arP arQ pp qq Q₁ev
...     | Pd , Qd , run , arPd , arQd , relP , relQ =
          (Pd ⟦ A ∥ B ⟧ Qd) , run , αpar-fsim-df A B arPd arQd relP relQ
-- the joint √: both impl operands are at `ret`, so both spec operands weakly terminate
-- (no drain: `αpar-w√`'s flush endpoints are `ret`-headed)
f-sim-αpar A B {P₂ = P₂} {Q₂ = Q₂} arP arQ pp qq .WSimF.on-ev (sRet feq)
  with αpar-√-step-inv feq
... | v√ eqP eqQ
      with pp .FSim.fwd .WSimF.on-ev (sRet eqP) | qq .FSim.fwd .WSimF.on-ev (sRet eqQ)
...     | _ , wP , _ | _ , wQ , _ =
          deadlock , αpar-w√ A B P₂ Q₂ wP wQ , fsim-refl deadlock

-- τ steps of the impl composite: one operand's τ
f-sim-αpar A B arP arQ pp qq .WSimF.on-tau step with αpar-τ-step-inv step
... | inj₁ (P₁′ , P₁τ , refl) with match-τL A B arP arQ pp qq P₁τ
...   | Pd , Qd , run , arPd , arQd , relP , relQ =
        (Pd ⟦ A ∥ B ⟧ Qd) , run , αpar-fsim-df A B arPd arQd relP relQ
f-sim-αpar A B arP arQ pp qq .WSimF.on-tau step
    | inj₂ (Q₁′ , Q₁τ , refl) with match-τR A B arP arQ pp qq Q₁τ
...   | Pd , Qd , run , arPd , arQd , relP , relQ =
        (Pd ⟦ A ∥ B ⟧ Qd) , run , αpar-fsim-df A B arPd arQd relP relQ

αpar-fsim-df A B arP arQ pp qq .FSim.fwd      = f-sim-αpar     A B arP arQ pp qq
αpar-fsim-df A B arP arQ pp qq .FSim.stab st  = αpar-fsim-stab A B pp qq st
αpar-fsim-df A B arP arQ pp qq .FSim.div→  d  =
  αpar-fsim-div→ A B (arP ∖√-refl) (arQ ∖√-refl) pp qq d

-------------------------------------------------------------------------------------
-- §9.  The refinement corollary.  `fsim→⊑FD : FSim R Q P → P ⊑FD Q` puts the SPEC on
-- the LEFT of `⊑FD`, so the divergence-free composite is the one being refined.
-------------------------------------------------------------------------------------

-- MONOTONICITY of `_⟦ A ∥ B ⟧_` for `⊑FD`, from an `FSim` WITNESS premise (not a bare
-- `⊑FD` fact — hence the `-fsim` premise-shape suffix) PLUS divergence-freedom on the
-- SPEC side (the `-df` side-condition suffix; the two suffixes are independent markers)
αpar-mono-⊑FD-fsim-df : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (A B : EventSet)
                   {P₁ P₂ : PTree E (ExtI E) R} {Q₁ Q₂ : PTree E (ExtI E) S}
                 → τ-AccReach P₂ → τ-AccReach Q₂
                 → FSim R P₁ P₂ → FSim S Q₁ Q₂
                 → (P₂ ⟦ A ∥ B ⟧ Q₂) ⊑FD (P₁ ⟦ A ∥ B ⟧ Q₁)
αpar-mono-⊑FD-fsim-df A B arP arQ pp qq = fsim→⊑FD (αpar-fsim-df A B arP arQ pp qq)
