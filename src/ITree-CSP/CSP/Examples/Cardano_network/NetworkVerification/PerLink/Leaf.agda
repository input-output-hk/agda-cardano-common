{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — per-link mux STEP characterizations
-- (`PerLink.Leaf`), the CONFIG-INDEPENDENT leaf layer.
--
-- The config-independent slice of the `perLink-single` campaign's third
-- layer (`PerLink.Step`), factored out (Milestone 2b Task 1) so the
-- upcoming GENERAL fold machinery (`PerLink.Fold`) can build on it
-- without going through the singleton-only glue.  Three strata:
--
--   · fully generic confinement bridge (`noView`/`noStep-Par`/
--     `Skip-no-ev`/`Skip-no-τ`/`noStep-∖`, `vev`-style `evN`, …) — needs
--     no `l`/`dc`/`idc` at all;
--   · `(l)`-only material: leaf-loop stability and `no-√` (the decode
--     never terminates), independent of the configured instance;
--   · `(l , dc , idc)`-parameterized (but config-INDEPENDENT) per-leaf
--     force/offer/fire/guard-τ lemmas, stability, offer refutations, and
--     the `-L` link-generalised τ/event classifier families (`l₀ ≡ l`
--     payloads) for the Input/Output cells and the four registers, plus
--     the `IS`/`TR`/`OS`/`RS` fold-degenerate composites built on them.
--
-- the 2a singleton `PerLink.Step` (deleted in 2b) imported this module
-- and added the SINGLETON-specific glue (`cfg≡ : linkConfig l ≡ (dc , idc) ∷ []`)
-- on top.
--
-- No postulates, holes, or `NON_TERMINATING`.
------------------------------------------------------------------------
open import Level using (0ℓ; lift)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂; Σ; Σ-syntax; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; ≡-≟-identity; sym; trans; cong; cong₂; subst)
open import Class.DecEq using (DecEq; _≟_)
open import Function.Base using (case_of_)
import Data.Fin.Properties as FinP

open import Process_Trees
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using (Dir; IDs; lo; hi)

module CSP.Examples.Cardano_network.NetworkVerification.PerLink.Leaf
  (p : Params) (Data : Set) ⦃ _ : DecEq Data ⦄ where

open PTree

open import CSP.Examples.Cardano_network.Net p
  using ( Net; Net-≟; Link
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack )
open Params p using (linkConfig)

import CSP.Operators {E = Net Data} (Net-≟ {Data}) as Op
open Op using (_∥⇘_⇙_; _⦀_; _∖_; chanSet; Skip; Par; Par⊤; ∅ES; EventSet; viewV)

open import Semantics.LTS {E = Net Data} {I = ExtI (Net Data)}
open import Semantics.DRBisim {E = Net Data} {I = ExtI (Net Data)}
  using (Diverges)

open import CSP.Examples.Cardano_network.Network p Data
  using ( NetProc
        ; csSR; csSR-dec; csRS; csRS-dec; csTA; csTA-dec )
open import CSP.Examples.Cardano_network.NetworkLink p Data
  using ( Transmitterₗ; RcvAckₗ; Receiverₗ; SndAckₗ )
open import CSP.Examples.Cardano_network.NetworkVerification.PerLink.State p Data
open import CSP.Examples.Cardano_network.NetworkVerification.PerLink.Decode p Data

open import CSP.Laws.Traces.TraceLawsParallelElim (Net-≟ {Data})
  using (Par-τ-elim; ParτR; τL; τR
        ; Par-ev-elim; ParevR; evSync; evL; evR; evBoth; ev√
        ; Par-force-ret-inv; viewV-ev; sil-τ-inv)
open import CSP.Laws.Traces.TraceLawsParallel (Net-≟ {Data})
  using (Par-soloL; Par-soloR; Par-sync; Par-τ-L; Par-τ-R)
open import CSP.Laws.Traces.TraceLawsHide (Net-≟ {Data})
  using ( Hide-τ-elim; HideτR; hτP; hτH
        ; Hide-ev-elim; HideevR; heV; he√
        ; Hide-τ; Hide-keep; Hide-hidden
        ; fHide-ret-inv )

------------------------------------------------------------------------
-- ⊤-merge for the ⊤-valued CSP parallel, the three value-level sync/hide
-- sets (exactly the `Decode`/`NetworkLink` forms), and the return type.
------------------------------------------------------------------------

-- the joint-√ merge (⊤ processes)
⊤merge : Poly.⊤ {0ℓ} → Poly.⊤ {0ℓ} → Poly.⊤ {0ℓ}
⊤merge _ _ = Poly.tt

------------------------------------------------------------------------
-- `≟-diag`: the reflexive decision of a `DecEq` returns `yes refl`.
-- Used to unblock the stuck `l ≟ l` / `d ≟ d` / `id ≟ id` / `x ≟ x`
-- redexes that guard the abstract-instance succV-chains.
------------------------------------------------------------------------

-- reflexive-diagonal of the `Class.DecEq` `_≟_`
≟-diag : ∀ {A : Set} ⦃ _ : DecEq A ⦄ (x : A) → (x ≟ x) ≡ yes refl
≟-diag x = ≡-≟-identity _≟_ refl

-- reflexive-diagonal of the Fin `_≟_` that `Net-≟` uses on the link index
≟-diagF : (x : Link) → (x FinP.≟ x) ≡ yes refl
≟-diagF x = ≡-≟-identity FinP._≟_ refl

-- a `nothing ≡ just _` is absurd (used to close Output-cont payload mismatches)
nothing-absurd : ∀ {A : Set} {W : NetProc} → nothing ≡ just W → A
nothing-absurd ()

-- generic ev-label builder for the network alphabet
evN : {B : Set} → Net Data B → B → Event√ NetR
evN {B} e a = evl (evLabel B e a)

-- the τ-branch part of a node (empty for non-react nodes); companion of the
-- `vis-of` re-used from `PerLink.Decode`
tau-of : NodeKind (Net Data) (ExtI (Net Data)) NetR
       → (i : AnyTypes (ExtI (Net Data))) → proj₁ i → Maybe NetProc
tau-of (react _ τc) = τc
tau-of _            = λ _ _ → nothing

------------------------------------------------------------------------
-- Confinement infrastructure (fully generic — needs no `l`/`dc`/`idc`).
-- `Par-soloL`/`Par-soloR` require the idle operand's `viewV … ≡ nothing`;
-- we derive it from "no visible step" (`noView`, valid even on a stuck
-- force) and compose non-offers through `⦀` (`noStep-Par`) and `∖`
-- (`noStep-∖`), never computing a stuck force.
------------------------------------------------------------------------

-- a process with no `(e,a)` visible step offers `nothing` on `(e,a)`
noView : ∀ {P : NetProc} {B} {e : Net Data B} {a}
       → (∀ {W} → ¬ (P ─[ ev (evN e a) ]─► W))
       → viewV (PTree.force P) (B , e) a ≡ nothing
noView {P} {B} {e} {a} ns with viewV (PTree.force P) (B , e) a in eq
... | nothing = refl
... | just W  = ⊥-elim (ns (viewV-ev refl eq))

-- `Par A ⊤merge P Q` makes no `(e,a)` step if neither operand does
-- (covers `⦀` = `Par ∅ES ⊤merge` and `∥⇘ A ⇙` = `Par A ⊤merge` alike;
--  a sync would need P to fire, contradicting `nsP`).
noStep-Par : ∀ {A : EventSet} {P Q : NetProc} {B} {e : Net Data B} {a}
           → (∀ {W} → ¬ (P ─[ ev (evN e a) ]─► W))
           → (∀ {W} → ¬ (Q ─[ ev (evN e a) ]─► W))
           → ∀ {W} → ¬ (Par A ⊤merge P Q ─[ ev (evN e a) ]─► W)
noStep-Par {A} {P} {Q} nsP nsQ step with Par-ev-elim A ⊤merge P Q step
... | evSync _ Pev _  = nsP Pev
... | evL _ Pev       = nsP Pev
... | evR _ Qev       = nsQ Qev
... | evBoth _ Pev _  = nsP Pev

-- `Skip` (a `ret` node) makes no visible step
Skip-no-ev : ∀ {B} {e : Net Data B} {a} {W} → ¬ (Skip ─[ ev (evN e a) ]─► W)
Skip-no-ev (sVis () _)

-- `Skip` (a `ret` node) makes no τ step
Skip-no-τ : ∀ {W : NetProc} → Skip ─[ τ ]─► W → ⊥
Skip-no-τ (sSil ())
Skip-no-τ (sTau () _)

-- `P ∖ A` (with `(e,a) ∉ A`) makes no `(e,a)` step if `P` doesn't
noStep-∖ : ∀ {P : NetProc} {A} {B} {e : Net Data B} {a}
         → ¬ (EventSet.mem A (B , e) a)
         → (∀ {W} → ¬ (P ─[ ev (evN e a) ]─► W))
         → ∀ {W} → ¬ ((P ∖ A) ─[ ev (evN e a) ]─► W)
noStep-∖ {P} {A} ¬mem nsP step with Hide-ev-elim A P step
... | heV W' ¬cs Pev = nsP Pev

------------------------------------------------------------------------
-- The `l`-only step layer: leaf-loop stability, the no-`ret` fact, and
-- `no-√` — none of these depend on the configured instance `(dc , idc)`.
------------------------------------------------------------------------

module _ (l : Link) where

  ------------------------------------------------------------------------
  -- Stability: each bare-leaf loop head (`loop0 (pchoice …)`) has an
  -- everywhere-nothing τ-branch map, so every τ-label step is refuted.
  -- (The `refl` matches `force (leaf) ≡ react …`, which holds because
  -- `loop0`'s node head is a `react` independently of the menu's `l`-gate.)
  ------------------------------------------------------------------------

  -- Transmitterₗ is stable (no τ at the loop head)
  Transmitterₗ-stable : ∀ {t} → Transmitterₗ l ─[ τ ]─► t → ⊥
  Transmitterₗ-stable (sSil ())
  Transmitterₗ-stable (sTau {i = _ , fin}                 refl ())
  Transmitterₗ-stable (sTau {i = _ , base _}              refl ())
  Transmitterₗ-stable (sTau {i = _ , pair fin (base _)}   refl ())
  Transmitterₗ-stable (sTau {i = _ , pair fin fin}        refl ())
  Transmitterₗ-stable (sTau {i = _ , pair fin (pair _ _)} refl ())
  Transmitterₗ-stable (sTau {i = _ , pair (base _) _}     refl ())
  Transmitterₗ-stable (sTau {i = _ , pair (pair _ _) _}   refl ())

  -- RcvAckₗ is stable
  RcvAckₗ-stable : ∀ {t} → RcvAckₗ l ─[ τ ]─► t → ⊥
  RcvAckₗ-stable (sSil ())
  RcvAckₗ-stable (sTau {i = _ , fin}                 refl ())
  RcvAckₗ-stable (sTau {i = _ , base _}              refl ())
  RcvAckₗ-stable (sTau {i = _ , pair fin (base _)}   refl ())
  RcvAckₗ-stable (sTau {i = _ , pair fin fin}        refl ())
  RcvAckₗ-stable (sTau {i = _ , pair fin (pair _ _)} refl ())
  RcvAckₗ-stable (sTau {i = _ , pair (base _) _}     refl ())
  RcvAckₗ-stable (sTau {i = _ , pair (pair _ _) _}   refl ())

  -- Receiverₗ is stable
  Receiverₗ-stable : ∀ {t} → Receiverₗ l ─[ τ ]─► t → ⊥
  Receiverₗ-stable (sSil ())
  Receiverₗ-stable (sTau {i = _ , fin}                 refl ())
  Receiverₗ-stable (sTau {i = _ , base _}              refl ())
  Receiverₗ-stable (sTau {i = _ , pair fin (base _)}   refl ())
  Receiverₗ-stable (sTau {i = _ , pair fin fin}        refl ())
  Receiverₗ-stable (sTau {i = _ , pair fin (pair _ _)} refl ())
  Receiverₗ-stable (sTau {i = _ , pair (base _) _}     refl ())
  Receiverₗ-stable (sTau {i = _ , pair (pair _ _) _}   refl ())

  -- SndAckₗ is stable
  SndAckₗ-stable : ∀ {t} → SndAckₗ l ─[ τ ]─► t → ⊥
  SndAckₗ-stable (sSil ())
  SndAckₗ-stable (sTau {i = _ , fin}                 refl ())
  SndAckₗ-stable (sTau {i = _ , base _}              refl ())
  SndAckₗ-stable (sTau {i = _ , pair fin (base _)}   refl ())
  SndAckₗ-stable (sTau {i = _ , pair fin fin}        refl ())
  SndAckₗ-stable (sTau {i = _ , pair fin (pair _ _)} refl ())
  SndAckₗ-stable (sTau {i = _ , pair (base _) _}     refl ())
  SndAckₗ-stable (sTau {i = _ , pair (pair _ _) _}   refl ())

  ------------------------------------------------------------------------
  -- `no-√`: the decode never terminates.  `force (decTrans l tb)` is
  -- always a `react`/`sil` (a buffer loop never `ret`s), so the `√`
  -- branch of the top `Hide-ev-elim` is refuted via `Par-force-ret-inv`.
  ------------------------------------------------------------------------

  -- the Transmitter register decode never `ret`s (loop head / stepped leaf)
  decTrans-noret : ∀ tb {x} → PTree.force (decTrans l tb) ≡ ret x → ⊥
  decTrans-noret free ()
  decTrans-noret (hold d id x) eqf rewrite ≟-diag l = case eqf of λ ()
  decTrans-noret (grd d id x) eqf
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x =
    case eqf of λ ()

  -- the decode of any mux state never offers a `√`
  no-√ : (st : MuxState l) {r : NetR} {M : NetProc}
       → ⟦ st ⟧ ─[ ev (√ r) ]─► M → ⊥
  no-√ st step
    with Hide-ev-elim csTA'
           (decTx l (iph st) (tb st) (ab st) ∥⇘ csTA' ⇙ decRx l (oph st) (rb st) (sb st))
           step
  ... | he√ eqf
        with Par-force-ret-inv csTA' ⊤merge
               {P = decTx l (iph st) (tb st) (ab st)}
               {Q = decRx l (oph st) (rb st) (sb st)} eqf
  ...   | _ , _ , decTxret , _ , _
          with Par-force-ret-inv csSR' ⊤merge
                 {P = decInputs l (linkConfig l) (iph st)}
                 {Q = decTrans l (tb st) ⦀ decRAck l (ab st)}
                 (fHide-ret-inv csSR'
                   (decInputs l (linkConfig l) (iph st)
                     ∥⇘ csSR' ⇙ (decTrans l (tb st) ⦀ decRAck l (ab st)))
                   decTxret)
  ...     | _ , _ , _ , TRret , _
            with Par-force-ret-inv ∅ES ⊤merge
                   {P = decTrans l (tb st)} {Q = decRAck l (ab st)} TRret
  ...       | _ , _ , decTransret , _ , _ = decTrans-noret (tb st) decTransret


------------------------------------------------------------------------
-- The config-INDEPENDENT per-instance leaf layer: force/offer/fire/
-- guard-τ lemmas, stability, offer refutations, and the `-L` link-
-- generalised classifier families for an ARBITRARY `(l , dc , idc)` —
-- none of this needs `linkConfig l` or the singleton hypothesis `cfg≡`.
-- Named (not anonymous) so the (since-deleted) 2a `PerLink.Step` could bring
-- it into scope for a fixed `(l , dc , idc)` via `open WithInstance l dc idc`,
-- with no call-site rewriting of the (many) uses below; kept named for
-- external consumers.
------------------------------------------------------------------------

module WithInstance (l : Link) (dc : Dir) (idc : IDs) where
  ------------------------------------------------------------------------
  -- Per-leaf single-step CONSTRUCTIONS (fires) and guard-τs.
  --
  -- For abstract `(dc , idc)` / payload `x` the succV-chains are STUCK, and
  -- `rewrite ≟-diag` does not reach the fresh redex created when an offer
  -- map is APPLIED (the p1 `sVis refl refl` idiom fails).  The fix: route
  -- every `sVis`/`sSil` through a `force-react`/`offer`/`force-sil` lemma
  -- whose goal SYNTACTICALLY contains the application, so `rewrite ≟-diag`
  -- (Class-`_≟_`) and `≟-diagF` (Fin-`_≟_`, used by `Net-≟` on the link)
  -- reduce both sides to `refl`.
  ------------------------------------------------------------------------

  -- Input cell (dc,idc): i0 -input-> i1 -sndmsg-> i2 -rcvack-> ig -τ-> i0.
  -- i1 cell force is a react (offer sndmsg); succV unblocked by the diag block
  force-react-i1 : ∀ {x} → PTree.force (decInput l (i1 x) dc idc)
                 ≡ react (vis-of (PTree.force (decInput l (i1 x) dc idc)))
                         (tau-of (PTree.force (decInput l (i1 x) dc idc)))
  force-react-i1 {x} rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc = refl

  -- i2 cell force is a react (offer rcvack); two-level diag block
  force-react-i2 : ∀ {x} → PTree.force (decInput l (i2 x) dc idc)
                 ≡ react (vis-of (PTree.force (decInput l (i2 x) dc idc)))
                         (tau-of (PTree.force (decInput l (i2 x) dc idc)))
  force-react-i2 {x}
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x = refl

  -- i0 offers `input` (→ i1 x)
  offer-i0 : ∀ {x} → vis-of (PTree.force (decInput l i0 dc idc)) (Data , input l dc idc) x
           ≡ just (decInput l (i1 x) dc idc)
  offer-i0 {x} rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc = refl

  -- i1 offers `sndmsg` (→ i2 x)
  offer-i1 : ∀ {x} → vis-of (PTree.force (decInput l (i1 x) dc idc)) (Data , sndmsg l dc idc) x
           ≡ just (decInput l (i2 x) dc idc)
  offer-i1 {x} rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x = refl

  -- i2 offers `rcvack` (→ ig x)
  offer-i2 : ∀ {x} → vis-of (PTree.force (decInput l (i2 x) dc idc)) (⊤ , rcvack l dc idc) tt
           ≡ just (decInput l (ig x) dc idc)
  offer-i2 {x} rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc = refl

  -- ig cell force is a `sil` (guard τ → i0)
  force-sil-ig : ∀ {x} → PTree.force (decInput l (ig x) dc idc) ≡ sil (decInput l i0 dc idc)
  force-sil-ig {x} rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc = refl

  -- i0 fires `input`
  dIn-i0-fire : ∀ {x} → decInput l i0 dc idc
              ─[ ev (evN (input l dc idc) x) ]─► decInput l (i1 x) dc idc
  dIn-i0-fire {x} = sVis refl (offer-i0 {x})

  -- i1 fires `sndmsg`
  dIn-i1-fire : ∀ {x} → decInput l (i1 x) dc idc
              ─[ ev (evN (sndmsg l dc idc) x) ]─► decInput l (i2 x) dc idc
  dIn-i1-fire {x} = sVis (force-react-i1 {x}) (offer-i1 {x})

  -- i2 fires `rcvack`
  dIn-i2-fire : ∀ {x} → decInput l (i2 x) dc idc
              ─[ ev (evN (rcvack l dc idc) tt) ]─► decInput l (ig x) dc idc
  dIn-i2-fire {x} = sVis (force-react-i2 {x}) (offer-i2 {x})

  -- ig takes the guard τ (→ i0)
  dIn-ig-τ : ∀ {x} → decInput l (ig x) dc idc ─[ τ ]─► decInput l i0 dc idc
  dIn-ig-τ {x} = sSil (force-sil-ig {x})

  -- Output cell (dc,idc): o0 -rcvmsg-> o1 -output-> o2 -sndack-> og -τ-> o0.
  -- o1 cell force is a react (offer output)
  force-react-o1 : ∀ {x} → PTree.force (decOutput l (o1 x) dc idc)
                 ≡ react (vis-of (PTree.force (decOutput l (o1 x) dc idc)))
                         (tau-of (PTree.force (decOutput l (o1 x) dc idc)))
  force-react-o1 {x} rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc = refl

  -- o2 cell force is a react (offer sndack)
  force-react-o2 : ∀ {x} → PTree.force (decOutput l (o2 x) dc idc)
                 ≡ react (vis-of (PTree.force (decOutput l (o2 x) dc idc)))
                         (tau-of (PTree.force (decOutput l (o2 x) dc idc)))
  force-react-o2 {x}
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x = refl

  -- o0 offers `rcvmsg` (→ o1 x)
  offer-o0 : ∀ {x} → vis-of (PTree.force (decOutput l o0 dc idc)) (Data , rcvmsg l dc idc) x
           ≡ just (decOutput l (o1 x) dc idc)
  offer-o0 {x} rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc = refl

  -- o1 offers `output` (→ o2 x)
  offer-o1 : ∀ {x} → vis-of (PTree.force (decOutput l (o1 x) dc idc)) (Data , output l dc idc) x
           ≡ just (decOutput l (o2 x) dc idc)
  offer-o1 {x}
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x = refl

  -- o2 offers `sndack` (→ og x)
  offer-o2 : ∀ {x} → vis-of (PTree.force (decOutput l (o2 x) dc idc)) (⊤ , sndack l dc idc) tt
           ≡ just (decOutput l (og x) dc idc)
  offer-o2 {x}
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x
          | ≟-diagF l | ≟-diag dc | ≟-diag idc = refl

  -- og cell force is a `sil` (guard τ → o0)
  force-sil-og : ∀ {x} → PTree.force (decOutput l (og x) dc idc) ≡ sil (decOutput l o0 dc idc)
  force-sil-og {x}
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x
          | ≟-diagF l | ≟-diag dc | ≟-diag idc = refl

  -- o0 fires `rcvmsg`
  dOut-o0-fire : ∀ {x} → decOutput l o0 dc idc
               ─[ ev (evN (rcvmsg l dc idc) x) ]─► decOutput l (o1 x) dc idc
  dOut-o0-fire {x} = sVis refl (offer-o0 {x})

  -- o1 fires `output`
  dOut-o1-fire : ∀ {x} → decOutput l (o1 x) dc idc
               ─[ ev (evN (output l dc idc) x) ]─► decOutput l (o2 x) dc idc
  dOut-o1-fire {x} = sVis (force-react-o1 {x}) (offer-o1 {x})

  -- o2 fires `sndack`
  dOut-o2-fire : ∀ {x} → decOutput l (o2 x) dc idc
               ─[ ev (evN (sndack l dc idc) tt) ]─► decOutput l (og x) dc idc
  dOut-o2-fire {x} = sVis (force-react-o2 {x}) (offer-o2 {x})

  -- og takes the guard τ (→ o0)
  dOut-og-τ : ∀ {x} → decOutput l (og x) dc idc ─[ τ ]─► decOutput l o0 dc idc
  dOut-og-τ {x} = sSil (force-sil-og {x})

  -- Transmitter register: free -sndmsg-> hold -tx-> grd -τ-> free (menu ≟ is Class).
  -- hold register force is a react (offer tx)
  force-react-Tr-h : ∀ {d id x} → PTree.force (decTrans l (hold d id x))
                   ≡ react (vis-of (PTree.force (decTrans l (hold d id x))))
                           (tau-of (PTree.force (decTrans l (hold d id x))))
  force-react-Tr-h {d} {id} {x} rewrite ≟-diag l = refl

  -- free offers `sndmsg` (→ hold)
  offer-Tr-f : ∀ {d id x} → vis-of (PTree.force (decTrans l free)) (Data , sndmsg l d id) x
             ≡ just (decTrans l (hold d id x))
  offer-Tr-f {d} {id} {x} rewrite ≟-diag l = refl

  -- hold offers `tx` (→ grd)
  offer-Tr-h : ∀ {d id x} → vis-of (PTree.force (decTrans l (hold d id x))) (Data , tx l d id) x
             ≡ just (decTrans l (grd d id x))
  offer-Tr-h {d} {id} {x}
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x = refl

  -- grd register force is a `sil` (guard τ → free)
  force-sil-Tr-g : ∀ {d id x} → PTree.force (decTrans l (grd d id x)) ≡ sil (decTrans l free)
  force-sil-Tr-g {d} {id} {x}
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x = refl

  -- free fires `sndmsg`
  dTr-free-fire : ∀ {d id x} → decTrans l free
                ─[ ev (evN (sndmsg l d id) x) ]─► decTrans l (hold d id x)
  dTr-free-fire {d} {id} {x} = sVis refl (offer-Tr-f {d} {id} {x})

  -- hold fires `tx`
  dTr-hold-fire : ∀ {d id x} → decTrans l (hold d id x)
                ─[ ev (evN (tx l d id) x) ]─► decTrans l (grd d id x)
  dTr-hold-fire {d} {id} {x} = sVis (force-react-Tr-h {d} {id} {x}) (offer-Tr-h {d} {id} {x})

  -- grd takes the guard τ (→ free)
  dTr-grd-τ : ∀ {d id x} → decTrans l (grd d id x) ─[ τ ]─► decTrans l free
  dTr-grd-τ {d} {id} {x} = sSil (force-sil-Tr-g {d} {id} {x})

  -- Receiver register: free -tx-> hold -rcvmsg-> grd -τ-> free (menu ≟ is Class).
  -- hold register force is a react (offer rcvmsg)
  force-react-Rc-h : ∀ {d id x} → PTree.force (decRcv l (hold d id x))
                   ≡ react (vis-of (PTree.force (decRcv l (hold d id x))))
                           (tau-of (PTree.force (decRcv l (hold d id x))))
  force-react-Rc-h {d} {id} {x} rewrite ≟-diag l = refl

  -- free offers `tx` (→ hold)
  offer-Rc-f : ∀ {d id x} → vis-of (PTree.force (decRcv l free)) (Data , tx l d id) x
             ≡ just (decRcv l (hold d id x))
  offer-Rc-f {d} {id} {x} rewrite ≟-diag l = refl

  -- hold offers `rcvmsg` (→ grd)
  offer-Rc-h : ∀ {d id x} → vis-of (PTree.force (decRcv l (hold d id x))) (Data , rcvmsg l d id) x
             ≡ just (decRcv l (grd d id x))
  offer-Rc-h {d} {id} {x}
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x = refl

  -- grd register force is a `sil` (guard τ → free)
  force-sil-Rc-g : ∀ {d id x} → PTree.force (decRcv l (grd d id x)) ≡ sil (decRcv l free)
  force-sil-Rc-g {d} {id} {x}
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x = refl

  -- free fires `tx`
  dRc-free-fire : ∀ {d id x} → decRcv l free
                ─[ ev (evN (tx l d id) x) ]─► decRcv l (hold d id x)
  dRc-free-fire {d} {id} {x} = sVis refl (offer-Rc-f {d} {id} {x})

  -- hold fires `rcvmsg`
  dRc-hold-fire : ∀ {d id x} → decRcv l (hold d id x)
                ─[ ev (evN (rcvmsg l d id) x) ]─► decRcv l (grd d id x)
  dRc-hold-fire {d} {id} {x} = sVis (force-react-Rc-h {d} {id} {x}) (offer-Rc-h {d} {id} {x})

  -- grd takes the guard τ (→ free)
  dRc-grd-τ : ∀ {d id x} → decRcv l (grd d id x) ─[ τ ]─► decRcv l free
  dRc-grd-τ {d} {id} {x} = sSil (force-sil-Rc-g {d} {id} {x})

  -- RcvAck register (⊤): free -ack-> hold -rcvack-> grd -τ-> free (menu ≟ is Class).
  -- hold register force is a react (offer rcvack)
  force-react-RA-h : ∀ {d id} → PTree.force (decRAck l (hold d id))
                   ≡ react (vis-of (PTree.force (decRAck l (hold d id))))
                           (tau-of (PTree.force (decRAck l (hold d id))))
  force-react-RA-h {d} {id} rewrite ≟-diag l = refl

  -- free offers `ack` (→ hold)
  offer-RA-f : ∀ {d id} → vis-of (PTree.force (decRAck l free)) (⊤ , ack l d id) tt
             ≡ just (decRAck l (hold d id))
  offer-RA-f {d} {id} rewrite ≟-diag l = refl

  -- hold offers `rcvack` (→ grd)
  offer-RA-h : ∀ {d id} → vis-of (PTree.force (decRAck l (hold d id))) (⊤ , rcvack l d id) tt
             ≡ just (decRAck l (grd d id))
  offer-RA-h {d} {id}
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id = refl

  -- grd register force is a `sil` (guard τ → free)
  force-sil-RA-g : ∀ {d id} → PTree.force (decRAck l (grd d id)) ≡ sil (decRAck l free)
  force-sil-RA-g {d} {id}
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id = refl

  -- free fires `ack`
  dRA-free-fire : ∀ {d id} → decRAck l free
                ─[ ev (evN (ack l d id) tt) ]─► decRAck l (hold d id)
  dRA-free-fire {d} {id} = sVis refl (offer-RA-f {d} {id})

  -- hold fires `rcvack`
  dRA-hold-fire : ∀ {d id} → decRAck l (hold d id)
                ─[ ev (evN (rcvack l d id) tt) ]─► decRAck l (grd d id)
  dRA-hold-fire {d} {id} = sVis (force-react-RA-h {d} {id}) (offer-RA-h {d} {id})

  -- grd takes the guard τ (→ free)
  dRA-grd-τ : ∀ {d id} → decRAck l (grd d id) ─[ τ ]─► decRAck l free
  dRA-grd-τ {d} {id} = sSil (force-sil-RA-g {d} {id})

  -- SndAck register (⊤): free -sndack-> hold -ack-> grd -τ-> free (menu ≟ is Class).
  -- hold register force is a react (offer ack)
  force-react-Sn-h : ∀ {d id} → PTree.force (decSnd l (hold d id))
                   ≡ react (vis-of (PTree.force (decSnd l (hold d id))))
                           (tau-of (PTree.force (decSnd l (hold d id))))
  force-react-Sn-h {d} {id} rewrite ≟-diag l = refl

  -- free offers `sndack` (→ hold)
  offer-Sn-f : ∀ {d id} → vis-of (PTree.force (decSnd l free)) (⊤ , sndack l d id) tt
             ≡ just (decSnd l (hold d id))
  offer-Sn-f {d} {id} rewrite ≟-diag l = refl

  -- hold offers `ack` (→ grd)
  offer-Sn-h : ∀ {d id} → vis-of (PTree.force (decSnd l (hold d id))) (⊤ , ack l d id) tt
             ≡ just (decSnd l (grd d id))
  offer-Sn-h {d} {id}
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id = refl

  -- grd register force is a `sil` (guard τ → free)
  force-sil-Sn-g : ∀ {d id} → PTree.force (decSnd l (grd d id)) ≡ sil (decSnd l free)
  force-sil-Sn-g {d} {id}
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id = refl

  -- free fires `sndack`
  dSn-free-fire : ∀ {d id} → decSnd l free
                ─[ ev (evN (sndack l d id) tt) ]─► decSnd l (hold d id)
  dSn-free-fire {d} {id} = sVis refl (offer-Sn-f {d} {id})

  -- hold fires `ack`
  dSn-hold-fire : ∀ {d id} → decSnd l (hold d id)
                ─[ ev (evN (ack l d id) tt) ]─► decSnd l (grd d id)
  dSn-hold-fire {d} {id} = sVis (force-react-Sn-h {d} {id}) (offer-Sn-h {d} {id})

  -- grd takes the guard τ (→ free)
  dSn-grd-τ : ∀ {d id} → decSnd l (grd d id) ─[ τ ]─► decSnd l free
  dSn-grd-τ {d} {id} = sSil (force-sil-Sn-g {d} {id})

  ------------------------------------------------------------------------
  -- Per-leaf visible-offer REFUTATIONS for the channels a leaf never
  -- offers (channel mismatch is definitional once the succV-chain is
  -- unblocked; guard phases force to `sil`, refuted on the react eqf).
  ------------------------------------------------------------------------
  -- decInput offers no `output` at any phase
  decInput-no-output : ∀ {ip dr id₀ x₀ W} → decInput l ip dc idc ─[ ev (evN (output l dr id₀) x₀) ]─► W → ⊥
  decInput-no-output {i0} (sVis refl ())
  decInput-no-output {(i1 x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decInput-no-output {(i2 x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decInput-no-output {(ig x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- decInput offers no `tx` at any phase
  decInput-no-tx : ∀ {ip dr id₀ x₀ W} → decInput l ip dc idc ─[ ev (evN (tx l dr id₀) x₀) ]─► W → ⊥
  decInput-no-tx {i0} (sVis refl ())
  decInput-no-tx {(i1 x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decInput-no-tx {(i2 x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decInput-no-tx {(ig x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- decInput offers no `ack` at any phase
  decInput-no-ack : ∀ {ip dr id₀ W} → decInput l ip dc idc ─[ ev (evN (ack l dr id₀) tt) ]─► W → ⊥
  decInput-no-ack {i0} (sVis refl ())
  decInput-no-ack {(i1 x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decInput-no-ack {(i2 x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decInput-no-ack {(ig x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- decOutput offers no `input` at any phase
  decOutput-no-input : ∀ {op dr id₀ x₀ W} → decOutput l op dc idc ─[ ev (evN (input l dr id₀) x₀) ]─► W → ⊥
  decOutput-no-input {o0} (sVis refl ())
  decOutput-no-input {(o1 x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decOutput-no-input {(o2 x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decOutput-no-input {(og x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- decOutput offers no `tx` at any phase
  decOutput-no-tx : ∀ {op dr id₀ x₀ W} → decOutput l op dc idc ─[ ev (evN (tx l dr id₀) x₀) ]─► W → ⊥
  decOutput-no-tx {o0} (sVis refl ())
  decOutput-no-tx {(o1 x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decOutput-no-tx {(o2 x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decOutput-no-tx {(og x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- decOutput offers no `ack` at any phase
  decOutput-no-ack : ∀ {op dr id₀ W} → decOutput l op dc idc ─[ ev (evN (ack l dr id₀) tt) ]─► W → ⊥
  decOutput-no-ack {o0} (sVis refl ())
  decOutput-no-ack {(o1 x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decOutput-no-ack {(o2 x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decOutput-no-ack {(og x)} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- decTrans offers no `input` at any phase
  decTrans-no-input : ∀ {tb dr id₀ x₀ W} → decTrans l tb ─[ ev (evN (input l dr id₀) x₀) ]─► W → ⊥
  decTrans-no-input {free} (sVis refl ())
  decTrans-no-input {(hold d id x)} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decTrans-no-input {(grd d id x)} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- decTrans offers no `output` at any phase
  decTrans-no-output : ∀ {tb dr id₀ x₀ W} → decTrans l tb ─[ ev (evN (output l dr id₀) x₀) ]─► W → ⊥
  decTrans-no-output {free} (sVis refl ())
  decTrans-no-output {(hold d id x)} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decTrans-no-output {(grd d id x)} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- decTrans offers no `ack` at any phase
  decTrans-no-ack : ∀ {tb dr id₀ W} → decTrans l tb ─[ ev (evN (ack l dr id₀) tt) ]─► W → ⊥
  decTrans-no-ack {free} (sVis refl ())
  decTrans-no-ack {(hold d id x)} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decTrans-no-ack {(grd d id x)} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- decTrans offers no `rcvack` at any phase
  decTrans-no-rcvack : ∀ {tb dr id₀ W} → decTrans l tb ─[ ev (evN (rcvack l dr id₀) tt) ]─► W → ⊥
  decTrans-no-rcvack {free} (sVis refl ())
  decTrans-no-rcvack {(hold d id x)} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decTrans-no-rcvack {(grd d id x)} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- decRAck offers no `input` at any phase
  decRAck-no-input : ∀ {ab dr id₀ x₀ W} → decRAck l ab ─[ ev (evN (input l dr id₀) x₀) ]─► W → ⊥
  decRAck-no-input {free} (sVis refl ())
  decRAck-no-input {(hold d id)} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRAck-no-input {(grd d id)} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _

  -- decRAck offers no `output` at any phase
  decRAck-no-output : ∀ {ab dr id₀ x₀ W} → decRAck l ab ─[ ev (evN (output l dr id₀) x₀) ]─► W → ⊥
  decRAck-no-output {free} (sVis refl ())
  decRAck-no-output {(hold d id)} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRAck-no-output {(grd d id)} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _

  -- decRAck offers no `sndmsg` at any phase
  decRAck-no-sndmsg : ∀ {ab dr id₀ x₀ W} → decRAck l ab ─[ ev (evN (sndmsg l dr id₀) x₀) ]─► W → ⊥
  decRAck-no-sndmsg {free} (sVis refl ())
  decRAck-no-sndmsg {(hold d id)} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRAck-no-sndmsg {(grd d id)} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _

  -- decRAck offers no `tx` at any phase
  decRAck-no-tx : ∀ {ab dr id₀ x₀ W} → decRAck l ab ─[ ev (evN (tx l dr id₀) x₀) ]─► W → ⊥
  decRAck-no-tx {free} (sVis refl ())
  decRAck-no-tx {(hold d id)} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRAck-no-tx {(grd d id)} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _

  -- decRcv offers no `input` at any phase
  decRcv-no-input : ∀ {rb dr id₀ x₀ W} → decRcv l rb ─[ ev (evN (input l dr id₀) x₀) ]─► W → ⊥
  decRcv-no-input {free} (sVis refl ())
  decRcv-no-input {(hold d id x)} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRcv-no-input {(grd d id x)} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- decRcv offers no `output` at any phase
  decRcv-no-output : ∀ {rb dr id₀ x₀ W} → decRcv l rb ─[ ev (evN (output l dr id₀) x₀) ]─► W → ⊥
  decRcv-no-output {free} (sVis refl ())
  decRcv-no-output {(hold d id x)} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRcv-no-output {(grd d id x)} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- decRcv offers no `sndack` at any phase
  decRcv-no-sndack : ∀ {rb dr id₀ W} → decRcv l rb ─[ ev (evN (sndack l dr id₀) tt) ]─► W → ⊥
  decRcv-no-sndack {free} (sVis refl ())
  decRcv-no-sndack {(hold d id x)} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRcv-no-sndack {(grd d id x)} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- decRcv offers no `ack` at any phase
  decRcv-no-ack : ∀ {rb dr id₀ W} → decRcv l rb ─[ ev (evN (ack l dr id₀) tt) ]─► W → ⊥
  decRcv-no-ack {free} (sVis refl ())
  decRcv-no-ack {(hold d id x)} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRcv-no-ack {(grd d id x)} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- decSnd offers no `input` at any phase
  decSnd-no-input : ∀ {sb dr id₀ x₀ W} → decSnd l sb ─[ ev (evN (input l dr id₀) x₀) ]─► W → ⊥
  decSnd-no-input {free} (sVis refl ())
  decSnd-no-input {(hold d id)} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decSnd-no-input {(grd d id)} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _

  -- decSnd offers no `output` at any phase
  decSnd-no-output : ∀ {sb dr id₀ x₀ W} → decSnd l sb ─[ ev (evN (output l dr id₀) x₀) ]─► W → ⊥
  decSnd-no-output {free} (sVis refl ())
  decSnd-no-output {(hold d id)} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decSnd-no-output {(grd d id)} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _

  -- decSnd offers no `tx` at any phase
  decSnd-no-tx : ∀ {sb dr id₀ x₀ W} → decSnd l sb ─[ ev (evN (tx l dr id₀) x₀) ]─► W → ⊥
  decSnd-no-tx {free} (sVis refl ())
  decSnd-no-tx {(hold d id)} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decSnd-no-tx {(grd d id)} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _

  -- decSnd offers no `rcvmsg` at any phase
  decSnd-no-rcvmsg : ∀ {sb dr id₀ x₀ W} → decSnd l sb ─[ ev (evN (rcvmsg l dr id₀) x₀) ]─► W → ⊥
  decSnd-no-rcvmsg {free} (sVis refl ())
  decSnd-no-rcvmsg {(hold d id)} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decSnd-no-rcvmsg {(grd d id)} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _
  ------------------------------------------------------------------------
  -- REFLECTION infrastructure — Part 1: per-leaf τ inversions.
  --
  -- Each cell/register admits a τ ONLY at its guard phase (ig/og/grd),
  -- landing back at the home phase; the react phases (i0/i1/i2, o0/o1/o2,
  -- free/hold registers) are all stable.  The loop heads reuse the
  -- (l)-only stability facts; the deeper react phases need the succV-chain
  -- unblocked by the same per-level diag block used by the fires.
  ------------------------------------------------------------------------

  -- Input cell i0 (loop head) is stable
  decInput-i0-noτ : ∀ {W} → decInput l i0 dc idc ─[ τ ]─► W → ⊥
  decInput-i0-noτ (sSil ())
  decInput-i0-noτ (sTau {i = _ , fin}                 refl ())
  decInput-i0-noτ (sTau {i = _ , base _}              refl ())
  decInput-i0-noτ (sTau {i = _ , pair fin (base _)}   refl ())
  decInput-i0-noτ (sTau {i = _ , pair fin fin}        refl ())
  decInput-i0-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
  decInput-i0-noτ (sTau {i = _ , pair (base _) _}     refl ())
  decInput-i0-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

  -- Input cell i1 is stable (react offering sndmsg; ∅t τ-branch)
  decInput-i1-noτ : ∀ {x W} → decInput l (i1 x) dc idc ─[ τ ]─► W → ⊥
  decInput-i1-noτ {x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sSil ()
  ... | sTau {i = _ , fin}                 refl ()
  ... | sTau {i = _ , base _}              refl ()
  ... | sTau {i = _ , pair fin (base _)}   refl ()
  ... | sTau {i = _ , pair fin fin}        refl ()
  ... | sTau {i = _ , pair fin (pair _ _)} refl ()
  ... | sTau {i = _ , pair (base _) _}     refl ()
  ... | sTau {i = _ , pair (pair _ _) _}   refl ()

  -- Input cell i2 is stable (react offering rcvack; ∅t τ-branch)
  decInput-i2-noτ : ∀ {x W} → decInput l (i2 x) dc idc ─[ τ ]─► W → ⊥
  decInput-i2-noτ {x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sSil ()
  ... | sTau {i = _ , fin}                 refl ()
  ... | sTau {i = _ , base _}              refl ()
  ... | sTau {i = _ , pair fin (base _)}   refl ()
  ... | sTau {i = _ , pair fin fin}        refl ()
  ... | sTau {i = _ , pair fin (pair _ _)} refl ()
  ... | sTau {i = _ , pair (base _) _}     refl ()
  ... | sTau {i = _ , pair (pair _ _) _}   refl ()

  -- Output cell o0 (loop head) is stable
  decOutput-o0-noτ : ∀ {W} → decOutput l o0 dc idc ─[ τ ]─► W → ⊥
  decOutput-o0-noτ (sSil ())
  decOutput-o0-noτ (sTau {i = _ , fin}                 refl ())
  decOutput-o0-noτ (sTau {i = _ , base _}              refl ())
  decOutput-o0-noτ (sTau {i = _ , pair fin (base _)}   refl ())
  decOutput-o0-noτ (sTau {i = _ , pair fin fin}        refl ())
  decOutput-o0-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
  decOutput-o0-noτ (sTau {i = _ , pair (base _) _}     refl ())
  decOutput-o0-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

  -- Output cell o1 is stable (react offering output; ∅t τ-branch)
  decOutput-o1-noτ : ∀ {x W} → decOutput l (o1 x) dc idc ─[ τ ]─► W → ⊥
  decOutput-o1-noτ {x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sSil ()
  ... | sTau {i = _ , fin}                 refl ()
  ... | sTau {i = _ , base _}              refl ()
  ... | sTau {i = _ , pair fin (base _)}   refl ()
  ... | sTau {i = _ , pair fin fin}        refl ()
  ... | sTau {i = _ , pair fin (pair _ _)} refl ()
  ... | sTau {i = _ , pair (base _) _}     refl ()
  ... | sTau {i = _ , pair (pair _ _) _}   refl ()

  -- Output cell o2 is stable (react offering sndack; ∅t τ-branch)
  decOutput-o2-noτ : ∀ {x W} → decOutput l (o2 x) dc idc ─[ τ ]─► W → ⊥
  decOutput-o2-noτ {x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sSil ()
  ... | sTau {i = _ , fin}                 refl ()
  ... | sTau {i = _ , base _}              refl ()
  ... | sTau {i = _ , pair fin (base _)}   refl ()
  ... | sTau {i = _ , pair fin fin}        refl ()
  ... | sTau {i = _ , pair fin (pair _ _)} refl ()
  ... | sTau {i = _ , pair (base _) _}     refl ()
  ... | sTau {i = _ , pair (pair _ _) _}   refl ()

  -- Transmitter hold is stable (react offering tx; ∅t τ-branch)
  decTrans-hold-noτ : ∀ {d id x W} → decTrans l (hold d id x) ─[ τ ]─► W → ⊥
  decTrans-hold-noτ {d} {id} {x} step rewrite ≟-diag l with step
  ... | sSil ()
  ... | sTau {i = _ , fin}                 refl ()
  ... | sTau {i = _ , base _}              refl ()
  ... | sTau {i = _ , pair fin (base _)}   refl ()
  ... | sTau {i = _ , pair fin fin}        refl ()
  ... | sTau {i = _ , pair fin (pair _ _)} refl ()
  ... | sTau {i = _ , pair (base _) _}     refl ()
  ... | sTau {i = _ , pair (pair _ _) _}   refl ()

  -- Receiver hold is stable (react offering rcvmsg; ∅t τ-branch)
  decRcv-hold-noτ : ∀ {d id x W} → decRcv l (hold d id x) ─[ τ ]─► W → ⊥
  decRcv-hold-noτ {d} {id} {x} step rewrite ≟-diag l with step
  ... | sSil ()
  ... | sTau {i = _ , fin}                 refl ()
  ... | sTau {i = _ , base _}              refl ()
  ... | sTau {i = _ , pair fin (base _)}   refl ()
  ... | sTau {i = _ , pair fin fin}        refl ()
  ... | sTau {i = _ , pair fin (pair _ _)} refl ()
  ... | sTau {i = _ , pair (base _) _}     refl ()
  ... | sTau {i = _ , pair (pair _ _) _}   refl ()

  -- SndAck hold is stable (react offering ack; ∅t τ-branch)
  decSnd-hold-noτ : ∀ {d id W} → decSnd l (hold d id) ─[ τ ]─► W → ⊥
  decSnd-hold-noτ {d} {id} step rewrite ≟-diag l with step
  ... | sSil ()
  ... | sTau {i = _ , fin}                 refl ()
  ... | sTau {i = _ , base _}              refl ()
  ... | sTau {i = _ , pair fin (base _)}   refl ()
  ... | sTau {i = _ , pair fin fin}        refl ()
  ... | sTau {i = _ , pair fin (pair _ _)} refl ()
  ... | sTau {i = _ , pair (base _) _}     refl ()
  ... | sTau {i = _ , pair (pair _ _) _}   refl ()

  -- RcvAck hold is stable (react offering rcvack; ∅t τ-branch)
  decRAck-hold-noτ : ∀ {d id W} → decRAck l (hold d id) ─[ τ ]─► W → ⊥
  decRAck-hold-noτ {d} {id} step rewrite ≟-diag l with step
  ... | sSil ()
  ... | sTau {i = _ , fin}                 refl ()
  ... | sTau {i = _ , base _}              refl ()
  ... | sTau {i = _ , pair fin (base _)}   refl ()
  ... | sTau {i = _ , pair fin fin}        refl ()
  ... | sTau {i = _ , pair fin (pair _ _)} refl ()
  ... | sTau {i = _ , pair (base _) _}     refl ()
  ... | sTau {i = _ , pair (pair _ _) _}   refl ()

  -- Guard-τ inversions: the guard phase's only step is the sil τ to home.
  -- Input ig → i0
  decInput-ig-τ-inv : ∀ {x W} → decInput l (ig x) dc idc ─[ τ ]─► W → W ≡ decInput l i0 dc idc
  decInput-ig-τ-inv {x} step = sil-τ-inv (force-sil-ig {x}) step

  -- Output og → o0
  decOutput-og-τ-inv : ∀ {x W} → decOutput l (og x) dc idc ─[ τ ]─► W → W ≡ decOutput l o0 dc idc
  decOutput-og-τ-inv {x} step = sil-τ-inv (force-sil-og {x}) step

  -- Transmitter grd → free
  decTrans-grd-τ-inv : ∀ {d id x W} → decTrans l (grd d id x) ─[ τ ]─► W → W ≡ decTrans l free
  decTrans-grd-τ-inv {d} {id} {x} step = sil-τ-inv (force-sil-Tr-g {d} {id} {x}) step

  -- Receiver grd → free
  decRcv-grd-τ-inv : ∀ {d id x W} → decRcv l (grd d id x) ─[ τ ]─► W → W ≡ decRcv l free
  decRcv-grd-τ-inv {d} {id} {x} step = sil-τ-inv (force-sil-Rc-g {d} {id} {x}) step

  -- SndAck grd → free
  decSnd-grd-τ-inv : ∀ {d id W} → decSnd l (grd d id) ─[ τ ]─► W → W ≡ decSnd l free
  decSnd-grd-τ-inv {d} {id} step = sil-τ-inv (force-sil-Sn-g {d} {id}) step

  -- RcvAck grd → free
  decRAck-grd-τ-inv : ∀ {d id W} → decRAck l (grd d id) ─[ τ ]─► W → W ≡ decRAck l free
  decRAck-grd-τ-inv {d} {id} step = sil-τ-inv (force-sil-RA-g {d} {id}) step

  -- Per-leaf τ CLASSIFIERS: a τ pins the guard phase and the home target.
  -- Input: only ig admits a τ (→ i0)
  decInput-τ-class : ∀ {ip W} → decInput l ip dc idc ─[ τ ]─► W
                   → (Σ[ x ∈ Data ] (ip ≡ ig x)) × (W ≡ decInput l i0 dc idc)
  decInput-τ-class {i0}   step = ⊥-elim (decInput-i0-noτ step)
  decInput-τ-class {i1 x} step = ⊥-elim (decInput-i1-noτ {x} step)
  decInput-τ-class {i2 x} step = ⊥-elim (decInput-i2-noτ {x} step)
  decInput-τ-class {ig x} step = (x , refl) , decInput-ig-τ-inv {x} step

  -- Output: only og admits a τ (→ o0)
  decOutput-τ-class : ∀ {op W} → decOutput l op dc idc ─[ τ ]─► W
                    → (Σ[ x ∈ Data ] (op ≡ og x)) × (W ≡ decOutput l o0 dc idc)
  decOutput-τ-class {o0}   step = ⊥-elim (decOutput-o0-noτ step)
  decOutput-τ-class {o1 x} step = ⊥-elim (decOutput-o1-noτ {x} step)
  decOutput-τ-class {o2 x} step = ⊥-elim (decOutput-o2-noτ {x} step)
  decOutput-τ-class {og x} step = (x , refl) , decOutput-og-τ-inv {x} step

  -- Transmitter: only grd admits a τ (→ free)
  decTrans-τ-class : ∀ {tb W} → decTrans l tb ─[ τ ]─► W
                   → (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] Σ[ x ∈ Data ] (tb ≡ grd d id x)) × (W ≡ decTrans l free)
  decTrans-τ-class {free}       step = ⊥-elim (Transmitterₗ-stable l step)
  decTrans-τ-class {hold d id x} step = ⊥-elim (decTrans-hold-noτ {d} {id} {x} step)
  decTrans-τ-class {grd d id x}  step = (d , id , x , refl) , decTrans-grd-τ-inv {d} {id} {x} step

  -- Receiver: only grd admits a τ (→ free)
  decRcv-τ-class : ∀ {rb W} → decRcv l rb ─[ τ ]─► W
                 → (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] Σ[ x ∈ Data ] (rb ≡ grd d id x)) × (W ≡ decRcv l free)
  decRcv-τ-class {free}       step = ⊥-elim (Receiverₗ-stable l step)
  decRcv-τ-class {hold d id x} step = ⊥-elim (decRcv-hold-noτ {d} {id} {x} step)
  decRcv-τ-class {grd d id x}  step = (d , id , x , refl) , decRcv-grd-τ-inv {d} {id} {x} step

  -- SndAck: only grd admits a τ (→ free)
  decSnd-τ-class : ∀ {sb W} → decSnd l sb ─[ τ ]─► W
                 → (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] (sb ≡ grd d id)) × (W ≡ decSnd l free)
  decSnd-τ-class {free}     step = ⊥-elim (SndAckₗ-stable l step)
  decSnd-τ-class {hold d id} step = ⊥-elim (decSnd-hold-noτ {d} {id} step)
  decSnd-τ-class {grd d id}  step = (d , id , refl) , decSnd-grd-τ-inv {d} {id} step

  -- RcvAck: only grd admits a τ (→ free)
  decRAck-τ-class : ∀ {ab W} → decRAck l ab ─[ τ ]─► W
                  → (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] (ab ≡ grd d id)) × (W ≡ decRAck l free)
  decRAck-τ-class {free}     step = ⊥-elim (RcvAckₗ-stable l step)
  decRAck-τ-class {hold d id} step = ⊥-elim (decRAck-hold-noτ {d} {id} step)
  decRAck-τ-class {grd d id}  step = (d , id , refl) , decRAck-grd-τ-inv {d} {id} step

  ------------------------------------------------------------------------
  -- REFLECTION infrastructure — Part 2: per-leaf event classifiers.
  --
  -- Each leaf offers exactly one event per phase; the classifiers invert a
  -- visible step to the phase + target.  Three proof shapes recur:
  --   · loop-head "receiver" leaves (free / cell i0,o0) accept the event
  --     binding its (dir,id[,payload]) — inverted via the matching `offer-*`
  --     lemma (receivers) or a nested channel-pin `with` (cells);
  --   · "emitter" phases (register hold, cell i1/i2/o1/o2) pin the event to
  --     the phase's own (dir,id[,payload]) — inverted by `Net-≟` (+ payload
  --     `≟`) then `sym (just-injective …)` with the target reduced by diag.
  ------------------------------------------------------------------------

  -- Transmitter free accepts sndmsg (binds dr id a → hold)
  decTrans-sndmsg-class : ∀ {tb dr id a W} → decTrans l tb ─[ ev (evN (sndmsg l dr id) a) ]─► W
                        → (tb ≡ free) × (W ≡ decTrans l (hold dr id a))
  decTrans-sndmsg-class {free} {dr} {id} {a} (sVis refl h) =
    refl , just-injective (trans (sym h) (offer-Tr-f {dr} {id} {a}))
  decTrans-sndmsg-class {hold d i x} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decTrans-sndmsg-class {grd d i x} step
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag i | ≟-diag x with step
  ... | sVis () _

  -- Transmitter hold emits tx (pins the phase's dr id a → grd)
  decTrans-tx-class : ∀ {tb dr id a W} → decTrans l tb ─[ ev (evN (tx l dr id) a) ]─► W
                    → (tb ≡ hold dr id a) × (W ≡ decTrans l (grd dr id a))
  decTrans-tx-class {free} (sVis refl ())
  decTrans-tx-class {hold d i x} {dr} {id} {a} step rewrite ≟-diag l with step
  ... | sVis refl h with Net-≟ {Data} (Data , tx l d i) (Data , tx l dr id) | h
  ...   | no _     | ()
  ...   | yes refl | h′ with a ≟ x | h′
  ...     | no _     | ()
  ...     | yes refl | h″ rewrite ≟-diagF l | ≟-diag d | ≟-diag i | ≟-diag x =
              refl , sym (just-injective h″)
  decTrans-tx-class {grd d i x} step
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag i | ≟-diag x with step
  ... | sVis () _

  -- Input i0 accepts input (pins dc idc; binds payload a → i1)
  decInput-input-class : ∀ {ip dr id a W} → decInput l ip dc idc ─[ ev (evN (input l dr id) a) ]─► W
                       → (ip ≡ i0) × (dr ≡ dc) × (id ≡ idc) × (W ≡ decInput l (i1 a) dc idc)
  decInput-input-class {i0} {dr} {id} {a} (sVis refl h)
    rewrite ≟-diagF l with dr ≟ dc | h
  ... | no _     | ()
  ... | yes refl | h′ with id ≟ idc | h′
  ...   | no _     | ()
  ...   | yes refl | h″ rewrite ≟-diag dr | ≟-diag id =
            refl , refl , refl , sym (just-injective h″)
  decInput-input-class {i1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decInput-input-class {i2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decInput-input-class {ig x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- Receiver free accepts tx (binds dr id a → hold)
  decRcv-tx-class : ∀ {rb dr id a W} → decRcv l rb ─[ ev (evN (tx l dr id) a) ]─► W
                  → (rb ≡ free) × (W ≡ decRcv l (hold dr id a))
  decRcv-tx-class {free} {dr} {id} {a} (sVis refl h) =
    refl , just-injective (trans (sym h) (offer-Rc-f {dr} {id} {a}))
  decRcv-tx-class {hold d i x} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRcv-tx-class {grd d i x} step
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag i | ≟-diag x with step
  ... | sVis () _

  -- SndAck free accepts sndack (binds dr id → hold; ⊤ payload)
  decSnd-sndack-class : ∀ {sb dr id W} → decSnd l sb ─[ ev (evN (sndack l dr id) tt) ]─► W
                      → (sb ≡ free) × (W ≡ decSnd l (hold dr id))
  decSnd-sndack-class {free} {dr} {id} (sVis refl h) =
    refl , just-injective (trans (sym h) (offer-Sn-f {dr} {id}))
  decSnd-sndack-class {hold d i} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decSnd-sndack-class {grd d i} step
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag i with step
  ... | sVis () _

  -- RcvAck free accepts ack (binds dr id → hold; ⊤ payload)
  decRAck-ack-class : ∀ {ab dr id W} → decRAck l ab ─[ ev (evN (ack l dr id) tt) ]─► W
                    → (ab ≡ free) × (W ≡ decRAck l (hold dr id))
  decRAck-ack-class {free} {dr} {id} (sVis refl h) =
    refl , just-injective (trans (sym h) (offer-RA-f {dr} {id}))
  decRAck-ack-class {hold d i} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRAck-ack-class {grd d i} step
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag i with step
  ... | sVis () _

  -- Receiver hold emits rcvmsg (pins the phase's dr id a → grd)
  decRcv-rcvmsg-class : ∀ {rb dr id a W} → decRcv l rb ─[ ev (evN (rcvmsg l dr id) a) ]─► W
                      → (rb ≡ hold dr id a) × (W ≡ decRcv l (grd dr id a))
  decRcv-rcvmsg-class {free} (sVis refl ())
  decRcv-rcvmsg-class {hold d i x} {dr} {id} {a} step rewrite ≟-diag l with step
  ... | sVis refl h with Net-≟ {Data} (Data , rcvmsg l d i) (Data , rcvmsg l dr id) | h
  ...   | no _     | ()
  ...   | yes refl | h′ with a ≟ x | h′
  ...     | no _     | ()
  ...     | yes refl | h″ rewrite ≟-diagF l | ≟-diag d | ≟-diag i | ≟-diag x =
              refl , sym (just-injective h″)
  decRcv-rcvmsg-class {grd d i x} step
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag i | ≟-diag x with step
  ... | sVis () _

  -- SndAck hold emits ack (pins the phase's dr id → grd; ⊤ payload)
  decSnd-ack-class : ∀ {sb dr id W} → decSnd l sb ─[ ev (evN (ack l dr id) tt) ]─► W
                   → (sb ≡ hold dr id) × (W ≡ decSnd l (grd dr id))
  decSnd-ack-class {free} (sVis refl ())
  decSnd-ack-class {hold d i} {dr} {id} step rewrite ≟-diag l with step
  ... | sVis refl h with Net-≟ {Data} (⊤ , ack l d i) (⊤ , ack l dr id) | h
  ...   | no _     | ()
  ...   | yes refl | h″ rewrite ≟-diagF l | ≟-diag d | ≟-diag i =
            refl , sym (just-injective h″)
  decSnd-ack-class {grd d i} step
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag i with step
  ... | sVis () _

  -- RcvAck hold emits rcvack (pins the phase's dr id → grd; ⊤ payload)
  decRAck-rcvack-class : ∀ {ab dr id W} → decRAck l ab ─[ ev (evN (rcvack l dr id) tt) ]─► W
                       → (ab ≡ hold dr id) × (W ≡ decRAck l (grd dr id))
  decRAck-rcvack-class {free} (sVis refl ())
  decRAck-rcvack-class {hold d i} {dr} {id} step rewrite ≟-diag l with step
  ... | sVis refl h with Net-≟ {Data} (⊤ , rcvack l d i) (⊤ , rcvack l dr id) | h
  ...   | no _     | ()
  ...   | yes refl | h″ rewrite ≟-diagF l | ≟-diag d | ≟-diag i =
            refl , sym (just-injective h″)
  decRAck-rcvack-class {grd d i} step
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag i with step
  ... | sVis () _

  -- Output o0 accepts rcvmsg (pins dc idc; binds payload a → o1)
  decOutput-rcvmsg-class : ∀ {op dr id a W} → decOutput l op dc idc ─[ ev (evN (rcvmsg l dr id) a) ]─► W
                         → (op ≡ o0) × (dr ≡ dc) × (id ≡ idc) × (W ≡ decOutput l (o1 a) dc idc)
  decOutput-rcvmsg-class {o0} {dr} {id} {a} (sVis refl h)
    rewrite ≟-diagF l with dr ≟ dc | h
  ... | no _     | ()
  ... | yes refl | h′ with id ≟ idc | h′
  ...   | no _     | ()
  ...   | yes refl | h″ rewrite ≟-diag dr | ≟-diag id =
            refl , refl , refl , sym (just-injective h″)
  decOutput-rcvmsg-class {o1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decOutput-rcvmsg-class {o2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decOutput-rcvmsg-class {og x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- Input i1 emits sndmsg (pins dc idc + payload a → i2)
  decInput-sndmsg-class : ∀ {ip dr id a W} → decInput l ip dc idc ─[ ev (evN (sndmsg l dr id) a) ]─► W
                        → (ip ≡ i1 a) × (dr ≡ dc) × (id ≡ idc) × (W ≡ decInput l (i2 a) dc idc)
  decInput-sndmsg-class {i0} (sVis refl ())
  decInput-sndmsg-class {i1 x} {dr} {id} {a} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl h with Net-≟ {Data} (Data , sndmsg l dc idc) (Data , sndmsg l dr id) | h
  ...   | no _     | ()
  ...   | yes refl | h′ with a ≟ x | h′
  ...     | no _     | ()
  ...     | yes refl | h″ rewrite ≟-diagF l | ≟-diag dr | ≟-diag id | ≟-diag x =
              refl , refl , refl , sym (just-injective h″)
  decInput-sndmsg-class {i2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decInput-sndmsg-class {ig x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- rcvack on i2 pins the instance to (dc,idc) (the `Net-≟` rename kept
  -- separate from the target so the deep `ig` target stays reducible).
  decInput-rcvack-pins : ∀ {x dr id W} → decInput l (i2 x) dc idc ─[ ev (evN (rcvack l dr id) tt) ]─► W
                       → (dr ≡ dc) × (id ≡ idc)
  decInput-rcvack-pins {x} {dr} {id} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl h with Net-≟ {Data} (⊤ , rcvack l dc idc) (⊤ , rcvack l dr id) | h
  ...   | no _     | ()
  ...   | yes refl | _ = refl , refl

  -- with the instance pinned to (dc,idc), the rcvack target is `ig` (via offer-i2);
  -- `subst`-through-`eqf` bridges the step's node to `offer-i2`'s stuck `vis-of`.
  decInput-rcvack-tgt : ∀ {x W} → decInput l (i2 x) dc idc ─[ ev (evN (rcvack l dc idc) tt) ]─► W
                      → W ≡ decInput l (ig x) dc idc
  decInput-rcvack-tgt {x} (sVis {v = v} eqf h) =
    just-injective (trans (sym h)
      (subst (λ n → vis-of n (⊤ , rcvack l dc idc) tt ≡ just (decInput l (ig x) dc idc))
             eqf (offer-i2 {x})))

  -- Input i2 emits rcvack (pins dc idc; ⊤ payload → ig, phase payload x)
  decInput-rcvack-class : ∀ {ip dr id W} → decInput l ip dc idc ─[ ev (evN (rcvack l dr id) tt) ]─► W
                        → Σ[ x ∈ Data ] ((ip ≡ i2 x) × (dr ≡ dc) × (id ≡ idc) × (W ≡ decInput l (ig x) dc idc))
  decInput-rcvack-class {i0} (sVis refl ())
  decInput-rcvack-class {i1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decInput-rcvack-class {i2 x} step with decInput-rcvack-pins {x} step
  ... | refl , refl = x , refl , refl , refl , decInput-rcvack-tgt {x} step
  decInput-rcvack-class {ig x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- Output o1 emits output (pins dc idc + payload a → o2)
  decOutput-output-class : ∀ {op dr id a W} → decOutput l op dc idc ─[ ev (evN (output l dr id) a) ]─► W
                         → (op ≡ o1 a) × (dr ≡ dc) × (id ≡ idc) × (W ≡ decOutput l (o2 a) dc idc)
  decOutput-output-class {o0} (sVis refl ())
  decOutput-output-class {o1 x} {dr} {id} {a} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl h with Net-≟ {Data} (Data , output l dc idc) (Data , output l dr id) | h
  ...   | no _     | ()
  ...   | yes refl | h′ with a ≟ x | h′
  ...     | no _     | ()
  ...     | yes refl | h″ rewrite ≟-diagF l | ≟-diag dr | ≟-diag id | ≟-diag x =
              refl , refl , refl , sym (just-injective h″)
  decOutput-output-class {o2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decOutput-output-class {og x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- sndack on o2 pins the instance to (dc,idc)
  decOutput-sndack-pins : ∀ {x dr id W} → decOutput l (o2 x) dc idc ─[ ev (evN (sndack l dr id) tt) ]─► W
                        → (dr ≡ dc) × (id ≡ idc)
  decOutput-sndack-pins {x} {dr} {id} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl h with Net-≟ {Data} (⊤ , sndack l dc idc) (⊤ , sndack l dr id) | h
  ...   | no _     | ()
  ...   | yes refl | _ = refl , refl

  -- with the instance pinned to (dc,idc), the sndack target is `og` (via offer-o2)
  decOutput-sndack-tgt : ∀ {x W} → decOutput l (o2 x) dc idc ─[ ev (evN (sndack l dc idc) tt) ]─► W
                       → W ≡ decOutput l (og x) dc idc
  decOutput-sndack-tgt {x} (sVis {v = v} eqf h) =
    just-injective (trans (sym h)
      (subst (λ n → vis-of n (⊤ , sndack l dc idc) tt ≡ just (decOutput l (og x) dc idc))
             eqf (offer-o2 {x})))

  -- Output o2 emits sndack (pins dc idc; ⊤ payload → og, phase payload x)
  decOutput-sndack-class : ∀ {op dr id W} → decOutput l op dc idc ─[ ev (evN (sndack l dr id) tt) ]─► W
                         → Σ[ x ∈ Data ] ((op ≡ o2 x) × (dr ≡ dc) × (id ≡ idc) × (W ≡ decOutput l (og x) dc idc))
  decOutput-sndack-class {o0} (sVis refl ())
  decOutput-sndack-class {o1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decOutput-sndack-class {o2 x} step with decOutput-sndack-pins {x} step
  ... | refl , refl = x , refl , refl , refl , decOutput-sndack-tgt {x} step
  decOutput-sndack-class {og x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  ------------------------------------------------------------------------
  -- REFLECTION infrastructure — Part 3: Tx-fold (`IS`/`TR`) classifiers.
  -- `IS = decInput ⦀ Skip` (the fold-degenerate Input side); `Skip` is inert
  -- so `IS` mirrors the cell.  `TR = decTrans ⦀ decRAck` interleaves the two
  -- Tx-side registers.  Each lifts a leaf classifier through the `⦀`.
  ------------------------------------------------------------------------

  -- IS τ: only the ig guard (→ i0)
  IS-τ : ∀ {iP W} → (decInput l iP dc idc ⦀ Skip) ─[ τ ]─► W
       → (Σ[ x ∈ Data ] (iP ≡ ig x)) × (W ≡ (decInput l i0 dc idc ⦀ Skip))
  IS-τ {iP} step with Par-τ-elim ∅ES ⊤merge (decInput l iP dc idc) Skip step
  ... | τL _ Iτ refl with decInput-τ-class {iP} Iτ
  ...   | xig , Weq = xig , cong (λ z → z ⦀ Skip) Weq
  IS-τ {iP} step | τR _ Sτ refl = ⊥-elim (Skip-no-τ Sτ)

  -- IS input: the cell accepts input at i0
  IS-input : ∀ {iP dr id a W} → (decInput l iP dc idc ⦀ Skip) ─[ ev (evN (input l dr id) a) ]─► W
           → (iP ≡ i0) × (dr ≡ dc) × (id ≡ idc) × (W ≡ (decInput l (i1 a) dc idc ⦀ Skip))
  IS-input {iP} step with Par-ev-elim ∅ES ⊤merge (decInput l iP dc idc) Skip step
  ... | evSync mem _ _  = ⊥-elim mem
  ... | evR _ Sev       = ⊥-elim (Skip-no-ev Sev)
  ... | evBoth _ _ Sev  = ⊥-elim (Skip-no-ev Sev)
  ... | evL _ Iev with decInput-input-class {iP} Iev
  ...   | e0 , edr , eid , Weq = e0 , edr , eid , cong (λ z → z ⦀ Skip) Weq

  -- IS sndmsg: the cell emits sndmsg at i1
  IS-sndmsg : ∀ {iP dr id a W} → (decInput l iP dc idc ⦀ Skip) ─[ ev (evN (sndmsg l dr id) a) ]─► W
            → (iP ≡ i1 a) × (dr ≡ dc) × (id ≡ idc) × (W ≡ (decInput l (i2 a) dc idc ⦀ Skip))
  IS-sndmsg {iP} step with Par-ev-elim ∅ES ⊤merge (decInput l iP dc idc) Skip step
  ... | evSync mem _ _  = ⊥-elim mem
  ... | evR _ Sev       = ⊥-elim (Skip-no-ev Sev)
  ... | evBoth _ _ Sev  = ⊥-elim (Skip-no-ev Sev)
  ... | evL _ Iev with decInput-sndmsg-class {iP} Iev
  ...   | e1 , edr , eid , Weq = e1 , edr , eid , cong (λ z → z ⦀ Skip) Weq

  -- IS rcvack: the cell emits rcvack at i2
  IS-rcvack : ∀ {iP dr id W} → (decInput l iP dc idc ⦀ Skip) ─[ ev (evN (rcvack l dr id) tt) ]─► W
            → Σ[ x ∈ Data ] ((iP ≡ i2 x) × (dr ≡ dc) × (id ≡ idc) × (W ≡ (decInput l (ig x) dc idc ⦀ Skip)))
  IS-rcvack {iP} step with Par-ev-elim ∅ES ⊤merge (decInput l iP dc idc) Skip step
  ... | evSync mem _ _  = ⊥-elim mem
  ... | evR _ Sev       = ⊥-elim (Skip-no-ev Sev)
  ... | evBoth _ _ Sev  = ⊥-elim (Skip-no-ev Sev)
  ... | evL _ Iev with decInput-rcvack-class {iP} Iev
  ...   | x , e2 , edr , eid , Weq = x , e2 , edr , eid , cong (λ z → z ⦀ Skip) Weq

  -- TR τ: either the Transmitter guard (gT) or the RcvAck guard (gR)
  TR-τ : ∀ {tb ab W} → (decTrans l tb ⦀ decRAck l ab) ─[ τ ]─► W
       → (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] Σ[ x ∈ Data ] (tb ≡ grd d id x) × (W ≡ (decTrans l free ⦀ decRAck l ab)))
       ⊎ (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] (ab ≡ grd d id) × (W ≡ (decTrans l tb ⦀ decRAck l free)))
  TR-τ {tb} {ab} step with Par-τ-elim ∅ES ⊤merge (decTrans l tb) (decRAck l ab) step
  ... | τL _ Tτ refl with decTrans-τ-class {tb} Tτ
  ...   | (d , id , x , eq) , Weq = inj₁ (d , id , x , eq , cong (λ z → z ⦀ decRAck l ab) Weq)
  TR-τ {tb} {ab} step | τR _ Aτ refl with decRAck-τ-class {ab} Aτ
  ...   | (d , id , eq) , Weq = inj₂ (d , id , eq , cong (λ z → decTrans l tb ⦀ z) Weq)

  -- TR sndmsg: the Transmitter accepts sndmsg at free (RcvAck refuses)
  TR-sndmsg : ∀ {tb ab dr id a W} → (decTrans l tb ⦀ decRAck l ab) ─[ ev (evN (sndmsg l dr id) a) ]─► W
            → (tb ≡ free) × (W ≡ (decTrans l (hold dr id a) ⦀ decRAck l ab))
  TR-sndmsg {tb} {ab} step with Par-ev-elim ∅ES ⊤merge (decTrans l tb) (decRAck l ab) step
  ... | evSync mem _ _   = ⊥-elim mem
  ... | evR _ Aev        = ⊥-elim (decRAck-no-sndmsg {ab} Aev)
  ... | evBoth _ _ Aev   = ⊥-elim (decRAck-no-sndmsg {ab} Aev)
  ... | evL _ Tev with decTrans-sndmsg-class {tb} Tev
  ...   | ef , Weq = ef , cong (λ z → z ⦀ decRAck l ab) Weq

  -- TR rcvack: the RcvAck emits rcvack at hold (Transmitter refuses)
  TR-rcvack : ∀ {tb ab dr id W} → (decTrans l tb ⦀ decRAck l ab) ─[ ev (evN (rcvack l dr id) tt) ]─► W
            → (ab ≡ hold dr id) × (W ≡ (decTrans l tb ⦀ decRAck l (grd dr id)))
  TR-rcvack {tb} {ab} step with Par-ev-elim ∅ES ⊤merge (decTrans l tb) (decRAck l ab) step
  ... | evSync mem _ _   = ⊥-elim mem
  ... | evL _ Tev        = ⊥-elim (decTrans-no-rcvack {tb} Tev)
  ... | evBoth _ Tev _   = ⊥-elim (decTrans-no-rcvack {tb} Tev)
  ... | evR _ Aev with decRAck-rcvack-class {ab} Aev
  ...   | eh , Weq = eh , cong (λ z → decTrans l tb ⦀ z) Weq

  -- TR tx: the Transmitter emits tx at hold (RcvAck refuses)
  TR-tx : ∀ {tb ab dr id a W} → (decTrans l tb ⦀ decRAck l ab) ─[ ev (evN (tx l dr id) a) ]─► W
        → (tb ≡ hold dr id a) × (W ≡ (decTrans l (grd dr id a) ⦀ decRAck l ab))
  TR-tx {tb} {ab} step with Par-ev-elim ∅ES ⊤merge (decTrans l tb) (decRAck l ab) step
  ... | evSync mem _ _   = ⊥-elim mem
  ... | evR _ Aev        = ⊥-elim (decRAck-no-tx {ab} Aev)
  ... | evBoth _ _ Aev   = ⊥-elim (decRAck-no-tx {ab} Aev)
  ... | evL _ Tev with decTrans-tx-class {tb} Tev
  ...   | eh , Weq = eh , cong (λ z → z ⦀ decRAck l ab) Weq

  -- TR ack: the RcvAck accepts ack at free (Transmitter refuses)
  TR-ack : ∀ {tb ab dr id W} → (decTrans l tb ⦀ decRAck l ab) ─[ ev (evN (ack l dr id) tt) ]─► W
         → (ab ≡ free) × (W ≡ (decTrans l tb ⦀ decRAck l (hold dr id)))
  TR-ack {tb} {ab} step with Par-ev-elim ∅ES ⊤merge (decTrans l tb) (decRAck l ab) step
  ... | evSync mem _ _   = ⊥-elim mem
  ... | evL _ Tev        = ⊥-elim (decTrans-no-ack {tb} Tev)
  ... | evBoth _ Tev _   = ⊥-elim (decTrans-no-ack {tb} Tev)
  ... | evR _ Aev with decRAck-ack-class {ab} Aev
  ...   | ef , Weq = ef , cong (λ z → decTrans l tb ⦀ z) Weq

  ------------------------------------------------------------------------
  -- REFLECTION infrastructure — Part 4: Rx-fold (`OS`/`RS`) classifiers.
  -- `OS = decOutput ⦀ Skip` (fold-degenerate Output side; `Skip` inert).
  -- `RS = decRcv ⦀ decSnd` interleaves the two Rx-side registers.
  ------------------------------------------------------------------------

  -- OS τ: only the og guard (→ o0)
  OS-τ : ∀ {oP W} → (decOutput l oP dc idc ⦀ Skip) ─[ τ ]─► W
       → (Σ[ x ∈ Data ] (oP ≡ og x)) × (W ≡ (decOutput l o0 dc idc ⦀ Skip))
  OS-τ {oP} step with Par-τ-elim ∅ES ⊤merge (decOutput l oP dc idc) Skip step
  ... | τL _ Oτ refl with decOutput-τ-class {oP} Oτ
  ...   | xog , Weq = xog , cong (λ z → z ⦀ Skip) Weq
  OS-τ {oP} step | τR _ Sτ refl = ⊥-elim (Skip-no-τ Sτ)

  -- OS rcvmsg: the cell accepts rcvmsg at o0
  OS-rcvmsg : ∀ {oP dr id a W} → (decOutput l oP dc idc ⦀ Skip) ─[ ev (evN (rcvmsg l dr id) a) ]─► W
            → (oP ≡ o0) × (dr ≡ dc) × (id ≡ idc) × (W ≡ (decOutput l (o1 a) dc idc ⦀ Skip))
  OS-rcvmsg {oP} step with Par-ev-elim ∅ES ⊤merge (decOutput l oP dc idc) Skip step
  ... | evSync mem _ _  = ⊥-elim mem
  ... | evR _ Sev       = ⊥-elim (Skip-no-ev Sev)
  ... | evBoth _ _ Sev  = ⊥-elim (Skip-no-ev Sev)
  ... | evL _ Oev with decOutput-rcvmsg-class {oP} Oev
  ...   | e0 , edr , eid , Weq = e0 , edr , eid , cong (λ z → z ⦀ Skip) Weq

  -- OS output: the cell emits output at o1
  OS-output : ∀ {oP dr id a W} → (decOutput l oP dc idc ⦀ Skip) ─[ ev (evN (output l dr id) a) ]─► W
            → (oP ≡ o1 a) × (dr ≡ dc) × (id ≡ idc) × (W ≡ (decOutput l (o2 a) dc idc ⦀ Skip))
  OS-output {oP} step with Par-ev-elim ∅ES ⊤merge (decOutput l oP dc idc) Skip step
  ... | evSync mem _ _  = ⊥-elim mem
  ... | evR _ Sev       = ⊥-elim (Skip-no-ev Sev)
  ... | evBoth _ _ Sev  = ⊥-elim (Skip-no-ev Sev)
  ... | evL _ Oev with decOutput-output-class {oP} Oev
  ...   | e1 , edr , eid , Weq = e1 , edr , eid , cong (λ z → z ⦀ Skip) Weq

  -- OS sndack: the cell emits sndack at o2
  OS-sndack : ∀ {oP dr id W} → (decOutput l oP dc idc ⦀ Skip) ─[ ev (evN (sndack l dr id) tt) ]─► W
            → Σ[ x ∈ Data ] ((oP ≡ o2 x) × (dr ≡ dc) × (id ≡ idc) × (W ≡ (decOutput l (og x) dc idc ⦀ Skip)))
  OS-sndack {oP} step with Par-ev-elim ∅ES ⊤merge (decOutput l oP dc idc) Skip step
  ... | evSync mem _ _  = ⊥-elim mem
  ... | evR _ Sev       = ⊥-elim (Skip-no-ev Sev)
  ... | evBoth _ _ Sev  = ⊥-elim (Skip-no-ev Sev)
  ... | evL _ Oev with decOutput-sndack-class {oP} Oev
  ...   | x , e2 , edr , eid , Weq = x , e2 , edr , eid , cong (λ z → z ⦀ Skip) Weq

  -- RS τ: either the Receiver guard (gRc) or the SndAck guard (gSa)
  RS-τ : ∀ {rb sb W} → (decRcv l rb ⦀ decSnd l sb) ─[ τ ]─► W
       → (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] Σ[ x ∈ Data ] (rb ≡ grd d id x) × (W ≡ (decRcv l free ⦀ decSnd l sb)))
       ⊎ (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] (sb ≡ grd d id) × (W ≡ (decRcv l rb ⦀ decSnd l free)))
  RS-τ {rb} {sb} step with Par-τ-elim ∅ES ⊤merge (decRcv l rb) (decSnd l sb) step
  ... | τL _ Rτ refl with decRcv-τ-class {rb} Rτ
  ...   | (d , id , x , eq) , Weq = inj₁ (d , id , x , eq , cong (λ z → z ⦀ decSnd l sb) Weq)
  RS-τ {rb} {sb} step | τR _ Sτ refl with decSnd-τ-class {sb} Sτ
  ...   | (d , id , eq) , Weq = inj₂ (d , id , eq , cong (λ z → decRcv l rb ⦀ z) Weq)

  -- RS rcvmsg: the Receiver emits rcvmsg at hold (SndAck refuses)
  RS-rcvmsg : ∀ {rb sb dr id a W} → (decRcv l rb ⦀ decSnd l sb) ─[ ev (evN (rcvmsg l dr id) a) ]─► W
            → (rb ≡ hold dr id a) × (W ≡ (decRcv l (grd dr id a) ⦀ decSnd l sb))
  RS-rcvmsg {rb} {sb} step with Par-ev-elim ∅ES ⊤merge (decRcv l rb) (decSnd l sb) step
  ... | evSync mem _ _   = ⊥-elim mem
  ... | evR _ Sev        = ⊥-elim (decSnd-no-rcvmsg {sb} Sev)
  ... | evBoth _ _ Sev   = ⊥-elim (decSnd-no-rcvmsg {sb} Sev)
  ... | evL _ Rev with decRcv-rcvmsg-class {rb} Rev
  ...   | eh , Weq = eh , cong (λ z → z ⦀ decSnd l sb) Weq

  -- RS sndack: the SndAck accepts sndack at free (Receiver refuses)
  RS-sndack : ∀ {rb sb dr id W} → (decRcv l rb ⦀ decSnd l sb) ─[ ev (evN (sndack l dr id) tt) ]─► W
            → (sb ≡ free) × (W ≡ (decRcv l rb ⦀ decSnd l (hold dr id)))
  RS-sndack {rb} {sb} step with Par-ev-elim ∅ES ⊤merge (decRcv l rb) (decSnd l sb) step
  ... | evSync mem _ _   = ⊥-elim mem
  ... | evL _ Rev        = ⊥-elim (decRcv-no-sndack {rb} Rev)
  ... | evBoth _ Rev _   = ⊥-elim (decRcv-no-sndack {rb} Rev)
  ... | evR _ Sev with decSnd-sndack-class {sb} Sev
  ...   | ef , Weq = ef , cong (λ z → decRcv l rb ⦀ z) Weq

  -- RS tx: the Receiver accepts tx at free (SndAck refuses)
  RS-tx : ∀ {rb sb dr id a W} → (decRcv l rb ⦀ decSnd l sb) ─[ ev (evN (tx l dr id) a) ]─► W
        → (rb ≡ free) × (W ≡ (decRcv l (hold dr id a) ⦀ decSnd l sb))
  RS-tx {rb} {sb} step with Par-ev-elim ∅ES ⊤merge (decRcv l rb) (decSnd l sb) step
  ... | evSync mem _ _   = ⊥-elim mem
  ... | evR _ Sev        = ⊥-elim (decSnd-no-tx {sb} Sev)
  ... | evBoth _ _ Sev   = ⊥-elim (decSnd-no-tx {sb} Sev)
  ... | evL _ Rev with decRcv-tx-class {rb} Rev
  ...   | ef , Weq = ef , cong (λ z → z ⦀ decSnd l sb) Weq

  -- RS ack: the SndAck emits ack at hold (Receiver refuses)
  RS-ack : ∀ {rb sb dr id W} → (decRcv l rb ⦀ decSnd l sb) ─[ ev (evN (ack l dr id) tt) ]─► W
         → (sb ≡ hold dr id) × (W ≡ (decRcv l rb ⦀ decSnd l (grd dr id)))
  RS-ack {rb} {sb} step with Par-ev-elim ∅ES ⊤merge (decRcv l rb) (decSnd l sb) step
  ... | evSync mem _ _   = ⊥-elim mem
  ... | evL _ Rev        = ⊥-elim (decRcv-no-ack {rb} Rev)
  ... | evBoth _ Rev _   = ⊥-elim (decRcv-no-ack {rb} Rev)
  ... | evR _ Sev with decSnd-ack-class {sb} Sev
  ...   | eh , Weq = eh , cong (λ z → decRcv l rb ⦀ z) Weq

  ------------------------------------------------------------------------
  -- REFLECTION infrastructure — Part 5: link-GENERALISED leaf classifiers.
  --
  -- On a SYNC leg the observed event carries a FRESH link `l₀` (from casing
  -- the hidden event `e = sndmsg l₀ …`), so the fixed-`l` classifiers fail
  -- with `l₀ != l`.  Each classifier below observes an arbitrary `l₀` and
  -- returns `l₀ ≡ l` as its head component: the menu's `Net-≟`/`l₀ ≟ l` test
  -- pins it (`yes refl` unifies `l₀ := l`), so the caller matches the
  -- returned `refl` and applies the partner (fixed-`l`) classifier as before.
  ------------------------------------------------------------------------

  -- Input i0 accepts input at any observed link (pins l₀,dc,idc; → i1 a)
  decInput-input-classL : ∀ {ip l₀ dr id a W} → decInput l ip dc idc ─[ ev (evN (input l₀ dr id) a) ]─► W
                        → (l₀ ≡ l) × (ip ≡ i0) × (dr ≡ dc) × (id ≡ idc) × (W ≡ decInput l (i1 a) dc idc)
  decInput-input-classL {i0} {l₀} {dr} {id} {a} (sVis refl h) with l₀ FinP.≟ l | h
  ... | no _     | ()
  ... | yes refl | h′ rewrite ≟-diagF l with dr ≟ dc | h′
  ...   | no _     | ()
  ...   | yes refl | h″ with id ≟ idc | h″
  ...     | no _     | ()
  ...     | yes refl | h‴ rewrite ≟-diag dr | ≟-diag id =
              refl , refl , refl , refl , sym (just-injective h‴)
  decInput-input-classL {i1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decInput-input-classL {i2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decInput-input-classL {ig x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- Input i1 emits sndmsg at any observed link (Net-≟ pins l₀,dc,idc; → i2 a)
  decInput-sndmsg-classL : ∀ {ip l₀ dr id a W} → decInput l ip dc idc ─[ ev (evN (sndmsg l₀ dr id) a) ]─► W
                         → (l₀ ≡ l) × (ip ≡ i1 a) × (dr ≡ dc) × (id ≡ idc) × (W ≡ decInput l (i2 a) dc idc)
  decInput-sndmsg-classL {i0} (sVis refl ())
  decInput-sndmsg-classL {i1 x} {l₀} {dr} {id} {a} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl h with Net-≟ {Data} (Data , sndmsg l dc idc) (Data , sndmsg l₀ dr id) | h
  ...   | no _     | ()
  ...   | yes refl | h′ with a ≟ x | h′
  ...     | no _     | ()
  ...     | yes refl | h″ rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x =
              refl , refl , refl , refl , sym (just-injective h″)
  decInput-sndmsg-classL {i2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decInput-sndmsg-classL {ig x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- rcvack on i2 at any observed link pins the instance (l₀,dc,idc)
  decInput-rcvack-pinsL : ∀ {x l₀ dr id W} → decInput l (i2 x) dc idc ─[ ev (evN (rcvack l₀ dr id) tt) ]─► W
                        → (l₀ ≡ l) × (dr ≡ dc) × (id ≡ idc)
  decInput-rcvack-pinsL {x} {l₀} {dr} {id} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl h with Net-≟ {Data} (⊤ , rcvack l dc idc) (⊤ , rcvack l₀ dr id) | h
  ...   | no _     | ()
  ...   | yes refl | _ = refl , refl , refl

  -- Input i2 emits rcvack at any observed link (→ ig x)
  decInput-rcvack-classL : ∀ {ip l₀ dr id W} → decInput l ip dc idc ─[ ev (evN (rcvack l₀ dr id) tt) ]─► W
                         → Σ[ x ∈ Data ] ((l₀ ≡ l) × (ip ≡ i2 x) × (dr ≡ dc) × (id ≡ idc) × (W ≡ decInput l (ig x) dc idc))
  decInput-rcvack-classL {i0} (sVis refl ())
  decInput-rcvack-classL {i1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decInput-rcvack-classL {i2 x} step with decInput-rcvack-pinsL {x} step
  ... | refl , refl , refl = x , refl , refl , refl , refl , decInput-rcvack-tgt {x} step
  decInput-rcvack-classL {ig x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- Output o0 accepts rcvmsg at any observed link (pins l₀,dc,idc; → o1 a)
  decOutput-rcvmsg-classL : ∀ {op l₀ dr id a W} → decOutput l op dc idc ─[ ev (evN (rcvmsg l₀ dr id) a) ]─► W
                          → (l₀ ≡ l) × (op ≡ o0) × (dr ≡ dc) × (id ≡ idc) × (W ≡ decOutput l (o1 a) dc idc)
  decOutput-rcvmsg-classL {o0} {l₀} {dr} {id} {a} (sVis refl h) with l₀ FinP.≟ l | h
  ... | no _     | ()
  ... | yes refl | h′ rewrite ≟-diagF l with dr ≟ dc | h′
  ...   | no _     | ()
  ...   | yes refl | h″ with id ≟ idc | h″
  ...     | no _     | ()
  ...     | yes refl | h‴ rewrite ≟-diag dr | ≟-diag id =
              refl , refl , refl , refl , sym (just-injective h‴)
  decOutput-rcvmsg-classL {o1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decOutput-rcvmsg-classL {o2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decOutput-rcvmsg-classL {og x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- Output o1 emits output at any observed link (Net-≟ pins l₀,dc,idc; → o2 a)
  decOutput-output-classL : ∀ {op l₀ dr id a W} → decOutput l op dc idc ─[ ev (evN (output l₀ dr id) a) ]─► W
                          → (l₀ ≡ l) × (op ≡ o1 a) × (dr ≡ dc) × (id ≡ idc) × (W ≡ decOutput l (o2 a) dc idc)
  decOutput-output-classL {o0} (sVis refl ())
  decOutput-output-classL {o1 x} {l₀} {dr} {id} {a} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl h with Net-≟ {Data} (Data , output l dc idc) (Data , output l₀ dr id) | h
  ...   | no _     | ()
  ...   | yes refl | h′ with a ≟ x | h′
  ...     | no _     | ()
  ...     | yes refl | h″ rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x =
              refl , refl , refl , refl , sym (just-injective h″)
  decOutput-output-classL {o2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decOutput-output-classL {og x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- sndack on o2 at any observed link pins the instance (l₀,dc,idc)
  decOutput-sndack-pinsL : ∀ {x l₀ dr id W} → decOutput l (o2 x) dc idc ─[ ev (evN (sndack l₀ dr id) tt) ]─► W
                         → (l₀ ≡ l) × (dr ≡ dc) × (id ≡ idc)
  decOutput-sndack-pinsL {x} {l₀} {dr} {id} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl h with Net-≟ {Data} (⊤ , sndack l dc idc) (⊤ , sndack l₀ dr id) | h
  ...   | no _     | ()
  ...   | yes refl | _ = refl , refl , refl

  -- Output o2 emits sndack at any observed link (→ og x)
  decOutput-sndack-classL : ∀ {op l₀ dr id W} → decOutput l op dc idc ─[ ev (evN (sndack l₀ dr id) tt) ]─► W
                          → Σ[ x ∈ Data ] ((l₀ ≡ l) × (op ≡ o2 x) × (dr ≡ dc) × (id ≡ idc) × (W ≡ decOutput l (og x) dc idc))
  decOutput-sndack-classL {o0} (sVis refl ())
  decOutput-sndack-classL {o1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decOutput-sndack-classL {o2 x} step with decOutput-sndack-pinsL {x} step
  ... | refl , refl , refl = x , refl , refl , refl , refl , decOutput-sndack-tgt {x} step
  decOutput-sndack-classL {og x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- Transmitter hold emits tx at any observed link (Net-≟ pins l₀; → grd)
  decTrans-tx-classL : ∀ {tb l₀ dr id a W} → decTrans l tb ─[ ev (evN (tx l₀ dr id) a) ]─► W
                     → (l₀ ≡ l) × (tb ≡ hold dr id a) × (W ≡ decTrans l (grd dr id a))
  decTrans-tx-classL {free} (sVis refl ())
  decTrans-tx-classL {hold d i x} {l₀} {dr} {id} {a} step rewrite ≟-diag l with step
  ... | sVis refl h with Net-≟ {Data} (Data , tx l d i) (Data , tx l₀ dr id) | h
  ...   | no _     | ()
  ...   | yes refl | h′ with a ≟ x | h′
  ...     | no _     | ()
  ...     | yes refl | h″ rewrite ≟-diagF l | ≟-diag d | ≟-diag i | ≟-diag x =
              refl , refl , sym (just-injective h″)
  decTrans-tx-classL {grd d i x} step
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag i | ≟-diag x with step
  ... | sVis () _

  -- SndAck hold emits ack at any observed link (Net-≟ pins l₀; ⊤ payload → grd)
  decSnd-ack-classL : ∀ {sb l₀ dr id W} → decSnd l sb ─[ ev (evN (ack l₀ dr id) tt) ]─► W
                    → (l₀ ≡ l) × (sb ≡ hold dr id) × (W ≡ decSnd l (grd dr id))
  decSnd-ack-classL {free} (sVis refl ())
  decSnd-ack-classL {hold d i} {l₀} {dr} {id} step rewrite ≟-diag l with step
  ... | sVis refl h with Net-≟ {Data} (⊤ , ack l d i) (⊤ , ack l₀ dr id) | h
  ...   | no _     | ()
  ...   | yes refl | h″ rewrite ≟-diagF l | ≟-diag d | ≟-diag i =
            refl , refl , sym (just-injective h″)
  decSnd-ack-classL {grd d i} step
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag i with step
  ... | sVis () _

  ------------------------------------------------------------------------
  -- REFLECTION infrastructure — Part 6: link-GENERALISED refutations and
  -- register-acceptor classifiers (the top csTA / solo channels, whose
  -- observed link `l₀` is likewise fresh).  Refutation bodies are
  -- link-agnostic (the offered menu never contains the channel), so they
  -- carry over verbatim with the observed link generalised to `l₀`.
  ------------------------------------------------------------------------

  -- decInput never offers tx / ack (at any observed link)
  decInput-no-txL : ∀ {ip l₀ dr id₀ x₀ W} → decInput l ip dc idc ─[ ev (evN (tx l₀ dr id₀) x₀) ]─► W → ⊥
  decInput-no-txL {i0} (sVis refl ())
  decInput-no-txL {i1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decInput-no-txL {i2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decInput-no-txL {ig x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  decInput-no-ackL : ∀ {ip l₀ dr id₀ W} → decInput l ip dc idc ─[ ev (evN (ack l₀ dr id₀) tt) ]─► W → ⊥
  decInput-no-ackL {i0} (sVis refl ())
  decInput-no-ackL {i1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decInput-no-ackL {i2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decInput-no-ackL {ig x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- decOutput never offers tx / ack (at any observed link)
  decOutput-no-txL : ∀ {op l₀ dr id₀ x₀ W} → decOutput l op dc idc ─[ ev (evN (tx l₀ dr id₀) x₀) ]─► W → ⊥
  decOutput-no-txL {o0} (sVis refl ())
  decOutput-no-txL {o1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decOutput-no-txL {o2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decOutput-no-txL {og x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  decOutput-no-ackL : ∀ {op l₀ dr id₀ W} → decOutput l op dc idc ─[ ev (evN (ack l₀ dr id₀) tt) ]─► W → ⊥
  decOutput-no-ackL {o0} (sVis refl ())
  decOutput-no-ackL {o1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decOutput-no-ackL {o2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decOutput-no-ackL {og x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- decTrans never offers input / ack (at any observed link)
  decTrans-no-inputL : ∀ {tb l₀ dr id₀ x₀ W} → decTrans l tb ─[ ev (evN (input l₀ dr id₀) x₀) ]─► W → ⊥
  decTrans-no-inputL {free} (sVis refl ())
  decTrans-no-inputL {hold d id x} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decTrans-no-inputL {grd d id x} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  decTrans-no-ackL : ∀ {tb l₀ dr id₀ W} → decTrans l tb ─[ ev (evN (ack l₀ dr id₀) tt) ]─► W → ⊥
  decTrans-no-ackL {free} (sVis refl ())
  decTrans-no-ackL {hold d id x} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decTrans-no-ackL {grd d id x} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- decRAck never offers input / tx (at any observed link)
  decRAck-no-inputL : ∀ {ab l₀ dr id₀ x₀ W} → decRAck l ab ─[ ev (evN (input l₀ dr id₀) x₀) ]─► W → ⊥
  decRAck-no-inputL {free} (sVis refl ())
  decRAck-no-inputL {hold d id} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRAck-no-inputL {grd d id} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _

  decRAck-no-txL : ∀ {ab l₀ dr id₀ x₀ W} → decRAck l ab ─[ ev (evN (tx l₀ dr id₀) x₀) ]─► W → ⊥
  decRAck-no-txL {free} (sVis refl ())
  decRAck-no-txL {hold d id} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRAck-no-txL {grd d id} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _

  -- decRcv never offers output / ack (at any observed link)
  decRcv-no-outputL : ∀ {rb l₀ dr id₀ x₀ W} → decRcv l rb ─[ ev (evN (output l₀ dr id₀) x₀) ]─► W → ⊥
  decRcv-no-outputL {free} (sVis refl ())
  decRcv-no-outputL {hold d id x} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRcv-no-outputL {grd d id x} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  decRcv-no-ackL : ∀ {rb l₀ dr id₀ W} → decRcv l rb ─[ ev (evN (ack l₀ dr id₀) tt) ]─► W → ⊥
  decRcv-no-ackL {free} (sVis refl ())
  decRcv-no-ackL {hold d id x} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRcv-no-ackL {grd d id x} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- decSnd never offers output / tx (at any observed link)
  decSnd-no-outputL : ∀ {sb l₀ dr id₀ x₀ W} → decSnd l sb ─[ ev (evN (output l₀ dr id₀) x₀) ]─► W → ⊥
  decSnd-no-outputL {free} (sVis refl ())
  decSnd-no-outputL {hold d id} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decSnd-no-outputL {grd d id} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _

  decSnd-no-txL : ∀ {sb l₀ dr id₀ x₀ W} → decSnd l sb ─[ ev (evN (tx l₀ dr id₀) x₀) ]─► W → ⊥
  decSnd-no-txL {free} (sVis refl ())
  decSnd-no-txL {hold d id} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decSnd-no-txL {grd d id} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _

  -- Receiver free accepts tx at any observed link (pins l₀; → hold)
  decRcv-tx-classL : ∀ {rb l₀ dr id a W} → decRcv l rb ─[ ev (evN (tx l₀ dr id) a) ]─► W
                   → (l₀ ≡ l) × (rb ≡ free) × (W ≡ decRcv l (hold dr id a))
  decRcv-tx-classL {free} {l₀} {dr} {id} {a} (sVis refl h) with l₀ FinP.≟ l | h
  ... | no _     | ()
  ... | yes refl | h′ rewrite ≟-diagF l = refl , refl , sym (just-injective h′)
  decRcv-tx-classL {hold d i x} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRcv-tx-classL {grd d i x} step
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag i | ≟-diag x with step
  ... | sVis () _

  -- RcvAck free accepts ack at any observed link (pins l₀; ⊤ payload → hold)
  decRAck-ack-classL : ∀ {ab l₀ dr id W} → decRAck l ab ─[ ev (evN (ack l₀ dr id) tt) ]─► W
                     → (l₀ ≡ l) × (ab ≡ free) × (W ≡ decRAck l (hold dr id))
  decRAck-ack-classL {free} {l₀} {dr} {id} (sVis refl h) with l₀ FinP.≟ l | h
  ... | no _     | ()
  ... | yes refl | h′ rewrite ≟-diagF l = refl , refl , sym (just-injective h′)
  decRAck-ack-classL {hold d i} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRAck-ack-classL {grd d i} step
    rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag i with step
  ... | sVis () _

  ------------------------------------------------------------------------
  -- REFLECTION infrastructure — Part 7: link-generalised composites.
  ------------------------------------------------------------------------

  -- IS refuses tx / ack; IS accepts input at i0 (pins l₀,dc,idc)
  IS-no-txL : ∀ {iP l₀ dr id a W} → (decInput l iP dc idc ⦀ Skip) ─[ ev (evN (tx l₀ dr id) a) ]─► W → ⊥
  IS-no-txL {iP} step with Par-ev-elim ∅ES ⊤merge (decInput l iP dc idc) Skip step
  ... | evSync mem _ _  = mem
  ... | evR _ Sev       = Skip-no-ev Sev
  ... | evBoth _ _ Sev  = Skip-no-ev Sev
  ... | evL _ Iev       = decInput-no-txL {iP} Iev

  IS-no-ackL : ∀ {iP l₀ dr id W} → (decInput l iP dc idc ⦀ Skip) ─[ ev (evN (ack l₀ dr id) tt) ]─► W → ⊥
  IS-no-ackL {iP} step with Par-ev-elim ∅ES ⊤merge (decInput l iP dc idc) Skip step
  ... | evSync mem _ _  = mem
  ... | evR _ Sev       = Skip-no-ev Sev
  ... | evBoth _ _ Sev  = Skip-no-ev Sev
  ... | evL _ Iev       = decInput-no-ackL {iP} Iev

  IS-inputL : ∀ {iP l₀ dr id a W} → (decInput l iP dc idc ⦀ Skip) ─[ ev (evN (input l₀ dr id) a) ]─► W
            → (l₀ ≡ l) × (iP ≡ i0) × (dr ≡ dc) × (id ≡ idc) × (W ≡ (decInput l (i1 a) dc idc ⦀ Skip))
  IS-inputL {iP} step with Par-ev-elim ∅ES ⊤merge (decInput l iP dc idc) Skip step
  ... | evSync mem _ _  = ⊥-elim mem
  ... | evR _ Sev       = ⊥-elim (Skip-no-ev Sev)
  ... | evBoth _ _ Sev  = ⊥-elim (Skip-no-ev Sev)
  ... | evL _ Iev with decInput-input-classL {iP} Iev
  ...   | el , e0 , edr , eid , Weq = el , e0 , edr , eid , cong (λ z → z ⦀ Skip) Weq

  -- TR emits tx at the Transmitter hold (RcvAck refuses tx)
  TR-txL : ∀ {tb ab l₀ dr id a W} → (decTrans l tb ⦀ decRAck l ab) ─[ ev (evN (tx l₀ dr id) a) ]─► W
         → (l₀ ≡ l) × (tb ≡ hold dr id a) × (W ≡ (decTrans l (grd dr id a) ⦀ decRAck l ab))
  TR-txL {tb} {ab} step with Par-ev-elim ∅ES ⊤merge (decTrans l tb) (decRAck l ab) step
  ... | evSync mem _ _   = ⊥-elim mem
  ... | evR _ Aev        = ⊥-elim (decRAck-no-txL {ab} Aev)
  ... | evBoth _ _ Aev   = ⊥-elim (decRAck-no-txL {ab} Aev)
  ... | evL _ Tev with decTrans-tx-classL {tb} Tev
  ...   | el , eh , Weq = el , eh , cong (λ z → z ⦀ decRAck l ab) Weq

  -- TR accepts ack at the RcvAck free (Transmitter refuses ack)
  TR-ackL : ∀ {tb ab l₀ dr id W} → (decTrans l tb ⦀ decRAck l ab) ─[ ev (evN (ack l₀ dr id) tt) ]─► W
          → (l₀ ≡ l) × (ab ≡ free) × (W ≡ (decTrans l tb ⦀ decRAck l (hold dr id)))
  TR-ackL {tb} {ab} step with Par-ev-elim ∅ES ⊤merge (decTrans l tb) (decRAck l ab) step
  ... | evSync mem _ _   = ⊥-elim mem
  ... | evL _ Tev        = ⊥-elim (decTrans-no-ackL {tb} Tev)
  ... | evBoth _ Tev _   = ⊥-elim (decTrans-no-ackL {tb} Tev)
  ... | evR _ Aev with decRAck-ack-classL {ab} Aev
  ...   | el , ef , Weq = el , ef , cong (λ z → decTrans l tb ⦀ z) Weq

  -- OS refuses tx / ack; OS emits output at o1 (pins l₀,dc,idc)
  OS-no-txL : ∀ {oP l₀ dr id a W} → (decOutput l oP dc idc ⦀ Skip) ─[ ev (evN (tx l₀ dr id) a) ]─► W → ⊥
  OS-no-txL {oP} step with Par-ev-elim ∅ES ⊤merge (decOutput l oP dc idc) Skip step
  ... | evSync mem _ _  = mem
  ... | evR _ Sev       = Skip-no-ev Sev
  ... | evBoth _ _ Sev  = Skip-no-ev Sev
  ... | evL _ Oev       = decOutput-no-txL {oP} Oev

  OS-no-ackL : ∀ {oP l₀ dr id W} → (decOutput l oP dc idc ⦀ Skip) ─[ ev (evN (ack l₀ dr id) tt) ]─► W → ⊥
  OS-no-ackL {oP} step with Par-ev-elim ∅ES ⊤merge (decOutput l oP dc idc) Skip step
  ... | evSync mem _ _  = mem
  ... | evR _ Sev       = Skip-no-ev Sev
  ... | evBoth _ _ Sev  = Skip-no-ev Sev
  ... | evL _ Oev       = decOutput-no-ackL {oP} Oev

  OS-outputL : ∀ {oP l₀ dr id a W} → (decOutput l oP dc idc ⦀ Skip) ─[ ev (evN (output l₀ dr id) a) ]─► W
             → (l₀ ≡ l) × (oP ≡ o1 a) × (dr ≡ dc) × (id ≡ idc) × (W ≡ (decOutput l (o2 a) dc idc ⦀ Skip))
  OS-outputL {oP} step with Par-ev-elim ∅ES ⊤merge (decOutput l oP dc idc) Skip step
  ... | evSync mem _ _  = ⊥-elim mem
  ... | evR _ Sev       = ⊥-elim (Skip-no-ev Sev)
  ... | evBoth _ _ Sev  = ⊥-elim (Skip-no-ev Sev)
  ... | evL _ Oev with decOutput-output-classL {oP} Oev
  ...   | el , e1 , edr , eid , Weq = el , e1 , edr , eid , cong (λ z → z ⦀ Skip) Weq

  -- RS accepts tx at the Receiver free (SndAck refuses tx)
  RS-txL : ∀ {rb sb l₀ dr id a W} → (decRcv l rb ⦀ decSnd l sb) ─[ ev (evN (tx l₀ dr id) a) ]─► W
         → (l₀ ≡ l) × (rb ≡ free) × (W ≡ (decRcv l (hold dr id a) ⦀ decSnd l sb))
  RS-txL {rb} {sb} step with Par-ev-elim ∅ES ⊤merge (decRcv l rb) (decSnd l sb) step
  ... | evSync mem _ _   = ⊥-elim mem
  ... | evR _ Sev        = ⊥-elim (decSnd-no-txL {sb} Sev)
  ... | evBoth _ _ Sev   = ⊥-elim (decSnd-no-txL {sb} Sev)
  ... | evL _ Rev with decRcv-tx-classL {rb} Rev
  ...   | el , ef , Weq = el , ef , cong (λ z → z ⦀ decSnd l sb) Weq

  -- RS emits ack at the SndAck hold (Receiver refuses ack)
  RS-ackL : ∀ {rb sb l₀ dr id W} → (decRcv l rb ⦀ decSnd l sb) ─[ ev (evN (ack l₀ dr id) tt) ]─► W
          → (l₀ ≡ l) × (sb ≡ hold dr id) × (W ≡ (decRcv l rb ⦀ decSnd l (grd dr id)))
  RS-ackL {rb} {sb} step with Par-ev-elim ∅ES ⊤merge (decRcv l rb) (decSnd l sb) step
  ... | evSync mem _ _   = ⊥-elim mem
  ... | evL _ Rev        = ⊥-elim (decRcv-no-ackL {rb} Rev)
  ... | evBoth _ Rev _   = ⊥-elim (decRcv-no-ackL {rb} Rev)
  ... | evR _ Sev with decSnd-ack-classL {sb} Sev
  ...   | el , eh , Weq = el , eh , cong (λ z → decRcv l rb ⦀ z) Weq

  -- IS emits sndmsg at i1 / rcvack at i2 (at any observed link, pins l₀)
  IS-sndmsgL : ∀ {iP l₀ dr id a W} → (decInput l iP dc idc ⦀ Skip) ─[ ev (evN (sndmsg l₀ dr id) a) ]─► W
             → (l₀ ≡ l) × (iP ≡ i1 a) × (dr ≡ dc) × (id ≡ idc) × (W ≡ (decInput l (i2 a) dc idc ⦀ Skip))
  IS-sndmsgL {iP} step with Par-ev-elim ∅ES ⊤merge (decInput l iP dc idc) Skip step
  ... | evSync mem _ _  = ⊥-elim mem
  ... | evR _ Sev       = ⊥-elim (Skip-no-ev Sev)
  ... | evBoth _ _ Sev  = ⊥-elim (Skip-no-ev Sev)
  ... | evL _ Iev with decInput-sndmsg-classL {iP} Iev
  ...   | el , e1 , edr , eid , Weq = el , e1 , edr , eid , cong (λ z → z ⦀ Skip) Weq

  IS-rcvackL : ∀ {iP l₀ dr id W} → (decInput l iP dc idc ⦀ Skip) ─[ ev (evN (rcvack l₀ dr id) tt) ]─► W
             → Σ[ x ∈ Data ] ((l₀ ≡ l) × (iP ≡ i2 x) × (dr ≡ dc) × (id ≡ idc) × (W ≡ (decInput l (ig x) dc idc ⦀ Skip)))
  IS-rcvackL {iP} step with Par-ev-elim ∅ES ⊤merge (decInput l iP dc idc) Skip step
  ... | evSync mem _ _  = ⊥-elim mem
  ... | evR _ Sev       = ⊥-elim (Skip-no-ev Sev)
  ... | evBoth _ _ Sev  = ⊥-elim (Skip-no-ev Sev)
  ... | evL _ Iev with decInput-rcvack-classL {iP} Iev
  ...   | x , el , e2 , edr , eid , Weq = x , el , e2 , edr , eid , cong (λ z → z ⦀ Skip) Weq

  -- OS accepts rcvmsg at o0 / emits sndack at o2 (at any observed link, pins l₀)
  OS-rcvmsgL : ∀ {oP l₀ dr id a W} → (decOutput l oP dc idc ⦀ Skip) ─[ ev (evN (rcvmsg l₀ dr id) a) ]─► W
             → (l₀ ≡ l) × (oP ≡ o0) × (dr ≡ dc) × (id ≡ idc) × (W ≡ (decOutput l (o1 a) dc idc ⦀ Skip))
  OS-rcvmsgL {oP} step with Par-ev-elim ∅ES ⊤merge (decOutput l oP dc idc) Skip step
  ... | evSync mem _ _  = ⊥-elim mem
  ... | evR _ Sev       = ⊥-elim (Skip-no-ev Sev)
  ... | evBoth _ _ Sev  = ⊥-elim (Skip-no-ev Sev)
  ... | evL _ Oev with decOutput-rcvmsg-classL {oP} Oev
  ...   | el , e0 , edr , eid , Weq = el , e0 , edr , eid , cong (λ z → z ⦀ Skip) Weq

  OS-sndackL : ∀ {oP l₀ dr id W} → (decOutput l oP dc idc ⦀ Skip) ─[ ev (evN (sndack l₀ dr id) tt) ]─► W
             → Σ[ x ∈ Data ] ((l₀ ≡ l) × (oP ≡ o2 x) × (dr ≡ dc) × (id ≡ idc) × (W ≡ (decOutput l (og x) dc idc ⦀ Skip)))
  OS-sndackL {oP} step with Par-ev-elim ∅ES ⊤merge (decOutput l oP dc idc) Skip step
  ... | evSync mem _ _  = ⊥-elim mem
  ... | evR _ Sev       = ⊥-elim (Skip-no-ev Sev)
  ... | evBoth _ _ Sev  = ⊥-elim (Skip-no-ev Sev)
  ... | evL _ Oev with decOutput-sndack-classL {oP} Oev
  ...   | x , el , e2 , edr , eid , Weq = x , el , e2 , edr , eid , cong (λ z → z ⦀ Skip) Weq

  -- TR refuses input; RS refuses output (used by the SOLO gluers)
  TR-no-inputL : ∀ {tb ab l₀ dr id a W} → (decTrans l tb ⦀ decRAck l ab) ─[ ev (evN (input l₀ dr id) a) ]─► W → ⊥
  TR-no-inputL {tb} {ab} step with Par-ev-elim ∅ES ⊤merge (decTrans l tb) (decRAck l ab) step
  ... | evSync mem _ _  = mem
  ... | evL _ Tev       = decTrans-no-inputL {tb} Tev
  ... | evR _ Aev       = decRAck-no-inputL {ab} Aev
  ... | evBoth _ Tev _  = decTrans-no-inputL {tb} Tev

  RS-no-outputL : ∀ {rb sb l₀ dr id a W} → (decRcv l rb ⦀ decSnd l sb) ─[ ev (evN (output l₀ dr id) a) ]─► W → ⊥
  RS-no-outputL {rb} {sb} step with Par-ev-elim ∅ES ⊤merge (decRcv l rb) (decSnd l sb) step
  ... | evSync mem _ _  = mem
  ... | evL _ Rev       = decRcv-no-outputL {rb} Rev
  ... | evR _ Sev       = decSnd-no-outputL {sb} Sev
  ... | evBoth _ Rev _  = decRcv-no-outputL {rb} Rev

  ----------------------------------------------------------------------
  -- REFLECTION infrastructure — Part 10: leaf refutations (l₀) for the
  -- channels a leaf never visibly offers (needed by refl-ev's dispatch).
  ----------------------------------------------------------------------

  -- decInput offers no rcvmsg at any phase / observed link
  decInput-no-rcvmsgL : ∀ {ip l₀ dr id₀ x₀ W} → decInput l ip dc idc ─[ ev (evN (rcvmsg l₀ dr id₀) x₀) ]─► W → ⊥
  decInput-no-rcvmsgL {i0} (sVis refl ())
  decInput-no-rcvmsgL {i1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decInput-no-rcvmsgL {i2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decInput-no-rcvmsgL {ig x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- decInput offers no sndack at any phase / observed link
  decInput-no-sndackL : ∀ {ip l₀ dr id₀ W} → decInput l ip dc idc ─[ ev (evN (sndack l₀ dr id₀) tt) ]─► W → ⊥
  decInput-no-sndackL {i0} (sVis refl ())
  decInput-no-sndackL {i1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decInput-no-sndackL {i2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decInput-no-sndackL {ig x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- decInput offers no output at any phase / observed link
  decInput-no-outputL : ∀ {ip l₀ dr id₀ x₀ W} → decInput l ip dc idc ─[ ev (evN (output l₀ dr id₀) x₀) ]─► W → ⊥
  decInput-no-outputL {i0} (sVis refl ())
  decInput-no-outputL {i1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decInput-no-outputL {i2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decInput-no-outputL {ig x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- decOutput offers no sndmsg at any phase / observed link
  decOutput-no-sndmsgL : ∀ {ip l₀ dr id₀ x₀ W} → decOutput l ip dc idc ─[ ev (evN (sndmsg l₀ dr id₀) x₀) ]─► W → ⊥
  decOutput-no-sndmsgL {o0} (sVis refl ())
  decOutput-no-sndmsgL {o1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decOutput-no-sndmsgL {o2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decOutput-no-sndmsgL {og x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- decOutput offers no rcvack at any phase / observed link
  decOutput-no-rcvackL : ∀ {ip l₀ dr id₀ W} → decOutput l ip dc idc ─[ ev (evN (rcvack l₀ dr id₀) tt) ]─► W → ⊥
  decOutput-no-rcvackL {o0} (sVis refl ())
  decOutput-no-rcvackL {o1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decOutput-no-rcvackL {o2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decOutput-no-rcvackL {og x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- decOutput offers no input at any phase / observed link
  decOutput-no-inputL : ∀ {ip l₀ dr id₀ x₀ W} → decOutput l ip dc idc ─[ ev (evN (input l₀ dr id₀) x₀) ]─► W → ⊥
  decOutput-no-inputL {o0} (sVis refl ())
  decOutput-no-inputL {o1 x} step rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis refl ()
  decOutput-no-inputL {o2 x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x with step
  ... | sVis refl ()
  decOutput-no-inputL {og x} step
    rewrite ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diagF l | ≟-diag dc | ≟-diag idc | ≟-diag x | ≟-diagF l | ≟-diag dc | ≟-diag idc with step
  ... | sVis () _

  -- decTrans offers no rcvmsg at any phase / observed link
  decTrans-no-rcvmsgL : ∀ {tbb l₀ dr id₀ x₀ W} → decTrans l tbb ─[ ev (evN (rcvmsg l₀ dr id₀) x₀) ]─► W → ⊥
  decTrans-no-rcvmsgL {free} (sVis refl ())
  decTrans-no-rcvmsgL {hold d id x} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decTrans-no-rcvmsgL {grd d id x} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- decTrans offers no sndack at any phase / observed link
  decTrans-no-sndackL : ∀ {tbb l₀ dr id₀ W} → decTrans l tbb ─[ ev (evN (sndack l₀ dr id₀) tt) ]─► W → ⊥
  decTrans-no-sndackL {free} (sVis refl ())
  decTrans-no-sndackL {hold d id x} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decTrans-no-sndackL {grd d id x} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- decTrans offers no output at any phase / observed link
  decTrans-no-outputL : ∀ {tbb l₀ dr id₀ x₀ W} → decTrans l tbb ─[ ev (evN (output l₀ dr id₀) x₀) ]─► W → ⊥
  decTrans-no-outputL {free} (sVis refl ())
  decTrans-no-outputL {hold d id x} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decTrans-no-outputL {grd d id x} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- decRAck offers no rcvmsg at any phase / observed link
  decRAck-no-rcvmsgL : ∀ {abb l₀ dr id₀ x₀ W} → decRAck l abb ─[ ev (evN (rcvmsg l₀ dr id₀) x₀) ]─► W → ⊥
  decRAck-no-rcvmsgL {free} (sVis refl ())
  decRAck-no-rcvmsgL {hold d id} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRAck-no-rcvmsgL {grd d id} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _

  -- decRAck offers no sndack at any phase / observed link
  decRAck-no-sndackL : ∀ {abb l₀ dr id₀ W} → decRAck l abb ─[ ev (evN (sndack l₀ dr id₀) tt) ]─► W → ⊥
  decRAck-no-sndackL {free} (sVis refl ())
  decRAck-no-sndackL {hold d id} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRAck-no-sndackL {grd d id} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _

  -- decRAck offers no output at any phase / observed link
  decRAck-no-outputL : ∀ {abb l₀ dr id₀ x₀ W} → decRAck l abb ─[ ev (evN (output l₀ dr id₀) x₀) ]─► W → ⊥
  decRAck-no-outputL {free} (sVis refl ())
  decRAck-no-outputL {hold d id} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRAck-no-outputL {grd d id} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _

  -- decRcv offers no sndmsg at any phase / observed link
  decRcv-no-sndmsgL : ∀ {tbb l₀ dr id₀ x₀ W} → decRcv l tbb ─[ ev (evN (sndmsg l₀ dr id₀) x₀) ]─► W → ⊥
  decRcv-no-sndmsgL {free} (sVis refl ())
  decRcv-no-sndmsgL {hold d id x} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRcv-no-sndmsgL {grd d id x} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- decRcv offers no rcvack at any phase / observed link
  decRcv-no-rcvackL : ∀ {tbb l₀ dr id₀ W} → decRcv l tbb ─[ ev (evN (rcvack l₀ dr id₀) tt) ]─► W → ⊥
  decRcv-no-rcvackL {free} (sVis refl ())
  decRcv-no-rcvackL {hold d id x} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRcv-no-rcvackL {grd d id x} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- decRcv offers no input at any phase / observed link
  decRcv-no-inputL : ∀ {tbb l₀ dr id₀ x₀ W} → decRcv l tbb ─[ ev (evN (input l₀ dr id₀) x₀) ]─► W → ⊥
  decRcv-no-inputL {free} (sVis refl ())
  decRcv-no-inputL {hold d id x} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decRcv-no-inputL {grd d id x} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- decSnd offers no sndmsg at any phase / observed link
  decSnd-no-sndmsgL : ∀ {abb l₀ dr id₀ x₀ W} → decSnd l abb ─[ ev (evN (sndmsg l₀ dr id₀) x₀) ]─► W → ⊥
  decSnd-no-sndmsgL {free} (sVis refl ())
  decSnd-no-sndmsgL {hold d id} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decSnd-no-sndmsgL {grd d id} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _

  -- decSnd offers no rcvack at any phase / observed link
  decSnd-no-rcvackL : ∀ {abb l₀ dr id₀ W} → decSnd l abb ─[ ev (evN (rcvack l₀ dr id₀) tt) ]─► W → ⊥
  decSnd-no-rcvackL {free} (sVis refl ())
  decSnd-no-rcvackL {hold d id} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decSnd-no-rcvackL {grd d id} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _

  -- decSnd offers no input at any phase / observed link
  decSnd-no-inputL : ∀ {abb l₀ dr id₀ x₀ W} → decSnd l abb ─[ ev (evN (input l₀ dr id₀) x₀) ]─► W → ⊥
  decSnd-no-inputL {free} (sVis refl ())
  decSnd-no-inputL {hold d id} step rewrite ≟-diag l with step
  ... | sVis refl ()
  decSnd-no-inputL {grd d id} step rewrite ≟-diag l | ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sVis () _


  ------------------------------------------------------------------------
  -- decTx/decRx (general vector): hidden-channel visible offers are
  -- confined to `nothing` by the ∖-menu (`sVis refl ()`) — this holds for
  -- the WHOLE config vector, no singleton exposure needed (contrast the
  -- non-offered-event confinements in `PerLink.Step`, which DO need the
  -- singleton vector exposed to combine the per-leaf refutations below).
  ------------------------------------------------------------------------

  -- IN-set (csSR'/csRS') visible offers are filtered to `nothing`
  decTx-no-sndmsg : ∀ {iphs tb ab l₀ dr id a W} → decTx l iphs tb ab ─[ ev (evN (sndmsg l₀ dr id) a) ]─► W → ⊥
  decTx-no-sndmsg {iphs} {tb} {ab} step
    with Hide-ev-elim csSR' (decInputs l (linkConfig l) iphs ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l ab)) step
  ... | heV _ ¬cs _ = ¬cs Poly.tt

  -- decTx never visibly offers rcvack (hidden inside csSR')
  decTx-no-rcvack : ∀ {iphs tb ab l₀ dr id W} → decTx l iphs tb ab ─[ ev (evN (rcvack l₀ dr id) tt) ]─► W → ⊥
  decTx-no-rcvack {iphs} {tb} {ab} step
    with Hide-ev-elim csSR' (decInputs l (linkConfig l) iphs ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l ab)) step
  ... | heV _ ¬cs _ = ¬cs Poly.tt

  -- decRx never visibly offers rcvmsg (hidden inside csRS')
  decRx-no-rcvmsg : ∀ {ophs rb sb l₀ dr id a W} → decRx l ophs rb sb ─[ ev (evN (rcvmsg l₀ dr id) a) ]─► W → ⊥
  decRx-no-rcvmsg {ophs} {rb} {sb} step
    with Hide-ev-elim csRS' (decOutputs l (linkConfig l) ophs ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l sb)) step
  ... | heV _ ¬cs _ = ¬cs Poly.tt

  -- decRx never visibly offers sndack (hidden inside csRS')
  decRx-no-sndack : ∀ {ophs rb sb l₀ dr id W} → decRx l ophs rb sb ─[ ev (evN (sndack l₀ dr id) tt) ]─► W → ⊥
  decRx-no-sndack {ophs} {rb} {sb} step
    with Hide-ev-elim csRS' (decOutputs l (linkConfig l) ophs ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l sb)) step
  ... | heV _ ¬cs _ = ¬cs Poly.tt
