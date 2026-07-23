{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — per-link mux GENERAL EXPANSION walk
-- (`PerLink.Exp`), the ARBITRARY-config capstone of Milestone 2b.
--
-- Assembles `PerLink.Fold`'s general forward/reflection six-lemma
-- interface into a divergence-respecting weak EXPANSION
-- `linkCopy l ⪰ ⟦ initial l ⟧`, whence (via `⪯→≈DR`) the headline
--
--   perLink : (l : Link) → linkConfig l ≢ [] → Unique (linkConfig l)
--           → NetOneLink l ≈DR linkCopy l
--
-- for ANY non-empty `Unique` config `linkConfig l`.  Where 2a's `Exp`
-- degenerated the spec side to `Copy l dc idc ⦀ Skip` (a singleton
-- config), this module runs a genuine `⦀⋆`-fold of Copy cells against the
-- multi-instance mux, per cell in lock-step.
--
-- Layers (bottom-up):
--   1. SPEC-SIDE COPY FOLD.  Per-cell Copy phase `CPh` (cp0 home / cp1 x
--      out-pending / cpg x guard), spec vector `PhV CPh cfg`, spec decode
--      `decCopies` matching `linkCopy l`, `spec-init`.  A small Copy-fold
--      sibling of `Fold`'s Layers 1-3 (the Copy cells are DIFFERENT leaves
--      from Input/Output, so `Fold`'s classifiers do not apply — a sibling
--      is built here).  Plus spec-side `no-√C` (uses `cfg≢[]`) and `¬DivC`.
--
-- No postulates, holes, or `NON_TERMINATING`.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂; Σ; Σ-syntax; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; _≢_)
open import Data.Nat.Properties using (≤-reflexive)
open import Class.DecEq using (DecEq; _≟_)
open import Function.Base using (case_of_)
import Data.Fin.Properties as FinP
import Data.Nat.Solver as ℕSolver
open ℕSolver.+-*-Solver
  using ()
  renaming (solve to ℕsolve; _:=_ to _:≡_; _:+_ to _:⊕_; con to ℕcon)

open import Process_Trees
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using (Dir; IDs; lo; hi)

module CSP.Examples.Cardano_network.NetworkVerification.PerLink.Exp
  (p : Params) (Data : Set) ⦃ _ : DecEq Data ⦄ where

open PTree

open import CSP.Examples.Cardano_network.Net p
  using ( Net; Net-≟; Link
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack )
open Params p using (linkConfig)

import CSP.Operators {E = Net Data} (Net-≟ {Data}) as Op
open Op using (_∥⇘_⇙_; _⦀_; ⦀⋆; _∖_; chanSet; Skip; Par; ∅ES; EventSet; viewV)

open import Semantics.LTS {E = Net Data} {I = ExtI (Net Data)} hiding (Diverges)
open import Semantics.WeakBisim {E = Net Data} {I = ExtI (Net Data)}
  using (_─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.DRBisim {E = Net Data} {I = ExtI (Net Data)}
  using (Diverges; _≈DR_)
open import Semantics.Expansion {E = Net Data} {I = ExtI (Net Data)}
  using (Expand; ExpBwdF; _⪰_; ⪯→≈DR)

open import CSP.Examples.Cardano_network.Network p Data
  using ( NetProc; Copy; copyMenu; linkCopy )
open import CSP.Examples.Cardano_network.NetworkLink p Data
  using ( NetOneLink )
open import CSP.Examples.Cardano_network.NetworkVerification.PerLink.State p Data
open import CSP.Examples.Cardano_network.NetworkVerification.PerLink.Decode p Data
  using ( NetR; vis-of; succV; ⟦_⟧; dec-init )
-- `Fold` re-exports `Leaf` publicly (⊤merge, ≟-diag(F), noView, noStep-Par,
-- Skip-no-ev/τ, evN, …) and supplies the general six-lemma step interface.
open import CSP.Examples.Cardano_network.NetworkVerification.PerLink.Fold p Data

open import CSP.Laws.Traces.TraceLawsParallelElim (Net-≟ {Data})
  using (Par-ev-elim; evSync; evL; evR; evBoth; Par-τ-elim; τL; τR; Par-force-ret-inv)
open import CSP.Laws.Traces.TraceLawsParallel (Net-≟ {Data})
  using (Par-soloL; Par-soloR; Par-τ-L; Par-τ-R)

------------------------------------------------------------------------
-- LAYER 1a — the per-cell Copy phase and its decoder.
--
-- Each `Copy l d id` is a loop with a three-state lifecycle, mirroring
-- 2a's `S0`/`S1 x`/`Sg x` but WITHOUT the inert `⦀ Skip` wrapper (the fold
-- supplies the parallel structure):
--   cp0    home        = `Copy l d id`            (offers `input l d id`)
--   cp1 x  out-pending = post-`input` derivative  (offers `output l d id`@x)
--   cpg x  guard       = post-`output` derivative (a single restart τ)
------------------------------------------------------------------------

-- per-cell Copy phase
data CPh : Set where
  cp0 : CPh
  cp1 : Data → CPh
  cpg : Data → CPh

-- decode one Copy cell at its phase (input · output succV chain)
decCopy : (l : Link) → CPh → Dir → IDs → NetProc
decCopy l cp0     d id = Copy l d id
decCopy l (cp1 x) d id = succV (Copy l d id) (Data , input l d id) x
decCopy l (cpg x) d id =
  succV (succV (Copy l d id) (Data , input l d id) x) (Data , output l d id) x

-- fold-decode the Copy cells (empty config ⇒ Skip), mirroring `linkCopy`'s
-- `⦀⋆ (map …)` cell by cell (the shape that makes `decCopies-home` one line)
decCopies : (l : Link) (xs : List (Dir × IDs)) → PhV CPh xs → NetProc
decCopies l []              []         = Skip
decCopies l ((d , id) ∷ xs) (ph ∷ phs) = decCopy l ph d id ⦀ decCopies l xs phs

-- all-home Copy vector, built by recursion so it reduces with the decoder
homeC : (xs : List (Dir × IDs)) → PhV CPh xs
homeC []       = []
homeC (_ ∷ xs) = cp0 ∷ homeC xs

-- all-home Copy fold ≡ the concrete interleaved Copy bundle
decCopies-home : (l : Link) (xs : List (Dir × IDs))
               → decCopies l xs (homeC xs)
                   ≡ ⦀⋆ (map (λ { (d , id) → Copy l d id }) xs)
decCopies-home l []              = refl
decCopies-home l ((d , id) ∷ xs) = cong (Copy l d id ⦀_) (decCopies-home l xs)

-- the all-home fold of the config decodes to exactly `linkCopy l`
spec-init : (l : Link) → decCopies l (linkConfig l) (homeC (linkConfig l)) ≡ linkCopy l
spec-init l = decCopies-home l (linkConfig l)

------------------------------------------------------------------------
-- LAYER 1b — per-cell Copy leaf lemmas (force/offer/fire, inversions,
-- stability), the bare-cell analogues of 2a's `S0`/`S1 x`/`Sg x` facts.
------------------------------------------------------------------------

module _ (l : Link) where

  -- `force (decCopy cp0)` is a react (its loop head), needed to fire visibly
  force-react-cp0 : ∀ {d id} → PTree.force (decCopy l cp0 d id)
                  ≡ react (vis-of (PTree.force (decCopy l cp0 d id)))
                          (tau-of (PTree.force (decCopy l cp0 d id)))
  force-react-cp0 = refl

  -- `decCopy cp0` offers `input l d id` at value x, landing on `cp1 x`
  offer-cp0 : ∀ {d id x}
            → vis-of (PTree.force (decCopy l cp0 d id)) (Data , input l d id) x
              ≡ just (decCopy l (cp1 x) d id)
  offer-cp0 {d} {id} {x} rewrite ≟-diagF l | ≟-diag d | ≟-diag id = refl

  -- `cp0` fires `input x` → `cp1 x`
  cp0─input─►cp1 : ∀ {d id x}
                 → decCopy l cp0 d id ─[ ev (evN (input l d id) x) ]─► decCopy l (cp1 x) d id
  cp0─input─►cp1 = sVis force-react-cp0 offer-cp0

  -- `force (decCopy cp1)` is a react (the Output-prefix head)
  force-react-cp1 : ∀ {d id x} → PTree.force (decCopy l (cp1 x) d id)
                  ≡ react (vis-of (PTree.force (decCopy l (cp1 x) d id)))
                          (tau-of (PTree.force (decCopy l (cp1 x) d id)))
  force-react-cp1 {d} {id} {x} rewrite ≟-diagF l | ≟-diag d | ≟-diag id = refl

  -- `decCopy cp1` offers `output l d id` at value x, landing on `cpg x`
  offer-cp1 : ∀ {d id x}
            → vis-of (PTree.force (decCopy l (cp1 x) d id)) (Data , output l d id) x
              ≡ just (decCopy l (cpg x) d id)
  offer-cp1 {d} {id} {x} rewrite ≟-diagF l | ≟-diag d | ≟-diag id
                               | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x = refl

  -- `cp1 x` fires `output x` → `cpg x`
  cp1─output─►cpg : ∀ {d id x}
                  → decCopy l (cp1 x) d id ─[ ev (evN (output l d id) x) ]─► decCopy l (cpg x) d id
  cp1─output─►cpg = sVis force-react-cp1 offer-cp1

  -- `force (decCopy cpg)` is a `sil` back to `cp0` (the loop-restart guard τ)
  force-sil-cpg : ∀ {d id x}
                → PTree.force (decCopy l (cpg x) d id) ≡ sil (decCopy l cp0 d id)
  force-sil-cpg {d} {id} {x} rewrite ≟-diagF l | ≟-diag d | ≟-diag id
                                   | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x = refl

  -- `cpg x` takes its single restart τ → `cp0`
  cpg─τ─►cp0 : ∀ {d id x} → decCopy l (cpg x) d id ─[ τ ]─► decCopy l cp0 d id
  cpg─τ─►cp0 = sSil force-sil-cpg

  ------------------------------------------------------------------------
  -- Visible inversions / menus of the Copy leaf phases.
  ------------------------------------------------------------------------

  -- diagonal: an `input l d id @ a` step of `cp0` lands on `cp1 a`
  cp0-diag-inv : ∀ {d id a W} → decCopy l cp0 d id ─[ ev (evN (input l d id) a) ]─► W
               → W ≡ decCopy l (cp1 a) d id
  cp0-diag-inv (sVis refl offer) = just-injective (trans (sym offer) offer-cp0)

  -- `cp0` fires ONLY `input l d id` (any value a), landing on `cp1 a`
  cp0-evL : ∀ {d id B} {e : Net Data B} {a} {W}
          → decCopy l cp0 d id ─[ ev (evN e a) ]─► W
          → Σ[ x ∈ Data ] ((evN e a ≡ evN (input l d id) x) × (W ≡ decCopy l (cp1 x) d id))
  cp0-evL {d} {id} {e = input l₀ d₀ id₀} {a} step with l₀ FinP.≟ l | d₀ ≟ d | id₀ ≟ id
  ... | yes refl | yes refl | yes refl = a , refl , cp0-diag-inv step
  ... | no ¬p    | _        | _        = ⊥-elim (off step)
    where off : ∀ {W} → decCopy l cp0 d id ─[ ev (evN (input l₀ d₀ id₀) a) ]─► W → ⊥
          off (sVis refl offer) with l₀ FinP.≟ l
          ... | no _  = nothing-absurd offer
          ... | yes q = ⊥-elim (¬p q)
  ... | yes refl | no ¬p    | _        = ⊥-elim (off step)
    where off : ∀ {W} → decCopy l cp0 d id ─[ ev (evN (input l d₀ id₀) a) ]─► W → ⊥
          off (sVis refl offer) rewrite ≟-diagF l with d₀ ≟ d
          ... | no _  = nothing-absurd offer
          ... | yes q = ⊥-elim (¬p q)
  ... | yes refl | yes refl | no ¬p    = ⊥-elim (off step)
    where off : ∀ {W} → decCopy l cp0 d id ─[ ev (evN (input l d id₀) a) ]─► W → ⊥
          off (sVis refl offer) rewrite ≟-diagF l | ≟-diag d with id₀ ≟ id
          ... | no _  = nothing-absurd offer
          ... | yes q = ⊥-elim (¬p q)
  cp0-evL {e = output l₀ d₀ id₀} (sVis refl offer) = ⊥-elim (nothing-absurd offer)
  cp0-evL {e = sndmsg l₀ d₀ id₀} (sVis refl offer) = ⊥-elim (nothing-absurd offer)
  cp0-evL {e = rcvmsg l₀ d₀ id₀} (sVis refl offer) = ⊥-elim (nothing-absurd offer)
  cp0-evL {e = tx     l₀ d₀ id₀} (sVis refl offer) = ⊥-elim (nothing-absurd offer)
  cp0-evL {e = sndack l₀ d₀ id₀} (sVis refl offer) = ⊥-elim (nothing-absurd offer)
  cp0-evL {e = rcvack l₀ d₀ id₀} (sVis refl offer) = ⊥-elim (nothing-absurd offer)
  cp0-evL {e = ack    l₀ d₀ id₀} (sVis refl offer) = ⊥-elim (nothing-absurd offer)

  -- `cp0` offers no `output` (its menu is `input`-only)
  cp0-no-output : ∀ {d id l₀ d₀ id₀ a W}
                → decCopy l cp0 d id ─[ ev (evN (output l₀ d₀ id₀) a) ]─► W → ⊥
  cp0-no-output (sVis refl offer) = nothing-absurd offer

  -- a visible step of `cp1 x` reads off `cp1 x`'s offer map at the fired event
  cp1-view : ∀ {d id x B} {e' : Net Data B} {a' W}
           → decCopy l (cp1 x) d id ─[ ev (evN e' a') ]─► W
           → vis-of (PTree.force (decCopy l (cp1 x) d id)) (B , e') a' ≡ just W
  cp1-view (sVis eqf offer) = trans (cong (λ n → vis-of n _ _) eqf) offer

  -- `cp1 x`'s force offers ONLY `output l d id @ x`; every other channel maps
  -- to `nothing` (the Output-prefix Cont guard)
  cp1-menu-input  : ∀ {d id x} {a' : Data} {l₀ d₀ id₀}
                  → vis-of (PTree.force (decCopy l (cp1 x) d id)) (Data , input l₀ d₀ id₀) a' ≡ nothing
  cp1-menu-input  {d} {id} {x} rewrite ≟-diagF l | ≟-diag d | ≟-diag id = refl
  cp1-menu-sndmsg : ∀ {d id x} {a' : Data} {l₀ d₀ id₀}
                  → vis-of (PTree.force (decCopy l (cp1 x) d id)) (Data , sndmsg l₀ d₀ id₀) a' ≡ nothing
  cp1-menu-sndmsg {d} {id} {x} rewrite ≟-diagF l | ≟-diag d | ≟-diag id = refl
  cp1-menu-rcvmsg : ∀ {d id x} {a' : Data} {l₀ d₀ id₀}
                  → vis-of (PTree.force (decCopy l (cp1 x) d id)) (Data , rcvmsg l₀ d₀ id₀) a' ≡ nothing
  cp1-menu-rcvmsg {d} {id} {x} rewrite ≟-diagF l | ≟-diag d | ≟-diag id = refl
  cp1-menu-tx     : ∀ {d id x} {a' : Data} {l₀ d₀ id₀}
                  → vis-of (PTree.force (decCopy l (cp1 x) d id)) (Data , tx l₀ d₀ id₀) a' ≡ nothing
  cp1-menu-tx     {d} {id} {x} rewrite ≟-diagF l | ≟-diag d | ≟-diag id = refl
  cp1-menu-sndack : ∀ {d id x} {a' : ⊤} {l₀ d₀ id₀}
                  → vis-of (PTree.force (decCopy l (cp1 x) d id)) (⊤ , sndack l₀ d₀ id₀) a' ≡ nothing
  cp1-menu-sndack {d} {id} {x} rewrite ≟-diagF l | ≟-diag d | ≟-diag id = refl
  cp1-menu-rcvack : ∀ {d id x} {a' : ⊤} {l₀ d₀ id₀}
                  → vis-of (PTree.force (decCopy l (cp1 x) d id)) (⊤ , rcvack l₀ d₀ id₀) a' ≡ nothing
  cp1-menu-rcvack {d} {id} {x} rewrite ≟-diagF l | ≟-diag d | ≟-diag id = refl
  cp1-menu-ack    : ∀ {d id x} {a' : ⊤} {l₀ d₀ id₀}
                  → vis-of (PTree.force (decCopy l (cp1 x) d id)) (⊤ , ack l₀ d₀ id₀) a' ≡ nothing
  cp1-menu-ack    {d} {id} {x} rewrite ≟-diagF l | ≟-diag d | ≟-diag id = refl

  -- diagonal: an `output l d id @ x` step of `cp1 x` lands on `cpg x`
  cp1-diag-inv : ∀ {d id x W} → decCopy l (cp1 x) d id ─[ ev (evN (output l d id) x) ]─► W
               → W ≡ decCopy l (cpg x) d id
  cp1-diag-inv {d} {id} {x} step = just-injective (trans (sym (cp1-view step)) offer-cp1)

  -- `output` at a DIFFERENT value a′ ≢ x: `cp1 x` offers nothing
  cp1-menu-output-val : ∀ {d id x} {a′ : Data} → ¬ (a′ ≡ x)
                      → vis-of (PTree.force (decCopy l (cp1 x) d id)) (Data , output l d id) a′ ≡ nothing
  cp1-menu-output-val {d} {id} {x} {a′} a≢
    rewrite ≟-diagF l | ≟-diag d | ≟-diag id
          | ≟-diagF l | ≟-diag d | ≟-diag id with a′ ≟ x
  ... | yes p = ⊥-elim (a≢ p)
  ... | no  _ = refl

  -- an `output` off the diagonal channel/instance: `cp1 x` offers nothing
  cp1-out-off : ∀ {d id x} {a′ : Data} {l₀ d₀ id₀} {W}
              → ¬ ((Data , output l₀ d₀ id₀) ≡ (Data , output l d id))
              → decCopy l (cp1 x) d id ─[ ev (evN (output l₀ d₀ id₀) a′) ]─► W → ⊥
  cp1-out-off {d} {id} {x} {a′} {l₀} {d₀} {id₀} ¬eq step with cp1-view step
  ... | v rewrite ≟-diagF l | ≟-diag d | ≟-diag id
        with Net-≟ (Data , output l d id) (Data , output l₀ d₀ id₀)
  ...   | no  _  = nothing-absurd v
  ...   | yes eq = ¬eq (sym eq)

  -- `cp1 x` fires ONLY `output l d id @ x`, landing on `cpg x`
  cp1-evL : ∀ {d id x B} {e : Net Data B} {a} {W}
          → decCopy l (cp1 x) d id ─[ ev (evN e a) ]─► W
          → Σ[ eq ∈ evN e a ≡ evN (output l d id) x ] (W ≡ decCopy l (cpg x) d id)
  cp1-evL {d} {id} {x} {e = output l₀ d₀ id₀} {a} step
    with l₀ FinP.≟ l | d₀ ≟ d | id₀ ≟ id | a ≟ x
  ... | yes refl | yes refl | yes refl | yes refl = refl , cp1-diag-inv step
  ... | yes refl | yes refl | yes refl | no  a≢   =
          ⊥-elim (nothing-absurd (trans (sym (cp1-menu-output-val a≢)) (cp1-view step)))
  ... | no  ¬p   | _        | _        | _        = ⊥-elim (cp1-out-off (λ { refl → ¬p refl }) step)
  ... | yes refl | no  ¬p   | _        | _        = ⊥-elim (cp1-out-off (λ { refl → ¬p refl }) step)
  ... | yes refl | yes refl | no  ¬p   | _        = ⊥-elim (cp1-out-off (λ { refl → ¬p refl }) step)
  cp1-evL {e = input  l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym cp1-menu-input) (cp1-view step)))
  cp1-evL {e = sndmsg l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym cp1-menu-sndmsg) (cp1-view step)))
  cp1-evL {e = rcvmsg l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym cp1-menu-rcvmsg) (cp1-view step)))
  cp1-evL {e = tx     l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym cp1-menu-tx) (cp1-view step)))
  cp1-evL {e = sndack l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym cp1-menu-sndack) (cp1-view step)))
  cp1-evL {e = rcvack l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym cp1-menu-rcvack) (cp1-view step)))
  cp1-evL {e = ack    l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym cp1-menu-ack) (cp1-view step)))

  ------------------------------------------------------------------------
  -- Stability of the Copy leaf phases + non-`ret` facts.
  ------------------------------------------------------------------------

  -- `cp0` has no τ (its react head is the pure-visible loop head)
  cp0-noτ : ∀ {d id W} → ¬ (decCopy l cp0 d id ─[ τ ]─► W)
  cp0-noτ (sSil ())
  cp0-noτ (sTau {i = _ , fin}                 refl ())
  cp0-noτ (sTau {i = _ , base _}              refl ())
  cp0-noτ (sTau {i = _ , pair fin (base _)}   refl ())
  cp0-noτ (sTau {i = _ , pair fin fin}        refl ())
  cp0-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
  cp0-noτ (sTau {i = _ , pair (base _) _}     refl ())
  cp0-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

  -- `cp1 x` has no τ (its react head is the pure-visible Output-prefix)
  cp1-noτ : ∀ {d id x W} → ¬ (decCopy l (cp1 x) d id ─[ τ ]─► W)
  cp1-noτ {d} {id} {x} step rewrite ≟-diagF l | ≟-diag d | ≟-diag id with step
  ... | sSil ()
  ... | sTau {i = _ , fin}                 refl ()
  ... | sTau {i = _ , base _}              refl ()
  ... | sTau {i = _ , pair fin (base _)}   refl ()
  ... | sTau {i = _ , pair fin fin}        refl ()
  ... | sTau {i = _ , pair fin (pair _ _)} refl ()
  ... | sTau {i = _ , pair (base _) _}     refl ()
  ... | sTau {i = _ , pair (pair _ _) _}   refl ()

  -- `cpg x` takes ONLY the restart τ → `cp0` (its force is `sil (decCopy cp0)`)
  cpg-τ-inv : ∀ {d id x W} → decCopy l (cpg x) d id ─[ τ ]─► W → W ≡ decCopy l cp0 d id
  cpg-τ-inv {d} {id} {x} step
    rewrite ≟-diagF l | ≟-diag d | ≟-diag id
          | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sSil refl = refl
  ... | sTau () _

  -- `cpg x` offers no visible event (its force is a `sil`)
  cpg-noev : ∀ {d id x B} {e : Net Data B} {a} {W} → ¬ (decCopy l (cpg x) d id ─[ ev (evN e a) ]─► W)
  cpg-noev {d} {id} {x} step
    rewrite ≟-diagF l | ≟-diag d | ≟-diag id
          | ≟-diagF l | ≟-diag d | ≟-diag id | ≟-diag x with step
  ... | sVis () _

  -- Copy leaf phases never `ret` (needed for the `sRet`/`ev √` legs)
  cp0-noret : ∀ {d id r} → PTree.force (decCopy l cp0 d id) ≡ ret r → ⊥
  cp0-noret ()
  cp1-noret : ∀ {d id x r} → PTree.force (decCopy l (cp1 x) d id) ≡ ret r → ⊥
  cp1-noret {d} {id} {x} eqf = case trans (sym force-react-cp1) eqf of λ ()
  cpg-noret : ∀ {d id x r} → PTree.force (decCopy l (cpg x) d id) ≡ ret r → ⊥
  cpg-noret {d} {id} {x} eqf = case trans (sym force-sil-cpg) eqf of λ ()

  ------------------------------------------------------------------------
  -- Per-leaf classifiers + foreign-instance refutations (fold-elim heads
  -- and fold-intro tail-idle side conditions).
  ------------------------------------------------------------------------

  -- an `input` step of a Copy cell pins the cell to `cp0` at its own instance
  decCopy-input-classL : ∀ {cph d id l₀ d₀ id₀ a W}
    → decCopy l cph d id ─[ ev (evN (input l₀ d₀ id₀) a) ]─► W
    → (cph ≡ cp0) × (l₀ ≡ l) × (d₀ ≡ d) × (id₀ ≡ id) × (W ≡ decCopy l (cp1 a) d id)
  decCopy-input-classL {cp0} step with cp0-evL step
  ... | a , refl , refl = refl , refl , refl , refl , refl
  decCopy-input-classL {cp1 x} step = ⊥-elim (nothing-absurd (trans (sym cp1-menu-input) (cp1-view step)))
  decCopy-input-classL {cpg x} step = ⊥-elim (cpg-noev step)

  -- an `output` step of a Copy cell pins the cell to `cp1 a` at its own instance
  decCopy-output-classL : ∀ {cph d id l₀ d₀ id₀ a W}
    → decCopy l cph d id ─[ ev (evN (output l₀ d₀ id₀) a) ]─► W
    → (cph ≡ cp1 a) × (l₀ ≡ l) × (d₀ ≡ d) × (id₀ ≡ id) × (W ≡ decCopy l (cpg a) d id)
  decCopy-output-classL {cp0} step = ⊥-elim (cp0-no-output step)
  decCopy-output-classL {cp1 x} {d} {id} {l₀} {d₀} {id₀} {a} step
    with l₀ FinP.≟ l | d₀ ≟ d | id₀ ≟ id | a ≟ x
  ... | yes refl | yes refl | yes refl | yes refl = refl , refl , refl , refl , cp1-diag-inv step
  ... | yes refl | yes refl | yes refl | no  a≢   =
          ⊥-elim (nothing-absurd (trans (sym (cp1-menu-output-val a≢)) (cp1-view step)))
  ... | no  ¬p   | _        | _        | _        = ⊥-elim (cp1-out-off (λ { refl → ¬p refl }) step)
  ... | yes refl | no  ¬p   | _        | _        = ⊥-elim (cp1-out-off (λ { refl → ¬p refl }) step)
  ... | yes refl | yes refl | no  ¬p   | _        = ⊥-elim (cp1-out-off (λ { refl → ¬p refl }) step)
  decCopy-output-classL {cpg x} step = ⊥-elim (cpg-noev step)

  -- a τ of a Copy cell is a guard cell (`cpg x`) restarting to `cp0`
  decCopy-τ-class : ∀ {cph d id W} → decCopy l cph d id ─[ τ ]─► W
                  → Σ[ x ∈ Data ] (cph ≡ cpg x) × (W ≡ decCopy l cp0 d id)
  decCopy-τ-class {cp0}   step = ⊥-elim (cp0-noτ step)
  decCopy-τ-class {cp1 x} step = ⊥-elim (cp1-noτ step)
  decCopy-τ-class {cpg x} step = x , refl , cpg-τ-inv step

  -- a Copy cell offers no foreign-instance `input`
  decCopy-no-input-≢ : ∀ {cph d id l₀ d₀ id₀ a W} → (d , id) ≢ (d₀ , id₀)
                     → decCopy l cph d id ─[ ev (evN (input l₀ d₀ id₀) a) ]─► W → ⊥
  decCopy-no-input-≢ {cph} ne step with decCopy-input-classL {cph} step
  ... | _ , _ , eqd , eqid , _ = ne (cong₂ _,_ (sym eqd) (sym eqid))

  -- a Copy cell offers no foreign-instance `output`
  decCopy-no-output-≢ : ∀ {cph d id l₀ d₀ id₀ a W} → (d , id) ≢ (d₀ , id₀)
                      → decCopy l cph d id ─[ ev (evN (output l₀ d₀ id₀) a) ]─► W → ⊥
  decCopy-no-output-≢ {cph} ne step with decCopy-output-classL {cph} step
  ... | _ , _ , eqd , eqid , _ = ne (cong₂ _,_ (sym eqd) (sym eqid))

  ------------------------------------------------------------------------
  -- LAYER 1c — the Copy-fold sibling of `Fold`'s decInputs machinery:
  -- foreign-instance confinement, elimination (τ / input / output), and
  -- introduction (fires), for the `⦀`-fold of Copy cells.  Inducts on the
  -- config `xs`/`phs` in lock-step with `decCopies`.  Visible elim/intro
  -- need `Unique` (the `evBoth` overlap / the tail-idle side condition);
  -- the guard-τ needs neither.
  ------------------------------------------------------------------------

  -- decCopies offers no `input` at an instance ∉ the config
  decCopies-no-input-∉ : ∀ {xs} {phs : PhV CPh xs} {l₀ d id x W}
                       → ¬ ((d , id) ∈ xs)
                       → decCopies l xs phs ─[ ev (evN (input l₀ d id) x) ]─► W → ⊥
  decCopies-no-input-∉ {[]} {[]} ∉ step = Skip-no-ev step
  decCopies-no-input-∉ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} ∉ step
    with Par-ev-elim ∅ES ⊤merge (decCopy l ph₀ d₀ id₀) (decCopies l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evR _ Tev      = decCopies-no-input-∉ {cfg'} {phs'} (λ m → ∉ (there m)) Tev
  ... | evL _ Iev      with decCopy-input-classL {ph₀} Iev
  ...   | _ , refl , refl , refl , _ = ∉ (here refl)
  decCopies-no-input-∉ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} ∉ step
      | evBoth _ Iev _ with decCopy-input-classL {ph₀} Iev
  ...   | _ , refl , refl , refl , _ = ∉ (here refl)

  -- decCopies offers no `output` at an instance ∉ the config
  decCopies-no-output-∉ : ∀ {xs} {phs : PhV CPh xs} {l₀ d id x W}
                        → ¬ ((d , id) ∈ xs)
                        → decCopies l xs phs ─[ ev (evN (output l₀ d id) x) ]─► W → ⊥
  decCopies-no-output-∉ {[]} {[]} ∉ step = Skip-no-ev step
  decCopies-no-output-∉ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} ∉ step
    with Par-ev-elim ∅ES ⊤merge (decCopy l ph₀ d₀ id₀) (decCopies l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evR _ Tev      = decCopies-no-output-∉ {cfg'} {phs'} (λ m → ∉ (there m)) Tev
  ... | evL _ Oev      with decCopy-output-classL {ph₀} Oev
  ...   | _ , refl , refl , refl , _ = ∉ (here refl)
  decCopies-no-output-∉ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} ∉ step
      | evBoth _ Oev _ with decCopy-output-classL {ph₀} Oev
  ...   | _ , refl , refl , refl , _ = ∉ (here refl)

  -- every τ of decCopies is a single Copy cell's guard τ (`cpg → cp0`)
  decCopies-τ : ∀ {xs} {phs : PhV CPh xs} {W} → decCopies l xs phs ─[ τ ]─► W
    → Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] Σ[ mem ∈ (d , id) ∈ xs ] Σ[ x ∈ Data ]
        (getPh phs mem ≡ cpg x) × (W ≡ decCopies l xs (setPh phs mem cp0))
  decCopies-τ {[]} {[]} step = ⊥-elim (Skip-no-τ step)
  decCopies-τ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} step
    with Par-τ-elim ∅ES ⊤merge (decCopy l ph₀ d₀ id₀) (decCopies l cfg' phs') step
  ... | τL _ Cτ refl with decCopy-τ-class {ph₀} Cτ
  ...   | x , eq , Weq =
            d₀ , id₀ , here refl , x , eq , cong (λ z → z ⦀ decCopies l cfg' phs') Weq
  decCopies-τ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} step
      | τR _ Tτ refl with decCopies-τ {cfg'} {phs'} Tτ
  ...   | d , id , mem' , x , gcpg , Weq =
            d , id , there mem' , x , gcpg , cong (λ z → decCopy l ph₀ d₀ id₀ ⦀ z) Weq

  -- every `input` step of decCopies is a home cell accepting it
  decCopies-inputL : ∀ {xs} {phs : PhV CPh xs} {l₀ dr id a W} (uniq : Unique xs)
    → decCopies l xs phs ─[ ev (evN (input l₀ dr id) a) ]─► W
    → Σ[ mem ∈ (dr , id) ∈ xs ]
        (l₀ ≡ l) × (getPh phs mem ≡ cp0) × (W ≡ decCopies l xs (setPh phs mem (cp1 a)))
  decCopies-inputL {[]} {[]} uniq step = ⊥-elim (Skip-no-ev step)
  decCopies-inputL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
    with Par-ev-elim ∅ES ⊤merge (decCopy l ph₀ d₀ id₀) (decCopies l cfg' phs') step
  ... | evSync mem _ _ = ⊥-elim mem
  ... | evL _ Iev with decCopy-input-classL {ph₀} Iev
  ...   | refl , refl , refl , refl , Weq =
            here refl , refl , refl , cong (λ z → z ⦀ decCopies l cfg' phs') Weq
  decCopies-inputL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
      | evR _ Tev with decCopies-inputL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...   | mem' , refl , gph , refl = there mem' , refl , gph , refl
  decCopies-inputL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
      | evBoth _ Iev Tev with decCopy-input-classL {ph₀} Iev
  ...   | refl , refl , refl , refl , _ with decCopies-inputL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...     | mem' , _ , _ , _ = ⊥-elim (All.lookup (AllPairs.head uniq) mem' refl)

  -- every `output` step of decCopies is an out-pending cell emitting it
  decCopies-outputL : ∀ {xs} {phs : PhV CPh xs} {l₀ dr id a W} (uniq : Unique xs)
    → decCopies l xs phs ─[ ev (evN (output l₀ dr id) a) ]─► W
    → Σ[ mem ∈ (dr , id) ∈ xs ]
        (l₀ ≡ l) × (getPh phs mem ≡ cp1 a) × (W ≡ decCopies l xs (setPh phs mem (cpg a)))
  decCopies-outputL {[]} {[]} uniq step = ⊥-elim (Skip-no-ev step)
  decCopies-outputL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
    with Par-ev-elim ∅ES ⊤merge (decCopy l ph₀ d₀ id₀) (decCopies l cfg' phs') step
  ... | evSync mem _ _ = ⊥-elim mem
  ... | evL _ Oev with decCopy-output-classL {ph₀} Oev
  ...   | refl , refl , refl , refl , Weq =
            here refl , refl , refl , cong (λ z → z ⦀ decCopies l cfg' phs') Weq
  decCopies-outputL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
      | evR _ Tev with decCopies-outputL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...   | mem' , refl , gph , refl = there mem' , refl , gph , refl
  decCopies-outputL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
      | evBoth _ Oev Tev with decCopy-output-classL {ph₀} Oev
  ...   | refl , refl , refl , refl , _ with decCopies-outputL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...     | mem' , _ , _ , _ = ⊥-elim (All.lookup (AllPairs.head uniq) mem' refl)

  -- decCopies input fire (home cell mem, cp0 → cp1 a)
  decCopies-input-fire : ∀ {xs} {phs : PhV CPh xs} {d id x} (uniq : Unique xs)
    → (mem : (d , id) ∈ xs) → getPh phs mem ≡ cp0
    → decCopies l xs phs ─[ ev (evN (input l d id) x) ]─► decCopies l xs (setPh phs mem (cp1 x))
  decCopies-input-fire {(d , id) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} uniq (here refl) gi
    rewrite gi =
      Par-soloL ∅ES ⊤merge (decCopy l cp0 d id) (decCopies l cfg' phs') (λ z → z)
        cp0─input─►cp1
        (noView {P = decCopies l cfg' phs'} {e = input l d id} {a = x}
          (decCopies-no-input-∉ {cfg'} {phs'} (λ m → All.lookup (AllPairs.head uniq) m refl)))
  decCopies-input-fire {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} uniq (there mem') gi =
      Par-soloR ∅ES ⊤merge (decCopy l ph₀ d₀ id₀) (decCopies l cfg' phs') (λ z → z)
        (decCopies-input-fire {cfg'} {phs'} (AllPairs.tail uniq) mem' gi)
        (noView {P = decCopy l ph₀ d₀ id₀} {e = input l d id} {a = x}
          (decCopy-no-input-≢ {ph₀} (All.lookup (AllPairs.head uniq) mem')))

  -- decCopies output fire (out-pending cell mem, cp1 x → cpg x)
  decCopies-output-fire : ∀ {xs} {phs : PhV CPh xs} {d id x} (uniq : Unique xs)
    → (mem : (d , id) ∈ xs) → getPh phs mem ≡ cp1 x
    → decCopies l xs phs ─[ ev (evN (output l d id) x) ]─► decCopies l xs (setPh phs mem (cpg x))
  decCopies-output-fire {(d , id) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} uniq (here refl) gi
    rewrite gi =
      Par-soloL ∅ES ⊤merge (decCopy l (cp1 x) d id) (decCopies l cfg' phs') (λ z → z)
        cp1─output─►cpg
        (noView {P = decCopies l cfg' phs'} {e = output l d id} {a = x}
          (decCopies-no-output-∉ {cfg'} {phs'} (λ m → All.lookup (AllPairs.head uniq) m refl)))
  decCopies-output-fire {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} uniq (there mem') gi =
      Par-soloR ∅ES ⊤merge (decCopy l ph₀ d₀ id₀) (decCopies l cfg' phs') (λ z → z)
        (decCopies-output-fire {cfg'} {phs'} (AllPairs.tail uniq) mem' gi)
        (noView {P = decCopy l ph₀ d₀ id₀} {e = output l d id} {a = x}
          (decCopy-no-output-≢ {ph₀} (All.lookup (AllPairs.head uniq) mem')))

  -- decCopies guard τ fire (cell mem, cpg x → cp0); no confinement needed
  decCopies-cpg-τ-fire : ∀ {xs} {phs : PhV CPh xs} {d id x}
    → (mem : (d , id) ∈ xs) → getPh phs mem ≡ cpg x
    → decCopies l xs phs ─[ τ ]─► decCopies l xs (setPh phs mem cp0)
  decCopies-cpg-τ-fire {(d , id) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} (here refl) gi
    rewrite gi =
      Par-τ-L ∅ES ⊤merge (decCopy l (cpg x) d id) (decCopies l cfg' phs') cpg─τ─►cp0
  decCopies-cpg-τ-fire {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} (there mem') gi =
      Par-τ-R ∅ES ⊤merge (decCopy l ph₀ d₀ id₀) (decCopies l cfg' phs')
        (decCopies-cpg-τ-fire {cfg'} {phs'} mem' gi)

  ------------------------------------------------------------------------
  -- LAYER 1d — spec-side `no-√C` and `¬DivC`.
  --   · `no-√C`: a NON-EMPTY Copy fold never `√`s (its head is a `Copy`
  --     loop, a react — `⦀⋆ [] = Skip` DOES, hence the `cons` shape; this
  --     is where `cfg≢[]` enters the walk).
  --   · `¬DivC`: every spec τ is one cell's `cpg → cp0` guard, strictly
  --     dropping the cpg-count measure `μV cpgN`, so no infinite τ chain.
  ------------------------------------------------------------------------

  -- a Copy leaf phase never `ret`s
  decCopy-noret : ∀ {cph d id r} → PTree.force (decCopy l cph d id) ≡ ret r → ⊥
  decCopy-noret {cp0}   = cp0-noret
  decCopy-noret {cp1 x} = cp1-noret
  decCopy-noret {cpg x} = cpg-noret

  -- a NON-EMPTY Copy fold never `ret`s (its head `Copy` loop never does)
  no-√C : ∀ {d id xs} {phs : PhV CPh ((d , id) ∷ xs)} {r}
        → PTree.force (decCopies l ((d , id) ∷ xs) phs) ≡ ret r → ⊥
  no-√C {phs = ph ∷ phs} eqf with Par-force-ret-inv ∅ES ⊤merge eqf
  ... | r₁ , r₂ , eqP , _ , _ = decCopy-noret {ph} eqP

  -- the cpg-count of a Copy phase (guard cells only)
  cpgN : CPh → ℕ
  cpgN cp0     = 0
  cpgN (cp1 _) = 0
  cpgN (cpg _) = 1

  -- a spec τ strictly drops the cpg-count measure
  μC-dec : ∀ {xs} {phs : PhV CPh xs} {d id} (mem : (d , id) ∈ xs) {x}
         → getPh phs mem ≡ cpg x
         → μV cpgN (setPh phs mem cp0) < μV cpgN phs
  μC-dec {phs = phs} mem {x} gcpg
    rewrite μV-drop cpgN phs mem (cpg x) cp0 1 gcpg refl =
    ≤-refl-suc (μV cpgN (setPh phs mem cp0))
    where
    -- n < n + 1
    ≤-refl-suc : ∀ n → n < n + 1
    ≤-refl-suc zero    = s≤s z≤n
    ≤-refl-suc (suc n) = s≤s (≤-refl-suc n)

  -- the Copy fold never diverges (cpg-count well-founded on `refl-τ`)
  ¬DivC-acc : ∀ {xs} (phs : PhV CPh xs) → Acc _<_ (μV cpgN phs)
            → ¬ Diverges (decCopies l xs phs)
  ¬DivC-acc phs (acc rs) dv with decCopies-τ (dv .Diverges.step)
  ... | d , id , mem , x , gcpg , Weq =
        ¬DivC-acc (setPh phs mem cp0) (rs (μC-dec {phs = phs} mem gcpg))
          (subst Diverges Weq (dv .Diverges.rest))

  ¬DivC : ∀ {xs} (phs : PhV CPh xs) → ¬ Diverges (decCopies l xs phs)
  ¬DivC phs = ¬DivC-acc phs (<-wellFounded (μV cpgN phs))

  ------------------------------------------------------------------------
  -- LAYER 2a — register-INSTANCE invariant `RInst` (the multi-instance
  -- form: every non-free buffer carries an instance actually IN the
  -- config) and mux reachability `Reach` (seeded at `initial`, closed
  -- under `⇒ᵢ`/`⇒ᵥ`).  Generalises 2a's singleton `RInst` by replacing
  -- the "= (dc , idc)" pinning with "∈ linkConfig l".
  ------------------------------------------------------------------------

  -- a message buffer's instance is configured (⊤ if free)
  MInst : MBuf → Set
  MInst free         = Poly.⊤ {0ℓ}
  MInst (hold d id _) = (d , id) ∈ linkConfig l
  MInst (grd d id _)  = (d , id) ∈ linkConfig l
  -- an ack buffer's instance is configured
  AInst : ABuf → Set
  AInst free       = Poly.⊤ {0ℓ}
  AInst (hold d id) = (d , id) ∈ linkConfig l
  AInst (grd d id)  = (d , id) ∈ linkConfig l
  -- all four buffers carry configured instances
  RInst : MuxState l → Set
  RInst st = MInst (tb st) × MInst (rb st) × AInst (sb st) × AInst (ab st)

  -- `RInst` at initial and along every edge (per-constructor bookkeeping)
  RInst-init : RInst (initial l)
  RInst-init = Poly.tt , Poly.tt , Poly.tt , Poly.tt
  RInst-step : ∀ {st st′} → st ⇒ᵢ st′ → RInst st → RInst st′
  RInst-step (sndmsg mem gph) (_ , mrb , asb , aab) = mem , mrb , asb , aab
  RInst-step (tx)             (mtb , _ , asb , aab) = mtb , mtb , asb , aab
  RInst-step (rcvmsg mem gph) ri                    = ri
  RInst-step (sndack mem gph) (mtb , mrb , _ , aab) = mtb , mrb , mem , aab
  RInst-step (ack)            (mtb , mrb , asb , _) = mtb , mrb , asb , asb
  RInst-step (rcvack mem gph) ri                    = ri
  RInst-step (gI mem gph)     ri                    = ri
  RInst-step (gO mem gph)     ri                    = ri
  RInst-step (gT)             (_ , mrb , asb , aab) = Poly.tt , mrb , asb , aab
  RInst-step (gRc)            (mtb , _ , asb , aab) = mtb , Poly.tt , asb , aab
  RInst-step (gSa)            (mtb , mrb , _ , aab) = mtb , mrb , Poly.tt , aab
  RInst-step (gR)             (mtb , mrb , asb , _) = mtb , mrb , asb , Poly.tt
  RInst-vis : ∀ {st e st′} → st ⇒ᵥ⟨ e ⟩ st′ → RInst st → RInst st′
  RInst-vis (input mem gph)  ri = ri
  RInst-vis (output mem gph) ri = ri

  -- mux reachability of link `l`, seeded at `initial`
  data Reach : MuxState l → Set where
    reach-init : Reach (initial l)
    reach-i    : ∀ {st st′} → Reach st → st ⇒ᵢ st′ → Reach st′
    reach-v    : ∀ {st e st′} → Reach st → st ⇒ᵥ⟨ e ⟩ st′ → Reach st′

  -- `RInst` holds along every reachable state
  reach-RInst : ∀ {st} → Reach st → RInst st
  reach-RInst reach-init       = RInst-init
  reach-RInst (reach-i r step) = RInst-step step (reach-RInst r)
  reach-RInst (reach-v r step) = RInst-vis step (reach-RInst r)

  ------------------------------------------------------------------------
  -- LAYER 2b — per-INSTANCE token / phase indicators.
  --
  -- The register indicators `holdM`/`holdA` are INSTANCE-AWARE (they count a
  -- register only when it holds THAT instance's token), because the four
  -- shared one-place buffers may hold a DIFFERENT instance's traffic.  The
  -- phase indicators `aOp`/`pOp`/`aIp`/`pIp` are payload-blind and identical
  -- to 2a's (they read a single cell's phase enum).  This is the key
  -- correction over 2a's `aM`/`aA`: at ≥2 instances a register token belongs
  -- to at most one instance, so the per-cell invariant must not read the
  -- register as if it were always the cell's own.
  ------------------------------------------------------------------------

  -- output-cell token (o1,o2 ⟺ hot) / phase (o1 only)
  aOp : OPh → ℕ
  aOp (o1 _) = 1
  aOp (o2 _) = 1
  aOp _      = 0
  pOp : OPh → ℕ
  pOp (o1 _) = 1
  pOp _      = 0
  -- input-cell token (i2 ⟺ hot) / phase (i1 only)
  aIp : IPh → ℕ
  aIp (i2 _) = 1
  aIp _      = 0
  pIp : IPh → ℕ
  pIp (i1 _) = 1
  pIp _      = 0

  -- message-buffer token for instance (d,id): 1 iff the buffer holds it
  holdM : Dir → IDs → MBuf → ℕ
  holdM d id (hold d′ id′ _) with d ≟ d′ | id ≟ id′
  ... | yes _ | yes _ = 1
  ... | _     | _     = 0
  holdM d id free       = 0
  holdM d id (grd _ _ _) = 0
  -- ack-buffer token for instance (d,id)
  holdA : Dir → IDs → ABuf → ℕ
  holdA d id (hold d′ id′) with d ≟ d′ | id ≟ id′
  ... | yes _ | yes _ = 1
  ... | _     | _     = 0
  holdA d id free      = 0
  holdA d id (grd _ _) = 0

  ------------------------------------------------------------------------
  -- Reduction lemmas for the instance-aware register indicators.
  ------------------------------------------------------------------------

  -- a register holding its own instance counts 1
  holdM-diag : ∀ {d id x} → holdM d id (hold d id x) ≡ 1
  holdM-diag {d} {id} rewrite ≟-diag d | ≟-diag id = refl
  holdA-diag : ∀ {d id} → holdA d id (hold d id) ≡ 1
  holdA-diag {d} {id} rewrite ≟-diag d | ≟-diag id = refl

  -- a register holding a DIFFERENT instance counts 0
  holdM-≢ : ∀ {d id d′ id′ x} → (d , id) ≢ (d′ , id′) → holdM d id (hold d′ id′ x) ≡ 0
  holdM-≢ {d} {id} {d′} {id′} ne with d ≟ d′ | id ≟ id′
  ... | yes refl | yes refl = ⊥-elim (ne refl)
  ... | no _     | _        = refl
  ... | yes _    | no _     = refl
  holdA-≢ : ∀ {d id d′ id′} → (d , id) ≢ (d′ , id′) → holdA d id (hold d′ id′) ≡ 0
  holdA-≢ {d} {id} {d′} {id′} ne with d ≟ d′ | id ≟ id′
  ... | yes refl | yes refl = ⊥-elim (ne refl)
  ... | no _     | _        = refl
  ... | yes _    | no _     = refl

  ------------------------------------------------------------------------
  -- Decidable equality on instances (Dir × IDs), assembled from the
  -- component `DecEq`s; used to split the moved instance from a read one.
  ------------------------------------------------------------------------

  -- decide equality of two instances
  _≟²_ : (a b : Dir × IDs) → Dec (a ≡ b)
  (d , id) ≟² (d′ , id′) with d ≟ d′ | id ≟ id′
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ { refl → ¬p refl }
  ... | yes _    | no ¬q    = no λ { refl → ¬q refl }

  ------------------------------------------------------------------------
  -- Phase-vector get/set algebra: diagonal read, instance-skew read, and
  -- membership uniqueness (all `Unique`-parametric where needed).
  ------------------------------------------------------------------------

  -- get-after-set at the SAME membership position
  get-set : ∀ {P xs} (ps : PhV P xs) {di} (m : di ∈ xs) (v : P)
          → getPh (setPh ps m v) m ≡ v
  get-set (ph ∷ ps) (here refl) v = refl
  get-set (ph ∷ ps) (there m)   v = get-set ps m v

  -- a set at a DIFFERENT-instance position leaves a read untouched
  getPh-inst≢ : ∀ {P xs} (ps : PhV P xs) {di dj} (mi : di ∈ xs) (mj : dj ∈ xs) (v : P)
              → di ≢ dj → getPh (setPh ps mj v) mi ≡ getPh ps mi
  getPh-inst≢ (ph ∷ ps) (here refl) (here refl) v ne = ⊥-elim (ne refl)
  getPh-inst≢ (ph ∷ ps) (here refl) (there mj) v ne = refl
  getPh-inst≢ (ph ∷ ps) (there mi) (here refl) v ne = refl
  getPh-inst≢ (ph ∷ ps) (there mi) (there mj) v ne = getPh-inst≢ ps mi mj v ne

  -- in a `Unique` config, two memberships of the SAME instance are equal
  mem-≡ : ∀ {xs : List (Dir × IDs)} → Unique xs → ∀ {di} (mi mj : di ∈ xs) → mi ≡ mj
  mem-≡ uniq (here refl) (here refl) = refl
  mem-≡ uniq (here refl) (there mj) = ⊥-elim (All.lookup (AllPairs.head uniq) mj refl)
  mem-≡ uniq (there mi) (here refl) = ⊥-elim (All.lookup (AllPairs.head uniq) mi refl)
  mem-≡ uniq (there mi) (there mj) = cong there (mem-≡ (AllPairs.tail uniq) mi mj)

  -- get-after-set read through ANOTHER same-instance membership (uses Unique)
  get-set-u : ∀ {P xs} {di} → Unique xs → (ps : PhV P xs) (mi mj : di ∈ xs) (v : P)
            → getPh (setPh ps mj v) mi ≡ v
  get-set-u uniq ps mi mj v =
    subst (λ m → getPh (setPh ps mj v) m ≡ v) (sym (mem-≡ uniq mi mj)) (get-set ps mj v)

  ------------------------------------------------------------------------
  -- LAYER 2c — the per-cell token invariant `InvM` and structural phase
  -- `phaseAt`, in COMPONENT form (`InvC`/`phaseC`) and lifted through a
  -- membership `mem`.  `InvM` is 2a's `Inv` re-`mem`'d with `holdM`/`holdA`
  -- in place of `aM`/`aA`; it says each instance's ack-return + forward
  -- tokens balance its input-cell token, and degenerates to 2a at a
  -- singleton config.
  ------------------------------------------------------------------------

  -- component token invariant for instance (d,id)
  InvC : Dir → IDs → IPh → OPh → MBuf → MBuf → ABuf → ABuf → Set
  InvC d id ip op tb rb sb ab =
    holdM d id tb + holdA d id ab + aOp op + holdM d id rb + holdA d id sb ≡ aIp ip
  -- component structural phase for instance (d,id)
  phaseC : Dir → IDs → IPh → OPh → MBuf → MBuf → ℕ
  phaseC d id ip op tb rb = pIp ip + holdM d id tb + pOp op + holdM d id rb

  -- lifted to a mux state at membership `mem`
  InvM : ∀ {d id} → (d , id) ∈ linkConfig l → MuxState l → Set
  InvM {d} {id} mem st =
    InvC d id (getPh (iph st) mem) (getPh (oph st) mem) (tb st) (rb st) (sb st) (ab st)
  phaseAt : ∀ {d id} → (d , id) ∈ linkConfig l → MuxState l → ℕ
  phaseAt {d} {id} mem st =
    phaseC d id (getPh (iph st) mem) (getPh (oph st) mem) (tb st) (rb st)

  ------------------------------------------------------------------------
  -- LAYER 2d — per-cell structural-phase preservation `phase-step`: every
  -- internal edge keeps each cell's `phaseAt` (the token merely moves inside
  -- that instance's own forward chain; a foreign instance's move is framed
  -- out by the `≟²` skew).  Only `sndmsg`/`tx`/`rcvmsg` do arithmetic; the
  -- ack-side / guard edges leave `phaseAt`'s reads untouched.
  ------------------------------------------------------------------------

  phase-step : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l)
             → ∀ {st st′} → st ⇒ᵢ st′ → phaseAt mem st ≡ phaseAt mem st′
  -- sndmsg: iph i1→i2 (moved cell), tb free→hold; token moves i1 ⇒ tb
  phase-step uniq {a} {b} mem (sndmsg {is} {os} {rb} {d = d} {id = id} {x = x} mem′ gph)
    with (a , b) ≟² (d , id)
  ... | yes refl rewrite mem-≡ uniq mem mem′ | gph | get-set is mem′ (i2 x) | holdM-diag {d} {id} {x} =
        ℕsolve 2 (λ P R → ℕcon 1 :⊕ ℕcon 0 :⊕ P :⊕ R :≡ ℕcon 0 :⊕ ℕcon 1 :⊕ P :⊕ R)
          refl (pOp (getPh os mem′)) (holdM d id rb)
  ... | no ne rewrite getPh-inst≢ is mem mem′ (i2 x) ne | holdM-≢ {x = x} ne = refl
  -- tx: tb hold→grd, rb free→hold; token moves tb ⇒ rb
  phase-step uniq {a} {b} mem (tx {is} {os} {d = d} {id = id} {x = x})
    with (a , b) ≟² (d , id)
  ... | yes refl rewrite holdM-diag {d} {id} {x} =
        ℕsolve 2 (λ P I → I :⊕ ℕcon 1 :⊕ P :⊕ ℕcon 0 :≡ I :⊕ ℕcon 0 :⊕ P :⊕ ℕcon 1)
          refl (pOp (getPh os mem)) (pIp (getPh is mem))
  ... | no ne rewrite holdM-≢ {x = x} ne = refl
  -- rcvmsg: oph o0→o1 (moved cell), rb hold→grd; token moves rb ⇒ output cell
  phase-step uniq {a} {b} mem (rcvmsg {is} {os} {tb} {d = d} {id = id} {x = x} mem′ gph)
    with (a , b) ≟² (d , id)
  ... | yes refl rewrite mem-≡ uniq mem mem′ | gph | get-set os mem′ (o1 x) | holdM-diag {d} {id} {x} =
        ℕsolve 2 (λ I T → I :⊕ T :⊕ ℕcon 0 :⊕ ℕcon 1 :≡ I :⊕ T :⊕ ℕcon 1 :⊕ ℕcon 0)
          refl (pIp (getPh is mem′)) (holdM d id tb)
  ... | no ne rewrite getPh-inst≢ os mem mem′ (o1 x) ne | holdM-≢ {x = x} ne = refl
  -- rcvack: iph i2→ig (moved cell), ab hold→grd (not in phaseAt); enum-preserving
  phase-step uniq {a} {b} mem (rcvack {is} {d = d} {id = id} {x = x} mem′ gph)
    with (a , b) ≟² (d , id)
  ... | yes refl rewrite mem-≡ uniq mem mem′ | gph | get-set is mem′ (ig x) = refl
  ... | no ne rewrite getPh-inst≢ is mem mem′ (ig x) ne = refl
  -- gI: iph ig→i0 (moved cell); enum-preserving
  phase-step uniq {a} {b} mem (gI {is} {d = d} {id = id} {x = x} mem′ gph)
    with (a , b) ≟² (d , id)
  ... | yes refl rewrite mem-≡ uniq mem mem′ | gph | get-set is mem′ i0 = refl
  ... | no ne rewrite getPh-inst≢ is mem mem′ i0 ne = refl
  -- gO: oph og→o0 (moved cell); enum-preserving
  phase-step uniq {a} {b} mem (gO {os = os} {d = d} {id = id} {x = x} mem′ gph)
    with (a , b) ≟² (d , id)
  ... | yes refl rewrite mem-≡ uniq mem mem′ | gph | get-set os mem′ o0 = refl
  ... | no ne rewrite getPh-inst≢ os mem mem′ o0 ne = refl
  -- sndack: oph o2→og (moved cell), sb free→hold (not in phaseAt); enum-preserving
  phase-step uniq {a} {b} mem (sndack {os = os} {d = d} {id = id} {x = x} mem′ gph)
    with (a , b) ≟² (d , id)
  ... | yes refl rewrite mem-≡ uniq mem mem′ | gph | get-set os mem′ (og x) = refl
  ... | no ne rewrite getPh-inst≢ os mem mem′ (og x) ne = refl
  -- register-only guard/ack edges: phaseAt's reads are literally unchanged
  phase-step uniq mem (ack)  = refl
  phase-step uniq mem (gSa)  = refl
  phase-step uniq mem (gR)   = refl
  phase-step uniq mem (gT)   = refl
  phase-step uniq mem (gRc)  = refl

  ------------------------------------------------------------------------
  -- LAYER 2e — the per-cell token invariant `InvM` is preserved along every
  -- edge and seeded at `initial`.  The diagonal (moved instance = read cell)
  -- IS 2a's single-cell `Inv-step` arithmetic (re-`mem`'d via `get-set-u`/
  -- `get-mem-u`/`holdM-diag`/`holdA-diag`); the skew (foreign instance) frames
  -- the reads out (`getPh-inst≢`/`holdM-≢`/`holdA-≢`), leaving `inv` intact.
  ------------------------------------------------------------------------

  -- suc is injective (for the two token-drop edges rcvack / rcvmsg)
  sucinj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  sucinj refl = refl

  -- read a cell through ANOTHER same-instance membership (uses Unique)
  get-mem-u : ∀ {P xs} {di} {w : P} → Unique xs → (ps : PhV P xs) (mi mj : di ∈ xs)
            → getPh ps mj ≡ w → getPh ps mi ≡ w
  get-mem-u uniq ps mi mj eq = trans (cong (λ m → getPh ps m) (mem-≡ uniq mi mj)) eq

  -- the all-home vectors read `i0` / `o0` at every position
  getPh-homeI : ∀ xs {di} (m : di ∈ xs) → getPh (homeI xs) m ≡ i0
  getPh-homeI (x ∷ xs) (here refl) = refl
  getPh-homeI (x ∷ xs) (there m)   = getPh-homeI xs m
  getPh-homeO : ∀ xs {di} (m : di ∈ xs) → getPh (homeO xs) m ≡ o0
  getPh-homeO (x ∷ xs) (here refl) = refl
  getPh-homeO (x ∷ xs) (there m)   = getPh-homeO xs m

  -- `InvM` at initial (all-home / all-free): every count is 0
  InvM-init : ∀ {a b} (mem : (a , b) ∈ linkConfig l) → InvM mem (initial l)
  InvM-init mem rewrite getPh-homeI (linkConfig l) mem | getPh-homeO (linkConfig l) mem = refl

  -- `InvM` preserved along every internal edge
  InvM-step : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l)
            → ∀ {st st′} → st ⇒ᵢ st′ → InvM mem st → InvM mem st′
  -- sndmsg: iph i1→i2 (token 0), tb free→hold (token +1); net conserved
  InvM-step uniq {a} {b} mem (sndmsg {is} {os} {rb} {sb} {ab} {d = d} {id = id} {x = x} mem′ gph) inv
    with (a , b) ≟² (d , id)
  ... | yes refl rewrite holdM-diag {d} {id} {x} | get-set-u uniq is mem mem′ (i2 x) =
        cong suc (trans inv (cong aIp (get-mem-u uniq is mem mem′ gph)))
  ... | no ne rewrite holdM-≢ {x = x} ne | getPh-inst≢ is mem mem′ (i2 x) ne = inv
  -- tx: tb hold→grd (token −1), rb free→hold (token +1); token slides
  InvM-step uniq {a} {b} mem (tx {is} {os} {sb = sb} {ab = ab} {d = d} {id = id} {x = x}) inv =
    trans (ℕsolve 4 (λ H A O S → ℕcon 0 :⊕ A :⊕ O :⊕ H :⊕ S :≡ H :⊕ A :⊕ O :⊕ ℕcon 0 :⊕ S)
             refl (holdM a b (hold d id x)) (holdA a b ab) (aOp (getPh os mem)) (holdA a b sb)) inv
  -- rcvmsg: oph o0→o1 (token +1 aOp), rb hold→grd (token −1); token slides
  InvM-step uniq {a} {b} mem (rcvmsg {is} {os} {tb} {sb} {ab} {d = d} {id = id} {x = x} mem′ gph) inv
    with (a , b) ≟² (d , id)
  ... | yes refl rewrite get-set-u uniq os mem mem′ (o1 x) =
        trans (ℕsolve 3 (λ T A S → T :⊕ A :⊕ ℕcon 1 :⊕ ℕcon 0 :⊕ S :≡ T :⊕ A :⊕ ℕcon 0 :⊕ ℕcon 1 :⊕ S)
                 refl (holdM d id tb) (holdA d id ab) (holdA d id sb))
          (subst (λ h → holdM d id tb + holdA d id ab + 0 + h + holdA d id sb ≡ aIp (getPh is mem))
                 (holdM-diag {d} {id} {x})
                 (subst (λ o → holdM d id tb + holdA d id ab + o + holdM d id (hold d id x) + holdA d id sb ≡ aIp (getPh is mem))
                        (cong aOp (get-mem-u uniq os mem mem′ gph)) inv))
  ... | no ne rewrite getPh-inst≢ os mem mem′ (o1 x) ne =
          subst (λ h → holdM a b tb + holdA a b ab + aOp (getPh os mem) + h + holdA a b sb ≡ aIp (getPh is mem))
                (holdM-≢ {x = x} ne) inv
  -- sndack: oph o2→og (token −1 aOp), sb free→hold (token +1); token slides
  InvM-step uniq {a} {b} mem (sndack {is} {os} {tb} {rb} {ab} {d = d} {id = id} {x = x} mem′ gph) inv
    with (a , b) ≟² (d , id)
  ... | yes refl rewrite get-set-u uniq os mem mem′ (og x) | holdA-diag {d} {id} =
        trans (ℕsolve 3 (λ T A R → T :⊕ A :⊕ ℕcon 0 :⊕ R :⊕ ℕcon 1 :≡ T :⊕ A :⊕ ℕcon 1 :⊕ R :⊕ ℕcon 0)
                 refl (holdM d id tb) (holdA d id ab) (holdM d id rb))
          (subst (λ o → holdM d id tb + holdA d id ab + o + holdM d id rb + holdA d id free ≡ aIp (getPh is mem))
                 (cong aOp (get-mem-u uniq os mem mem′ gph)) inv)
  ... | no ne rewrite getPh-inst≢ os mem mem′ (og x) ne | holdA-≢ ne = inv
  -- ack: sb hold→grd (token −1), ab free→hold (token +1); token slides
  InvM-step uniq {a} {b} mem (ack {is} {os} {tb} {rb} {d = d} {id = id}) inv =
    trans (ℕsolve 4 (λ T HA O R → T :⊕ HA :⊕ O :⊕ R :⊕ ℕcon 0 :≡ T :⊕ ℕcon 0 :⊕ O :⊕ R :⊕ HA)
             refl (holdM a b tb) (holdA a b (hold d id)) (aOp (getPh os mem)) (holdM a b rb)) inv
  -- rcvack: iph i2→ig (token −1 aIp), ab hold→grd (token −1); token consumed
  InvM-step uniq {a} {b} mem (rcvack {is} {os} {tb} {rb} {sb} {d = d} {id = id} {x = x} mem′ gph) inv
    with (a , b) ≟² (d , id)
  ... | yes refl rewrite get-set-u uniq is mem mem′ (ig x) =
        sucinj (trans (ℕsolve 4 (λ t o r s → ℕcon 1 :⊕ (t :⊕ ℕcon 0 :⊕ o :⊕ r :⊕ s) :≡ t :⊕ ℕcon 1 :⊕ o :⊕ r :⊕ s)
                         refl (holdM d id tb) (aOp (getPh os mem)) (holdM d id rb) (holdA d id sb))
                 (trans (subst (λ h → holdM d id tb + h + aOp (getPh os mem) + holdM d id rb + holdA d id sb ≡ aIp (getPh is mem))
                               (holdA-diag {d} {id}) inv)
                        (cong aIp (get-mem-u uniq is mem mem′ gph))))
  ... | no ne rewrite getPh-inst≢ is mem mem′ (ig x) ne =
          subst (λ h → holdM a b tb + h + aOp (getPh os mem) + holdM a b rb + holdA a b sb ≡ aIp (getPh is mem))
                (holdA-≢ ne) inv
  -- gI: iph ig→i0 (both aIp 0); frame
  InvM-step uniq {a} {b} mem (gI {is} {os} {d = d} {id = id} {x = x} mem′ gph) inv
    with (a , b) ≟² (d , id)
  ... | yes refl rewrite get-set-u uniq is mem mem′ i0 =
        trans inv (cong aIp (get-mem-u uniq is mem mem′ gph))
  ... | no ne rewrite getPh-inst≢ is mem mem′ i0 ne = inv
  -- gO: oph og→o0 (both aOp 0); frame
  InvM-step uniq {a} {b} mem (gO {is} {os} {tb = tb} {rb = rb} {sb = sb} {ab = ab} {d = d} {id = id} {x = x} mem′ gph) inv
    with (a , b) ≟² (d , id)
  ... | yes refl rewrite get-set-u uniq os mem mem′ o0 =
        subst (λ o → holdM d id tb + holdA d id ab + o + holdM d id rb + holdA d id sb ≡ aIp (getPh is mem))
              (cong aOp (get-mem-u uniq os mem mem′ gph)) inv
  ... | no ne rewrite getPh-inst≢ os mem mem′ o0 ne = inv
  -- register guard restarts: grd→free (both token 0); frame
  InvM-step uniq mem (gT)  inv = inv
  InvM-step uniq mem (gRc) inv = inv
  InvM-step uniq mem (gSa) inv = inv
  InvM-step uniq mem (gR)  inv = inv

  -- `InvM` preserved along both visible edges (input keeps aIp 0, output keeps aOp 1)
  InvM-vis : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l)
           → ∀ {st e st′} → st ⇒ᵥ⟨ e ⟩ st′ → InvM mem st → InvM mem st′
  InvM-vis uniq {a} {b} mem (input {is} {os} {d = d} {id = id} {x = x} mem′ gph) inv
    with (a , b) ≟² (d , id)
  ... | yes refl rewrite get-set-u uniq is mem mem′ (i1 x) =
        trans inv (cong aIp (get-mem-u uniq is mem mem′ gph))
  ... | no ne rewrite getPh-inst≢ is mem mem′ (i1 x) ne = inv
  InvM-vis uniq {a} {b} mem (output {is} {os} {tb = tb} {rb = rb} {sb = sb} {ab = ab} {d = d} {id = id} {x = x} mem′ gph) inv
    with (a , b) ≟² (d , id)
  ... | yes refl rewrite get-set-u uniq os mem mem′ (o2 x) =
        subst (λ o → holdM d id tb + holdA d id ab + o + holdM d id rb + holdA d id sb ≡ aIp (getPh is mem))
              (cong aOp (get-mem-u uniq os mem mem′ gph)) inv
  ... | no ne rewrite getPh-inst≢ os mem mem′ (o2 x) ne = inv

  -- `InvM` holds at every reachable state, at every cell
  reach-InvM : (uniq : Unique (linkConfig l)) → ∀ {st} → Reach st
             → ∀ {a b} (mem : (a , b) ∈ linkConfig l) → InvM mem st
  reach-InvM uniq reach-init       mem = InvM-init mem
  reach-InvM uniq (reach-i r step) mem = InvM-step uniq mem step (reach-InvM uniq r mem)
  reach-InvM uniq (reach-v r step) mem = InvM-vis uniq mem step (reach-InvM uniq r mem)

  ------------------------------------------------------------------------
  -- LAYER 3a — arithmetic / view scaffolding for the liveness drains.
  ------------------------------------------------------------------------

  -- a sum of two ℕ is 0 ⇒ both are 0
  sum0 : ∀ a b → a + b ≡ 0 → (a ≡ 0) × (b ≡ 0)
  sum0 zero    b eq = refl , eq
  sum0 (suc a) b ()
  -- the input-cell token count is 0 or 1
  aIp-01 : ∀ ip → (aIp ip ≡ 0) ⊎ (aIp ip ≡ 1)
  aIp-01 i0     = inj₁ refl
  aIp-01 (i1 _) = inj₁ refl
  aIp-01 (i2 _) = inj₂ refl
  aIp-01 (ig _) = inj₁ refl
  -- phase-1 output reads off `o1`
  pOp-o1 : ∀ op → pOp op ≡ 1 → Σ[ v ∈ Data ] op ≡ o1 v
  pOp-o1 (o1 v) _ = v , refl
  pOp-o1 o0     ()
  pOp-o1 (o2 _) ()
  pOp-o1 (og _) ()
  -- output token 0 ⇒ home or guard
  aOp0-o0og : ∀ op → aOp op ≡ 0 → (op ≡ o0) ⊎ (Σ[ v ∈ Data ] op ≡ og v)
  aOp0-o0og o0     _ = inj₁ refl
  aOp0-o0og (og v) _ = inj₂ (v , refl)
  aOp0-o0og (o1 _) ()
  aOp0-o0og (o2 _) ()
  -- input phase view at a cell
  data IViewAt {a b} (mem : (a , b) ∈ linkConfig l) (st : MuxState l) : Set where
    vI0 : getPh (iph st) mem ≡ i0 → IViewAt mem st
    vI1 : ∀ y → getPh (iph st) mem ≡ i1 y → IViewAt mem st
    vI2 : ∀ y → getPh (iph st) mem ≡ i2 y → IViewAt mem st
    vIg : ∀ y → getPh (iph st) mem ≡ ig y → IViewAt mem st
  whichIV : ∀ {a b} (mem : (a , b) ∈ linkConfig l) (st : MuxState l) → IViewAt mem st
  whichIV mem st with getPh (iph st) mem in eq
  ... | i0   = vI0 eq
  ... | i1 y = vI1 y eq
  ... | i2 y = vI2 y eq
  ... | ig y = vIg y eq

  ------------------------------------------------------------------------
  -- A receiver holding instance `mem'`'s token forces that cell's OUTPUT
  -- side home/guard (its `aOp` is 0), by `InvM mem'` (token ≤ 1).  Then the
  -- pipeline move is `rcvmsg` (o0) or the guard `gO` (og).
  ------------------------------------------------------------------------

  -- receiver-hold ⇒ that cell's output token is 0
  rbhold-aOp0 : ∀ {d′ id′} (mem′ : (d′ , id′) ∈ linkConfig l) {is os tb sb ab x}
              → InvM mem′ (mkMux is os tb (hold d′ id′ x) sb ab) → aOp (getPh os mem′) ≡ 0
  rbhold-aOp0 {d′} {id′} mem′ {is} {os} {tb} {sb} {ab} {x} inv
    with aIp-01 (getPh is mem′)
  ... | inj₁ z = ⊥-elim (case trans step z of λ ())
    where step : suc (holdM d′ id′ tb + holdA d′ id′ ab + aOp (getPh os mem′) + holdA d′ id′ sb)
               ≡ aIp (getPh is mem′)
          step = trans (ℕsolve 4 (λ T A O S → ℕcon 1 :⊕ (T :⊕ A :⊕ O :⊕ S)
                                            :≡ T :⊕ A :⊕ O :⊕ ℕcon 1 :⊕ S)
                          refl (holdM d′ id′ tb) (holdA d′ id′ ab) (aOp (getPh os mem′)) (holdA d′ id′ sb))
                 (subst (λ h → holdM d′ id′ tb + holdA d′ id′ ab + aOp (getPh os mem′) + h + holdA d′ id′ sb
                             ≡ aIp (getPh is mem′)) (holdM-diag {d′} {id′} {x}) inv)
  ... | inj₂ o =
        proj₂ (sum0 (holdM d′ id′ tb + holdA d′ id′ ab) (aOp (getPh os mem′))
                (proj₁ (sum0 (holdM d′ id′ tb + holdA d′ id′ ab + aOp (getPh os mem′)) (holdA d′ id′ sb)
                  (sucinj (trans step o)))))
    where step : suc (holdM d′ id′ tb + holdA d′ id′ ab + aOp (getPh os mem′) + holdA d′ id′ sb)
               ≡ aIp (getPh is mem′)
          step = trans (ℕsolve 4 (λ T A O S → ℕcon 1 :⊕ (T :⊕ A :⊕ O :⊕ S)
                                            :≡ T :⊕ A :⊕ O :⊕ ℕcon 1 :⊕ S)
                          refl (holdM d′ id′ tb) (holdA d′ id′ ab) (aOp (getPh os mem′)) (holdA d′ id′ sb))
                 (subst (λ h → holdM d′ id′ tb + holdA d′ id′ ab + aOp (getPh os mem′) + h + holdA d′ id′ sb
                             ≡ aIp (getPh is mem′)) (holdM-diag {d′} {id′} {x}) inv)

  -- setting some cell to `v ≢ i0` keeps every cell out of `i0` (used by the
  -- liveness drains to certify a token slide never lands a cell home)
  set-≢i0 : (uniq : Unique (linkConfig l)) (ps : PhV IPh (linkConfig l))
          → ∀ {a b c d} (mem : (a , b) ∈ linkConfig l) (memk : (c , d) ∈ linkConfig l) {v}
          → v ≢ i0 → getPh ps memk ≢ i0 → getPh (setPh ps mem v) memk ≢ i0
  set-≢i0 uniq ps {a} {b} {c} {d} mem memk {v} v≢ ne with (c , d) ≟² (a , b)
  ... | yes refl = λ eq → v≢ (trans (sym (get-set-u uniq ps memk mem v)) eq)
  ... | no nn    = λ eq → ne (trans (sym (getPh-inst≢ ps memk mem v nn)) eq)

  ------------------------------------------------------------------------
  -- LAYER 3b — the MULTI-INSTANCE liveness drain step `liveB-i`.
  --
  -- From any reachable state with instance `mem` in-flight (`phaseAt mem = 1`)
  -- but not yet output-ready (`oph mem ≠ o1`), SOME internal move is enabled.
  -- Priority-scans the shared forward pipeline most-advanced-first (rb, then
  -- tb, then `mem`'s input cell), draining whatever OTHER instance's token
  -- blocks `mem` — the register move exists for the blocking instance by its
  -- own `RInst`/`InvM`.  Mirrors 2a's `liveB` but over the shared registers.
  ------------------------------------------------------------------------

  -- (`liveB-i` also CERTIFIES its move keeps every cell out of `i0` — it
  -- never fires `gI` — so a forward drain preserves foreign `cpg` cells.)
  liveB-i : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l)
          → (st : MuxState l) → Reach st → phaseAt mem st ≡ 1
          → (∀ v → getPh (oph st) mem ≢ o1 v)
          → Σ[ st′ ∈ MuxState l ] (st ⇒ᵢ st′)
              × (∀ {c d} (memk : (c , d) ∈ linkConfig l) → getPh (iph st) memk ≢ i0 → getPh (iph st′) memk ≢ i0)
  -- receiver at guard: restart it
  liveB-i uniq mem (mkMux is os tb (grd d′ id′ x′) sb ab) r ph o≢ = _ , gRc , λ {_} {_} memk ne → ne
  -- receiver holding (another) instance: advance it (rcvmsg / gO)
  liveB-i uniq mem (mkMux is os tb (hold d′ id′ x′) sb ab) r ph o≢ =
    case aOp0-o0og (getPh os mem′)
           (rbhold-aOp0 mem′ {is = is} {os = os} {tb = tb} {sb = sb} {ab = ab} {x = x′}
             (reach-InvM uniq r mem′)) of λ
      { (inj₁ oeq)       → _ , rcvmsg mem′ oeq , λ {_} {_} memk ne → ne
      ; (inj₂ (v , oeq)) → _ , gO mem′ oeq , λ {_} {_} memk ne → ne }
    where mem′ = proj₁ (proj₂ (reach-RInst r))
  -- receiver free, transmitter at guard: restart it
  liveB-i uniq mem (mkMux is os (grd d′ id′ x′) free sb ab) r ph o≢ = _ , gT , λ {_} {_} memk ne → ne
  -- receiver free, transmitter holding: slide it forward (tx)
  liveB-i uniq mem (mkMux is os (hold d′ id′ x′) free sb ab) r ph o≢ = _ , tx , λ {_} {_} memk ne → ne
  -- receiver + transmitter free: mem's token must be at i1; fire sndmsg
  liveB-i uniq {a} {b} mem (mkMux is os free free sb ab) r ph o≢
    with whichIV mem (mkMux is os free free sb ab)
  ... | vI1 y ieq = _ , sndmsg mem ieq , λ {_} {_} memk → set-≢i0 uniq is mem memk (λ ())
  ... | vI0 ieq   = ⊥-elim (freeBad (cong pIp ieq))
    where freeBad : pIp (getPh is mem) ≡ 0 → ⊥
          freeBad piz with pOp-o1 (getPh os mem)
            (trans (ℕsolve 1 (λ P → P :≡ P :⊕ ℕcon 0) refl (pOp (getPh os mem)))
              (subst (λ p → p + holdM a b free + pOp (getPh os mem) + holdM a b free ≡ 1) piz ph))
          ... | v , oeq = o≢ v oeq
  ... | vI2 y ieq = ⊥-elim (freeBad (cong pIp ieq))
    where freeBad : pIp (getPh is mem) ≡ 0 → ⊥
          freeBad piz with pOp-o1 (getPh os mem)
            (trans (ℕsolve 1 (λ P → P :≡ P :⊕ ℕcon 0) refl (pOp (getPh os mem)))
              (subst (λ p → p + holdM a b free + pOp (getPh os mem) + holdM a b free ≡ 1) piz ph))
          ... | v , oeq = o≢ v oeq
  ... | vIg y ieq = ⊥-elim (freeBad (cong pIp ieq))
    where freeBad : pIp (getPh is mem) ≡ 0 → ⊥
          freeBad piz with pOp-o1 (getPh os mem)
            (trans (ℕsolve 1 (λ P → P :≡ P :⊕ ℕcon 0) refl (pOp (getPh os mem)))
              (subst (λ p → p + holdM a b free + pOp (getPh os mem) + holdM a b free ≡ 1) piz ph))
          ... | v , oeq = o≢ v oeq

  ------------------------------------------------------------------------
  -- LAYER 3c — the phase-A liveness drain step `liveA-i` (symmetric to
  -- `liveB-i` over the ACK-return pipeline).  From a reachable state with
  -- instance `mem` at phase 0 but input cell not yet home (`iph mem ≠ i0`),
  -- SOME internal move is enabled: drain the shared ack registers (ab, sb)
  -- of whatever instance blocks, else advance `mem`'s own ack-return
  -- (`sndack` at o2 / guard `gI` at ig).
  ------------------------------------------------------------------------

  -- input token 1 ⇒ reads off `i2`
  aIp1-i2 : ∀ ip → aIp ip ≡ 1 → Σ[ v ∈ Data ] ip ≡ i2 v
  aIp1-i2 (i2 v) _ = v , refl
  aIp1-i2 i0     ()
  aIp1-i2 (i1 _) ()
  aIp1-i2 (ig _) ()
  -- output token 1 with phase 0 ⇒ reads off `o2`
  aOp1-pOp0-o2 : ∀ op → aOp op ≡ 1 → pOp op ≡ 0 → Σ[ v ∈ Data ] op ≡ o2 v
  aOp1-pOp0-o2 (o2 v) _ _  = v , refl
  aOp1-pOp0-o2 (o1 _) _ ()
  aOp1-pOp0-o2 o0     () _
  aOp1-pOp0-o2 (og _) () _

  -- ack-buffer holding instance `mem''`'s token forces that cell's input `i2`
  abhold-aIp1 : ∀ {d′ id′} (mem′′ : (d′ , id′) ∈ linkConfig l) {is os tb rb sb}
              → InvM mem′′ (mkMux is os tb rb sb (hold d′ id′)) → aIp (getPh is mem′′) ≡ 1
  abhold-aIp1 {d′} {id′} mem′′ {is} {os} {tb} {rb} {sb} inv
    with aIp-01 (getPh is mem′′)
  ... | inj₂ o = o
  ... | inj₁ z = ⊥-elim (case trans step z of λ ())
    where step : suc (holdM d′ id′ tb + aOp (getPh os mem′′) + holdM d′ id′ rb + holdA d′ id′ sb)
               ≡ aIp (getPh is mem′′)
          step = trans (ℕsolve 4 (λ T O R S → ℕcon 1 :⊕ (T :⊕ O :⊕ R :⊕ S)
                                            :≡ T :⊕ ℕcon 1 :⊕ O :⊕ R :⊕ S)
                          refl (holdM d′ id′ tb) (aOp (getPh os mem′′)) (holdM d′ id′ rb) (holdA d′ id′ sb))
                 (subst (λ h → holdM d′ id′ tb + h + aOp (getPh os mem′′) + holdM d′ id′ rb + holdA d′ id′ sb
                             ≡ aIp (getPh is mem′′)) (holdA-diag {d′} {id′}) inv)

  -- (`liveA-i` also CERTIFIES its move keeps every FOREIGN cell out of `i0`
  -- — its only `gI` is at the TARGET `mem` — so a phase-A drain preserves
  -- every other `cpg` cell's `iph ≢ i0`.)
  liveA-i : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l)
          → (st : MuxState l) → Reach st → phaseAt mem st ≡ 0
          → getPh (iph st) mem ≢ i0
          → Σ[ st′ ∈ MuxState l ] (st ⇒ᵢ st′)
              × (∀ {c d} (memk : (c , d) ∈ linkConfig l) → (c , d) ≢ (a , b) → getPh (iph st) memk ≢ i0 → getPh (iph st′) memk ≢ i0)
  -- rcv-ack buffer at guard: restart it
  liveA-i uniq mem (mkMux is os tb rb sb (grd d′ id′)) r ph i≢ = _ , gR , λ {_} {_} memk ex ne → ne
  -- rcv-ack buffer holding (another) instance: return it (rcvack)
  liveA-i uniq mem (mkMux is os tb rb sb (hold d′ id′)) r ph i≢ =
    case aIp1-i2 (getPh is mem′′)
           (abhold-aIp1 mem′′ {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb}
             (reach-InvM uniq r mem′′)) of λ
      { (v , ieq) → _ , rcvack mem′′ ieq , λ {_} {_} memk ex ne → set-≢i0 uniq is mem′′ memk (λ ()) ne }
    where mem′′ = proj₂ (proj₂ (proj₂ (reach-RInst r)))
  -- rcv-ack free, snd-ack at guard: restart it
  liveA-i uniq mem (mkMux is os tb rb (grd d′ id′) free) r ph i≢ = _ , gSa , λ {_} {_} memk ex ne → ne
  -- rcv-ack free, snd-ack holding: hand off the ack (ack)
  liveA-i uniq mem (mkMux is os tb rb (hold d′ id′) free) r ph i≢ = _ , ack , λ {_} {_} memk ex ne → ne
  -- ack registers free: advance mem's own ack-return (gI at ig / sndack at o2)
  liveA-i uniq {a} {b} mem (mkMux is os tb rb free free) r ph i≢
    with whichIV mem (mkMux is os tb rb free free)
  ... | vI0 ieq   = ⊥-elim (i≢ ieq)
  ... | vI1 y ieq = ⊥-elim (case subst (λ w → pIp w + holdM a b tb + pOp (getPh os mem) + holdM a b rb ≡ 0) ieq ph of λ ())
  ... | vIg y ieq = _ , gI mem ieq , λ {_} {_} memk ex ne eq → ne (trans (sym (getPh-inst≢ is memk mem i0 ex)) eq)
  ... | vI2 y ieq = case aOp1-pOp0-o2 (getPh os mem) aOp≡1 pOp≡0 of λ { (v , oeq) → _ , sndack mem oeq , λ {_} {_} memk ex ne → ne }
    where
    inv : InvM mem (mkMux is os tb rb free free)
    inv = reach-InvM uniq r mem
    -- from phase 0 (pIp i2 = 0): the forward register/pOp contributions vanish
    ph0 : holdM a b tb + pOp (getPh os mem) + holdM a b rb ≡ 0
    ph0 = trans (ℕsolve 3 (λ T P R → T :⊕ P :⊕ R :≡ ℕcon 0 :⊕ T :⊕ P :⊕ R) refl
                   (holdM a b tb) (pOp (getPh os mem)) (holdM a b rb))
          (subst (λ w → pIp w + holdM a b tb + pOp (getPh os mem) + holdM a b rb ≡ 0) ieq ph)
    tb≡0 : holdM a b tb ≡ 0
    tb≡0 = proj₁ (sum0 (holdM a b tb) (pOp (getPh os mem)) (proj₁ (sum0 (holdM a b tb + pOp (getPh os mem)) (holdM a b rb) ph0)))
    pOp≡0 : pOp (getPh os mem) ≡ 0
    pOp≡0 = proj₂ (sum0 (holdM a b tb) (pOp (getPh os mem)) (proj₁ (sum0 (holdM a b tb + pOp (getPh os mem)) (holdM a b rb) ph0)))
    rb≡0 : holdM a b rb ≡ 0
    rb≡0 = proj₂ (sum0 (holdM a b tb + pOp (getPh os mem)) (holdM a b rb) ph0)
    -- InvM at i2 with both message registers empty forces the output token 1
    inv1 : holdM a b tb + 0 + aOp (getPh os mem) + holdM a b rb + 0 ≡ 1
    inv1 = subst (λ w → holdM a b tb + 0 + aOp (getPh os mem) + holdM a b rb + 0 ≡ aIp w) ieq inv
    aOp≡1 : aOp (getPh os mem) ≡ 1
    aOp≡1 = trans (ℕsolve 1 (λ O → O :≡ O :⊕ ℕcon 0 :⊕ ℕcon 0) refl (aOp (getPh os mem)))
              (subst (λ rr → 0 + 0 + aOp (getPh os mem) + rr + 0 ≡ 1) rb≡0
                (subst (λ tt′ → tt′ + 0 + aOp (getPh os mem) + holdM a b rb + 0 ≡ 1) tb≡0 inv1))

  ------------------------------------------------------------------------
  -- LAYER 3d — internal runs `_⇒ᵢ*_`, their realisation as τ* runs of the
  -- decode (via `Fold.fire-⇒ᵢ`), and the two μ-well-founded drains
  -- `drainA` / `drainB` looping the liveness engines to input-home /
  -- output-ready.  Per-cell `phaseAt` is preserved along each drain step
  -- (`phase-step`), so the loop invariant survives the recursion.
  ------------------------------------------------------------------------

  -- an internal run
  infix 4 _⇒ᵢ*_
  data _⇒ᵢ*_ : MuxState l → MuxState l → Set where
    ε   : ∀ {st} → st ⇒ᵢ* st
    _◅_ : ∀ {st st′ st″} → st ⇒ᵢ st′ → st′ ⇒ᵢ* st″ → st ⇒ᵢ* st″

  -- reachability along an internal run
  reach-i* : ∀ {st st-d} → Reach st → st ⇒ᵢ* st-d → Reach st-d
  reach-i* r ε             = r
  reach-i* r (step ◅ path) = reach-i* (reach-i r step) path

  -- realise an internal run as a τ* run of the decode
  real-⇒ᵢ* : (uniq : Unique (linkConfig l)) → ∀ {st st-d} → st ⇒ᵢ* st-d → ⟦ st ⟧ ─[τ*]─► ⟦ st-d ⟧
  real-⇒ᵢ* uniq ε             = τ*-refl
  real-⇒ᵢ* uniq (step ◅ path) = τ*-step (fire-⇒ᵢ l uniq step) (real-⇒ᵢ* uniq path)

  -- decide input-home / output-ready at a cell
  decI0 : ∀ ip → (ip ≡ i0) ⊎ (ip ≢ i0)
  decI0 i0     = inj₁ refl
  decI0 (i1 x) = inj₂ λ ()
  decI0 (i2 x) = inj₂ λ ()
  decI0 (ig x) = inj₂ λ ()
  decO1 : ∀ op → (Σ[ v ∈ Data ] op ≡ o1 v) ⊎ (∀ v → op ≢ o1 v)
  decO1 o0     = inj₂ λ v ()
  decO1 (o1 v) = inj₁ (v , refl)
  decO1 (o2 v) = inj₂ λ v ()
  decO1 (og v) = inj₂ λ v ()

  -- drain a phase-0 cell to input-home (iph = i0)
  drainA-acc : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l)
             → (st : MuxState l) → Reach st → phaseAt mem st ≡ 0 → Acc _<_ (μ st)
             → Σ[ st-d ∈ MuxState l ] ((st ⇒ᵢ* st-d) × (getPh (iph st-d) mem ≡ i0)
                 × (∀ {c d} (memk : (c , d) ∈ linkConfig l) → (c , d) ≢ (a , b) → getPh (iph st) memk ≢ i0 → getPh (iph st-d) memk ≢ i0))
  drainA-acc uniq mem st r ph (acc rs) with decI0 (getPh (iph st) mem)
  ... | inj₁ i≡ = st , ε , i≡ , λ {_} {_} memk ex ne → ne
  ... | inj₂ i≢ with liveA-i uniq mem st r ph i≢
  ...   | st′ , step , certStep with drainA-acc uniq mem st′ (reach-i r step)
                            (trans (sym (phase-step uniq mem step)) ph) (rs (μ-dec step))
  ...     | st-d , path , i≡ , certRest =
            st-d , step ◅ path , i≡ , (λ {_} {_} memk ex ne → certRest memk ex (certStep memk ex ne))
  drainA : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l)
         → (st : MuxState l) → Reach st → phaseAt mem st ≡ 0
         → Σ[ st-d ∈ MuxState l ] ((st ⇒ᵢ* st-d) × (getPh (iph st-d) mem ≡ i0)
             × (∀ {c d} (memk : (c , d) ∈ linkConfig l) → (c , d) ≢ (a , b) → getPh (iph st) memk ≢ i0 → getPh (iph st-d) memk ≢ i0))
  drainA uniq mem st r ph = drainA-acc uniq mem st r ph (<-wellFounded (μ st))

  -- drain a phase-1 cell to output-ready (oph = o1 v)
  drainB-acc : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l)
             → (st : MuxState l) → Reach st → phaseAt mem st ≡ 1 → Acc _<_ (μ st)
             → Σ[ st-d ∈ MuxState l ] ((st ⇒ᵢ* st-d) × Σ[ v ∈ Data ] (getPh (oph st-d) mem ≡ o1 v)
                 × (∀ {c d} (memk : (c , d) ∈ linkConfig l) → getPh (iph st) memk ≢ i0 → getPh (iph st-d) memk ≢ i0))
  drainB-acc uniq mem st r ph (acc rs) with decO1 (getPh (oph st) mem)
  ... | inj₁ (v , o≡) = st , ε , v , o≡ , λ {_} {_} memk ne → ne
  ... | inj₂ o≢ with liveB-i uniq mem st r ph o≢
  ...   | st′ , step , certStep with drainB-acc uniq mem st′ (reach-i r step)
                            (trans (sym (phase-step uniq mem step)) ph) (rs (μ-dec step))
  ...     | st-d , path , v , o≡ , certRest =
            st-d , step ◅ path , v , o≡ , (λ {_} {_} memk ne → certRest memk (certStep memk ne))
  drainB : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l)
         → (st : MuxState l) → Reach st → phaseAt mem st ≡ 1
         → Σ[ st-d ∈ MuxState l ] ((st ⇒ᵢ* st-d) × Σ[ v ∈ Data ] (getPh (oph st-d) mem ≡ o1 v)
             × (∀ {c d} (memk : (c , d) ∈ linkConfig l) → getPh (iph st) memk ≢ i0 → getPh (iph st-d) memk ≢ i0))
  drainB uniq mem st r ph = drainB-acc uniq mem st r ph (<-wellFounded (μ st))

  ------------------------------------------------------------------------
  -- LAYER 4a — the per-cell PAYLOAD invariant `PInvAt`: every hot data cell
  -- of instance `mem` (its `i1`/`i2`, its `o1`/`o2`, and a register holding
  -- ITS token) carries the in-flight payload `x`.  Guards / foreign holds
  -- are unconstrained.  Preserved by every internal edge, established at a
  -- fresh `input`.  Mirrors 2a's §4 `PInv`, re-`mem`'d with instance-aware
  -- register predicates.
  ------------------------------------------------------------------------

  -- per-cell payload predicates (⊤ on home/guard, `≡ x` on hot data cells)
  PI : IPh → Data → Set
  PI i0     x = Poly.⊤ {0ℓ}
  PI (i1 v) x = v ≡ x
  PI (i2 v) x = v ≡ x
  PI (ig v) x = Poly.⊤ {0ℓ}
  PO : OPh → Data → Set
  PO o0     x = Poly.⊤ {0ℓ}
  PO (o1 v) x = v ≡ x
  PO (o2 v) x = v ≡ x
  PO (og v) x = Poly.⊤ {0ℓ}
  -- a message register carries mem's payload only when it holds mem's token
  PMh : Dir → IDs → MBuf → Data → Set
  PMh d id (hold d′ id′ v) x with (d , id) ≟² (d′ , id′)
  ... | yes _ = v ≡ x
  ... | no  _ = Poly.⊤ {0ℓ}
  PMh d id free        x = Poly.⊤ {0ℓ}
  PMh d id (grd _ _ _) x = Poly.⊤ {0ℓ}

  -- the whole payload invariant on a mux state at cell mem
  PInvAt : Data → ∀ {a b} → (a , b) ∈ linkConfig l → MuxState l → Set
  PInvAt x {a} {b} mem st = PI (getPh (iph st) mem) x × PO (getPh (oph st) mem) x
                          × PMh a b (tb st) x × PMh a b (rb st) x

  -- a token/phase-0 register gives the trivial predicate
  PO-0 : ∀ {op x} → aOp op ≡ 0 → PO op x
  PO-0 {o0}   _ = Poly.tt
  PO-0 {og _} _ = Poly.tt
  PMfree : ∀ {a b x} → PMh a b free x
  PMfree = Poly.tt

  ------------------------------------------------------------------------
  -- `PInvAt` preserved along every internal edge (diagonal shuffles the
  -- payload along the moved instance's chain; skew frames it out).
  ------------------------------------------------------------------------

  PInv-step : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l) {x}
            → ∀ {st st′} → st ⇒ᵢ st′ → PInvAt x mem st → PInvAt x mem st′
  -- sndmsg: payload i1 ⇒ tb
  PInv-step uniq {a} {b} mem (sndmsg {is} {os} {rb} {d = d} {id = id} {x = x} mem′ gph) (pi , po , ptb , prb)
    with (a , b) ≟² (d , id)
  ... | yes refl =
        subst (λ w → PI w _) (sym (get-set-u uniq is mem mem′ (i2 x))) piv , po , piv , prb
    where piv = subst (λ w → PI w _) (get-mem-u uniq is mem mem′ gph) pi
  ... | no ne =
        subst (λ w → PI w _) (sym (getPh-inst≢ is mem mem′ (i2 x) ne)) pi , po , Poly.tt , prb
  -- tx: payload tb ⇒ rb
  PInv-step uniq {a} {b} mem (tx {is} {os} {d = d} {id = id} {x = x}) (pi , po , ptb , prb)
    with (a , b) ≟² (d , id)
  ... | yes refl = pi , po , Poly.tt , ptb
  ... | no ne    = pi , po , Poly.tt , Poly.tt
  -- rcvmsg: payload rb ⇒ oph
  PInv-step uniq {a} {b} mem (rcvmsg {is} {os} {tb} {d = d} {id = id} {x = x} mem′ gph) (pi , po , ptb , prb)
    with (a , b) ≟² (d , id)
  ... | yes refl = pi , subst (λ w → PO w _) (sym (get-set-u uniq os mem mem′ (o1 x))) prb , ptb , Poly.tt
  ... | no ne    = pi , subst (λ w → PO w _) (sym (getPh-inst≢ os mem mem′ (o1 x) ne)) po , ptb , Poly.tt
  -- sndack: oph o2 ⇒ og (guard, ⊤)
  PInv-step uniq {a} {b} mem (sndack {is} {os} {d = d} {id = id} {x = x} mem′ gph) (pi , po , ptb , prb)
    with (a , b) ≟² (d , id)
  ... | yes refl = pi , subst (λ w → PO w _) (sym (get-set-u uniq os mem mem′ (og x))) Poly.tt , ptb , prb
  ... | no ne    = pi , subst (λ w → PO w _) (sym (getPh-inst≢ os mem mem′ (og x) ne)) po , ptb , prb
  -- ack: registers not in PInvAt
  PInv-step uniq mem (ack) p = p
  -- rcvack: iph i2 ⇒ ig (guard, ⊤)
  PInv-step uniq {a} {b} mem (rcvack {is} {os} {d = d} {id = id} {x = x} mem′ gph) (pi , po , ptb , prb)
    with (a , b) ≟² (d , id)
  ... | yes refl = subst (λ w → PI w _) (sym (get-set-u uniq is mem mem′ (ig x))) Poly.tt , po , ptb , prb
  ... | no ne    = subst (λ w → PI w _) (sym (getPh-inst≢ is mem mem′ (ig x) ne)) pi , po , ptb , prb
  -- gI: iph ig ⇒ i0 (both ⊤)
  PInv-step uniq {a} {b} mem (gI {is} {os} {d = d} {id = id} {x = x} mem′ gph) (pi , po , ptb , prb)
    with (a , b) ≟² (d , id)
  ... | yes refl = subst (λ w → PI w _) (sym (get-set-u uniq is mem mem′ i0)) Poly.tt , po , ptb , prb
  ... | no ne    = subst (λ w → PI w _) (sym (getPh-inst≢ is mem mem′ i0 ne)) pi , po , ptb , prb
  -- gO: oph og ⇒ o0 (both ⊤)
  PInv-step uniq {a} {b} mem (gO {is} {os} {d = d} {id = id} {x = x} mem′ gph) (pi , po , ptb , prb)
    with (a , b) ≟² (d , id)
  ... | yes refl = pi , subst (λ w → PO w _) (sym (get-set-u uniq os mem mem′ o0)) Poly.tt , ptb , prb
  ... | no ne    = pi , subst (λ w → PO w _) (sym (getPh-inst≢ os mem mem′ o0 ne)) po , ptb , prb
  -- gT: tb grd ⇒ free
  PInv-step uniq mem (gT) (pi , po , ptb , prb) = pi , po , Poly.tt , prb
  -- gRc: rb grd ⇒ free
  PInv-step uniq mem (gRc) (pi , po , ptb , prb) = pi , po , ptb , Poly.tt
  -- gSa / gR: ack registers not in PInvAt
  PInv-step uniq mem (gSa) p = p
  PInv-step uniq mem (gR)  p = p

  -- a fresh `input w` establishes `PInvAt w` for the fired cell
  PInv-input : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l) {w}
             → ∀ {st st′} → st ⇒ᵥ⟨ inp a b w ⟩ st′ → InvM mem st → PInvAt w mem st′
  PInv-input uniq {a} {b} mem (input {is} {os} {tb} {rb} {sb} {ab} mem′ gph) inv =
        subst (λ w → PI w _) (sym (get-set-u uniq is mem mem′ (i1 _))) refl
      , PO-0 tokO , PMfree-tb , PMfree-rb
    where
    -- from `getPh is mem = i0` (via mem-≡, gph): InvM forces every token 0
    tok≡0 : holdM a b (tb) + holdA a b (ab) + aOp (getPh os mem) + holdM a b (rb) + holdA a b (sb) ≡ 0
    tok≡0 = trans inv (cong aIp (get-mem-u uniq is mem mem′ gph))
    tokO : aOp (getPh os mem) ≡ 0
    tokO = proj₂ (sum0 (holdM a b tb + holdA a b ab) (aOp (getPh os mem))
             (proj₁ (sum0 (holdM a b tb + holdA a b ab + aOp (getPh os mem)) (holdM a b rb)
               (proj₁ (sum0 (holdM a b tb + holdA a b ab + aOp (getPh os mem) + holdM a b rb) (holdA a b sb) tok≡0)))))
    tokT : holdM a b tb ≡ 0
    tokT = proj₁ (sum0 (holdM a b tb) (holdA a b ab)
             (proj₁ (sum0 (holdM a b tb + holdA a b ab) (aOp (getPh os mem))
               (proj₁ (sum0 (holdM a b tb + holdA a b ab + aOp (getPh os mem)) (holdM a b rb)
                 (proj₁ (sum0 (holdM a b tb + holdA a b ab + aOp (getPh os mem) + holdM a b rb) (holdA a b sb) tok≡0)))))))
    tokR : holdM a b rb ≡ 0
    tokR = proj₂ (sum0 (holdM a b tb + holdA a b ab + aOp (getPh os mem)) (holdM a b rb)
             (proj₁ (sum0 (holdM a b tb + holdA a b ab + aOp (getPh os mem) + holdM a b rb) (holdA a b sb) tok≡0)))
    PMfree-tb : PMh a b tb _
    PMfree-tb = holdM0-PM tb tokT
      where holdM0-PM : ∀ m → holdM a b m ≡ 0 → PMh a b m _
            holdM0-PM free       _ = Poly.tt
            holdM0-PM (grd _ _ _) _ = Poly.tt
            holdM0-PM (hold d′ id′ v) e with (a , b) ≟² (d′ , id′)
            ... | no  _ = Poly.tt
            ... | yes refl = ⊥-elim (case trans (sym (holdM-diag {a} {b} {v})) e of λ ())
    PMfree-rb : PMh a b rb _
    PMfree-rb = holdM0-PM rb tokR
      where holdM0-PM : ∀ m → holdM a b m ≡ 0 → PMh a b m _
            holdM0-PM free       _ = Poly.tt
            holdM0-PM (grd _ _ _) _ = Poly.tt
            holdM0-PM (hold d′ id′ v) e with (a , b) ≟² (d′ , id′)
            ... | no  _ = Poly.tt
            ... | yes refl = ⊥-elim (case trans (sym (holdM-diag {a} {b} {v})) e of λ ())

  ------------------------------------------------------------------------
  -- LAYER 5a — the per-cell CORRESPONDENCE `CellOK`/`Corr` and its
  -- preservation scaffolding.  `CellOK` couples one spec phase to the mux
  -- state at that cell: `cp0` ⟺ the input cell is fully home (`iph ≡ i0`);
  -- `cp1 x` ⟺ a forward message is live (`phaseAt ≡ 1`) carrying payload `x`
  -- (`PInvAt x`); `cpg x` ⟺ the message has been output but the ack-return
  -- is still in flight (`phaseAt ≡ 0` yet `iph ≢ i0`).  `Corr phs st`
  -- bundles reachability with `CellOK` at every configured cell.
  ------------------------------------------------------------------------

  -- per-cell correspondence between a spec phase and the mux state at a cell
  CellOK : CPh → ∀ {a b} → (a , b) ∈ linkConfig l → MuxState l → Set
  CellOK cp0     mem st = getPh (iph st) mem ≡ i0
  CellOK (cp1 x) mem st = (phaseAt mem st ≡ 1) × PInvAt x mem st
  CellOK (cpg x) mem st = (phaseAt mem st ≡ 0) × (getPh (iph st) mem ≢ i0)

  -- whole-vector correspondence: reachable, and every cell in sync
  Corr : PhV CPh (linkConfig l) → MuxState l → Set
  Corr phs st = Reach st
              × (∀ {a b} (mem : (a , b) ∈ linkConfig l) → CellOK (getPh phs mem) mem st)

  -- a view of a Copy phase (VIEW type, avoiding `with … in`)
  data CPhView (ph : CPh) : Set where
    isCp0 : ph ≡ cp0   → CPhView ph
    isCp1 : ∀ x → ph ≡ cp1 x → CPhView ph
    isCpg : ∀ x → ph ≡ cpg x → CPhView ph
  whichCP : (ph : CPh) → CPhView ph
  whichCP cp0     = isCp0 refl
  whichCP (cp1 x) = isCp1 x refl
  whichCP (cpg x) = isCpg x refl

  ------------------------------------------------------------------------
  -- LAYER 5b — small arithmetic bridges for the correspondence transitions.
  ------------------------------------------------------------------------

  -- output token 0 ⇒ output phase 0
  aOp0-pOp0 : ∀ op → aOp op ≡ 0 → pOp op ≡ 0
  aOp0-pOp0 o0     _ = refl
  aOp0-pOp0 (og _) _ = refl
  aOp0-pOp0 (o1 _) ()
  aOp0-pOp0 (o2 _) ()

  -- an input-HOME cell (`pIp ≡ 0 ∧ aIp ≡ 0`, i.e. `iph ∈ {i0, ig}`) has
  -- structural phase 0 (`InvM` forces every forward token of the cell to 0)
  home-phase0 : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l) {st}
              → InvM mem st → pIp (getPh (iph st) mem) ≡ 0 → aIp (getPh (iph st) mem) ≡ 0
              → phaseAt mem st ≡ 0
  home-phase0 uniq {a} {b} mem {mkMux is os tb rb sb ab} inv pi ai =
    let s1 = sum0 (holdM a b tb + holdA a b ab + aOp (getPh os mem) + holdM a b rb) (holdA a b sb) (trans inv ai)
        s2 = sum0 (holdM a b tb + holdA a b ab + aOp (getPh os mem)) (holdM a b rb) (proj₁ s1)
        s3 = sum0 (holdM a b tb + holdA a b ab) (aOp (getPh os mem)) (proj₁ s2)
        s4 = sum0 (holdM a b tb) (holdA a b ab) (proj₁ s3)
    in trans (cong₂ (λ t r → pIp (getPh is mem) + t + pOp (getPh os mem) + r) (proj₁ s4) (proj₂ s2))
             (trans (cong (λ p → pIp (getPh is mem) + 0 + p + 0) (aOp0-pOp0 (getPh os mem) (proj₂ s3)))
                    (cong (λ q → q + 0 + 0 + 0) pi))

  -- an output-hot cell (`aOp ≡ 1`) has its input cell hot too (`iph ≢ i0`)
  aOp1-iph≢i0 : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l) {st}
              → InvM mem st → aOp (getPh (oph st) mem) ≡ 1 → getPh (iph st) mem ≢ i0
  aOp1-iph≢i0 uniq {a} {b} mem {mkMux is os tb rb sb ab} inv ao1 i0eq = case contra of λ ()
    where
    inv1 : holdM a b tb + holdA a b ab + 1 + holdM a b rb + holdA a b sb ≡ 0
    inv1 = trans (subst (λ o → holdM a b tb + holdA a b ab + o + holdM a b rb + holdA a b sb
                             ≡ aIp (getPh is mem)) ao1 inv) (cong aIp i0eq)
    contra : suc (holdM a b tb + holdA a b ab + holdM a b rb + holdA a b sb) ≡ 0
    contra = trans (ℕsolve 4 (λ T A R S → ℕcon 1 :⊕ (T :⊕ A :⊕ R :⊕ S) :≡ T :⊕ A :⊕ ℕcon 1 :⊕ R :⊕ S)
                      refl (holdM a b tb) (holdA a b ab) (holdM a b rb) (holdA a b sb)) inv1

  -- firing a fresh `input w` at a home cell lands structural phase 1
  phaseAt-in : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l)
             → ∀ {is os tb rb sb ab w} → getPh is mem ≡ i0 → InvM mem (mkMux is os tb rb sb ab)
             → phaseAt mem (mkMux (setPh is mem (i1 w)) os tb rb sb ab) ≡ 1
  phaseAt-in uniq {a} {b} mem {is} {os} {tb} {rb} {sb} {ab} {w} i0eq inv =
    let s1 = sum0 (holdM a b tb + holdA a b ab + aOp (getPh os mem) + holdM a b rb) (holdA a b sb) (trans inv (cong aIp i0eq))
        s2 = sum0 (holdM a b tb + holdA a b ab + aOp (getPh os mem)) (holdM a b rb) (proj₁ s1)
        s3 = sum0 (holdM a b tb + holdA a b ab) (aOp (getPh os mem)) (proj₁ s2)
        s4 = sum0 (holdM a b tb) (holdA a b ab) (proj₁ s3)
    in trans (cong (λ ip → pIp ip + holdM a b tb + pOp (getPh os mem) + holdM a b rb) (get-set is mem (i1 w)))
             (trans (cong₂ (λ t r → 1 + t + pOp (getPh os mem) + r) (proj₁ s4) (proj₂ s2))
                    (cong (λ p → 1 + 0 + p + 0) (aOp0-pOp0 (getPh os mem) (proj₂ s3))))

  -- firing `output v` at an out-ready cell drops structural phase 1 → 0
  phaseAt-out : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l)
              → ∀ {is os tb rb sb ab v} → getPh os mem ≡ o1 v
              → phaseAt mem (mkMux is os tb rb sb ab) ≡ 1
              → phaseAt mem (mkMux is (setPh os mem (o2 v)) tb rb sb ab) ≡ 0
  phaseAt-out uniq {a} {b} mem {is} {os} {tb} {rb} {sb} {ab} {v} gph ph1
    rewrite get-set os mem (o2 v) =
    trans (ℕsolve 3 (λ P T R → P :⊕ T :⊕ ℕcon 0 :⊕ R :≡ P :⊕ T :⊕ R)
             refl (pIp (getPh is mem)) (holdM a b tb) (holdM a b rb)) e0
    where
    e1 : pIp (getPh is mem) + holdM a b tb + 1 + holdM a b rb ≡ 1
    e1 = subst (λ o → pIp (getPh is mem) + holdM a b tb + pOp o + holdM a b rb ≡ 1) gph ph1
    e0 : pIp (getPh is mem) + holdM a b tb + holdM a b rb ≡ 0
    e0 = sucinj (trans (ℕsolve 3 (λ P T R → ℕcon 1 :⊕ (P :⊕ T :⊕ R) :≡ P :⊕ T :⊕ ℕcon 1 :⊕ R)
                          refl (pIp (getPh is mem)) (holdM a b tb) (holdM a b rb)) e1)

  ------------------------------------------------------------------------
  -- LAYER 5c — how a cell's `iph` evolves under moves.  `iph-i0-pres`:
  -- input-home (`iph ≡ i0`) is preserved by EVERY internal move (a move
  -- that would touch this cell's `iph` requires it hot first).  `set-≢i0`:
  -- setting some cell to a NON-`i0` value keeps any cell out of `i0`.
  ------------------------------------------------------------------------

  -- input-home is preserved along every internal edge
  iph-i0-pres : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l) {st st′}
              → st ⇒ᵢ st′ → getPh (iph st) mem ≡ i0 → getPh (iph st′) mem ≡ i0
  iph-i0-pres uniq mem (tx)         e = e
  iph-i0-pres uniq mem (rcvmsg _ _) e = e
  iph-i0-pres uniq mem (sndack _ _) e = e
  iph-i0-pres uniq mem (ack)        e = e
  iph-i0-pres uniq mem (gO _ _)     e = e
  iph-i0-pres uniq mem (gT)         e = e
  iph-i0-pres uniq mem (gRc)        e = e
  iph-i0-pres uniq mem (gSa)        e = e
  iph-i0-pres uniq mem (gR)         e = e
  iph-i0-pres uniq {a} {b} mem (sndmsg {is = is} {d = d} {id = id} {x = x} mem′ gph) e
    with (a , b) ≟² (d , id)
  ... | yes refl = ⊥-elim (case trans (sym e) (get-mem-u uniq is mem mem′ gph) of λ ())
  ... | no ne    = trans (getPh-inst≢ is mem mem′ (i2 x) ne) e
  iph-i0-pres uniq {a} {b} mem (rcvack {is = is} {d = d} {id = id} {x = x} mem′ gph) e
    with (a , b) ≟² (d , id)
  ... | yes refl = ⊥-elim (case trans (sym e) (get-mem-u uniq is mem mem′ gph) of λ ())
  ... | no ne    = trans (getPh-inst≢ is mem mem′ (ig x) ne) e
  iph-i0-pres uniq {a} {b} mem (gI {is = is} {d = d} {id = id} mem′ gph) e
    with (a , b) ≟² (d , id)
  ... | yes refl = get-set-u uniq is mem mem′ i0
  ... | no ne    = trans (getPh-inst≢ is mem mem′ i0 ne) e

  ------------------------------------------------------------------------
  -- LAYER 5d — `CellOK` preservation transformers.  `CellOK-pres` carries a
  -- single cell across one internal edge given the two `iph`-tracking facts;
  -- the phase/payload parts reuse `phase-step`/`PInv-step`.  The `*-skew`
  -- variants carry a FOREIGN cell across a visible input/output at another
  -- instance (the moved cell's register/phase reads are framed out).
  ------------------------------------------------------------------------

  -- a cell crosses one internal edge (caller supplies `iph` preservations)
  CellOK-pres : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l)
                (cph : CPh) {st st′} → st ⇒ᵢ st′
              → (getPh (iph st) mem ≡ i0 → getPh (iph st′) mem ≡ i0)
              → (getPh (iph st) mem ≢ i0 → getPh (iph st′) mem ≢ i0)
              → CellOK cph mem st → CellOK cph mem st′
  CellOK-pres uniq mem cp0     step pi0 pne ok           = pi0 ok
  CellOK-pres uniq mem (cp1 x) step pi0 pne (ph1 , pinv) =
    trans (sym (phase-step uniq mem step)) ph1 , PInv-step uniq mem step pinv
  CellOK-pres uniq mem (cpg x) step pi0 pne (ph0 , ine)  =
    trans (sym (phase-step uniq mem step)) ph0 , pne ine

  -- a FOREIGN cell crosses a visible `input w` at another instance
  CellOK-in-skew : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l)
                   {c d} (memk : (c , d) ∈ linkConfig l) (cph : CPh) {is os tb rb sb ab w}
                 → (c , d) ≢ (a , b)
                 → CellOK cph memk (mkMux is os tb rb sb ab)
                 → CellOK cph memk (mkMux (setPh is mem (i1 w)) os tb rb sb ab)
  CellOK-in-skew uniq mem memk cp0     {is} {w = w} ne ok rewrite getPh-inst≢ is memk mem (i1 w) ne = ok
  CellOK-in-skew uniq mem memk (cp1 x) {is} {w = w} ne ok rewrite getPh-inst≢ is memk mem (i1 w) ne = ok
  CellOK-in-skew uniq mem memk (cpg x) {is} {w = w} ne ok rewrite getPh-inst≢ is memk mem (i1 w) ne = ok

  -- a FOREIGN cell crosses a visible `output v` at another instance
  CellOK-out-skew : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l)
                    {c d} (memk : (c , d) ∈ linkConfig l) (cph : CPh) {is os tb rb sb ab v}
                  → (c , d) ≢ (a , b)
                  → CellOK cph memk (mkMux is os tb rb sb ab)
                  → CellOK cph memk (mkMux is (setPh os mem (o2 v)) tb rb sb ab)
  CellOK-out-skew uniq mem memk cp0     ne ok = ok
  CellOK-out-skew uniq mem memk (cp1 x) {os = os} {v = v} ne ok rewrite getPh-inst≢ os memk mem (o2 v) ne = ok
  CellOK-out-skew uniq mem memk (cpg x) {os = os} {v = v} ne ok rewrite getPh-inst≢ os memk mem (o2 v) ne = ok

  ------------------------------------------------------------------------
  -- LAYER 5e — the same preservations lifted along an internal RUN `⇒ᵢ*`.
  ------------------------------------------------------------------------

  -- structural phase is invariant along an internal run
  phase-i* : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l) {st st-d}
           → st ⇒ᵢ* st-d → phaseAt mem st ≡ phaseAt mem st-d
  phase-i* uniq mem ε            = refl
  phase-i* uniq mem (step ◅ path) = trans (phase-step uniq mem step) (phase-i* uniq mem path)

  -- the payload invariant is preserved along an internal run
  PInv-i* : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l) {x st st-d}
          → st ⇒ᵢ* st-d → PInvAt x mem st → PInvAt x mem st-d
  PInv-i* uniq mem ε            p = p
  PInv-i* uniq mem (step ◅ path) p = PInv-i* uniq mem path (PInv-step uniq mem step p)

  -- input-home is preserved along an internal run
  iph-i0-i* : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l) {st st-d}
            → st ⇒ᵢ* st-d → getPh (iph st) mem ≡ i0 → getPh (iph st-d) mem ≡ i0
  iph-i0-i* uniq mem ε            e = e
  iph-i0-i* uniq mem (step ◅ path) e = iph-i0-i* uniq mem path (iph-i0-pres uniq mem step e)

  -- a cell crosses a whole internal run (caller supplies the `iph ≢ i0` fact)
  CellOK-i* : (uniq : Unique (linkConfig l)) → ∀ {a b} (mem : (a , b) ∈ linkConfig l)
              (cph : CPh) {st st-d} → st ⇒ᵢ* st-d
            → (getPh (iph st) mem ≢ i0 → getPh (iph st-d) mem ≢ i0)
            → CellOK cph mem st → CellOK cph mem st-d
  CellOK-i* uniq mem cp0     path pne ok           = iph-i0-i* uniq mem path ok
  CellOK-i* uniq mem (cp1 x) path pne (ph1 , pinv) =
    trans (sym (phase-i* uniq mem path)) ph1 , PInv-i* uniq mem path pinv
  CellOK-i* uniq mem (cpg x) path pne (ph0 , ine)  =
    trans (sym (phase-i* uniq mem path)) ph0 , pne ine

  ------------------------------------------------------------------------
  -- LAYER 5f — spec-side `no-√` (general) and the VISIBLE classifier.  A
  -- non-empty Copy fold never `√`s (`no-√C-cfg`).  A visible step of a Copy
  -- LEAF is an `input` (cp0) or `output` (cp1) (`decCopy-visL`, total over
  -- the event); lifted to the fold (`decCopies-visL`) it names the firing
  -- cell (the `evBoth` overlap refuted by `Unique`).
  ------------------------------------------------------------------------

  -- a non-empty config's fold never `ret`s (generalises `no-√C` with `≢[]`)
  no-√C-cfg : ∀ {xs} {phs : PhV CPh xs} {r} → xs ≢ []
            → PTree.force (decCopies l xs phs) ≡ ret r → ⊥
  no-√C-cfg {[]} ne eqf = ⊥-elim (ne refl)
  no-√C-cfg {(d , id) ∷ xs} {ph ∷ phs} ne eqf = no-√C {phs = ph ∷ phs} eqf

  -- a visible step of a Copy LEAF is input (cp0) or output (cp1)
  decCopy-visL : ∀ {cph d id B} {e : Net Data B} {a W}
               → decCopy l cph d id ─[ ev (evN e a) ]─► W
               → (Σ[ x ∈ Data ] (cph ≡ cp0) × (evN e a ≡ evN (input l d id) x) × (W ≡ decCopy l (cp1 x) d id))
               ⊎ (Σ[ x ∈ Data ] (cph ≡ cp1 x) × (evN e a ≡ evN (output l d id) x) × (W ≡ decCopy l (cpg x) d id))
  decCopy-visL {cp0}   step with cp0-evL step
  ... | x , eeq , Weq = inj₁ (x , refl , eeq , Weq)
  decCopy-visL {cp1 x} step with cp1-evL step
  ... | eeq , Weq = inj₂ (x , refl , eeq , Weq)
  decCopy-visL {cpg x} step = ⊥-elim (cpg-noev step)

  -- a visible step of the Copy fold names the firing cell (input or output)
  decCopies-visL : ∀ {xs} {phs : PhV CPh xs} {B} {e : Net Data B} {a W} (uniq : Unique xs)
    → decCopies l xs phs ─[ ev (evN e a) ]─► W
    → (Σ[ dr ∈ Dir ] Σ[ id ∈ IDs ] Σ[ mem ∈ (dr , id) ∈ xs ] Σ[ x ∈ Data ]
         (evN e a ≡ evN (input l dr id) x) × (getPh phs mem ≡ cp0) × (W ≡ decCopies l xs (setPh phs mem (cp1 x))))
    ⊎ (Σ[ dr ∈ Dir ] Σ[ id ∈ IDs ] Σ[ mem ∈ (dr , id) ∈ xs ] Σ[ x ∈ Data ]
         (evN e a ≡ evN (output l dr id) x) × (getPh phs mem ≡ cp1 x) × (W ≡ decCopies l xs (setPh phs mem (cpg x))))
  decCopies-visL {[]} {[]} uniq step = ⊥-elim (Skip-no-ev step)
  decCopies-visL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
    with Par-ev-elim ∅ES ⊤merge (decCopy l ph₀ d₀ id₀) (decCopies l cfg' phs') step
  ... | evSync mem _ _ = ⊥-elim mem
  ... | evL _ Cev with decCopy-visL {ph₀} Cev
  ...   | inj₁ (x , refl , eeq , Weq) =
            inj₁ (d₀ , id₀ , here refl , x , eeq , refl , cong (λ z → z ⦀ decCopies l cfg' phs') Weq)
  ...   | inj₂ (x , refl , eeq , Weq) =
            inj₂ (d₀ , id₀ , here refl , x , eeq , refl , cong (λ z → z ⦀ decCopies l cfg' phs') Weq)
  decCopies-visL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step | evR _ Tev
    with decCopies-visL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...   | inj₁ (dr , id , mem' , x , eeq , gph , refl) = inj₁ (dr , id , there mem' , x , eeq , gph , refl)
  ...   | inj₂ (dr , id , mem' , x , eeq , gph , refl) = inj₂ (dr , id , there mem' , x , eeq , gph , refl)
  decCopies-visL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step | evBoth _ Cev Tev with decCopy-visL {ph₀} Cev
  ...   | inj₁ (x , refl , refl , _) =
            ⊥-elim (decCopies-no-input-∉ {cfg'} {phs'} (λ m → All.lookup (AllPairs.head uniq) m refl) Tev)
  ...   | inj₂ (x , refl , refl , _) =
            ⊥-elim (decCopies-no-output-∉ {cfg'} {phs'} (λ m → All.lookup (AllPairs.head uniq) m refl) Tev)

  ------------------------------------------------------------------------
  -- LAYER 5g — `Corr-istep`: one internal mux move either leaves the spec
  -- vector in sync (spec STUTTERS) or is a guard `gI` that resets a `cpg`
  -- cell home (spec fires ITS restart τ, mapping that cell `cpg → cp0`).
  -- The `gI`-on-`cp0`/`cp1` sub-cases are impossible (`cp0` forces `iph ≡ i0`
  -- ≠ `ig`; `cp1` forces phase 1, but `iph ≡ ig` forces phase 0).
  ------------------------------------------------------------------------

  Corr-istep : (uniq : Unique (linkConfig l)) → ∀ {phs st st′} → Corr phs st → st ⇒ᵢ st′
             → Corr phs st′
             ⊎ (Σ[ a ∈ Dir ] Σ[ b ∈ IDs ] Σ[ mem′ ∈ (a , b) ∈ linkConfig l ] Σ[ x ∈ Data ]
                  (getPh phs mem′ ≡ cpg x) × Corr (setPh phs mem′ cp0) st′)
  Corr-istep uniq {phs} (r , cells) mv@(tx) =
    inj₁ (reach-i r mv , λ memk → CellOK-pres uniq memk (getPh phs memk) mv (λ z → z) (λ z → z) (cells memk))
  Corr-istep uniq {phs} (r , cells) mv@(rcvmsg mem′ gph) =
    inj₁ (reach-i r mv , λ memk → CellOK-pres uniq memk (getPh phs memk) mv (λ z → z) (λ z → z) (cells memk))
  Corr-istep uniq {phs} (r , cells) mv@(sndack mem′ gph) =
    inj₁ (reach-i r mv , λ memk → CellOK-pres uniq memk (getPh phs memk) mv (λ z → z) (λ z → z) (cells memk))
  Corr-istep uniq {phs} (r , cells) mv@(ack) =
    inj₁ (reach-i r mv , λ memk → CellOK-pres uniq memk (getPh phs memk) mv (λ z → z) (λ z → z) (cells memk))
  Corr-istep uniq {phs} (r , cells) mv@(gO mem′ gph) =
    inj₁ (reach-i r mv , λ memk → CellOK-pres uniq memk (getPh phs memk) mv (λ z → z) (λ z → z) (cells memk))
  Corr-istep uniq {phs} (r , cells) mv@(gT) =
    inj₁ (reach-i r mv , λ memk → CellOK-pres uniq memk (getPh phs memk) mv (λ z → z) (λ z → z) (cells memk))
  Corr-istep uniq {phs} (r , cells) mv@(gRc) =
    inj₁ (reach-i r mv , λ memk → CellOK-pres uniq memk (getPh phs memk) mv (λ z → z) (λ z → z) (cells memk))
  Corr-istep uniq {phs} (r , cells) mv@(gSa) =
    inj₁ (reach-i r mv , λ memk → CellOK-pres uniq memk (getPh phs memk) mv (λ z → z) (λ z → z) (cells memk))
  Corr-istep uniq {phs} (r , cells) mv@(gR) =
    inj₁ (reach-i r mv , λ memk → CellOK-pres uniq memk (getPh phs memk) mv (λ z → z) (λ z → z) (cells memk))
  Corr-istep uniq {phs} (r , cells) mv@(sndmsg {is = is} mem′ gph) =
    inj₁ (reach-i r mv
         , λ memk → CellOK-pres uniq memk (getPh phs memk) mv
                      (iph-i0-pres uniq memk mv) (set-≢i0 uniq is mem′ memk (λ ())) (cells memk))
  Corr-istep uniq {phs} (r , cells) mv@(rcvack {is = is} mem′ gph) =
    inj₁ (reach-i r mv
         , λ memk → CellOK-pres uniq memk (getPh phs memk) mv
                      (iph-i0-pres uniq memk mv) (set-≢i0 uniq is mem′ memk (λ ())) (cells memk))
  Corr-istep uniq {phs} (r , cells) mv@(gI {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb} {ab = ab} {d = d} {id = id} {x = x} mem′ gph)
    with whichCP (getPh phs mem′)
  ... | isCp0 gpeq   =
        ⊥-elim (case trans (sym (subst (λ c → CellOK c mem′ (mkMux is os tb rb sb ab)) gpeq (cells mem′))) gph of λ ())
  ... | isCp1 x' gpeq =
        ⊥-elim (case trans (sym (home-phase0 uniq {d} {id} mem′ {mkMux is os tb rb sb ab} (reach-InvM uniq r mem′) (cong pIp gph) (cong aIp gph)))
                           (proj₁ (subst (λ c → CellOK c mem′ (mkMux is os tb rb sb ab)) gpeq (cells mem′))) of λ ())
  ... | isCpg x' gpeq =
        inj₂ (d , id , mem′ , x' , gpeq , (reach-i r mv , newcells))
    where
    newcells : ∀ {c e} (memk : (c , e) ∈ linkConfig l)
             → CellOK (getPh (setPh phs mem′ cp0) memk) memk (mkMux (setPh is mem′ i0) os tb rb sb ab)
    newcells {c} {e} memk with (c , e) ≟² (d , id)
    ... | yes refl = subst (λ cc → CellOK cc memk (mkMux (setPh is mem′ i0) os tb rb sb ab)) (sym (get-set-u uniq phs memk mem′ cp0))
                       (get-set-u uniq is memk mem′ i0)
    ... | no nn = subst (λ cc → CellOK cc memk (mkMux (setPh is mem′ i0) os tb rb sb ab)) (sym (getPh-inst≢ phs memk mem′ cp0 nn))
                    (CellOK-pres uniq memk (getPh phs memk) mv
                      (iph-i0-pres uniq memk mv)
                      (λ ine eq → ine (trans (sym (getPh-inst≢ is memk mem′ i0 nn)) eq))
                      (cells memk))

  ------------------------------------------------------------------------
  -- LAYER 5h — the two VISIBLE-move correspondence transitions.  A fired
  -- `input v` on a `cp0` cell yields `cp1 v` (`phaseAt ≡ 1`, payload `v`);
  -- a fired `output v` on a `cp1 v` cell yields `cpg v` (`phaseAt ≡ 0`,
  -- `iph ≢ i0`).  Foreign cells are framed out via the `*-skew` lemmas.
  ------------------------------------------------------------------------

  -- home vector reads `cp0` at every cell
  getPh-homeC : ∀ xs {c e} (memk : (c , e) ∈ xs) → getPh (homeC xs) memk ≡ cp0
  getPh-homeC (x ∷ xs) (here refl) = refl
  getPh-homeC (x ∷ xs) (there m)   = getPh-homeC xs m

  -- an output-ready cell has non-zero structural phase (used to refute `cpg`)
  phase-o1≢0 : ∀ {a b} (mem : (a , b) ∈ linkConfig l) {st v}
             → getPh (oph st) mem ≡ o1 v → phaseAt mem st ≡ 0 → ⊥
  phase-o1≢0 {a} {b} mem {mkMux is os tb rb sb ab} {v} gph ph0 =
    case trans (ℕsolve 3 (λ P T R → ℕcon 1 :⊕ (P :⊕ T :⊕ R) :≡ P :⊕ T :⊕ ℕcon 1 :⊕ R)
                 refl (pIp (getPh is mem)) (holdM a b tb) (holdM a b rb))
               (subst (λ o → pIp (getPh is mem) + holdM a b tb + pOp o + holdM a b rb ≡ 0) gph ph0) of λ ()

  -- transition on a fired `input v` (cell `mem` moves `cp0 → cp1 v`)
  Corr-input : (uniq : Unique (linkConfig l)) → ∀ {phs a b} (mem : (a , b) ∈ linkConfig l) {st st′ v}
             → Corr phs st → getPh phs mem ≡ cp0 → st ⇒ᵥ⟨ inp a b v ⟩ st′
             → Corr (setPh phs mem (cp1 v)) st′
  Corr-input uniq {phs} {a} {b} mem {v = v} (r , cells) gcp0 (input {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb} {ab = ab} mem′ gph)
    with mem-≡ uniq mem′ mem
  ... | refl = reach-v r (input mem gph) , newcells
    where
    newcells : ∀ {c e} (memk : (c , e) ∈ linkConfig l)
             → CellOK (getPh (setPh phs mem (cp1 v)) memk) memk (mkMux (setPh is mem (i1 v)) os tb rb sb ab)
    newcells {c} {e} memk with (c , e) ≟² (a , b)
    ... | yes refl = subst (λ mk → CellOK (getPh (setPh phs mem (cp1 v)) mk) mk (mkMux (setPh is mem (i1 v)) os tb rb sb ab))
                       (sym (mem-≡ uniq memk mem))
                       (subst (λ cc → CellOK cc mem (mkMux (setPh is mem (i1 v)) os tb rb sb ab)) (sym (get-set phs mem (cp1 v)))
                         ( phaseAt-in uniq mem {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb} {ab = ab} {w = v} gph
                                      (reach-InvM uniq {st = mkMux is os tb rb sb ab} r mem)
                         , PInv-input uniq mem (input {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb} {ab = ab} mem gph)
                                      (reach-InvM uniq {st = mkMux is os tb rb sb ab} r mem) ))
    ... | no nn = subst (λ cc → CellOK cc memk (mkMux (setPh is mem (i1 v)) os tb rb sb ab)) (sym (getPh-inst≢ phs memk mem (cp1 v) nn))
                    (CellOK-in-skew uniq mem memk (getPh phs memk) nn (cells memk))

  -- transition on a fired `output v` (cell `mem` moves `cp1 v → cpg v`)
  Corr-output : (uniq : Unique (linkConfig l)) → ∀ {phs a b} (mem : (a , b) ∈ linkConfig l) {st st′ v}
              → Corr phs st → getPh phs mem ≡ cp1 v → st ⇒ᵥ⟨ out a b v ⟩ st′
              → Corr (setPh phs mem (cpg v)) st′
  Corr-output uniq {phs} {a} {b} mem {v = v} (r , cells) gcp1 (output {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb} {ab = ab} mem′ gph)
    with mem-≡ uniq mem′ mem
  ... | refl = reach-v r (output mem gph) , newcells
    where
    newcells : ∀ {c e} (memk : (c , e) ∈ linkConfig l)
             → CellOK (getPh (setPh phs mem (cpg v)) memk) memk (mkMux is (setPh os mem (o2 v)) tb rb sb ab)
    newcells {c} {e} memk with (c , e) ≟² (a , b)
    ... | yes refl = subst (λ mk → CellOK (getPh (setPh phs mem (cpg v)) mk) mk (mkMux is (setPh os mem (o2 v)) tb rb sb ab))
                       (sym (mem-≡ uniq memk mem))
                       (subst (λ cc → CellOK cc mem (mkMux is (setPh os mem (o2 v)) tb rb sb ab)) (sym (get-set phs mem (cpg v)))
                         ( phaseAt-out uniq mem {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb} {ab = ab} {v = v} gph
                                       (proj₁ (subst (λ cc → CellOK cc mem (mkMux is os tb rb sb ab)) gcp1 (cells mem)))
                         , aOp1-iph≢i0 uniq mem {st = mkMux is (setPh os mem (o2 v)) tb rb sb ab}
                             (reach-InvM uniq {st = mkMux is (setPh os mem (o2 v)) tb rb sb ab}
                                (reach-v r (output {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb} {ab = ab} mem gph)) mem)
                             (subst (λ o → aOp o ≡ 1) (sym (get-set os mem (o2 v))) refl) ))
    ... | no nn = subst (λ cc → CellOK cc memk (mkMux is (setPh os mem (o2 v)) tb rb sb ab)) (sym (getPh-inst≢ phs memk mem (cpg v) nn))
                    (CellOK-out-skew uniq mem memk (getPh phs memk) nn (cells memk))

  ------------------------------------------------------------------------
  -- LAYER 6 — THE EXPANSION WALK `exp`.  A single coinductive relation
  -- carrying the spec vector `phs` in lock-step correspondence `Corr` with a
  -- reachable mux state.  fwd: a spec `input`/`output` is a home/out-pending
  -- cell fired (input: directly; output: after a `drainB`); a spec restart τ
  -- (`cpg → cp0`) is matched by a `drainA` to input-home.  bwd: a mux visible
  -- move is the matching spec fire; a mux τ either leaves the spec put
  -- (STUTTER) or is a `gI` that a `cpg` cell answers with its restart τ.
  ------------------------------------------------------------------------

  exp : (uniq : Unique (linkConfig l)) → linkConfig l ≢ []
      → (phs : PhV CPh (linkConfig l)) (st : MuxState l) → Corr phs st
      → decCopies l (linkConfig l) phs ⪰ ⟦ st ⟧
  -- fwd on-ev: a spec visible step is a cell's input (cp0) or output (cp1)
  exp uniq ne phs st corr .Expand.fwd .WSimF.on-ev (sRet eqf) = ⊥-elim (no-√C-cfg ne eqf)
  exp uniq ne phs st@(mkMux is os tb rb sb ab) (r , cells) .Expand.fwd .WSimF.on-ev (sVis eqf breq)
    with decCopies-visL uniq (sVis eqf breq)
  ... | inj₁ (dr , id , mem , x , eeq , gcp0 , Weq) rewrite Weq =
        let i0eq = subst (λ c → CellOK c mem st) gcp0 (cells mem)
            imove = input {x = x} mem i0eq
        in _ , wev τ*-refl (subst (λ z → ⟦ st ⟧ ─[ ev z ]─► ⟦ mkMux (setPh is mem (i1 x)) os tb rb sb ab ⟧) (sym eeq)
                              (fire-⇒ᵥ l uniq {st = st} imove)) τ*-refl
             , exp uniq ne (setPh phs mem (cp1 x)) (mkMux (setPh is mem (i1 x)) os tb rb sb ab)
                 (Corr-input uniq {phs = phs} mem {st = st} (r , cells) gcp0 imove)
  ... | inj₂ (dr , id , mem , x , eeq , gcp1 , Weq) rewrite Weq
        with subst (λ c → CellOK c mem st) gcp1 (cells mem)
  ...   | (ph1 , pinv) with drainB uniq mem st r ph1
  ...     | st-d , path , v , o1eq , certB
              with subst (λ o → PO o x) o1eq (proj₁ (proj₂ (PInv-i* uniq mem path pinv)))
  ...         | refl =
                let omove = output {x = x} mem o1eq
                    corr-d : Corr phs st-d
                    corr-d = reach-i* r path , λ {_} {_} memk → CellOK-i* uniq memk (getPh phs memk) path (certB memk) (cells memk)
                in _ , wev (real-⇒ᵢ* uniq path)
                         (subst (λ z → ⟦ st-d ⟧ ─[ ev z ]─►
                                   ⟦ mkMux (MuxState.iph st-d) (setPh (MuxState.oph st-d) mem (o2 x))
                                           (MuxState.tb st-d) (MuxState.rb st-d) (MuxState.sb st-d) (MuxState.ab st-d) ⟧)
                            (sym eeq) (fire-⇒ᵥ l uniq {st = st-d} omove)) τ*-refl
                     , exp uniq ne (setPh phs mem (cpg x))
                         (mkMux (MuxState.iph st-d) (setPh (MuxState.oph st-d) mem (o2 x))
                                (MuxState.tb st-d) (MuxState.rb st-d) (MuxState.sb st-d) (MuxState.ab st-d))
                         (Corr-output uniq {phs = phs} mem {st = st-d} corr-d gcp1 omove)
  -- fwd on-tau: a spec restart τ (cpg → cp0) is matched by a drainA to i0
  exp uniq ne phs st@(mkMux is os tb rb sb ab) (r , cells) .Expand.fwd .WSimF.on-tau step with decCopies-τ step
  ... | dr , id , mem , x , gcpg , Weq
        with subst (λ c → CellOK c mem st) gcpg (cells mem)
  ...   | (ph0 , ine) with drainA uniq mem st r ph0
  ...     | st-d , path , i0eq , certA rewrite Weq =
            _ , wτ (real-⇒ᵢ* uniq path)
              , exp uniq ne (setPh phs mem cp0) st-d (reach-i* r path , newcells)
    where
    newcells : ∀ {c e} (memk : (c , e) ∈ linkConfig l) → CellOK (getPh (setPh phs mem cp0) memk) memk st-d
    newcells {c} {e} memk with (c , e) ≟² (dr , id)
    ... | yes refl = subst (λ cc → CellOK cc memk st-d) (sym (get-set-u uniq phs memk mem cp0))
                       (get-mem-u uniq (iph st-d) memk mem i0eq)
    ... | no nn = subst (λ cc → CellOK cc memk st-d) (sym (getPh-inst≢ phs memk mem cp0 nn))
                    (CellOK-i* uniq memk (getPh phs memk) path (certA memk nn) (cells memk))
  -- bwd on-ev: a mux visible move is the matching spec fire (else refuted)
  exp uniq ne phs st (r , cells) .Expand.bwd .ExpBwdF.bon-ev {√ r′} step = ⊥-elim (no-√ l st step)
  exp uniq ne phs st@(mkMux is os tb rb sb ab) (r , cells) .Expand.bwd .ExpBwdF.bon-ev {evl (evLabel B e′ a′)} step
    with refl-ev l uniq {st = st} step
  ... | inp dr id v , st′ , input mem gph , leq , Meq rewrite Meq with whichCP (getPh phs mem)
  ...   | isCp0 gcp0 =
          _ , subst (λ z → decCopies l (linkConfig l) phs ─[ ev z ]─► decCopies l (linkConfig l) (setPh phs mem (cp1 v))) (sym leq)
                (decCopies-input-fire {phs = phs} {x = v} uniq mem gcp0)
            , exp uniq ne (setPh phs mem (cp1 v)) st′
                (Corr-input uniq {phs = phs} mem {st = st} {st′ = st′} (r , cells) gcp0 (input mem gph))
  ...   | isCp1 x′ gcp1 =
          ⊥-elim (case trans (sym (home-phase0 uniq mem {st = st} (reach-InvM uniq r mem) (cong pIp gph) (cong aIp gph)))
                             (proj₁ (subst (λ c → CellOK c mem st) gcp1 (cells mem))) of λ ())
  ...   | isCpg x′ gcpg =
          ⊥-elim (proj₂ (subst (λ c → CellOK c mem st) gcpg (cells mem)) gph)
  exp uniq ne phs st@(mkMux is os tb rb sb ab) (r , cells) .Expand.bwd .ExpBwdF.bon-ev {evl (evLabel B e′ a′)} step
      | out dr id v , st′ , output mem gph , leq , Meq rewrite Meq with whichCP (getPh phs mem)
  ...   | isCp0 gcp0 =
          ⊥-elim (aOp1-iph≢i0 uniq mem {st = st} (reach-InvM uniq r mem) (subst (λ o → aOp o ≡ 1) (sym gph) refl)
                    (subst (λ c → CellOK c mem st) gcp0 (cells mem)))
  ...   | isCpg x′ gcpg =
          ⊥-elim (phase-o1≢0 mem {st = st} gph (proj₁ (subst (λ c → CellOK c mem st) gcpg (cells mem))))
  ...   | isCp1 x′ gcp1 with subst (λ c → CellOK c mem st) gcp1 (cells mem)
  ...     | (ph1 , pinv) with subst (λ o → PO o x′) gph (proj₁ (proj₂ pinv))
  ...       | refl =
              _ , subst (λ z → decCopies l (linkConfig l) phs ─[ ev z ]─► decCopies l (linkConfig l) (setPh phs mem (cpg x′))) (sym leq)
                    (decCopies-output-fire {phs = phs} uniq mem gcp1)
                , exp uniq ne (setPh phs mem (cpg x′)) st′
                    (Corr-output uniq {phs = phs} mem {st = st} {st′ = st′} (r , cells) gcp1 (output mem gph))
  -- bwd on-tau: a mux τ leaves the spec put (STUTTER) or answers a gI-restart
  exp uniq ne phs st (r , cells) .Expand.bwd .ExpBwdF.bon-tau step with refl-τ l uniq {st = st} step
  ... | st′ , imove , refl with Corr-istep uniq {phs = phs} {st = st} {st′ = st′} (r , cells) imove
  ...   | inj₁ corr′ = inj₂ (exp uniq ne phs st′ corr′)
  ...   | inj₂ (a , b , mem′ , x , gcpg , corr″) =
          inj₁ (decCopies l (linkConfig l) (setPh phs mem′ cp0)
               , decCopies-cpg-τ-fire {phs = phs} mem′ gcpg
               , exp uniq ne (setPh phs mem′ cp0) st′ corr″)
  -- neither side diverges
  exp uniq ne phs st corr .Expand.div→ dv = ⊥-elim (¬DivC phs dv)
  exp uniq ne phs st corr .Expand.div← dv = ⊥-elim (noDiv l uniq st dv)

  ------------------------------------------------------------------------
  -- THE DELIVERABLE.  Assemble the expansion at the all-home vector /
  -- `initial l`, then rewrite both sides (`spec-init` on the spec side,
  -- `dec-init` on the mux side) into the headline `≈DR`.
  ------------------------------------------------------------------------

  perLink : linkConfig l ≢ [] → Unique (linkConfig l) → NetOneLink l ≈DR linkCopy l
  perLink ne uniq =
    subst (NetOneLink l ≈DR_) (spec-init l)
      (subst (_≈DR decCopies l (linkConfig l) (homeC (linkConfig l))) (dec-init l)
        (⪯→≈DR (exp uniq ne (homeC (linkConfig l)) (initial l) (reach-init , cells-init))))
    where
    -- every home cell corresponds to a fully-home mux cell (`iph ≡ i0`)
    cells-init : ∀ {a b} (memk : (a , b) ∈ linkConfig l)
               → CellOK (getPh (homeC (linkConfig l)) memk) memk (initial l)
    cells-init memk = subst (λ c → CellOK c memk (initial l)) (sym (getPh-homeC (linkConfig l) memk))
                        (getPh-homeI (linkConfig l) memk)
