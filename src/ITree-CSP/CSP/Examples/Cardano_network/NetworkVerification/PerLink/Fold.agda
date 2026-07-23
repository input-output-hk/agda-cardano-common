{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — per-link mux GENERAL FOLD machinery
-- (`PerLink.Fold`), the ARBITRARY-config (`linkConfig l` any non-empty,
-- `Unique` list) replacement of `PerLink.Step`'s singleton layer.
--
-- Where `PerLink.Step` degenerated the two cell folds `decInputs`/
-- `decOutputs` to `cell ⦀ Skip` (a singleton config), this module works
-- with the genuine `⦀`-fold over an arbitrary config and supplies the
-- SAME six-lemma interface (`fire-⇒ᵥ`, `fire-⇒ᵢ`, `refl-τ`, `refl-ev`,
-- `no-√`, `noDiv`).  The register / `∥⇘…⇙` / `∖` gluing layers are
-- IDENTICAL to the singleton case — only the two cell-fold operands are
-- generalised; the fold work is confined to this module's first half.
--
-- Layers (bottom-up):
--   1. FOLD CONFINEMENT.  A fold offers a visible event only for events
--      of a channel its cells own, and only at an instance actually in
--      the config: `decInputs-no-*L` (foreign CHANNEL) and
--      `decInputs-no-*-∉` (foreign INSTANCE).  Uniq-free (the ∉ variants
--      merely consume a non-membership witness).  Per-leaf `≢`
--      refutations `decInput-no-*-≢` handle the head-idle side conditions.
--   2. FOLD ELIMINATION.  Every τ / visible step of a fold is a step of
--      exactly one cell at some membership position `mem`, with a
--      `setPh`-shaped residual: `decInputs-τ` and the visible classifiers
--      `decInputs-{input,sndmsg,rcvack}L`.  The visible classifiers need
--      `Unique` to refute the `evBoth` overlap (two DISTINCT cells never
--      offer the same instance's event).
--   3. FOLD INTRODUCTION.  A cell at `mem` that fires makes the fold fire
--      to the `setPh` residual: `decInputs-{input,sndmsg,rcvack}-fire`
--      and the guard `decInputs-ig-τ-fire`.  The visible fires need
--      `Unique` (the `Par-solo*` side condition asks the OTHER cells not
--      to offer this instance's event); the τ fire does not.
--   4. STEP INTERFACE.  The register-gluer / `refl-*` / `noDiv`
--      re-assembly, mirroring `PerLink.Step` with the fold operands
--      generalised.  `no-√` is re-exported from `PerLink.Leaf` (already
--      config-general).
--
-- Every visible lemma is stated over an ARBITRARY config list `xs` so it
-- inducts on `xs`/`phs` in lock-step with `decInputs`/`decOutputs`; the
-- top-level lemmas specialise `xs := linkConfig l`.
--
-- No postulates, holes, or `NON_TERMINATING`.
------------------------------------------------------------------------
open import Level using (0ℓ; lift)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂; Σ; Σ-syntax; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using (Dir; IDs; lo; hi; N2N_ChainSync)

module CSP.Examples.Cardano_network.NetworkVerification.PerLink.Fold
  (p : Params) (Data : Set) ⦃ _ : DecEq Data ⦄ where

open PTree

open import CSP.Examples.Cardano_network.Net p
  using ( Net; Net-≟; Link
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack )
open Params p using (linkConfig)

import CSP.Operators {E = Net Data} (Net-≟ {Data}) as Op
open Op using (_∥⇘_⇙_; _⦀_; _∖_; chanSet; Skip; Par; Par⊤; ∅ES; EventSet; viewV)

open import Semantics.LTS {E = Net Data} {I = ExtI (Net Data)} hiding (Diverges)
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

-- the config-independent leaf layer (re-exported `public`, exactly as
-- `PerLink.Step` did: confinement bridge, `(l)`-only `no-√`, and the
-- `(l , dc , idc)`-parameterised `WithInstance` per-leaf machinery)
open import CSP.Examples.Cardano_network.NetworkVerification.PerLink.Leaf p Data public

------------------------------------------------------------------------
-- All fold lemmas fix the link `l` (each cell instantiates `WithInstance
-- l d id`) but range over an ARBITRARY config list; they induct on the
-- config in lock-step with `decInputs`/`decOutputs`.
------------------------------------------------------------------------

module _ (l : Link) where

  ------------------------------------------------------------------------
  -- LAYER 1a — Input fold: foreign-CHANNEL confinement.  A `decInputs`
  -- fold never offers tx / ack / output / rcvmsg / sndack (no Input cell
  -- offers them), by induction on the config with the per-leaf `-L`
  -- refutations at the head and recursion at the tail.  `∅ES` kills the
  -- sync branch; the head refutes both `evL` and `evBoth`.
  ------------------------------------------------------------------------

  -- decInputs never offers tx
  decInputs-no-txL : ∀ {xs} {phs : PhV IPh xs} {l₀ dr id a W}
                   → decInputs l xs phs ─[ ev (evN (tx l₀ dr id) a) ]─► W → ⊥
  decInputs-no-txL {[]} {[]} step = Skip-no-ev step
  decInputs-no-txL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} step
    with Par-ev-elim ∅ES ⊤merge (decInput l ph₀ d₀ id₀) (decInputs l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evL _ Iev      = WithInstance.decInput-no-txL l d₀ id₀ {ph₀} Iev
  ... | evR _ Tev      = decInputs-no-txL {cfg'} {phs'} Tev
  ... | evBoth _ Iev _ = WithInstance.decInput-no-txL l d₀ id₀ {ph₀} Iev

  -- decInputs never offers ack
  decInputs-no-ackL : ∀ {xs} {phs : PhV IPh xs} {l₀ dr id W}
                    → decInputs l xs phs ─[ ev (evN (ack l₀ dr id) tt) ]─► W → ⊥
  decInputs-no-ackL {[]} {[]} step = Skip-no-ev step
  decInputs-no-ackL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} step
    with Par-ev-elim ∅ES ⊤merge (decInput l ph₀ d₀ id₀) (decInputs l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evL _ Iev      = WithInstance.decInput-no-ackL l d₀ id₀ {ph₀} Iev
  ... | evR _ Tev      = decInputs-no-ackL {cfg'} {phs'} Tev
  ... | evBoth _ Iev _ = WithInstance.decInput-no-ackL l d₀ id₀ {ph₀} Iev

  -- decInputs never offers output
  decInputs-no-outputL : ∀ {xs} {phs : PhV IPh xs} {l₀ dr id a W}
                       → decInputs l xs phs ─[ ev (evN (output l₀ dr id) a) ]─► W → ⊥
  decInputs-no-outputL {[]} {[]} step = Skip-no-ev step
  decInputs-no-outputL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} step
    with Par-ev-elim ∅ES ⊤merge (decInput l ph₀ d₀ id₀) (decInputs l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evL _ Iev      = WithInstance.decInput-no-outputL l d₀ id₀ {ph₀} Iev
  ... | evR _ Tev      = decInputs-no-outputL {cfg'} {phs'} Tev
  ... | evBoth _ Iev _ = WithInstance.decInput-no-outputL l d₀ id₀ {ph₀} Iev

  -- decInputs never offers rcvmsg
  decInputs-no-rcvmsgL : ∀ {xs} {phs : PhV IPh xs} {l₀ dr id a W}
                       → decInputs l xs phs ─[ ev (evN (rcvmsg l₀ dr id) a) ]─► W → ⊥
  decInputs-no-rcvmsgL {[]} {[]} step = Skip-no-ev step
  decInputs-no-rcvmsgL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} step
    with Par-ev-elim ∅ES ⊤merge (decInput l ph₀ d₀ id₀) (decInputs l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evL _ Iev      = WithInstance.decInput-no-rcvmsgL l d₀ id₀ {ph₀} Iev
  ... | evR _ Tev      = decInputs-no-rcvmsgL {cfg'} {phs'} Tev
  ... | evBoth _ Iev _ = WithInstance.decInput-no-rcvmsgL l d₀ id₀ {ph₀} Iev

  -- decInputs never offers sndack
  decInputs-no-sndackL : ∀ {xs} {phs : PhV IPh xs} {l₀ dr id W}
                       → decInputs l xs phs ─[ ev (evN (sndack l₀ dr id) tt) ]─► W → ⊥
  decInputs-no-sndackL {[]} {[]} step = Skip-no-ev step
  decInputs-no-sndackL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} step
    with Par-ev-elim ∅ES ⊤merge (decInput l ph₀ d₀ id₀) (decInputs l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evL _ Iev      = WithInstance.decInput-no-sndackL l d₀ id₀ {ph₀} Iev
  ... | evR _ Tev      = decInputs-no-sndackL {cfg'} {phs'} Tev
  ... | evBoth _ Iev _ = WithInstance.decInput-no-sndackL l d₀ id₀ {ph₀} Iev

  ------------------------------------------------------------------------
  -- LAYER 1b — Output fold: foreign-CHANNEL confinement (symmetric).
  ------------------------------------------------------------------------

  -- decOutputs never offers input
  decOutputs-no-inputL : ∀ {xs} {phs : PhV OPh xs} {l₀ dr id a W}
                       → decOutputs l xs phs ─[ ev (evN (input l₀ dr id) a) ]─► W → ⊥
  decOutputs-no-inputL {[]} {[]} step = Skip-no-ev step
  decOutputs-no-inputL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} step
    with Par-ev-elim ∅ES ⊤merge (decOutput l ph₀ d₀ id₀) (decOutputs l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evL _ Oev      = WithInstance.decOutput-no-inputL l d₀ id₀ {ph₀} Oev
  ... | evR _ Tev      = decOutputs-no-inputL {cfg'} {phs'} Tev
  ... | evBoth _ Oev _ = WithInstance.decOutput-no-inputL l d₀ id₀ {ph₀} Oev

  -- decOutputs never offers sndmsg
  decOutputs-no-sndmsgL : ∀ {xs} {phs : PhV OPh xs} {l₀ dr id a W}
                        → decOutputs l xs phs ─[ ev (evN (sndmsg l₀ dr id) a) ]─► W → ⊥
  decOutputs-no-sndmsgL {[]} {[]} step = Skip-no-ev step
  decOutputs-no-sndmsgL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} step
    with Par-ev-elim ∅ES ⊤merge (decOutput l ph₀ d₀ id₀) (decOutputs l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evL _ Oev      = WithInstance.decOutput-no-sndmsgL l d₀ id₀ {ph₀} Oev
  ... | evR _ Tev      = decOutputs-no-sndmsgL {cfg'} {phs'} Tev
  ... | evBoth _ Oev _ = WithInstance.decOutput-no-sndmsgL l d₀ id₀ {ph₀} Oev

  -- decOutputs never offers rcvack
  decOutputs-no-rcvackL : ∀ {xs} {phs : PhV OPh xs} {l₀ dr id W}
                        → decOutputs l xs phs ─[ ev (evN (rcvack l₀ dr id) tt) ]─► W → ⊥
  decOutputs-no-rcvackL {[]} {[]} step = Skip-no-ev step
  decOutputs-no-rcvackL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} step
    with Par-ev-elim ∅ES ⊤merge (decOutput l ph₀ d₀ id₀) (decOutputs l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evL _ Oev      = WithInstance.decOutput-no-rcvackL l d₀ id₀ {ph₀} Oev
  ... | evR _ Tev      = decOutputs-no-rcvackL {cfg'} {phs'} Tev
  ... | evBoth _ Oev _ = WithInstance.decOutput-no-rcvackL l d₀ id₀ {ph₀} Oev

  -- decOutputs never offers tx
  decOutputs-no-txL : ∀ {xs} {phs : PhV OPh xs} {l₀ dr id a W}
                    → decOutputs l xs phs ─[ ev (evN (tx l₀ dr id) a) ]─► W → ⊥
  decOutputs-no-txL {[]} {[]} step = Skip-no-ev step
  decOutputs-no-txL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} step
    with Par-ev-elim ∅ES ⊤merge (decOutput l ph₀ d₀ id₀) (decOutputs l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evL _ Oev      = WithInstance.decOutput-no-txL l d₀ id₀ {ph₀} Oev
  ... | evR _ Tev      = decOutputs-no-txL {cfg'} {phs'} Tev
  ... | evBoth _ Oev _ = WithInstance.decOutput-no-txL l d₀ id₀ {ph₀} Oev

  -- decOutputs never offers ack
  decOutputs-no-ackL : ∀ {xs} {phs : PhV OPh xs} {l₀ dr id W}
                     → decOutputs l xs phs ─[ ev (evN (ack l₀ dr id) tt) ]─► W → ⊥
  decOutputs-no-ackL {[]} {[]} step = Skip-no-ev step
  decOutputs-no-ackL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} step
    with Par-ev-elim ∅ES ⊤merge (decOutput l ph₀ d₀ id₀) (decOutputs l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evL _ Oev      = WithInstance.decOutput-no-ackL l d₀ id₀ {ph₀} Oev
  ... | evR _ Tev      = decOutputs-no-ackL {cfg'} {phs'} Tev
  ... | evBoth _ Oev _ = WithInstance.decOutput-no-ackL l d₀ id₀ {ph₀} Oev

  ------------------------------------------------------------------------
  -- LAYER 1c — per-leaf foreign-INSTANCE refutation: a single Input cell
  -- at instance `(d₀,id₀)` offers no `input`/`sndmsg`/`rcvack` of a
  -- DIFFERENT instance `(d,id)` — the head-idle side condition of the
  -- fold-intro `there` case.  The `-classL` menu pins the offered event's
  -- instance to the cell's own, contradicting `(d₀,id₀) ≢ (d,id)`.
  ------------------------------------------------------------------------

  -- an Input cell offers no foreign-instance `input`
  decInput-no-input-≢ : ∀ {ip d₀ id₀ l₀ d id x W} → (d₀ , id₀) ≢ (d , id)
                      → decInput l ip d₀ id₀ ─[ ev (evN (input l₀ d id) x) ]─► W → ⊥
  decInput-no-input-≢ {ip} {d₀} {id₀} ne step
    with WithInstance.decInput-input-classL l d₀ id₀ {ip} step
  ... | refl , _ , refl , refl , _ = ne refl

  -- an Input cell offers no foreign-instance `sndmsg`
  decInput-no-sndmsg-≢ : ∀ {ip d₀ id₀ l₀ d id x W} → (d₀ , id₀) ≢ (d , id)
                       → decInput l ip d₀ id₀ ─[ ev (evN (sndmsg l₀ d id) x) ]─► W → ⊥
  decInput-no-sndmsg-≢ {ip} {d₀} {id₀} ne step
    with WithInstance.decInput-sndmsg-classL l d₀ id₀ {ip} step
  ... | refl , _ , refl , refl , _ = ne refl

  -- an Input cell offers no foreign-instance `rcvack`
  decInput-no-rcvack-≢ : ∀ {ip d₀ id₀ l₀ d id W} → (d₀ , id₀) ≢ (d , id)
                       → decInput l ip d₀ id₀ ─[ ev (evN (rcvack l₀ d id) tt) ]─► W → ⊥
  decInput-no-rcvack-≢ {ip} {d₀} {id₀} ne step
    with WithInstance.decInput-rcvack-classL l d₀ id₀ {ip} step
  ... | _ , refl , _ , refl , refl , _ = ne refl

  -- an Output cell offers no foreign-instance `rcvmsg`
  decOutput-no-rcvmsg-≢ : ∀ {op d₀ id₀ l₀ d id x W} → (d₀ , id₀) ≢ (d , id)
                        → decOutput l op d₀ id₀ ─[ ev (evN (rcvmsg l₀ d id) x) ]─► W → ⊥
  decOutput-no-rcvmsg-≢ {op} {d₀} {id₀} ne step
    with WithInstance.decOutput-rcvmsg-classL l d₀ id₀ {op} step
  ... | refl , _ , refl , refl , _ = ne refl

  -- an Output cell offers no foreign-instance `output`
  decOutput-no-output-≢ : ∀ {op d₀ id₀ l₀ d id x W} → (d₀ , id₀) ≢ (d , id)
                        → decOutput l op d₀ id₀ ─[ ev (evN (output l₀ d id) x) ]─► W → ⊥
  decOutput-no-output-≢ {op} {d₀} {id₀} ne step
    with WithInstance.decOutput-output-classL l d₀ id₀ {op} step
  ... | refl , _ , refl , refl , _ = ne refl

  -- an Output cell offers no foreign-instance `sndack`
  decOutput-no-sndack-≢ : ∀ {op d₀ id₀ l₀ d id W} → (d₀ , id₀) ≢ (d , id)
                        → decOutput l op d₀ id₀ ─[ ev (evN (sndack l₀ d id) tt) ]─► W → ⊥
  decOutput-no-sndack-≢ {op} {d₀} {id₀} ne step
    with WithInstance.decOutput-sndack-classL l d₀ id₀ {op} step
  ... | _ , refl , _ , refl , refl , _ = ne refl

  ------------------------------------------------------------------------
  -- LAYER 1d — fold foreign-INSTANCE confinement: a fold offers its own
  -- channels only at instances actually in the config.  Consuming a
  -- non-membership witness `¬ ((d,id) ∈ xs)` these refute the step; the
  -- head case pins the offered instance to the head's own via the
  -- `-classL` menu (contradicting `here`), the tail recurses on `there`.
  ------------------------------------------------------------------------

  -- decInputs offers no `input` at an instance ∉ the config
  decInputs-no-input-∉ : ∀ {xs} {phs : PhV IPh xs} {l₀ d id x W}
                       → ¬ ((d , id) ∈ xs)
                       → decInputs l xs phs ─[ ev (evN (input l₀ d id) x) ]─► W → ⊥
  decInputs-no-input-∉ {[]} {[]} ∉ step = Skip-no-ev step
  decInputs-no-input-∉ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} ∉ step
    with Par-ev-elim ∅ES ⊤merge (decInput l ph₀ d₀ id₀) (decInputs l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evR _ Tev      = decInputs-no-input-∉ {cfg'} {phs'} (λ m → ∉ (there m)) Tev
  ... | evL _ Iev      with WithInstance.decInput-input-classL l d₀ id₀ {ph₀} Iev
  ...   | refl , _ , refl , refl , _ = ∉ (here refl)
  decInputs-no-input-∉ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} ∉ step
      | evBoth _ Iev _ with WithInstance.decInput-input-classL l d₀ id₀ {ph₀} Iev
  ...   | refl , _ , refl , refl , _ = ∉ (here refl)

  -- decInputs offers no `sndmsg` at an instance ∉ the config
  decInputs-no-sndmsg-∉ : ∀ {xs} {phs : PhV IPh xs} {l₀ d id x W}
                        → ¬ ((d , id) ∈ xs)
                        → decInputs l xs phs ─[ ev (evN (sndmsg l₀ d id) x) ]─► W → ⊥
  decInputs-no-sndmsg-∉ {[]} {[]} ∉ step = Skip-no-ev step
  decInputs-no-sndmsg-∉ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} ∉ step
    with Par-ev-elim ∅ES ⊤merge (decInput l ph₀ d₀ id₀) (decInputs l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evR _ Tev      = decInputs-no-sndmsg-∉ {cfg'} {phs'} (λ m → ∉ (there m)) Tev
  ... | evL _ Iev      with WithInstance.decInput-sndmsg-classL l d₀ id₀ {ph₀} Iev
  ...   | refl , _ , refl , refl , _ = ∉ (here refl)
  decInputs-no-sndmsg-∉ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} ∉ step
      | evBoth _ Iev _ with WithInstance.decInput-sndmsg-classL l d₀ id₀ {ph₀} Iev
  ...   | refl , _ , refl , refl , _ = ∉ (here refl)

  -- decInputs offers no `rcvack` at an instance ∉ the config
  decInputs-no-rcvack-∉ : ∀ {xs} {phs : PhV IPh xs} {l₀ d id W}
                        → ¬ ((d , id) ∈ xs)
                        → decInputs l xs phs ─[ ev (evN (rcvack l₀ d id) tt) ]─► W → ⊥
  decInputs-no-rcvack-∉ {[]} {[]} ∉ step = Skip-no-ev step
  decInputs-no-rcvack-∉ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} ∉ step
    with Par-ev-elim ∅ES ⊤merge (decInput l ph₀ d₀ id₀) (decInputs l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evR _ Tev      = decInputs-no-rcvack-∉ {cfg'} {phs'} (λ m → ∉ (there m)) Tev
  ... | evL _ Iev      with WithInstance.decInput-rcvack-classL l d₀ id₀ {ph₀} Iev
  ...   | _ , refl , _ , refl , refl , _ = ∉ (here refl)
  decInputs-no-rcvack-∉ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} ∉ step
      | evBoth _ Iev _ with WithInstance.decInput-rcvack-classL l d₀ id₀ {ph₀} Iev
  ...   | _ , refl , _ , refl , refl , _ = ∉ (here refl)

  -- decOutputs offers no `rcvmsg` at an instance ∉ the config
  decOutputs-no-rcvmsg-∉ : ∀ {xs} {phs : PhV OPh xs} {l₀ d id x W}
                         → ¬ ((d , id) ∈ xs)
                         → decOutputs l xs phs ─[ ev (evN (rcvmsg l₀ d id) x) ]─► W → ⊥
  decOutputs-no-rcvmsg-∉ {[]} {[]} ∉ step = Skip-no-ev step
  decOutputs-no-rcvmsg-∉ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} ∉ step
    with Par-ev-elim ∅ES ⊤merge (decOutput l ph₀ d₀ id₀) (decOutputs l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evR _ Tev      = decOutputs-no-rcvmsg-∉ {cfg'} {phs'} (λ m → ∉ (there m)) Tev
  ... | evL _ Oev      with WithInstance.decOutput-rcvmsg-classL l d₀ id₀ {ph₀} Oev
  ...   | refl , _ , refl , refl , _ = ∉ (here refl)
  decOutputs-no-rcvmsg-∉ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} ∉ step
      | evBoth _ Oev _ with WithInstance.decOutput-rcvmsg-classL l d₀ id₀ {ph₀} Oev
  ...   | refl , _ , refl , refl , _ = ∉ (here refl)

  -- decOutputs offers no `output` at an instance ∉ the config
  decOutputs-no-output-∉ : ∀ {xs} {phs : PhV OPh xs} {l₀ d id x W}
                         → ¬ ((d , id) ∈ xs)
                         → decOutputs l xs phs ─[ ev (evN (output l₀ d id) x) ]─► W → ⊥
  decOutputs-no-output-∉ {[]} {[]} ∉ step = Skip-no-ev step
  decOutputs-no-output-∉ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} ∉ step
    with Par-ev-elim ∅ES ⊤merge (decOutput l ph₀ d₀ id₀) (decOutputs l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evR _ Tev      = decOutputs-no-output-∉ {cfg'} {phs'} (λ m → ∉ (there m)) Tev
  ... | evL _ Oev      with WithInstance.decOutput-output-classL l d₀ id₀ {ph₀} Oev
  ...   | refl , _ , refl , refl , _ = ∉ (here refl)
  decOutputs-no-output-∉ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} ∉ step
      | evBoth _ Oev _ with WithInstance.decOutput-output-classL l d₀ id₀ {ph₀} Oev
  ...   | refl , _ , refl , refl , _ = ∉ (here refl)

  -- decOutputs offers no `sndack` at an instance ∉ the config
  decOutputs-no-sndack-∉ : ∀ {xs} {phs : PhV OPh xs} {l₀ d id W}
                         → ¬ ((d , id) ∈ xs)
                         → decOutputs l xs phs ─[ ev (evN (sndack l₀ d id) tt) ]─► W → ⊥
  decOutputs-no-sndack-∉ {[]} {[]} ∉ step = Skip-no-ev step
  decOutputs-no-sndack-∉ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} ∉ step
    with Par-ev-elim ∅ES ⊤merge (decOutput l ph₀ d₀ id₀) (decOutputs l cfg' phs') step
  ... | evSync mem _ _ = mem
  ... | evR _ Tev      = decOutputs-no-sndack-∉ {cfg'} {phs'} (λ m → ∉ (there m)) Tev
  ... | evL _ Oev      with WithInstance.decOutput-sndack-classL l d₀ id₀ {ph₀} Oev
  ...   | _ , refl , _ , refl , refl , _ = ∉ (here refl)
  decOutputs-no-sndack-∉ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} ∉ step
      | evBoth _ Oev _ with WithInstance.decOutput-sndack-classL l d₀ id₀ {ph₀} Oev
  ...   | _ , refl , _ , refl , refl , _ = ∉ (here refl)

  ------------------------------------------------------------------------
  -- LAYER 2 — FOLD ELIMINATION (τ).  Every τ of a fold is one cell's
  -- guard τ (ig/og → home), at some `mem`, with a `setPh …home` residual.
  -- Induction: `τL` = head guard (per-leaf `-τ-class`), `τR` = recurse.
  -- No `Unique` (a τ-step of `Par` picks exactly one operand — no overlap).
  ------------------------------------------------------------------------

  -- every τ of decInputs is a single Input cell's guard τ
  decInputs-τ : ∀ {xs} {phs : PhV IPh xs} {W} → decInputs l xs phs ─[ τ ]─► W
    → Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] Σ[ mem ∈ (d , id) ∈ xs ] Σ[ x ∈ Data ]
        (getPh phs mem ≡ ig x) × (W ≡ decInputs l xs (setPh phs mem i0))
  decInputs-τ {[]} {[]} step = ⊥-elim (Skip-no-τ step)
  decInputs-τ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} step
    with Par-τ-elim ∅ES ⊤merge (decInput l ph₀ d₀ id₀) (decInputs l cfg' phs') step
  ... | τL _ Iτ refl with WithInstance.decInput-τ-class l d₀ id₀ Iτ
  ...   | (x , eig) , Weq =
            d₀ , id₀ , here refl , x , eig , cong (λ z → z ⦀ decInputs l cfg' phs') Weq
  decInputs-τ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} step
      | τR _ Tτ refl with decInputs-τ {cfg'} {phs'} Tτ
  ...   | d , id , mem' , x , gig , Weq =
            d , id , there mem' , x , gig , cong (λ z → decInput l ph₀ d₀ id₀ ⦀ z) Weq

  -- every τ of decOutputs is a single Output cell's guard τ
  decOutputs-τ : ∀ {xs} {phs : PhV OPh xs} {W} → decOutputs l xs phs ─[ τ ]─► W
    → Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] Σ[ mem ∈ (d , id) ∈ xs ] Σ[ x ∈ Data ]
        (getPh phs mem ≡ og x) × (W ≡ decOutputs l xs (setPh phs mem o0))
  decOutputs-τ {[]} {[]} step = ⊥-elim (Skip-no-τ step)
  decOutputs-τ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} step
    with Par-τ-elim ∅ES ⊤merge (decOutput l ph₀ d₀ id₀) (decOutputs l cfg' phs') step
  ... | τL _ Oτ refl with WithInstance.decOutput-τ-class l d₀ id₀ Oτ
  ...   | (x , eog) , Weq =
            d₀ , id₀ , here refl , x , eog , cong (λ z → z ⦀ decOutputs l cfg' phs') Weq
  decOutputs-τ {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} step
      | τR _ Tτ refl with decOutputs-τ {cfg'} {phs'} Tτ
  ...   | d , id , mem' , x , gog , Weq =
            d , id , there mem' , x , gog , cong (λ z → decOutput l ph₀ d₀ id₀ ⦀ z) Weq

  ------------------------------------------------------------------------
  -- LAYER 2 — FOLD ELIMINATION (visible).  Every visible step of a fold
  -- is exactly one cell's offer, at the `mem` whose instance matches the
  -- fired event.  Induction: `evL` = head (per-leaf `-classL` pins the
  -- instance to `here`), `evR` = recurse (`there`), `evSync` vacuous
  -- (`∅ES`), and `evBoth` REFUTED via `Unique`: the head classifier pins
  -- the event to the head instance, the tail (recursion) exhibits it in
  -- the tail config, and the head-∉-tail component of `Unique` closes it.
  ------------------------------------------------------------------------

  -- every `input` step of decInputs is a home cell accepting it
  decInputs-inputL : ∀ {xs} {phs : PhV IPh xs} {l₀ dr id a W} (uniq : Unique xs)
    → decInputs l xs phs ─[ ev (evN (input l₀ dr id) a) ]─► W
    → Σ[ mem ∈ (dr , id) ∈ xs ]
        (l₀ ≡ l) × (getPh phs mem ≡ i0) × (W ≡ decInputs l xs (setPh phs mem (i1 a)))
  decInputs-inputL {[]} {[]} uniq step = ⊥-elim (Skip-no-ev step)
  decInputs-inputL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
    with Par-ev-elim ∅ES ⊤merge (decInput l ph₀ d₀ id₀) (decInputs l cfg' phs') step
  ... | evSync mem _ _ = ⊥-elim mem
  ... | evL _ Iev with WithInstance.decInput-input-classL l d₀ id₀ {ph₀} Iev
  ...   | refl , e0 , refl , refl , Weq =
            here refl , refl , e0 , cong (λ z → z ⦀ decInputs l cfg' phs') Weq
  decInputs-inputL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
      | evR _ Tev with decInputs-inputL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...   | mem' , refl , gph , refl = there mem' , refl , gph , refl
  decInputs-inputL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
      | evBoth _ Iev Tev with WithInstance.decInput-input-classL l d₀ id₀ {ph₀} Iev
  ...   | refl , _ , refl , refl , _ with decInputs-inputL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...     | mem' , _ , _ , _ = ⊥-elim (All.lookup (AllPairs.head uniq) mem' refl)

  -- every `sndmsg` step of decInputs is a loaded cell emitting it
  decInputs-sndmsgL : ∀ {xs} {phs : PhV IPh xs} {l₀ dr id a W} (uniq : Unique xs)
    → decInputs l xs phs ─[ ev (evN (sndmsg l₀ dr id) a) ]─► W
    → Σ[ mem ∈ (dr , id) ∈ xs ]
        (l₀ ≡ l) × (getPh phs mem ≡ i1 a) × (W ≡ decInputs l xs (setPh phs mem (i2 a)))
  decInputs-sndmsgL {[]} {[]} uniq step = ⊥-elim (Skip-no-ev step)
  decInputs-sndmsgL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
    with Par-ev-elim ∅ES ⊤merge (decInput l ph₀ d₀ id₀) (decInputs l cfg' phs') step
  ... | evSync mem _ _ = ⊥-elim mem
  ... | evL _ Iev with WithInstance.decInput-sndmsg-classL l d₀ id₀ {ph₀} Iev
  ...   | refl , e1 , refl , refl , Weq =
            here refl , refl , e1 , cong (λ z → z ⦀ decInputs l cfg' phs') Weq
  decInputs-sndmsgL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
      | evR _ Tev with decInputs-sndmsgL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...   | mem' , refl , gph , refl = there mem' , refl , gph , refl
  decInputs-sndmsgL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
      | evBoth _ Iev Tev with WithInstance.decInput-sndmsg-classL l d₀ id₀ {ph₀} Iev
  ...   | refl , _ , refl , refl , _ with decInputs-sndmsgL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...     | mem' , _ , _ , _ = ⊥-elim (All.lookup (AllPairs.head uniq) mem' refl)

  -- every `rcvack` step of decInputs is a sent cell emitting it
  decInputs-rcvackL : ∀ {xs} {phs : PhV IPh xs} {l₀ dr id W} (uniq : Unique xs)
    → decInputs l xs phs ─[ ev (evN (rcvack l₀ dr id) tt) ]─► W
    → Σ[ mem ∈ (dr , id) ∈ xs ] Σ[ x ∈ Data ]
        (l₀ ≡ l) × (getPh phs mem ≡ i2 x) × (W ≡ decInputs l xs (setPh phs mem (ig x)))
  decInputs-rcvackL {[]} {[]} uniq step = ⊥-elim (Skip-no-ev step)
  decInputs-rcvackL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
    with Par-ev-elim ∅ES ⊤merge (decInput l ph₀ d₀ id₀) (decInputs l cfg' phs') step
  ... | evSync mem _ _ = ⊥-elim mem
  ... | evL _ Iev with WithInstance.decInput-rcvack-classL l d₀ id₀ {ph₀} Iev
  ...   | x , refl , e2 , refl , refl , Weq =
            here refl , x , refl , e2 , cong (λ z → z ⦀ decInputs l cfg' phs') Weq
  decInputs-rcvackL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
      | evR _ Tev with decInputs-rcvackL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...   | mem' , x , refl , gph , refl = there mem' , x , refl , gph , refl
  decInputs-rcvackL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
      | evBoth _ Iev Tev with WithInstance.decInput-rcvack-classL l d₀ id₀ {ph₀} Iev
  ...   | x , refl , _ , refl , refl , _ with decInputs-rcvackL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...     | mem' , _ , _ , _ , _ = ⊥-elim (All.lookup (AllPairs.head uniq) mem' refl)

  -- every `rcvmsg` step of decOutputs is a home cell accepting it
  decOutputs-rcvmsgL : ∀ {xs} {phs : PhV OPh xs} {l₀ dr id a W} (uniq : Unique xs)
    → decOutputs l xs phs ─[ ev (evN (rcvmsg l₀ dr id) a) ]─► W
    → Σ[ mem ∈ (dr , id) ∈ xs ]
        (l₀ ≡ l) × (getPh phs mem ≡ o0) × (W ≡ decOutputs l xs (setPh phs mem (o1 a)))
  decOutputs-rcvmsgL {[]} {[]} uniq step = ⊥-elim (Skip-no-ev step)
  decOutputs-rcvmsgL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
    with Par-ev-elim ∅ES ⊤merge (decOutput l ph₀ d₀ id₀) (decOutputs l cfg' phs') step
  ... | evSync mem _ _ = ⊥-elim mem
  ... | evL _ Oev with WithInstance.decOutput-rcvmsg-classL l d₀ id₀ {ph₀} Oev
  ...   | refl , e0 , refl , refl , Weq =
            here refl , refl , e0 , cong (λ z → z ⦀ decOutputs l cfg' phs') Weq
  decOutputs-rcvmsgL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
      | evR _ Tev with decOutputs-rcvmsgL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...   | mem' , refl , gph , refl = there mem' , refl , gph , refl
  decOutputs-rcvmsgL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
      | evBoth _ Oev Tev with WithInstance.decOutput-rcvmsg-classL l d₀ id₀ {ph₀} Oev
  ...   | refl , _ , refl , refl , _ with decOutputs-rcvmsgL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...     | mem' , _ , _ , _ = ⊥-elim (All.lookup (AllPairs.head uniq) mem' refl)

  -- every `output` step of decOutputs is a ready cell emitting it
  decOutputs-outputL : ∀ {xs} {phs : PhV OPh xs} {l₀ dr id a W} (uniq : Unique xs)
    → decOutputs l xs phs ─[ ev (evN (output l₀ dr id) a) ]─► W
    → Σ[ mem ∈ (dr , id) ∈ xs ]
        (l₀ ≡ l) × (getPh phs mem ≡ o1 a) × (W ≡ decOutputs l xs (setPh phs mem (o2 a)))
  decOutputs-outputL {[]} {[]} uniq step = ⊥-elim (Skip-no-ev step)
  decOutputs-outputL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
    with Par-ev-elim ∅ES ⊤merge (decOutput l ph₀ d₀ id₀) (decOutputs l cfg' phs') step
  ... | evSync mem _ _ = ⊥-elim mem
  ... | evL _ Oev with WithInstance.decOutput-output-classL l d₀ id₀ {ph₀} Oev
  ...   | refl , e1 , refl , refl , Weq =
            here refl , refl , e1 , cong (λ z → z ⦀ decOutputs l cfg' phs') Weq
  decOutputs-outputL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
      | evR _ Tev with decOutputs-outputL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...   | mem' , refl , gph , refl = there mem' , refl , gph , refl
  decOutputs-outputL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
      | evBoth _ Oev Tev with WithInstance.decOutput-output-classL l d₀ id₀ {ph₀} Oev
  ...   | refl , _ , refl , refl , _ with decOutputs-outputL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...     | mem' , _ , _ , _ = ⊥-elim (All.lookup (AllPairs.head uniq) mem' refl)

  -- every `sndack` step of decOutputs is a done cell emitting it
  decOutputs-sndackL : ∀ {xs} {phs : PhV OPh xs} {l₀ dr id W} (uniq : Unique xs)
    → decOutputs l xs phs ─[ ev (evN (sndack l₀ dr id) tt) ]─► W
    → Σ[ mem ∈ (dr , id) ∈ xs ] Σ[ x ∈ Data ]
        (l₀ ≡ l) × (getPh phs mem ≡ o2 x) × (W ≡ decOutputs l xs (setPh phs mem (og x)))
  decOutputs-sndackL {[]} {[]} uniq step = ⊥-elim (Skip-no-ev step)
  decOutputs-sndackL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
    with Par-ev-elim ∅ES ⊤merge (decOutput l ph₀ d₀ id₀) (decOutputs l cfg' phs') step
  ... | evSync mem _ _ = ⊥-elim mem
  ... | evL _ Oev with WithInstance.decOutput-sndack-classL l d₀ id₀ {ph₀} Oev
  ...   | x , refl , e2 , refl , refl , Weq =
            here refl , x , refl , e2 , cong (λ z → z ⦀ decOutputs l cfg' phs') Weq
  decOutputs-sndackL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
      | evR _ Tev with decOutputs-sndackL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...   | mem' , x , refl , gph , refl = there mem' , x , refl , gph , refl
  decOutputs-sndackL {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} uniq step
      | evBoth _ Oev Tev with WithInstance.decOutput-sndack-classL l d₀ id₀ {ph₀} Oev
  ...   | x , refl , _ , refl , refl , _ with decOutputs-sndackL {cfg'} {phs'} (AllPairs.tail uniq) Tev
  ...     | mem' , _ , _ , _ , _ = ⊥-elim (All.lookup (AllPairs.head uniq) mem' refl)

  ------------------------------------------------------------------------
  -- LAYER 3 — FOLD INTRODUCTION.  A cell that fires at `mem` makes the
  -- fold fire to the `setPh` residual, by induction on `mem`: `here` lifts
  -- the head fire past the idle tail (`Par-soloL`, tail non-offer from the
  -- ∉-confinement + `Unique`'s head-∉-tail), `there` lifts the tail fire
  -- past the idle head (`Par-soloR`, head non-offer from the per-leaf `≢`
  -- refutation + `Unique`'s head-≢-target).  The guard τ needs neither
  -- side condition (`Par-τ-{L,R}` has none).
  ------------------------------------------------------------------------

  -- decInputs input fire (home cell mem, i0 → i1 a)
  decInputs-input-fire : ∀ {xs} {phs : PhV IPh xs} {d id x} (uniq : Unique xs)
    → (mem : (d , id) ∈ xs) → getPh phs mem ≡ i0
    → decInputs l xs phs ─[ ev (evN (input l d id) x) ]─► decInputs l xs (setPh phs mem (i1 x))
  decInputs-input-fire {(d , id) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} uniq (here refl) gi
    rewrite gi =
      Par-soloL ∅ES ⊤merge (decInput l i0 d id) (decInputs l cfg' phs') (λ z → z)
        (WithInstance.dIn-i0-fire l d id {x})
        (noView {P = decInputs l cfg' phs'} {e = input l d id} {a = x}
          (decInputs-no-input-∉ {cfg'} {phs'} (λ m → All.lookup (AllPairs.head uniq) m refl)))
  decInputs-input-fire {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} uniq (there mem') gi =
      Par-soloR ∅ES ⊤merge (decInput l ph₀ d₀ id₀) (decInputs l cfg' phs') (λ z → z)
        (decInputs-input-fire {cfg'} {phs'} (AllPairs.tail uniq) mem' gi)
        (noView {P = decInput l ph₀ d₀ id₀} {e = input l d id} {a = x}
          (decInput-no-input-≢ {ph₀} (All.lookup (AllPairs.head uniq) mem')))

  -- decInputs sndmsg fire (loaded cell mem, i1 x → i2 x)
  decInputs-sndmsg-fire : ∀ {xs} {phs : PhV IPh xs} {d id x} (uniq : Unique xs)
    → (mem : (d , id) ∈ xs) → getPh phs mem ≡ i1 x
    → decInputs l xs phs ─[ ev (evN (sndmsg l d id) x) ]─► decInputs l xs (setPh phs mem (i2 x))
  decInputs-sndmsg-fire {(d , id) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} uniq (here refl) gi
    rewrite gi =
      Par-soloL ∅ES ⊤merge (decInput l (i1 x) d id) (decInputs l cfg' phs') (λ z → z)
        (WithInstance.dIn-i1-fire l d id {x})
        (noView {P = decInputs l cfg' phs'} {e = sndmsg l d id} {a = x}
          (decInputs-no-sndmsg-∉ {cfg'} {phs'} (λ m → All.lookup (AllPairs.head uniq) m refl)))
  decInputs-sndmsg-fire {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} uniq (there mem') gi =
      Par-soloR ∅ES ⊤merge (decInput l ph₀ d₀ id₀) (decInputs l cfg' phs') (λ z → z)
        (decInputs-sndmsg-fire {cfg'} {phs'} (AllPairs.tail uniq) mem' gi)
        (noView {P = decInput l ph₀ d₀ id₀} {e = sndmsg l d id} {a = x}
          (decInput-no-sndmsg-≢ {ph₀} (All.lookup (AllPairs.head uniq) mem')))

  -- decInputs rcvack fire (sent cell mem, i2 x → ig x)
  decInputs-rcvack-fire : ∀ {xs} {phs : PhV IPh xs} {d id x} (uniq : Unique xs)
    → (mem : (d , id) ∈ xs) → getPh phs mem ≡ i2 x
    → decInputs l xs phs ─[ ev (evN (rcvack l d id) tt) ]─► decInputs l xs (setPh phs mem (ig x))
  decInputs-rcvack-fire {(d , id) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} uniq (here refl) gi
    rewrite gi =
      Par-soloL ∅ES ⊤merge (decInput l (i2 x) d id) (decInputs l cfg' phs') (λ z → z)
        (WithInstance.dIn-i2-fire l d id {x})
        (noView {P = decInputs l cfg' phs'} {e = rcvack l d id} {a = tt}
          (decInputs-no-rcvack-∉ {cfg'} {phs'} (λ m → All.lookup (AllPairs.head uniq) m refl)))
  decInputs-rcvack-fire {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} uniq (there mem') gi =
      Par-soloR ∅ES ⊤merge (decInput l ph₀ d₀ id₀) (decInputs l cfg' phs') (λ z → z)
        (decInputs-rcvack-fire {cfg'} {phs'} (AllPairs.tail uniq) mem' gi)
        (noView {P = decInput l ph₀ d₀ id₀} {e = rcvack l d id} {a = tt}
          (decInput-no-rcvack-≢ {ph₀} (All.lookup (AllPairs.head uniq) mem')))

  -- decInputs guard τ fire (cell mem, ig x → i0); no confinement needed
  decInputs-ig-τ-fire : ∀ {xs} {phs : PhV IPh xs} {d id x}
    → (mem : (d , id) ∈ xs) → getPh phs mem ≡ ig x
    → decInputs l xs phs ─[ τ ]─► decInputs l xs (setPh phs mem i0)
  decInputs-ig-τ-fire {(d , id) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} (here refl) gi
    rewrite gi =
      Par-τ-L ∅ES ⊤merge (decInput l (ig x) d id) (decInputs l cfg' phs')
        (WithInstance.dIn-ig-τ l d id {x})
  decInputs-ig-τ-fire {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} (there mem') gi =
      Par-τ-R ∅ES ⊤merge (decInput l ph₀ d₀ id₀) (decInputs l cfg' phs')
        (decInputs-ig-τ-fire {cfg'} {phs'} mem' gi)

  -- decOutputs rcvmsg fire (home cell mem, o0 → o1 x)
  decOutputs-rcvmsg-fire : ∀ {xs} {phs : PhV OPh xs} {d id x} (uniq : Unique xs)
    → (mem : (d , id) ∈ xs) → getPh phs mem ≡ o0
    → decOutputs l xs phs ─[ ev (evN (rcvmsg l d id) x) ]─► decOutputs l xs (setPh phs mem (o1 x))
  decOutputs-rcvmsg-fire {(d , id) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} uniq (here refl) gi
    rewrite gi =
      Par-soloL ∅ES ⊤merge (decOutput l o0 d id) (decOutputs l cfg' phs') (λ z → z)
        (WithInstance.dOut-o0-fire l d id {x})
        (noView {P = decOutputs l cfg' phs'} {e = rcvmsg l d id} {a = x}
          (decOutputs-no-rcvmsg-∉ {cfg'} {phs'} (λ m → All.lookup (AllPairs.head uniq) m refl)))
  decOutputs-rcvmsg-fire {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} uniq (there mem') gi =
      Par-soloR ∅ES ⊤merge (decOutput l ph₀ d₀ id₀) (decOutputs l cfg' phs') (λ z → z)
        (decOutputs-rcvmsg-fire {cfg'} {phs'} (AllPairs.tail uniq) mem' gi)
        (noView {P = decOutput l ph₀ d₀ id₀} {e = rcvmsg l d id} {a = x}
          (decOutput-no-rcvmsg-≢ {ph₀} (All.lookup (AllPairs.head uniq) mem')))

  -- decOutputs output fire (ready cell mem, o1 x → o2 x)
  decOutputs-output-fire : ∀ {xs} {phs : PhV OPh xs} {d id x} (uniq : Unique xs)
    → (mem : (d , id) ∈ xs) → getPh phs mem ≡ o1 x
    → decOutputs l xs phs ─[ ev (evN (output l d id) x) ]─► decOutputs l xs (setPh phs mem (o2 x))
  decOutputs-output-fire {(d , id) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} uniq (here refl) gi
    rewrite gi =
      Par-soloL ∅ES ⊤merge (decOutput l (o1 x) d id) (decOutputs l cfg' phs') (λ z → z)
        (WithInstance.dOut-o1-fire l d id {x})
        (noView {P = decOutputs l cfg' phs'} {e = output l d id} {a = x}
          (decOutputs-no-output-∉ {cfg'} {phs'} (λ m → All.lookup (AllPairs.head uniq) m refl)))
  decOutputs-output-fire {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} uniq (there mem') gi =
      Par-soloR ∅ES ⊤merge (decOutput l ph₀ d₀ id₀) (decOutputs l cfg' phs') (λ z → z)
        (decOutputs-output-fire {cfg'} {phs'} (AllPairs.tail uniq) mem' gi)
        (noView {P = decOutput l ph₀ d₀ id₀} {e = output l d id} {a = x}
          (decOutput-no-output-≢ {ph₀} (All.lookup (AllPairs.head uniq) mem')))

  -- decOutputs sndack fire (done cell mem, o2 x → og x)
  decOutputs-sndack-fire : ∀ {xs} {phs : PhV OPh xs} {d id x} (uniq : Unique xs)
    → (mem : (d , id) ∈ xs) → getPh phs mem ≡ o2 x
    → decOutputs l xs phs ─[ ev (evN (sndack l d id) tt) ]─► decOutputs l xs (setPh phs mem (og x))
  decOutputs-sndack-fire {(d , id) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} uniq (here refl) gi
    rewrite gi =
      Par-soloL ∅ES ⊤merge (decOutput l (o2 x) d id) (decOutputs l cfg' phs') (λ z → z)
        (WithInstance.dOut-o2-fire l d id {x})
        (noView {P = decOutputs l cfg' phs'} {e = sndack l d id} {a = tt}
          (decOutputs-no-sndack-∉ {cfg'} {phs'} (λ m → All.lookup (AllPairs.head uniq) m refl)))
  decOutputs-sndack-fire {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} uniq (there mem') gi =
      Par-soloR ∅ES ⊤merge (decOutput l ph₀ d₀ id₀) (decOutputs l cfg' phs') (λ z → z)
        (decOutputs-sndack-fire {cfg'} {phs'} (AllPairs.tail uniq) mem' gi)
        (noView {P = decOutput l ph₀ d₀ id₀} {e = sndack l d id} {a = tt}
          (decOutput-no-sndack-≢ {ph₀} (All.lookup (AllPairs.head uniq) mem')))

  -- decOutputs guard τ fire (cell mem, og x → o0); no confinement needed
  decOutputs-og-τ-fire : ∀ {xs} {phs : PhV OPh xs} {d id x}
    → (mem : (d , id) ∈ xs) → getPh phs mem ≡ og x
    → decOutputs l xs phs ─[ τ ]─► decOutputs l xs (setPh phs mem o0)
  decOutputs-og-τ-fire {(d , id) ∷ cfg'} {ph₀ ∷ phs'} {d} {id} {x} (here refl) gi
    rewrite gi =
      Par-τ-L ∅ES ⊤merge (decOutput l (og x) d id) (decOutputs l cfg' phs')
        (WithInstance.dOut-og-τ l d id {x})
  decOutputs-og-τ-fire {(d₀ , id₀) ∷ cfg'} {ph₀ ∷ phs'} (there mem') gi =
      Par-τ-R ∅ES ⊤merge (decOutput l ph₀ d₀ id₀) (decOutputs l cfg' phs')
        (decOutputs-og-τ-fire {cfg'} {phs'} mem' gi)

  ------------------------------------------------------------------------
  -- LAYER 4 — STEP INTERFACE.  The register / `∥⇘…⇙` / `∖` gluing is
  -- IDENTICAL to `PerLink.Step`; only the two cell-fold operands change.
  --
  -- The register composites (`TR-*`/`RS-*`) and the register leaf fires /
  -- refutations live in `WithInstance` but IGNORE the instance `(dc,idc)`
  -- (their types mention only `decTrans`/`decRAck`/`decRcv`/`decSnd`, all
  -- link-indexed).  We open `WithInstance` at an ARBITRARY instance purely
  -- to bring them into scope; nothing below depends on the chosen one.
  ------------------------------------------------------------------------
  open WithInstance l lo N2N_ChainSync

  ------------------------------------------------------------------------
  -- Tx-side τ classifier: every τ of `decTx` is an Input guard (gI), a
  -- register guard (gT/gR), or a hidden sndmsg / rcvack SYNC.  Mirrors
  -- `Step.decTxˢ-τ-class` with the fold classifiers replacing `IS-*`.
  ------------------------------------------------------------------------
  decTx-τ-class : (uniq : Unique (linkConfig l)) → ∀ {iphs tb ab W}
    → decTx l iphs tb ab ─[ τ ]─► W
    → (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] Σ[ mem ∈ (d , id) ∈ linkConfig l ] Σ[ x ∈ Data ]
         (getPh iphs mem ≡ i1 x) × (tb ≡ free)
         × (W ≡ decTx l (setPh iphs mem (i2 x)) (hold d id x) ab))
    ⊎ (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] Σ[ mem ∈ (d , id) ∈ linkConfig l ] Σ[ x ∈ Data ]
         (getPh iphs mem ≡ i2 x) × (ab ≡ hold d id)
         × (W ≡ decTx l (setPh iphs mem (ig x)) tb (grd d id)))
    ⊎ (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] Σ[ mem ∈ (d , id) ∈ linkConfig l ] Σ[ x ∈ Data ]
         (getPh iphs mem ≡ ig x) × (W ≡ decTx l (setPh iphs mem i0) tb ab))
    ⊎ (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] Σ[ x ∈ Data ] (tb ≡ grd d id x) × (W ≡ decTx l iphs free ab))
    ⊎ (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] (ab ≡ grd d id) × (W ≡ decTx l iphs tb free))
  decTx-τ-class uniq {iphs} {tb} {ab} step
    with Hide-τ-elim csSR' (decInputs l (linkConfig l) iphs ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l ab)) step
  ... | hτP _ parτ refl
        with Par-τ-elim csSR' ⊤merge (decInputs l (linkConfig l) iphs) (decTrans l tb ⦀ decRAck l ab) parτ
  ...   | τL _ Iτ refl with decInputs-τ {linkConfig l} {iphs} Iτ
  ...     | d , id , mem , x , gph , Weq =
              inj₂ (inj₂ (inj₁ (d , id , mem , x , gph ,
                cong (λ z → (z ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l ab)) ∖ csSR') Weq)))
  decTx-τ-class uniq {iphs} {tb} {ab} step | hτP _ parτ refl | τR _ TRτ refl with TR-τ {tb} {ab} TRτ
  ...     | inj₁ (d , id , x , eq , Weq) =
              inj₂ (inj₂ (inj₂ (inj₁ (d , id , x , eq ,
                cong (λ z → (decInputs l (linkConfig l) iphs ∥⇘ csSR' ⇙ z) ∖ csSR') Weq))))
  ...     | inj₂ (d , id , eq , Weq) =
              inj₂ (inj₂ (inj₂ (inj₂ (d , id , eq ,
                cong (λ z → (decInputs l (linkConfig l) iphs ∥⇘ csSR' ⇙ z) ∖ csSR') Weq))))
  decTx-τ-class uniq {iphs} {tb} {ab} step | hτH {B} {e} {a} _ mem parev refl with e
  ... | sndmsg l₀ dr id
        with Par-ev-elim csSR' ⊤merge (decInputs l (linkConfig l) iphs) (decTrans l tb ⦀ decRAck l ab) parev
  ...   | evL  ¬cs _   = ⊥-elim (¬cs mem)
  ...   | evR  ¬cs _   = ⊥-elim (¬cs mem)
  ...   | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
  ...   | evSync _ Iev TRev with decInputs-sndmsgL {phs = iphs} uniq Iev
  ...     | mem′ , refl , gph , WiEq with TR-sndmsg {tb} {ab} TRev
  ...       | tbEq , WtrEq =
                inj₁ (dr , id , mem′ , a , gph , tbEq ,
                  cong₂ (λ zi ztr → (zi ∥⇘ csSR' ⇙ ztr) ∖ csSR') WiEq WtrEq)
  decTx-τ-class uniq {iphs} {tb} {ab} step | hτH {B} {e} {a} _ mem parev refl | rcvack l₀ dr id
        with Par-ev-elim csSR' ⊤merge (decInputs l (linkConfig l) iphs) (decTrans l tb ⦀ decRAck l ab) parev
  ...   | evL  ¬cs _   = ⊥-elim (¬cs mem)
  ...   | evR  ¬cs _   = ⊥-elim (¬cs mem)
  ...   | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
  ...   | evSync _ Iev TRev with decInputs-rcvackL {phs = iphs} uniq Iev
  ...     | mem′ , x , refl , gph , WiEq with TR-rcvack {tb} {ab} TRev
  ...       | abEq , WtrEq =
                inj₂ (inj₁ (dr , id , mem′ , x , gph , abEq ,
                  cong₂ (λ zi ztr → (zi ∥⇘ csSR' ⇙ ztr) ∖ csSR') WiEq WtrEq))
  decTx-τ-class uniq {iphs} {tb} {ab} step | hτH {B} {e} {a} _ mem parev refl | input l₀ dr id  = ⊥-elim mem
  decTx-τ-class uniq {iphs} {tb} {ab} step | hτH {B} {e} {a} _ mem parev refl | output l₀ dr id = ⊥-elim mem
  decTx-τ-class uniq {iphs} {tb} {ab} step | hτH {B} {e} {a} _ mem parev refl | rcvmsg l₀ dr id = ⊥-elim mem
  decTx-τ-class uniq {iphs} {tb} {ab} step | hτH {B} {e} {a} _ mem parev refl | tx l₀ dr id     = ⊥-elim mem
  decTx-τ-class uniq {iphs} {tb} {ab} step | hτH {B} {e} {a} _ mem parev refl | sndack l₀ dr id = ⊥-elim mem
  decTx-τ-class uniq {iphs} {tb} {ab} step | hτH {B} {e} {a} _ mem parev refl | ack l₀ dr id    = ⊥-elim mem

  ------------------------------------------------------------------------
  -- Rx-side τ classifier: gO / gRc / gSa or a hidden rcvmsg / sndack SYNC.
  ------------------------------------------------------------------------
  decRx-τ-class : (uniq : Unique (linkConfig l)) → ∀ {ophs rb sb W}
    → decRx l ophs rb sb ─[ τ ]─► W
    → (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] Σ[ mem ∈ (d , id) ∈ linkConfig l ] Σ[ x ∈ Data ]
         (getPh ophs mem ≡ o0) × (rb ≡ hold d id x)
         × (W ≡ decRx l (setPh ophs mem (o1 x)) (grd d id x) sb))
    ⊎ (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] Σ[ mem ∈ (d , id) ∈ linkConfig l ] Σ[ x ∈ Data ]
         (getPh ophs mem ≡ o2 x) × (sb ≡ free)
         × (W ≡ decRx l (setPh ophs mem (og x)) rb (hold d id)))
    ⊎ (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] Σ[ mem ∈ (d , id) ∈ linkConfig l ] Σ[ x ∈ Data ]
         (getPh ophs mem ≡ og x) × (W ≡ decRx l (setPh ophs mem o0) rb sb))
    ⊎ (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] Σ[ x ∈ Data ] (rb ≡ grd d id x) × (W ≡ decRx l ophs free sb))
    ⊎ (Σ[ d ∈ Dir ] Σ[ id ∈ IDs ] (sb ≡ grd d id) × (W ≡ decRx l ophs rb free))
  decRx-τ-class uniq {ophs} {rb} {sb} step
    with Hide-τ-elim csRS' (decOutputs l (linkConfig l) ophs ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l sb)) step
  ... | hτP _ parτ refl
        with Par-τ-elim csRS' ⊤merge (decOutputs l (linkConfig l) ophs) (decRcv l rb ⦀ decSnd l sb) parτ
  ...   | τL _ Oτ refl with decOutputs-τ {linkConfig l} {ophs} Oτ
  ...     | d , id , mem , x , gph , Weq =
              inj₂ (inj₂ (inj₁ (d , id , mem , x , gph ,
                cong (λ z → (z ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l sb)) ∖ csRS') Weq)))
  decRx-τ-class uniq {ophs} {rb} {sb} step | hτP _ parτ refl | τR _ RSτ refl with RS-τ {rb} {sb} RSτ
  ...     | inj₁ (d , id , x , eq , Weq) =
              inj₂ (inj₂ (inj₂ (inj₁ (d , id , x , eq ,
                cong (λ z → (decOutputs l (linkConfig l) ophs ∥⇘ csRS' ⇙ z) ∖ csRS') Weq))))
  ...     | inj₂ (d , id , eq , Weq) =
              inj₂ (inj₂ (inj₂ (inj₂ (d , id , eq ,
                cong (λ z → (decOutputs l (linkConfig l) ophs ∥⇘ csRS' ⇙ z) ∖ csRS') Weq))))
  decRx-τ-class uniq {ophs} {rb} {sb} step | hτH {B} {e} {a} _ mem parev refl with e
  ... | rcvmsg l₀ dr id
        with Par-ev-elim csRS' ⊤merge (decOutputs l (linkConfig l) ophs) (decRcv l rb ⦀ decSnd l sb) parev
  ...   | evL  ¬cs _   = ⊥-elim (¬cs mem)
  ...   | evR  ¬cs _   = ⊥-elim (¬cs mem)
  ...   | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
  ...   | evSync _ Oev RSev with decOutputs-rcvmsgL {phs = ophs} uniq Oev
  ...     | mem′ , refl , gph , WoEq with RS-rcvmsg {rb} {sb} RSev
  ...       | rbEq , WrsEq =
                inj₁ (dr , id , mem′ , a , gph , rbEq ,
                  cong₂ (λ zo zrs → (zo ∥⇘ csRS' ⇙ zrs) ∖ csRS') WoEq WrsEq)
  decRx-τ-class uniq {ophs} {rb} {sb} step | hτH {B} {e} {a} _ mem parev refl | sndack l₀ dr id
        with Par-ev-elim csRS' ⊤merge (decOutputs l (linkConfig l) ophs) (decRcv l rb ⦀ decSnd l sb) parev
  ...   | evL  ¬cs _   = ⊥-elim (¬cs mem)
  ...   | evR  ¬cs _   = ⊥-elim (¬cs mem)
  ...   | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
  ...   | evSync _ Oev RSev with decOutputs-sndackL {phs = ophs} uniq Oev
  ...     | mem′ , x , refl , gph , WoEq with RS-sndack {rb} {sb} RSev
  ...       | sbEq , WrsEq =
                inj₂ (inj₁ (dr , id , mem′ , x , gph , sbEq ,
                  cong₂ (λ zo zrs → (zo ∥⇘ csRS' ⇙ zrs) ∖ csRS') WoEq WrsEq))
  decRx-τ-class uniq {ophs} {rb} {sb} step | hτH {B} {e} {a} _ mem parev refl | input l₀ dr id  = ⊥-elim mem
  decRx-τ-class uniq {ophs} {rb} {sb} step | hτH {B} {e} {a} _ mem parev refl | output l₀ dr id = ⊥-elim mem
  decRx-τ-class uniq {ophs} {rb} {sb} step | hτH {B} {e} {a} _ mem parev refl | sndmsg l₀ dr id = ⊥-elim mem
  decRx-τ-class uniq {ophs} {rb} {sb} step | hτH {B} {e} {a} _ mem parev refl | tx l₀ dr id     = ⊥-elim mem
  decRx-τ-class uniq {ophs} {rb} {sb} step | hτH {B} {e} {a} _ mem parev refl | rcvack l₀ dr id = ⊥-elim mem
  decRx-τ-class uniq {ophs} {rb} {sb} step | hτH {B} {e} {a} _ mem parev refl | ack l₀ dr id    = ⊥-elim mem

  ------------------------------------------------------------------------
  -- Tx-side top-visible (csTA) gluers: emit tx / accept ack (register), and
  -- accept input (SOLO, fold).  The register events refuse on the fold side
  -- (foreign channel); the SOLO input refuses on the register side.
  ------------------------------------------------------------------------

  -- Tx side emits tx at the Transmitter hold (fold refuses tx)
  decTx-tx : ∀ {iphs tb ab l₀ dr id a W} → decTx l iphs tb ab ─[ ev (evN (tx l₀ dr id) a) ]─► W
           → (l₀ ≡ l) × (tb ≡ hold dr id a) × (W ≡ decTx l iphs (grd dr id a) ab)
  decTx-tx {iphs} {tb} {ab} step
    with Hide-ev-elim csSR' (decInputs l (linkConfig l) iphs ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l ab)) step
  ... | heV _ ¬cs parev
        with Par-ev-elim csSR' ⊤merge (decInputs l (linkConfig l) iphs) (decTrans l tb ⦀ decRAck l ab) parev
  ...   | evSync mem _ _  = ⊥-elim (¬cs mem)
  ...   | evL _ Iev       = ⊥-elim (decInputs-no-txL {phs = iphs} Iev)
  ...   | evBoth _ Iev _  = ⊥-elim (decInputs-no-txL {phs = iphs} Iev)
  ...   | evR _ TRev with TR-txL {tb} {ab} TRev
  ...     | el , eh , Weq = el , eh , cong (λ z → (decInputs l (linkConfig l) iphs ∥⇘ csSR' ⇙ z) ∖ csSR') Weq

  -- Tx side accepts ack at the RcvAck free (fold refuses ack)
  decTx-ack : ∀ {iphs tb ab l₀ dr id W} → decTx l iphs tb ab ─[ ev (evN (ack l₀ dr id) tt) ]─► W
            → (l₀ ≡ l) × (ab ≡ free) × (W ≡ decTx l iphs tb (hold dr id))
  decTx-ack {iphs} {tb} {ab} step
    with Hide-ev-elim csSR' (decInputs l (linkConfig l) iphs ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l ab)) step
  ... | heV _ ¬cs parev
        with Par-ev-elim csSR' ⊤merge (decInputs l (linkConfig l) iphs) (decTrans l tb ⦀ decRAck l ab) parev
  ...   | evSync mem _ _  = ⊥-elim (¬cs mem)
  ...   | evL _ Iev       = ⊥-elim (decInputs-no-ackL {phs = iphs} Iev)
  ...   | evBoth _ Iev _  = ⊥-elim (decInputs-no-ackL {phs = iphs} Iev)
  ...   | evR _ TRev with TR-ackL {tb} {ab} TRev
  ...     | el , ef , Weq = el , ef , cong (λ z → (decInputs l (linkConfig l) iphs ∥⇘ csSR' ⇙ z) ∖ csSR') Weq

  -- Tx side accepts input at a home Input cell (SOLO; register refuses input)
  decTx-input : (uniq : Unique (linkConfig l)) → ∀ {iphs tb ab l₀ dr id a W}
              → decTx l iphs tb ab ─[ ev (evN (input l₀ dr id) a) ]─► W
              → Σ[ mem ∈ (dr , id) ∈ linkConfig l ]
                  (l₀ ≡ l) × (getPh iphs mem ≡ i0) × (W ≡ decTx l (setPh iphs mem (i1 a)) tb ab)
  decTx-input uniq {iphs} {tb} {ab} step
    with Hide-ev-elim csSR' (decInputs l (linkConfig l) iphs ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l ab)) step
  ... | heV _ ¬cs parev
        with Par-ev-elim csSR' ⊤merge (decInputs l (linkConfig l) iphs) (decTrans l tb ⦀ decRAck l ab) parev
  ...   | evSync mem _ _  = ⊥-elim (¬cs mem)
  ...   | evR _ TRev      = ⊥-elim (TR-no-inputL {tb} {ab} TRev)
  ...   | evBoth _ _ TRev = ⊥-elim (TR-no-inputL {tb} {ab} TRev)
  ...   | evL _ Iev with decInputs-inputL {phs = iphs} uniq Iev
  ...     | mem , el , gph , Weq =
              mem , el , gph , cong (λ z → (z ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l ab)) ∖ csSR') Weq

  ------------------------------------------------------------------------
  -- Rx-side top-visible (csTA) gluers: accept tx / emit ack (register), and
  -- emit output (SOLO, fold).
  ------------------------------------------------------------------------

  -- Rx side accepts tx at the Receiver free (fold refuses tx)
  decRx-tx : ∀ {ophs rb sb l₀ dr id a W} → decRx l ophs rb sb ─[ ev (evN (tx l₀ dr id) a) ]─► W
           → (l₀ ≡ l) × (rb ≡ free) × (W ≡ decRx l ophs (hold dr id a) sb)
  decRx-tx {ophs} {rb} {sb} step
    with Hide-ev-elim csRS' (decOutputs l (linkConfig l) ophs ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l sb)) step
  ... | heV _ ¬cs parev
        with Par-ev-elim csRS' ⊤merge (decOutputs l (linkConfig l) ophs) (decRcv l rb ⦀ decSnd l sb) parev
  ...   | evSync mem _ _  = ⊥-elim (¬cs mem)
  ...   | evL _ Oev       = ⊥-elim (decOutputs-no-txL {phs = ophs} Oev)
  ...   | evBoth _ Oev _  = ⊥-elim (decOutputs-no-txL {phs = ophs} Oev)
  ...   | evR _ RSev with RS-txL {rb} {sb} RSev
  ...     | el , ef , Weq = el , ef , cong (λ z → (decOutputs l (linkConfig l) ophs ∥⇘ csRS' ⇙ z) ∖ csRS') Weq

  -- Rx side emits ack at the SndAck hold (fold refuses ack)
  decRx-ack : ∀ {ophs rb sb l₀ dr id W} → decRx l ophs rb sb ─[ ev (evN (ack l₀ dr id) tt) ]─► W
            → (l₀ ≡ l) × (sb ≡ hold dr id) × (W ≡ decRx l ophs rb (grd dr id))
  decRx-ack {ophs} {rb} {sb} step
    with Hide-ev-elim csRS' (decOutputs l (linkConfig l) ophs ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l sb)) step
  ... | heV _ ¬cs parev
        with Par-ev-elim csRS' ⊤merge (decOutputs l (linkConfig l) ophs) (decRcv l rb ⦀ decSnd l sb) parev
  ...   | evSync mem _ _  = ⊥-elim (¬cs mem)
  ...   | evL _ Oev       = ⊥-elim (decOutputs-no-ackL {phs = ophs} Oev)
  ...   | evBoth _ Oev _  = ⊥-elim (decOutputs-no-ackL {phs = ophs} Oev)
  ...   | evR _ RSev with RS-ackL {rb} {sb} RSev
  ...     | el , eh , Weq = el , eh , cong (λ z → (decOutputs l (linkConfig l) ophs ∥⇘ csRS' ⇙ z) ∖ csRS') Weq

  -- Rx side emits output at a ready Output cell (SOLO; register refuses output)
  decRx-output : (uniq : Unique (linkConfig l)) → ∀ {ophs rb sb l₀ dr id a W}
               → decRx l ophs rb sb ─[ ev (evN (output l₀ dr id) a) ]─► W
               → Σ[ mem ∈ (dr , id) ∈ linkConfig l ]
                   (l₀ ≡ l) × (getPh ophs mem ≡ o1 a) × (W ≡ decRx l (setPh ophs mem (o2 a)) rb sb)
  decRx-output uniq {ophs} {rb} {sb} step
    with Hide-ev-elim csRS' (decOutputs l (linkConfig l) ophs ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l sb)) step
  ... | heV _ ¬cs parev
        with Par-ev-elim csRS' ⊤merge (decOutputs l (linkConfig l) ophs) (decRcv l rb ⦀ decSnd l sb) parev
  ...   | evSync mem _ _  = ⊥-elim (¬cs mem)
  ...   | evR _ RSev      = ⊥-elim (RS-no-outputL {rb} {sb} RSev)
  ...   | evBoth _ _ RSev = ⊥-elim (RS-no-outputL {rb} {sb} RSev)
  ...   | evL _ Oev with decOutputs-outputL {phs = ophs} uniq Oev
  ...     | mem , el , gph , Weq =
              mem , el , gph , cong (λ z → (z ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l sb)) ∖ csRS') Weq

  ------------------------------------------------------------------------
  -- Side visible-refutations: the Tx side never offers rcvmsg/sndack/output,
  -- the Rx side never offers sndmsg/rcvack/input (foreign channels, both
  -- levels).  Used by `refl-ev`'s dispatch.
  ------------------------------------------------------------------------

  -- decTx never offers rcvmsg
  decTx-no-rcvmsg : ∀ {iphs tb ab l₀ dr id a W} → decTx l iphs tb ab ─[ ev (evN (rcvmsg l₀ dr id) a) ]─► W → ⊥
  decTx-no-rcvmsg {iphs} {tb} {ab} =
    noStep-∖ {P = decInputs l (linkConfig l) iphs ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l ab)} {A = csSR'} (λ ())
      (noStep-Par {A = csSR'} (decInputs-no-rcvmsgL {phs = iphs})
        (noStep-Par {A = ∅ES} (decTrans-no-rcvmsgL {tb}) (decRAck-no-rcvmsgL {ab})))

  -- decTx never offers sndack
  decTx-no-sndack : ∀ {iphs tb ab l₀ dr id W} → decTx l iphs tb ab ─[ ev (evN (sndack l₀ dr id) tt) ]─► W → ⊥
  decTx-no-sndack {iphs} {tb} {ab} =
    noStep-∖ {P = decInputs l (linkConfig l) iphs ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l ab)} {A = csSR'} (λ ())
      (noStep-Par {A = csSR'} (decInputs-no-sndackL {phs = iphs})
        (noStep-Par {A = ∅ES} (decTrans-no-sndackL {tb}) (decRAck-no-sndackL {ab})))

  -- decTx never offers output
  decTx-no-output : ∀ {iphs tb ab l₀ dr id a W} → decTx l iphs tb ab ─[ ev (evN (output l₀ dr id) a) ]─► W → ⊥
  decTx-no-output {iphs} {tb} {ab} =
    noStep-∖ {P = decInputs l (linkConfig l) iphs ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l ab)} {A = csSR'} (λ ())
      (noStep-Par {A = csSR'} (decInputs-no-outputL {phs = iphs})
        (noStep-Par {A = ∅ES} (decTrans-no-outputL {tb}) (decRAck-no-outputL {ab})))

  -- decRx never offers sndmsg
  decRx-no-sndmsg : ∀ {ophs rb sb l₀ dr id a W} → decRx l ophs rb sb ─[ ev (evN (sndmsg l₀ dr id) a) ]─► W → ⊥
  decRx-no-sndmsg {ophs} {rb} {sb} =
    noStep-∖ {P = decOutputs l (linkConfig l) ophs ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l sb)} {A = csRS'} (λ ())
      (noStep-Par {A = csRS'} (decOutputs-no-sndmsgL {phs = ophs})
        (noStep-Par {A = ∅ES} (decRcv-no-sndmsgL {rb}) (decSnd-no-sndmsgL {sb})))

  -- decRx never offers rcvack
  decRx-no-rcvack : ∀ {ophs rb sb l₀ dr id W} → decRx l ophs rb sb ─[ ev (evN (rcvack l₀ dr id) tt) ]─► W → ⊥
  decRx-no-rcvack {ophs} {rb} {sb} =
    noStep-∖ {P = decOutputs l (linkConfig l) ophs ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l sb)} {A = csRS'} (λ ())
      (noStep-Par {A = csRS'} (decOutputs-no-rcvackL {phs = ophs})
        (noStep-Par {A = ∅ES} (decRcv-no-rcvackL {rb}) (decSnd-no-rcvackL {sb})))

  -- decRx never offers input
  decRx-no-input : ∀ {ophs rb sb l₀ dr id a W} → decRx l ophs rb sb ─[ ev (evN (input l₀ dr id) a) ]─► W → ⊥
  decRx-no-input {ophs} {rb} {sb} =
    noStep-∖ {P = decOutputs l (linkConfig l) ophs ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l sb)} {A = csRS'} (λ ())
      (noStep-Par {A = csRS'} (decOutputs-no-inputL {phs = ophs})
        (noStep-Par {A = ∅ES} (decRcv-no-inputL {rb}) (decSnd-no-inputL {sb})))

  ------------------------------------------------------------------------
  -- DELIVERABLE `refl-τ`: every τ of `⟦ st ⟧` reflects to a `st ⇒ᵢ st′`,
  -- residual definitionally matching.  Mirrors `Step.refl-τ`, the general
  -- gluers supplying the existential `mem`.
  ------------------------------------------------------------------------
  refl-τ : (uniq : Unique (linkConfig l))
         → {st : MuxState l} {M : NetProc}
         → ⟦ st ⟧ ─[ τ ]─► M → Σ[ st′ ∈ MuxState l ] (st ⇒ᵢ st′) × (M ≡ ⟦ st′ ⟧)
  refl-τ uniq {mkMux is os tb rb sb ab} step
    with Hide-τ-elim csTA' (decTx l is tb ab ∥⇘ csTA' ⇙ decRx l os rb sb) step
  ... | hτP _ parτ refl with Par-τ-elim csTA' ⊤merge (decTx l is tb ab) (decRx l os rb sb) parτ
  ...   | τL _ Txτ refl with decTx-τ-class uniq {is} {tb} {ab} Txτ
  ...     | inj₁ (d , id , mem , x , gph , refl , Weq) =
              _ , sndmsg mem gph , cong (λ z → (z ∥⇘ csTA' ⇙ decRx l os rb sb) ∖ csTA') Weq
  ...     | inj₂ (inj₁ (d , id , mem , x , gph , refl , Weq)) =
              _ , rcvack mem gph , cong (λ z → (z ∥⇘ csTA' ⇙ decRx l os rb sb) ∖ csTA') Weq
  ...     | inj₂ (inj₂ (inj₁ (d , id , mem , x , gph , Weq))) =
              _ , gI mem gph , cong (λ z → (z ∥⇘ csTA' ⇙ decRx l os rb sb) ∖ csTA') Weq
  ...     | inj₂ (inj₂ (inj₂ (inj₁ (d , id , x , refl , Weq)))) =
              _ , gT , cong (λ z → (z ∥⇘ csTA' ⇙ decRx l os rb sb) ∖ csTA') Weq
  ...     | inj₂ (inj₂ (inj₂ (inj₂ (d , id , refl , Weq)))) =
              _ , gR , cong (λ z → (z ∥⇘ csTA' ⇙ decRx l os rb sb) ∖ csTA') Weq
  refl-τ uniq {mkMux is os tb rb sb ab} step
    | hτP _ parτ refl | τR _ Rxτ refl with decRx-τ-class uniq {os} {rb} {sb} Rxτ
  ...     | inj₁ (d , id , mem , x , gph , refl , Weq) =
              _ , rcvmsg mem gph , cong (λ z → (decTx l is tb ab ∥⇘ csTA' ⇙ z) ∖ csTA') Weq
  ...     | inj₂ (inj₁ (d , id , mem , x , gph , refl , Weq)) =
              _ , sndack mem gph , cong (λ z → (decTx l is tb ab ∥⇘ csTA' ⇙ z) ∖ csTA') Weq
  ...     | inj₂ (inj₂ (inj₁ (d , id , mem , x , gph , Weq))) =
              _ , gO mem gph , cong (λ z → (decTx l is tb ab ∥⇘ csTA' ⇙ z) ∖ csTA') Weq
  ...     | inj₂ (inj₂ (inj₂ (inj₁ (d , id , x , refl , Weq)))) =
              _ , gRc , cong (λ z → (decTx l is tb ab ∥⇘ csTA' ⇙ z) ∖ csTA') Weq
  ...     | inj₂ (inj₂ (inj₂ (inj₂ (d , id , refl , Weq)))) =
              _ , gSa , cong (λ z → (decTx l is tb ab ∥⇘ csTA' ⇙ z) ∖ csTA') Weq
  refl-τ uniq {mkMux is os tb rb sb ab} step | hτH {B} {e} {a} _ mem parev refl with e
  ...   | tx l₀ dr id with Par-ev-elim csTA' ⊤merge (decTx l is tb ab) (decRx l os rb sb) parev
  ...     | evL  ¬cs _   = ⊥-elim (¬cs mem)
  ...     | evR  ¬cs _   = ⊥-elim (¬cs mem)
  ...     | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
  ...     | evSync _ Txev Rxev with decTx-tx {is} {tb} {ab} Txev
  ...       | refl , refl , WTx with decRx-tx {os} {rb} {sb} Rxev
  ...         | _ , refl , WRx = _ , tx , cong₂ (λ zt zr → (zt ∥⇘ csTA' ⇙ zr) ∖ csTA') WTx WRx
  refl-τ uniq {mkMux is os tb rb sb ab} step | hτH {B} {e} {a} _ mem parev refl | ack l₀ dr id
        with Par-ev-elim csTA' ⊤merge (decTx l is tb ab) (decRx l os rb sb) parev
  ...     | evL  ¬cs _   = ⊥-elim (¬cs mem)
  ...     | evR  ¬cs _   = ⊥-elim (¬cs mem)
  ...     | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
  ...     | evSync _ Txev Rxev with decTx-ack {is} {tb} {ab} Txev
  ...       | refl , refl , WTx with decRx-ack {os} {rb} {sb} Rxev
  ...         | _ , refl , WRx = _ , ack , cong₂ (λ zt zr → (zt ∥⇘ csTA' ⇙ zr) ∖ csTA') WTx WRx
  refl-τ uniq {mkMux is os tb rb sb ab} step | hτH {B} {e} {a} _ mem parev refl | input l₀ dr id  = ⊥-elim mem
  refl-τ uniq {mkMux is os tb rb sb ab} step | hτH {B} {e} {a} _ mem parev refl | output l₀ dr id = ⊥-elim mem
  refl-τ uniq {mkMux is os tb rb sb ab} step | hτH {B} {e} {a} _ mem parev refl | sndmsg l₀ dr id = ⊥-elim mem
  refl-τ uniq {mkMux is os tb rb sb ab} step | hτH {B} {e} {a} _ mem parev refl | rcvmsg l₀ dr id = ⊥-elim mem
  refl-τ uniq {mkMux is os tb rb sb ab} step | hτH {B} {e} {a} _ mem parev refl | rcvack l₀ dr id = ⊥-elim mem
  refl-τ uniq {mkMux is os tb rb sb ab} step | hτH {B} {e} {a} _ mem parev refl | sndack l₀ dr id = ⊥-elim mem

  ------------------------------------------------------------------------
  -- DELIVERABLE `noDiv`: `⟦ st ⟧` never diverges (`refl-τ` + `μ-dec` + `<`-wf).
  ------------------------------------------------------------------------
  noDiv-acc : (uniq : Unique (linkConfig l))
            → (st : MuxState l) → Acc _<_ (μ st) → ¬ Diverges ⟦ st ⟧
  noDiv-acc uniq st (acc rs) dv with refl-τ uniq (dv .Diverges.step)
  ... | st′ , red , Weq =
        noDiv-acc uniq st′ (rs (μ-dec red)) (subst Diverges Weq (dv .Diverges.rest))

  -- the decode never diverges
  noDiv : (uniq : Unique (linkConfig l))
        → (st : MuxState l) → ¬ Diverges ⟦ st ⟧
  noDiv uniq st = noDiv-acc uniq st (<-wellFounded (μ st))

  ------------------------------------------------------------------------
  -- DELIVERABLE `fire-⇒ᵥ` / `fire-⇒ᵢ`: forward construction.  Same stack
  -- as `PerLink.Step`'s per-constructor fires, the fold-intro replacing the
  -- singleton `Par-soloL ∅ES … dIn-*-fire`.  No `cfg≡` exposure is needed —
  -- `decTx`/`decRx` already carry `linkConfig l`.
  ------------------------------------------------------------------------

  -- decode a visible label to its concrete network event
  vev : VLabel → Event√ NetR
  vev (inp d id x) = evN (input l d id) x
  vev (out d id x) = evN (output l d id) x

  -- every visible mux move is the matching visible LTS step of the decode
  fire-⇒ᵥ : (uniq : Unique (linkConfig l))
          → {st : MuxState l} {e : VLabel} {st′ : MuxState l}
          → st ⇒ᵥ⟨ e ⟩ st′ → ⟦ st ⟧ ─[ ev (vev e) ]─► ⟦ st′ ⟧
  fire-⇒ᵥ uniq (input {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb} {ab = ab}
                      {d = d} {id = id} {x = x} mem gi) =
    Hide-keep csTA' (decTx l is tb ab ∥⇘ csTA' ⇙ decRx l os rb sb) (λ ())
      (Par-soloL csTA' ⊤merge (decTx l is tb ab) (decRx l os rb sb) (λ ())
        (Hide-keep csSR' (decInputs l (linkConfig l) is ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l ab)) (λ ())
          (Par-soloL csSR' ⊤merge (decInputs l (linkConfig l) is) (decTrans l tb ⦀ decRAck l ab) (λ ())
            (decInputs-input-fire uniq mem gi)
            (noView {e = input l d id} {a = x}
              (noStep-Par {A = ∅ES} (decTrans-no-input {tb}) (decRAck-no-input {ab})))))
        (noView {e = input l d id} {a = x} (decRx-no-input {os} {rb} {sb})))
  fire-⇒ᵥ uniq (output {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb} {ab = ab}
                       {d = d} {id = id} {x = x} mem gi) =
    Hide-keep csTA' (decTx l is tb ab ∥⇘ csTA' ⇙ decRx l os rb sb) (λ ())
      (Par-soloR csTA' ⊤merge (decTx l is tb ab) (decRx l os rb sb) (λ ())
        (Hide-keep csRS' (decOutputs l (linkConfig l) os ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l sb)) (λ ())
          (Par-soloL csRS' ⊤merge (decOutputs l (linkConfig l) os) (decRcv l rb ⦀ decSnd l sb) (λ ())
            (decOutputs-output-fire uniq mem gi)
            (noView {e = output l d id} {a = x}
              (noStep-Par {A = ∅ES} (decRcv-no-output {rb}) (decSnd-no-output {sb})))))
        (noView {e = output l d id} {a = x} (decTx-no-output {is} {tb} {ab})))

  -- every internal mux move is a τ step of the decode
  fire-⇒ᵢ : (uniq : Unique (linkConfig l))
          → {st st′ : MuxState l} → st ⇒ᵢ st′ → ⟦ st ⟧ ─[ τ ]─► ⟦ st′ ⟧
  -- sndmsg handoff: Input cell (mem) i1→i2 (out) ∥csSR' Transmitter free→hold (in)
  fire-⇒ᵢ uniq (sndmsg {is = is} {os = os} {rb = rb} {sb = sb} {ab = ab} {d = d} {id = id} {x = x} mem gi) =
    Hide-τ csTA' (decTx l is free ab ∥⇘ csTA' ⇙ decRx l os rb sb)
      (Par-τ-L csTA' ⊤merge (decTx l is free ab) (decRx l os rb sb)
        (Hide-hidden csSR' (decInputs l (linkConfig l) is ∥⇘ csSR' ⇙ (decTrans l free ⦀ decRAck l ab)) _
          (Par-sync csSR' ⊤merge (decInputs l (linkConfig l) is) (decTrans l free ⦀ decRAck l ab) _
            (decInputs-sndmsg-fire uniq mem gi)
            (Par-soloL ∅ES ⊤merge (decTrans l free) (decRAck l ab) (λ z → z)
               dTr-free-fire (noView {e = sndmsg l d id} {a = x} (decRAck-no-sndmsg {ab}))))))
  -- rcvack handoff: Input cell (mem) i2→ig (in) ∥csSR' RcvAck hold→grd (out)
  fire-⇒ᵢ uniq (rcvack {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb} {d = d} {id = id} {x = x} mem gi) =
    Hide-τ csTA' (decTx l is tb (hold d id) ∥⇘ csTA' ⇙ decRx l os rb sb)
      (Par-τ-L csTA' ⊤merge (decTx l is tb (hold d id)) (decRx l os rb sb)
        (Hide-hidden csSR' (decInputs l (linkConfig l) is ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l (hold d id))) _
          (Par-sync csSR' ⊤merge (decInputs l (linkConfig l) is) (decTrans l tb ⦀ decRAck l (hold d id)) _
            (decInputs-rcvack-fire uniq mem gi)
            (Par-soloR ∅ES ⊤merge (decTrans l tb) (decRAck l (hold d id)) (λ z → z)
               dRA-hold-fire (noView {e = rcvack l d id} {a = tt} (decTrans-no-rcvack {tb}))))))
  -- rcvmsg handoff: Receiver hold→grd (out) ∥csRS' Output cell (mem) o0→o1 (in)
  fire-⇒ᵢ uniq (rcvmsg {is = is} {os = os} {tb = tb} {sb = sb} {ab = ab} {d = d} {id = id} {x = x} mem gi) =
    Hide-τ csTA' (decTx l is tb ab ∥⇘ csTA' ⇙ decRx l os (hold d id x) sb)
      (Par-τ-R csTA' ⊤merge (decTx l is tb ab) (decRx l os (hold d id x) sb)
        (Hide-hidden csRS' (decOutputs l (linkConfig l) os ∥⇘ csRS' ⇙ (decRcv l (hold d id x) ⦀ decSnd l sb)) _
          (Par-sync csRS' ⊤merge (decOutputs l (linkConfig l) os) (decRcv l (hold d id x) ⦀ decSnd l sb) _
            (decOutputs-rcvmsg-fire uniq mem gi)
            (Par-soloL ∅ES ⊤merge (decRcv l (hold d id x)) (decSnd l sb) (λ z → z)
               dRc-hold-fire (noView {e = rcvmsg l d id} {a = x} (decSnd-no-rcvmsg {sb}))))))
  -- sndack handoff: Output cell (mem) o2→og (out) ∥csRS' SndAck free→hold (in)
  fire-⇒ᵢ uniq (sndack {is = is} {os = os} {tb = tb} {rb = rb} {ab = ab} {d = d} {id = id} {x = x} mem gi) =
    Hide-τ csTA' (decTx l is tb ab ∥⇘ csTA' ⇙ decRx l os rb free)
      (Par-τ-R csTA' ⊤merge (decTx l is tb ab) (decRx l os rb free)
        (Hide-hidden csRS' (decOutputs l (linkConfig l) os ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l free)) _
          (Par-sync csRS' ⊤merge (decOutputs l (linkConfig l) os) (decRcv l rb ⦀ decSnd l free) _
            (decOutputs-sndack-fire uniq mem gi)
            (Par-soloR ∅ES ⊤merge (decRcv l rb) (decSnd l free) (λ z → z)
               dSn-free-fire (noView {e = sndack l d id} {a = tt} (decRcv-no-sndack {rb}))))))
  -- tx handoff: Transmitter hold→grd (out) ∥csTA' Receiver free→hold (in), TOP sync
  fire-⇒ᵢ uniq (tx {is = is} {os = os} {sb = sb} {ab = ab} {d = d} {id = id} {x = x}) =
    Hide-hidden csTA' (decTx l is (hold d id x) ab ∥⇘ csTA' ⇙ decRx l os free sb) _
      (Par-sync csTA' ⊤merge (decTx l is (hold d id x) ab) (decRx l os free sb) _
        (Hide-keep csSR' (decInputs l (linkConfig l) is ∥⇘ csSR' ⇙ (decTrans l (hold d id x) ⦀ decRAck l ab)) (λ ())
          (Par-soloR csSR' ⊤merge (decInputs l (linkConfig l) is) (decTrans l (hold d id x) ⦀ decRAck l ab) (λ ())
            (Par-soloL ∅ES ⊤merge (decTrans l (hold d id x)) (decRAck l ab) (λ z → z)
               dTr-hold-fire (noView {e = tx l d id} {a = x} (decRAck-no-tx {ab})))
            (noView {P = decInputs l (linkConfig l) is} {e = tx l d id} {a = x} (decInputs-no-txL {phs = is}))))
        (Hide-keep csRS' (decOutputs l (linkConfig l) os ∥⇘ csRS' ⇙ (decRcv l free ⦀ decSnd l sb)) (λ ())
          (Par-soloR csRS' ⊤merge (decOutputs l (linkConfig l) os) (decRcv l free ⦀ decSnd l sb) (λ ())
            (Par-soloL ∅ES ⊤merge (decRcv l free) (decSnd l sb) (λ z → z)
               dRc-free-fire (noView {e = tx l d id} {a = x} (decSnd-no-tx {sb})))
            (noView {P = decOutputs l (linkConfig l) os} {e = tx l d id} {a = x} (decOutputs-no-txL {phs = os})))))
  -- ack handoff: SndAck hold→grd (out) ∥csTA' RcvAck free→hold (in), TOP sync
  fire-⇒ᵢ uniq (ack {is = is} {os = os} {tb = tb} {rb = rb} {d = d} {id = id}) =
    Hide-hidden csTA' (decTx l is tb free ∥⇘ csTA' ⇙ decRx l os rb (hold d id)) _
      (Par-sync csTA' ⊤merge (decTx l is tb free) (decRx l os rb (hold d id)) _
        (Hide-keep csSR' (decInputs l (linkConfig l) is ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l free)) (λ ())
          (Par-soloR csSR' ⊤merge (decInputs l (linkConfig l) is) (decTrans l tb ⦀ decRAck l free) (λ ())
            (Par-soloR ∅ES ⊤merge (decTrans l tb) (decRAck l free) (λ z → z)
               dRA-free-fire (noView {e = ack l d id} {a = tt} (decTrans-no-ack {tb})))
            (noView {P = decInputs l (linkConfig l) is} {e = ack l d id} {a = tt} (decInputs-no-ackL {phs = is}))))
        (Hide-keep csRS' (decOutputs l (linkConfig l) os ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l (hold d id))) (λ ())
          (Par-soloR csRS' ⊤merge (decOutputs l (linkConfig l) os) (decRcv l rb ⦀ decSnd l (hold d id)) (λ ())
            (Par-soloR ∅ES ⊤merge (decRcv l rb) (decSnd l (hold d id)) (λ z → z)
               dSn-hold-fire (noView {e = ack l d id} {a = tt} (decRcv-no-ack {rb})))
            (noView {P = decOutputs l (linkConfig l) os} {e = ack l d id} {a = tt} (decOutputs-no-ackL {phs = os})))))
  -- gI: Input guard τ (cell mem, ig → i0)
  fire-⇒ᵢ uniq (gI {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb} {ab = ab} {x = x} mem gi) =
    Hide-τ csTA' (decTx l is tb ab ∥⇘ csTA' ⇙ decRx l os rb sb)
      (Par-τ-L csTA' ⊤merge (decTx l is tb ab) (decRx l os rb sb)
        (Hide-τ csSR' (decInputs l (linkConfig l) is ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l ab))
          (Par-τ-L csSR' ⊤merge (decInputs l (linkConfig l) is) (decTrans l tb ⦀ decRAck l ab)
            (decInputs-ig-τ-fire mem gi))))
  -- gO: Output guard τ (cell mem, og → o0)
  fire-⇒ᵢ uniq (gO {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb} {ab = ab} {x = x} mem gi) =
    Hide-τ csTA' (decTx l is tb ab ∥⇘ csTA' ⇙ decRx l os rb sb)
      (Par-τ-R csTA' ⊤merge (decTx l is tb ab) (decRx l os rb sb)
        (Hide-τ csRS' (decOutputs l (linkConfig l) os ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l sb))
          (Par-τ-L csRS' ⊤merge (decOutputs l (linkConfig l) os) (decRcv l rb ⦀ decSnd l sb)
            (decOutputs-og-τ-fire mem gi))))
  -- gT: Transmitter guard τ (grd → free)
  fire-⇒ᵢ uniq (gT {is = is} {os = os} {rb = rb} {sb = sb} {ab = ab} {d = d} {id = id} {x = x}) =
    Hide-τ csTA' (decTx l is (grd d id x) ab ∥⇘ csTA' ⇙ decRx l os rb sb)
      (Par-τ-L csTA' ⊤merge (decTx l is (grd d id x) ab) (decRx l os rb sb)
        (Hide-τ csSR' (decInputs l (linkConfig l) is ∥⇘ csSR' ⇙ (decTrans l (grd d id x) ⦀ decRAck l ab))
          (Par-τ-R csSR' ⊤merge (decInputs l (linkConfig l) is) (decTrans l (grd d id x) ⦀ decRAck l ab)
            (Par-τ-L ∅ES ⊤merge (decTrans l (grd d id x)) (decRAck l ab) dTr-grd-τ))))
  -- gRc: Receiver guard τ (grd → free)
  fire-⇒ᵢ uniq (gRc {is = is} {os = os} {tb = tb} {sb = sb} {ab = ab} {d = d} {id = id} {x = x}) =
    Hide-τ csTA' (decTx l is tb ab ∥⇘ csTA' ⇙ decRx l os (grd d id x) sb)
      (Par-τ-R csTA' ⊤merge (decTx l is tb ab) (decRx l os (grd d id x) sb)
        (Hide-τ csRS' (decOutputs l (linkConfig l) os ∥⇘ csRS' ⇙ (decRcv l (grd d id x) ⦀ decSnd l sb))
          (Par-τ-R csRS' ⊤merge (decOutputs l (linkConfig l) os) (decRcv l (grd d id x) ⦀ decSnd l sb)
            (Par-τ-L ∅ES ⊤merge (decRcv l (grd d id x)) (decSnd l sb) dRc-grd-τ))))
  -- gSa: SndAck guard τ (grd → free)
  fire-⇒ᵢ uniq (gSa {is = is} {os = os} {tb = tb} {rb = rb} {ab = ab} {d = d} {id = id}) =
    Hide-τ csTA' (decTx l is tb ab ∥⇘ csTA' ⇙ decRx l os rb (grd d id))
      (Par-τ-R csTA' ⊤merge (decTx l is tb ab) (decRx l os rb (grd d id))
        (Hide-τ csRS' (decOutputs l (linkConfig l) os ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l (grd d id)))
          (Par-τ-R csRS' ⊤merge (decOutputs l (linkConfig l) os) (decRcv l rb ⦀ decSnd l (grd d id))
            (Par-τ-R ∅ES ⊤merge (decRcv l rb) (decSnd l (grd d id)) dSn-grd-τ))))
  -- gR: RcvAck guard τ (grd → free)
  fire-⇒ᵢ uniq (gR {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb} {d = d} {id = id}) =
    Hide-τ csTA' (decTx l is tb (grd d id) ∥⇘ csTA' ⇙ decRx l os rb sb)
      (Par-τ-L csTA' ⊤merge (decTx l is tb (grd d id)) (decRx l os rb sb)
        (Hide-τ csSR' (decInputs l (linkConfig l) is ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l (grd d id)))
          (Par-τ-R csSR' ⊤merge (decInputs l (linkConfig l) is) (decTrans l tb ⦀ decRAck l (grd d id))
            (Par-τ-R ∅ES ⊤merge (decTrans l tb) (decRAck l (grd d id)) dRA-grd-τ))))

  ------------------------------------------------------------------------
  -- DELIVERABLE `refl-ev`: every VISIBLE (∉ csTA') step of `⟦ st ⟧` is a
  -- `_⇒ᵥ⟨_⟩_` move whose fired event is `vev e`.  Only `input` (Tx solo)
  -- and `output` (Rx solo) survive the hides; the rest is refuted.
  ------------------------------------------------------------------------
  refl-ev : (uniq : Unique (linkConfig l))
          → {st : MuxState l} {B : Set} {e' : Net Data B} {a' : B} {M : NetProc}
          → ⟦ st ⟧ ─[ ev (evN e' a') ]─► M
          → Σ[ e ∈ VLabel ] Σ[ st′ ∈ MuxState l ]
              (st ⇒ᵥ⟨ e ⟩ st′) × (evN e' a' ≡ vev e) × (M ≡ ⟦ st′ ⟧)
  refl-ev uniq {mkMux is os tb rb sb ab} {B} {e'} {a'} step
    with Hide-ev-elim csTA' (decTx l is tb ab ∥⇘ csTA' ⇙ decRx l os rb sb) step
  ... | heV _ ¬cs parev with e'
  ...   | input l₀ dr id with Par-ev-elim csTA' ⊤merge (decTx l is tb ab) (decRx l os rb sb) parev
  ...     | evSync mem _ _  = ⊥-elim mem
  ...     | evR _ Rxev      = ⊥-elim (decRx-no-input {os} {rb} {sb} Rxev)
  ...     | evBoth _ _ Rxev = ⊥-elim (decRx-no-input {os} {rb} {sb} Rxev)
  ...     | evL _ Txev with decTx-input uniq {is} {tb} {ab} Txev
  ...       | mem , refl , gph , Weq =
                inp dr id a' , _ , input mem gph , refl ,
                cong (λ z → (z ∥⇘ csTA' ⇙ decRx l os rb sb) ∖ csTA') Weq
  refl-ev uniq {mkMux is os tb rb sb ab} {B} {e'} {a'} step | heV _ ¬cs parev | output l₀ dr id
          with Par-ev-elim csTA' ⊤merge (decTx l is tb ab) (decRx l os rb sb) parev
  ...     | evSync mem _ _  = ⊥-elim mem
  ...     | evL _ Txev      = ⊥-elim (decTx-no-output {is} {tb} {ab} Txev)
  ...     | evBoth _ Txev _ = ⊥-elim (decTx-no-output {is} {tb} {ab} Txev)
  ...     | evR _ Rxev with decRx-output uniq {os} {rb} {sb} Rxev
  ...       | mem , refl , gph , Weq =
                out dr id a' , _ , output mem gph , refl ,
                cong (λ z → (decTx l is tb ab ∥⇘ csTA' ⇙ z) ∖ csTA') Weq
  refl-ev uniq {mkMux is os tb rb sb ab} {B} {e'} {a'} step | heV _ ¬cs parev | tx l₀ dr id  = ⊥-elim (¬cs Poly.tt)
  refl-ev uniq {mkMux is os tb rb sb ab} {B} {e'} {a'} step | heV _ ¬cs parev | ack l₀ dr id = ⊥-elim (¬cs Poly.tt)
  refl-ev uniq {mkMux is os tb rb sb ab} {B} {e'} {a'} step | heV _ ¬cs parev | sndmsg l₀ dr id
          with Par-ev-elim csTA' ⊤merge (decTx l is tb ab) (decRx l os rb sb) parev
  ...     | evSync mem _ _  = ⊥-elim mem
  ...     | evL _ Txev      = ⊥-elim (decTx-no-sndmsg {is} {tb} {ab} Txev)
  ...     | evBoth _ Txev _ = ⊥-elim (decTx-no-sndmsg {is} {tb} {ab} Txev)
  ...     | evR _ Rxev      = ⊥-elim (decRx-no-sndmsg {os} {rb} {sb} Rxev)
  refl-ev uniq {mkMux is os tb rb sb ab} {B} {e'} {a'} step | heV _ ¬cs parev | rcvmsg l₀ dr id
          with Par-ev-elim csTA' ⊤merge (decTx l is tb ab) (decRx l os rb sb) parev
  ...     | evSync mem _ _  = ⊥-elim mem
  ...     | evL _ Txev      = ⊥-elim (decTx-no-rcvmsg {is} {tb} {ab} Txev)
  ...     | evBoth _ Txev _ = ⊥-elim (decTx-no-rcvmsg {is} {tb} {ab} Txev)
  ...     | evR _ Rxev      = ⊥-elim (decRx-no-rcvmsg {os} {rb} {sb} Rxev)
  refl-ev uniq {mkMux is os tb rb sb ab} {B} {e'} {a'} step | heV _ ¬cs parev | rcvack l₀ dr id
          with Par-ev-elim csTA' ⊤merge (decTx l is tb ab) (decRx l os rb sb) parev
  ...     | evSync mem _ _  = ⊥-elim mem
  ...     | evL _ Txev      = ⊥-elim (decTx-no-rcvack {is} {tb} {ab} Txev)
  ...     | evBoth _ Txev _ = ⊥-elim (decTx-no-rcvack {is} {tb} {ab} Txev)
  ...     | evR _ Rxev      = ⊥-elim (decRx-no-rcvack {os} {rb} {sb} Rxev)
  refl-ev uniq {mkMux is os tb rb sb ab} {B} {e'} {a'} step | heV _ ¬cs parev | sndack l₀ dr id
          with Par-ev-elim csTA' ⊤merge (decTx l is tb ab) (decRx l os rb sb) parev
  ...     | evSync mem _ _  = ⊥-elim mem
  ...     | evL _ Txev      = ⊥-elim (decTx-no-sndack {is} {tb} {ab} Txev)
  ...     | evBoth _ Txev _ = ⊥-elim (decTx-no-sndack {is} {tb} {ab} Txev)
  ...     | evR _ Rxev      = ⊥-elim (decRx-no-sndack {os} {rb} {sb} Rxev)

  ------------------------------------------------------------------------
  -- DELIVERABLE `no-√`: re-exported from `PerLink.Leaf` (already config-
  -- general — it inducts through the same `decInputs`/`decTrans` stack and
  -- never mentions the config's cardinality).  `Leaf.no-√ l` is exactly the
  -- interface entry, so the top-level six-lemma bundle is
  -- `fire-⇒ᵥ`/`fire-⇒ᵢ`/`refl-τ`/`refl-ev`/`Leaf.no-√ l`/`noDiv`.
  ------------------------------------------------------------------------
  no-√-Fold : (st : MuxState l) {r : NetR} {M : NetProc}
            → ⟦ st ⟧ ─[ ev (√ r) ]─► M → ⊥
  no-√-Fold = no-√ l
