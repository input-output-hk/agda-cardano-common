{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the four-node diamond as a `Topology`
-- instance, and THE FAITHFULNESS GATE.
--
-- `Parametric.Node` builds a network out of a graph.  This module
-- instantiates that graph at the existing four-node diamond (A = 0,
-- B = 1, C = 2, D = 3; links AB = 0, AC = 1, BD = 2, CD = 3), feeds it
-- the EXISTING scripted node logic (`produce`/`consume` of
-- `FourNode.FourNodeDiamond`), and proves
--
--     systemOf (diamondLogic blkA) ≡ systemBroken blkA
--
-- by `refl` — i.e. the generic scaffolding reproduces the hand-written
-- system ON THE NOSE, definitionally, with no bisimulation and no
-- proof obligation.  If this gate could not be closed the abstraction
-- would be wrong, so it is deliberately stated with `≡` and nothing
-- weaker.
--
-- Two orderings are load-bearing and are the first place to look if a
-- later edit breaks the gate:
--   * `endpointsOf` lists a node's endpoints in the SAME order as the
--     `⦀` chain of the corresponding hand-written `nodeA`…`nodeD`
--     (`⦀` is not commutative up to `≡`);
--   * the node indices 0…3 enumerate A, B, C, D in the order of
--     `systemBroken`'s `nodeA ⦀ (nodeB ⦀ (nodeC ⦀ nodeD))`.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.AllPairs as AP
import Data.List.Relation.Unary.All as All
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (0ℓ)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)

open import Process_Trees using (ExtI)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology)

module CSP.Examples.Cardano_network.Parametric.DiamondInstance where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; Block₃; apiES; produce; consume
        ; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondBroken
  using ( systemBroken )
open import CSP.Examples.Cardano_network.Base using (Dir; lo; hi)
open import CSP.Examples.Cardano_network.Net p using (Net_Api; Net_Api-≟; Link)
open import CSP.Examples.Cardano_network.Data p using (Payload)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (_⦀_; _>>=_; _>>_; Skip)

-- the four nodes of the diamond as `Fin 4` indices, in `systemBroken`'s order
nA nB nC nD : Fin 4
nA = fzero
nB = fsuc fzero
nC = fsuc (fsuc fzero)
nD = fsuc (fsuc (fsuc fzero))

-- the (lo-end , hi-end) node pair of each link: AB = (A,B), AC = (A,C), BD = (B,D), CD = (C,D)
dEnds : Link → Fin 4 × Fin 4
dEnds fzero                           = nA , nB
dEnds (fsuc fzero)                    = nA , nC
dEnds (fsuc (fsuc fzero))             = nB , nD
dEnds (fsuc (fsuc (fsuc fzero)))      = nC , nD

-- each node's incident (link , own-direction) endpoints, in the order of the `⦀`
-- chain of the corresponding hand-written node: A = (AB,lo)(AC,lo), B = (AB,hi)(BD,lo),
-- C = (AC,hi)(CD,lo), D = (BD,hi)(CD,hi)
dEndpointsOf : Fin 4 → (Link × Dir) × List (Link × Dir)
dEndpointsOf fzero                      = (linkAB , lo) , (linkAC , lo) ∷ []
dEndpointsOf (fsuc fzero)               = (linkAB , hi) , (linkBD , lo) ∷ []
dEndpointsOf (fsuc (fsuc fzero))        = (linkAC , hi) , (linkCD , lo) ∷ []
dEndpointsOf (fsuc (fsuc (fsuc fzero))) = (linkBD , hi) , (linkCD , hi) ∷ []

-- a two-endpoint list is `Unique` exactly when its two entries differ (every node of
-- the diamond has degree 2, so this is the only shape needed here)
uniq₂ : ∀ {e₀ e₁ : Link × Dir} → e₀ ≢ e₁ → Unique (e₀ ∷ e₁ ∷ [])
uniq₂ ne = AP._∷_ (All._∷_ ne All.[]) (AP._∷_ All.[] AP.[])

-- the four-node diamond as a `Topology`; the soundness/completeness proofs are
-- inline pattern lambdas because their types mention the record's derived `endAt`,
-- which only reduces once the link and direction are concrete
diamond : Topology p
diamond = record
  { numNodes-1 = 3
  ; ends = dEnds
  ; ends-irrefl = λ { fzero ()
                    ; (fsuc fzero) ()
                    ; (fsuc (fsuc fzero)) ()
                    ; (fsuc (fsuc (fsuc fzero))) () }
  ; endpointsOf = dEndpointsOf
  ; endpoints-sound = λ { fzero _ _ (here refl) → refl
                        ; fzero _ _ (there (here refl)) → refl
                        ; (fsuc fzero) _ _ (here refl) → refl
                        ; (fsuc fzero) _ _ (there (here refl)) → refl
                        ; (fsuc (fsuc fzero)) _ _ (here refl) → refl
                        ; (fsuc (fsuc fzero)) _ _ (there (here refl)) → refl
                        ; (fsuc (fsuc (fsuc fzero))) _ _ (here refl) → refl
                        ; (fsuc (fsuc (fsuc fzero))) _ _ (there (here refl)) → refl }
  ; endpoints-complete = λ { _ fzero lo refl → here refl
                           ; _ fzero hi refl → here refl
                           ; _ (fsuc fzero) lo refl → there (here refl)
                           ; _ (fsuc fzero) hi refl → here refl
                           ; _ (fsuc (fsuc fzero)) lo refl → there (here refl)
                           ; _ (fsuc (fsuc fzero)) hi refl → here refl
                           ; _ (fsuc (fsuc (fsuc fzero))) lo refl → there (here refl)
                           ; _ (fsuc (fsuc (fsuc fzero))) hi refl → there (here refl) }
  ; endpoints-unique = λ { fzero                      → uniq₂ λ ()
                         ; (fsuc fzero)               → uniq₂ λ ()
                         ; (fsuc (fsuc fzero))        → uniq₂ λ ()
                         ; (fsuc (fsuc (fsuc fzero))) → uniq₂ λ () }
  }

open import CSP.Examples.Cardano_network.Parametric.Node p diamond apiES
  using (Proc; bundleAt; linkBundles; node; systemOf)

-- the existing scripted per-node application logic, indexed by node: A produces `blkA`
-- on both its server directions, B and C relay, D consumes on both its client links
diamondLogic : Block₃ → Fin 4 → Proc
diamondLogic blkA fzero                      = produce linkAB hi blkA ⦀ produce linkAC hi blkA
diamondLogic _    (fsuc fzero)               = consume linkAB hi >>= λ b → produce linkBD hi b
diamondLogic _    (fsuc (fsuc fzero))        = consume linkAC hi >>= λ b → produce linkCD hi b
diamondLogic _    (fsuc (fsuc (fsuc fzero))) = (consume linkBD hi >> Skip) ⦀ (consume linkCD hi >> Skip)

-- THE GATE: the generic scaffolding, instantiated at the diamond topology with the
-- existing scripted logic, IS the existing hand-written system, definitionally
diamond-faithful : ∀ (blkA : Block₃) → systemOf (diamondLogic blkA) ≡ systemBroken blkA
diamond-faithful blkA = refl

------------------------------------------------------------------------
-- The existing liveness theorem, re-derived over the generic layer
------------------------------------------------------------------------

open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Trace; atom; ¬_; □ᵗ; ◇ᵗ; ⟦_⟧; drop )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Spec
  using ( producedA; arrivedD; brkG1; brkG2 )
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.BlockLivenessProof as BLP

-- the body of `BlockLiveness⁺At` (Liveness/LTL/Spec, verbatim) abstracted over the
-- process, so that it can be transported along the faithfulness gate
LivenessAt : Proc → Set _
LivenessAt P = ∀ (b : Block₃) (tr : Trace (⊤ {0ℓ}) P)
             → (□ᵗ (¬ atom brkG1) tr ⊎ □ᵗ (¬ atom brkG2) tr)
             → ∀ (n : ℕ) → ⟦ atom (producedA b) ⟧ (drop n tr)
             → ◇ᵗ (atom (arrivedD b)) (drop n tr)

-- the four-node block-liveness theorem, restated about the GENERIC system: the
-- scaffolding loses nothing, the transport being the gate itself
blockLiveness-generic : ∀ (blkA : Block₃) → LivenessAt (systemOf (diamondLogic blkA))
blockLiveness-generic blkA =
  subst LivenessAt (sym (diamond-faithful blkA)) (BLP.blockLiveness⁺ blkA)
