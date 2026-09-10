{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the BREAKABLE-MEDIUM equivalence
--
--   NetworkLinkBreakableA ≈DR CopySpecBreakableA
--
-- i.e. the headline `NetworkLink ≈DR CopySpec` of `NetworkLinkEquiv`,
-- re-run one layer up: each link is first renamed into the `Net_Api`
-- alphabet and then interrupted by its own `break l` fault-injection
-- event, and the whole family is interleaved with `⦀Fin numLinks`.
--
-- The route is a three-step congruence chain per link,
--
--   perLink l          : NetOneLink l ≈DR linkCopy l          (PerLink.Exp)
--     → cong-renameMap  : netLinkMediumA l ≈DR linkMediumA l  (unconditional)
--     → cong-△          : breakableNetLinkA l ≈DR breakableLinkA l
--     → cong-⦀Fin       : the whole medium
--
-- carrying `perLink`'s two HONEST hypotheses (`linkConfig l ≢ []` and
-- `Unique (linkConfig l)`) exactly as `NetworkLinkEquiv.netLink≈DR` does.
--
-- THE NEW WORK is the alphabet layer.  `NetworkLinkOffers.linkAlpha` is over
-- the PRE-rename `Net` alphabet and does not mention `break`, so it cannot
-- feed `cong-⦀Fin` here.  This module builds the post-rename family
-- `linkAlphaA` (classify-based, so disjointness is a one-liner) and derives
-- its `OffersOnly` witnesses through the two GENERIC lemmas added for this
-- proof: `OffersOnly-renameMap` (`CSP.Laws.Bisim.RenameOffers`, cross-alphabet)
-- and `OffersOnly-△` (`CSP.Laws.Bisim.DRCongruenceRep`).
--
-- `cong-△`'s three `Sep△` obligations are discharged by the new generic
-- `sep△-from-OffersOnly`, whose `liveL` component needs the medium to be
-- non-terminating — supplied by the new `NoRet` invariant: `NoRet-loop0` for
-- one `Copy` cell, `NoRet-⦀` for the fold (this is where `linkConfig l ≢ []`
-- is spent a SECOND time — the empty fold is `Skip`, which √s), then
-- `NoRet-renameMap` across the rename and `≈DR-NoRet` across `perLink`.
--
-- No postulates, holes, or `NON_TERMINATING` beyond what `PerLink.Exp` and
-- the FD layer already carry.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; _×_; Σ; Σ-syntax; proj₁; proj₂)
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

open import Process_Trees using (PTree; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.MediumEquivA (p : Params) where

open Params p using (numLinks; linkConfig)
open import CSP.Examples.Cardano_network.Base using (Dir; IDs)
open import CSP.Examples.Cardano_network.Net p
  using ( Net; Net-≟; Net_Api; Net_Api-≟; Link
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack
        ; done; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; store; env; break )
open import CSP.Examples.Cardano_network.Data p using (Payload; DecEq-Payload)
open import CSP.Examples.Cardano_network.Network p Payload
  using (NetProc; linkCopy; Copy)
open import CSP.Examples.Cardano_network.NetworkLink p Payload using (NetOneLink)
open import CSP.Examples.Cardano_network.NetCommon p
  using ( ιNet; ιNet⁻¹; ιNet-linv
        ; linkMediumA; breakableLinkA; CopySpecBreakableA
        ; netLinkMediumA; breakableNetLinkA; NetworkLinkBreakableA )
-- the PRE-rename link alphabet and the two `Net`-side confinement results
open import CSP.Examples.Cardano_network.NetworkVerification.NetworkLinkOffers p Payload
  using (linkAlpha; oo-NetOneLink; oo-linkCopy)
-- the per-link equivalence, PROVED (two honest hypotheses, no axiom)
open import CSP.Examples.Cardano_network.NetworkVerification.PerLink.Exp p Payload
  using (perLink)

-- the CSP operator vocabulary at each alphabet (only `⦀⋆` is needed source-side)
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Prefix₀; Skip; _△_; _⦀_; ⦀Fin)
import CSP.Operators {E = Net Payload} (Net-≟ {Payload}) as OpN

-- the confinement / congruence layer at the TARGET alphabet
open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
  using ( Alpha; Disj; OffersOnly; OffersOnly-mono; OffersOnly-Prefix₀
        ; OffersOnly-Skip; OffersOnly-△; NoRet; ≈DR-NoRet
        ; sep△-from-OffersOnly; cong-⦀Fin )
-- …and at the SOURCE alphabet (the `NoRet` half of the chain starts there)
import CSP.Laws.Bisim.DRCongruenceRep (Net-≟ {Payload}) as RepN
open import CSP.Laws.Bisim.DRCongruence (Net_Api-≟ {Payload}) using (Sep△; cong-△)
open import CSP.Laws.Bisim.DRCongruence (Net-≟ {Payload}) using (cong-renameMap)
-- the two GENERIC cross-alphabet transports built for this proof
open import CSP.Laws.Bisim.RenameOffers
  (Net-≟ {Payload}) (Net_Api-≟ {Payload}) ιNet ιNet⁻¹ ιNet-linv
  using (ι-vis-inv; OffersOnly-renameMap; NoRet-renameMap)

open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_≈DR_; drbisim-refl)
open import Semantics.FailuresDivergences {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_≈FD_; _⊑FD_)
open import Semantics.DRImpliesFD {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (drbisim→≈FD)

------------------------------------------------------------------------
-- The POST-rename link alphabets.
------------------------------------------------------------------------

-- the two event kinds a breakable link cell can offer: a renamed wire event or
-- the link's own `break`
data EvKind : Set where
  wire brk : EvKind

-- classify a `Net_Api` event: its kind and the link it belongs to (the node-local
-- `done`/`api*`/`store`/`env` channels belong to no link and classify as `nothing`)
classify : (at : AnyTypes (Net_Api Payload)) → proj₁ at → Maybe (EvKind × Link)
classify (_ , input  l _ _) _ = just (wire , l)
classify (_ , output l _ _) _ = just (wire , l)
classify (_ , sndmsg l _ _) _ = just (wire , l)
classify (_ , rcvmsg l _ _) _ = just (wire , l)
classify (_ , tx     l _ _) _ = just (wire , l)
classify (_ , sndack l _ _) _ = just (wire , l)
classify (_ , rcvack l _ _) _ = just (wire , l)
classify (_ , ack    l _ _) _ = just (wire , l)
classify (_ , break  l)     _ = just (brk  , l)
classify _                  _ = nothing

-- link l's renamed WIRE alphabet: the ι-image of `linkAlpha l`; `break` is NOT in it
linkAlphaN : Link → Alpha
linkAlphaN l at a = classify at a ≡ just (wire , l)

-- link l's fault-injection alphabet: exactly `break l`
breakAlpha : Link → Alpha
breakAlpha l at a = classify at a ≡ just (brk , l)

-- link l's FULL alphabet: any event (of either kind) belonging to link l
linkAlphaA : Link → Alpha
linkAlphaA l at a = Σ[ k ∈ EvKind ] classify at a ≡ just (k , l)

-- the wire alphabet is inside the full one
N⊆A : ∀ (l : Link) at a → linkAlphaN l at a → linkAlphaA l at a
N⊆A l at a q = wire , q

-- the break alphabet is inside the full one
B⊆A : ∀ (l : Link) at a → breakAlpha l at a → linkAlphaA l at a
B⊆A l at a q = brk , q

-- a link's wire events and its `break` are never the same event (different kinds)
disjNB : (l : Link) → Disj (linkAlphaN l) (breakAlpha l)
disjNB l at a q₁ q₂ = case trans (sym q₁) q₂ of λ ()

-- distinct links confine disjoint alphabets: an event classified into both carries
-- both links, forcing them equal
linkAlphaA-disj : ∀ {i j : Link} → i ≢ j → Disj (linkAlphaA i) (linkAlphaA j)
linkAlphaA-disj i≢j at a (k , q₁) (k′ , q₂) =
  case trans (sym q₁) q₂ of λ { refl → i≢j refl }

------------------------------------------------------------------------
-- Alphabet transport across the rename: the eight wire channels are relabelled
-- identically by `ιNet`, every other `Net_Api` channel has no `ιNet`-preimage.
------------------------------------------------------------------------

-- `linkAlphaN l` covers the `ι-vis-inv`-image of `linkAlpha l`
ι-alpha : (l : Link) (bt : AnyTypes (Net_Api Payload)) (b : proj₁ bt)
          (at : AnyTypes (Net Payload)) (a : proj₁ at)
        → ι-vis-inv bt b ≡ just (at , a) → linkAlpha l at a → linkAlphaN l bt b
ι-alpha l (_ , input  l₀ d id) b _ _ refl q = cong (λ x → just (wire , x)) q
ι-alpha l (_ , output l₀ d id) b _ _ refl q = cong (λ x → just (wire , x)) q
ι-alpha l (_ , sndmsg l₀ d id) b _ _ refl q = cong (λ x → just (wire , x)) q
ι-alpha l (_ , rcvmsg l₀ d id) b _ _ refl q = cong (λ x → just (wire , x)) q
ι-alpha l (_ , tx     l₀ d id) b _ _ refl q = cong (λ x → just (wire , x)) q
ι-alpha l (_ , sndack l₀ d id) b _ _ refl q = cong (λ x → just (wire , x)) q
ι-alpha l (_ , rcvack l₀ d id) b _ _ refl q = cong (λ x → just (wire , x)) q
ι-alpha l (_ , ack    l₀ d id) b _ _ refl q = cong (λ x → just (wire , x)) q
ι-alpha l (_ , done  _ _ _) b _ _ () _
ι-alpha l (_ , apiCS _ _ _) b _ _ () _
ι-alpha l (_ , apiBF _ _ _) b _ _ () _
ι-alpha l (_ , apiTS _ _ _) b _ _ () _
ι-alpha l (_ , apiKA _ _ _) b _ _ () _
ι-alpha l (_ , apiLN _ _ _) b _ _ () _
ι-alpha l (_ , apiLF _ _ _) b _ _ () _
ι-alpha l (_ , store _ _ _) b _ _ () _
ι-alpha l (_ , env   _ _ _) b _ _ () _
ι-alpha l (_ , break _)     b _ _ () _

------------------------------------------------------------------------
-- `OffersOnly` for the two renamed mediums and for the breakable cells.
------------------------------------------------------------------------

-- the renamed concrete mux only ever offers link-l wire events
oo-netLinkMediumA : (l : Link) → OffersOnly (linkAlphaN l) (netLinkMediumA l)
oo-netLinkMediumA l = OffersOnly-renameMap (ι-alpha l) (oo-NetOneLink l)

-- the renamed copy bundle only ever offers link-l wire events
oo-linkMediumA : (l : Link) → OffersOnly (linkAlphaN l) (linkMediumA l)
oo-linkMediumA l = OffersOnly-renameMap (ι-alpha l) (oo-linkCopy l)

-- the fault-injection handler offers exactly `break l`, then terminates
oo-break : (l : Link) → OffersOnly (breakAlpha l) (Prefix₀ (break l) (Skip {0ℓ}))
oo-break l = OffersOnly-Prefix₀ (λ _ → refl) OffersOnly-Skip

-- a breakable concrete cell offers only link-l events (wire or its own break)
oo-breakableNetLinkA : (l : Link) → OffersOnly (linkAlphaA l) (breakableNetLinkA l)
oo-breakableNetLinkA l =
  OffersOnly-△ (OffersOnly-mono (N⊆A l) (oo-netLinkMediumA l))
               (OffersOnly-mono (B⊆A l) (oo-break l))

-- a breakable copy cell offers only link-l events (wire or its own break)
oo-breakableLinkA : (l : Link) → OffersOnly (linkAlphaA l) (breakableLinkA l)
oo-breakableLinkA l =
  OffersOnly-△ (OffersOnly-mono (N⊆A l) (oo-linkMediumA l))
               (OffersOnly-mono (B⊆A l) (oo-break l))

------------------------------------------------------------------------
-- `NoRet` for the two mediums — `Sep△`'s `liveL` component.
------------------------------------------------------------------------

-- a `⦀⋆`-fold of a NON-EMPTY mapped list never terminates when its head cell doesn't
-- (`Par` returns only when BOTH operands do); the empty fold is `Skip`, which DOES √,
-- which is precisely why `linkConfig l ≢ []` is needed here as well as in `perLink`
nr-⦀⋆-map : ∀ {B : Set} {f : B → NetProc}
          → (∀ b → RepN.NoRet (f b)) → (xs : List B) → xs ≢ []
          → RepN.NoRet (OpN.⦀⋆ (map f xs))
nr-⦀⋆-map hf []       ne = ⊥-elim (ne refl)
nr-⦀⋆-map hf (x ∷ xs) _  = RepN.NoRet-⦀ (hf x)

-- one Copy cell is a `loop0`, hence never terminates
nr-Copy : (l : Link) (d : Dir) (id : IDs) → RepN.NoRet (Copy l d id)
nr-Copy l d id = RepN.NoRet-loop0

-- a non-empty link's copy bundle never terminates
nr-linkCopy : (l : Link) → linkConfig l ≢ [] → RepN.NoRet (linkCopy l)
nr-linkCopy l ne = nr-⦀⋆-map (λ { (d , id) → nr-Copy l d id }) (linkConfig l) ne

-- renaming preserves non-termination (a renamed `ret` came from a source `ret`)
nr-linkMediumA : (l : Link) → linkConfig l ≢ [] → NoRet (linkMediumA l)
nr-linkMediumA l ne = NoRet-renameMap (nr-linkCopy l ne)

------------------------------------------------------------------------
-- The per-link chain, and the fold.
------------------------------------------------------------------------

-- the renamed per-link equivalence: `cong-renameMap` is UNCONDITIONAL, so this is
-- exactly `perLink`'s content one alphabet up
perLinkA : (l : Link) → linkConfig l ≢ [] → Unique (linkConfig l)
         → netLinkMediumA l ≈DR linkMediumA l
perLinkA l ne uq = cong-renameMap ιNet ιNet⁻¹ ιNet-linv (perLink l ne uq)

-- the concrete side inherits non-termination BACKWARD across the per-link ≈DR
nr-netLinkMediumA : (l : Link) → linkConfig l ≢ [] → Unique (linkConfig l)
                  → NoRet (netLinkMediumA l)
nr-netLinkMediumA l ne uq = ≈DR-NoRet (perLinkA l ne uq) (nr-linkMediumA l ne)

-- separation of the concrete medium from its own break handler
sep△-net : (l : Link) → linkConfig l ≢ [] → Unique (linkConfig l)
         → Sep△ (netLinkMediumA l) (Prefix₀ (break l) (Skip {0ℓ}))
sep△-net l ne uq =
  sep△-from-OffersOnly (disjNB l) (nr-netLinkMediumA l ne uq)
                       (oo-netLinkMediumA l) (oo-break l)

-- separation of the copy medium from its own break handler
sep△-cp : (l : Link) → linkConfig l ≢ []
        → Sep△ (linkMediumA l) (Prefix₀ (break l) (Skip {0ℓ}))
sep△-cp l ne =
  sep△-from-OffersOnly (disjNB l) (nr-linkMediumA l ne)
                       (oo-linkMediumA l) (oo-break l)

-- ONE BREAKABLE LINK: the concrete breakable cell is ≈DR its copy-spec counterpart
breakablePerLink : (l : Link) → linkConfig l ≢ [] → Unique (linkConfig l)
                 → breakableNetLinkA l ≈DR breakableLinkA l
breakablePerLink l ne uq =
  cong-△ (sep△-net l ne uq) (sep△-cp l ne) (sep△-cp l ne)
         (perLinkA l ne uq) (drbisim-refl (Prefix₀ (break l) (Skip {0ℓ})))

-- (A) THE BREAKABLE-MEDIUM EQUIVALENCE, link by link through `cong-⦀Fin`
netLinkBreakable≈DR : (∀ l → linkConfig l ≢ [] × Unique (linkConfig l))
                    → NetworkLinkBreakableA ≈DR CopySpecBreakableA
netLinkBreakable≈DR hyp =
  cong-⦀Fin linkAlphaA
    (λ i j i≢j → linkAlphaA-disj i≢j)
    oo-breakableNetLinkA oo-breakableLinkA
    (λ l → breakablePerLink l (proj₁ (hyp l)) (proj₂ (hyp l)))

-- the failures-divergences equivalence (FDR's [FD= both ways)
netLinkBreakable≈FD : (∀ l → linkConfig l ≢ [] × Unique (linkConfig l))
                    → NetworkLinkBreakableA ≈FD CopySpecBreakableA
netLinkBreakable≈FD hyp = drbisim→≈FD (netLinkBreakable≈DR hyp)

-- the two refinement directions separately
netLinkBreakable⊑FD : (∀ l → linkConfig l ≢ [] × Unique (linkConfig l))
                    → NetworkLinkBreakableA ⊑FD CopySpecBreakableA
netLinkBreakable⊑FD hyp = proj₁ (netLinkBreakable≈FD hyp)

specBreakable⊑FD : (∀ l → linkConfig l ≢ [] × Unique (linkConfig l))
                 → CopySpecBreakableA ⊑FD NetworkLinkBreakableA
specBreakable⊑FD hyp = proj₂ (netLinkBreakable≈FD hyp)
