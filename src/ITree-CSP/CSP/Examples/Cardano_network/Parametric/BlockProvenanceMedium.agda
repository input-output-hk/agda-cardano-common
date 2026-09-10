{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — BLOCK PROVENANCE AT THE COPY MEDIUM:
-- `NetCommon.CopySpecBreakableA` is well-formed (`BlockProvenance.Wf`) on
-- the medium's alphabet `medG` — everything but its one rely, `input`.
--
-- Assembled in three moves, following `MediumEquivA.oo-breakableLinkA`
-- step for step:
--
--   * `linkMediumA l = renameMap (linkCopy l)` — the `Net`-side fact of
--     `Parametric.BlockProvenanceCopy` is TRANSPORTED along `ιNet` by
--     `BlockProvenance.Rename.wf-renameMap`.  Because the source alphabet
--     and carrier there are PULLBACKS of `medG`/`Carries` along `ιNet`,
--     the three transport premises are three `subst`s of ONE fact,
--     `vis-inv-sound`, itself the 18-clause observation that `ιNet⁻¹`
--     answers `just` only on the image of `ιNet` (as `BlockProvenancePeers`
--     does for `ιBF`).
--   * `breakableLinkA l = linkMediumA l △ (break l ⟶₀ Skip)` — the
--     interrupt congruence `wf-△`; the handler is a prefix on a channel
--     that carries no block, then `Skip` (`wf-Skip`: the broken link is
--     the deadlocked, hence trivially well-formed, medium).
--   * `CopySpecBreakableA = ⦀Fin numLinks breakableLinkA` — `wf-⦀Fin`.
--
-- FOR TASK 5.  `medG` INCLUDES `output _ _ _` and EXCLUDES `input _ _ _`,
-- the mirror image of the node side (`peersG`, and `nodeG` shrunk to
-- match, exclude `output`).  So the top-level union of the two guarantee
-- alphabets is total: every block-carrying label — in particular both
-- `ioES` labels, which `wf-Hide`'s `HideCov ioES` needs — is guaranteed by
-- exactly one side.  `Sep ioES medG nodeG` is trivial: outside `ioES`
-- `medG` is total.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.BlockProvenanceMedium where

open import Level using (0ℓ)
open import Data.Empty using (⊥-elim)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl; ⊆-trans)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Process_Trees using (AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O
import CSP.Examples.Cardano_network.Parametric.AnnounceSafe as AS
import CSP.Examples.Cardano_network.Parametric.AnnounceInvariant as AI
import CSP.Examples.Cardano_network.Parametric.BlockProvenance as BP
import CSP.Examples.Cardano_network.Parametric.BlockProvenanceCopy as BPC

-- the same three parameters as every other `Parametric.BlockProvenance*` module
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  open Params p using (Block; numLinks)
  open N p
    using ( Net; Net-≟; Link; Net_Api; Net_Api-≟
          ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
          ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; store; env; break )
  open D p using (Payload)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (Prefix₀; Skip)
  open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (sRet; sSil; sVis; sTau)
  open import CSP.Examples.Cardano_network.NetCommon p
    using ( ιNet; ιNet⁻¹; ιNet-linv
          ; linkMediumA; breakableLinkA; CopySpecBreakableA )
  import CSP.Rename {E₁ = Net Payload} {E₂ = Net_Api Payload} ιNet ιNet⁻¹ ιNet-linv as RenNet
  open AS.Generic p t apiES using (Minted)
  open AI.Generic p t apiES using (WellAnnounced)
  open BP.Generic p t apiES
  open BPC.Generic p t apiES using (medG; cpG; CarriesCp; wf-linkCopy)

  ------------------------------------------------------------------------
  -- The copy bundle: transport along `ιNet`
  ------------------------------------------------------------------------

  -- the two carriers the transport relates: the state-agnostic source one of
  -- `BlockProvenanceCopy` and this module's target one — the SAME arguments both give
  module RNet = BP.Rename (Net-≟ {Payload}) (Net_Api-≟ {Payload}) ιNet ιNet⁻¹ ιNet-linv
                          Minted Block CarriesCp Carries WellAnnounced
                          next _⊆_ ⊆-refl ⊆-trans next-⊇

  -- `ιNet⁻¹` answers `just e₁` only on `ιNet e₁`: one clause per `Net_Api` shape
  ιNet⁻¹-sound : ∀ {A} (e₂ : Net_Api Payload A) (e₁ : Net Payload A)
               → ιNet⁻¹ e₂ ≡ just e₁ → e₂ ≡ ιNet e₁
  ιNet⁻¹-sound (input  _ _ _) _ refl = refl
  ιNet⁻¹-sound (output _ _ _) _ refl = refl
  ιNet⁻¹-sound (sndmsg _ _ _) _ refl = refl
  ιNet⁻¹-sound (rcvmsg _ _ _) _ refl = refl
  ιNet⁻¹-sound (tx     _ _ _) _ refl = refl
  ιNet⁻¹-sound (sndack _ _ _) _ refl = refl
  ιNet⁻¹-sound (rcvack _ _ _) _ refl = refl
  ιNet⁻¹-sound (ack    _ _ _) _ refl = refl
  ιNet⁻¹-sound (done   _ _ _) _ ()
  ιNet⁻¹-sound (apiCS  _ _ _) _ ()
  ιNet⁻¹-sound (apiBF  _ _ _) _ ()
  ιNet⁻¹-sound (apiTS  _ _ _) _ ()
  ιNet⁻¹-sound (apiKA  _ _ _) _ ()
  ιNet⁻¹-sound (apiLN  _ _ _) _ ()
  ιNet⁻¹-sound (apiLF  _ _ _) _ ()
  ιNet⁻¹-sound (store  _ _ _) _ ()
  ιNet⁻¹-sound (env    _ _ _) _ ()
  ιNet⁻¹-sound (break  _)     _ ()

  -- a concrete target event: a channel and a value on it
  ConcEv : Set₁
  ConcEv = Σ[ bt ∈ AnyTypes (Net_Api Payload) ] proj₁ bt

  -- THE ONE TRANSPORT FACT: `ι-vis-inv` answers `just (at , a)` only on the ι-image
  -- of `at`, carrying that same `a`
  vis-inv-sound : ∀ bt b at a → RenNet.ι-vis-inv bt b ≡ just (at , a)
                → _≡_ {A = ConcEv} (bt , b) ((proj₁ at , ιNet (proj₂ at)) , a)
  vis-inv-sound (A , e₂) b at a eq with ιNet⁻¹ e₂ in eq′
  ... | nothing = case eq of λ ()
  ... | just e₁ with just-injective eq
  ...   | refl = cong (λ e → (A , e) , b) (ιNet⁻¹-sound e₂ e₁ eq′)

  -- the three premises of `wf-renameMap`, each a `subst` along it: the alphabet pulls
  -- back, and the carried block is the same on both sides
  al : ∀ bt b at a → RenNet.ι-vis-inv bt b ≡ just (at , a) → medG bt b → cpG at a
  al bt b (A , e) a eq = subst (λ ce → medG (proj₁ ce) (proj₂ ce)) (vis-inv-sound bt b (A , e) a eq)

  c→ : ∀ bt b at a → RenNet.ι-vis-inv bt b ≡ just (at , a)
     → ∀ {blk} → Carries bt b blk → CarriesCp at a blk
  c→ bt b (A , e) a eq {blk} =
    subst (λ ce → Carries (proj₁ ce) (proj₂ ce) blk) (vis-inv-sound bt b (A , e) a eq)

  c← : ∀ bt b at a → RenNet.ι-vis-inv bt b ≡ just (at , a)
     → ∀ {blk} → CarriesCp at a blk → Carries bt b blk
  c← bt b (A , e) a eq {blk} =
    subst (λ ce → Carries (proj₁ ce) (proj₂ ce) blk) (sym (vis-inv-sound bt b (A , e) a eq))

  -- ONE LINK'S COPY BUNDLE, in the network alphabet
  wf-linkMediumA : ∀ {ms} (l : Link) → Wf medG ms (linkMediumA l)
  wf-linkMediumA l = RNet.wf-renameMap al c→ c← (wf-linkCopy l)

  ------------------------------------------------------------------------
  -- The break handler, the breakable link, the medium
  ------------------------------------------------------------------------

  -- the fault-injection handler `break l ⟶₀ Skip`: its one channel carries no block
  -- (`λ ()` on `Carries`), and it continues as `Skip`.  The `with` mirrors
  -- `Prefix-cont`'s own decision, as `BlockProvenanceWfR.wfR-Prefix` does.
  wf-break : ∀ {ms} (l : Link) → Wf medG ms (Prefix₀ (break l) (Skip {0ℓ}))
  wf-break l .nowW _ _ (sVis {at = at} refl br) with Net_Api-≟ (_ , break l) at
  ... | no  _    = ⊥-elim (case br of λ ())
  ... | yes refl = λ ()
  wf-break l .stepW _ (sRet ())
  wf-break l .stepW _ (sSil ())
  wf-break l .stepW _ (sTau refl ())
  wf-break l .stepW _ (sVis {at = at} refl br) _ with Net_Api-≟ (_ , break l) at
  ... | no  _    = ⊥-elim (case br of λ ())
  ... | yes refl = subst (Wf _ _) (just-injective br) wf-Skip

  -- ONE BREAKABLE LINK: the bundle until its `break` fires, then nothing
  wf-breakableLinkA : ∀ {ms} (l : Link) → Wf medG ms (breakableLinkA l)
  wf-breakableLinkA l = wf-△ (wf-linkMediumA l) (wf-break l)

  -- THE COPY MEDIUM: every link's breakable bundle, interleaved
  wf-CopySpecBreakableA : ∀ {ms} → Wf medG ms CopySpecBreakableA
  wf-CopySpecBreakableA = wf-⦀Fin numLinks wf-breakableLinkA
