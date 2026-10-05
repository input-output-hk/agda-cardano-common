{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- PipePairAssemblyFlip — the FourNode M3 FLIPPED bundle bisim: the eight
-- flipped per-peer `≈DR` bisims (client lo / server hi) folded by cong-⦀ into
-- `b0flip : (l) → miniProtocols l lo hi ≈DR specBundleFlip l`.  The mirror of
-- M1's `PipePairAssembly.b0`.  Impl-side per-peer OffersOnly at the flipped
-- dir are derived for FREE via `≈DR-OO` from the ∀d spec-side peerAlpha OOs.
--
-- No postulates, holes, or `NON_TERMINATING`.  Script-generated
-- (`.superpowers/sdd/gen-assembly-flip.py`; only the Agda is committed).
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p )
open import CSP.Examples.Cardano_network.Params using (Params)
open Params p
open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.Net p

open import CSP.Examples.Cardano_network.NetworkPar p
  using ( KAclientA; KAserverA; CSclientA; CSserverA
        ; BFclientA; BFserverA; TSclientA; TSserverA; miniProtocols )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _⦀_; ∅ES; EventSet )
open EventSet using ( mem )

open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _≈DR_ )

open import CSP.Laws.Bisim.DRCongruence (Net_Api-≟ {Payload})
  using ( Sep; cong-⦀ )
open Sep
open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
  using ( Alpha; OffersOnly; OffersOnly-mono; OffersOnly-⦀; sep-from-OffersOnly; ≈DR-OO )

-- the contract surface + peer alphabets + all spec-side OffersOnly (∀d)
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePair
-- the flipped spec bundle (mirror of miniProtocols l lo hi)
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.NodeAOffers
  using ( specBundleFlip )
-- the eight flipped per-peer bisims (client lo / server hi)
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairFlipKAs using ( kaServer≈DRhi )
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairFlipKAc using ( kaClient≈DRlo )
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairFlipBFs using ( bfServer≈DRhi )
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairFlipBFc using ( bfClient≈DRlo )
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairFlipCSs using ( csServer≈DRhi )
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairFlipCSc using ( csClient≈DRlo )
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairFlipTSs using ( tsServer≈DRhi )
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairFlipTSc using ( tsClient≈DRlo )

module CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairAssemblyFlip where

-- impl-side per-peer OffersOnly at the flipped dir, derived via ≈DR-OO from the
-- ∀d spec-side peerAlpha OO + the flipped bisim (backward OffersOnly transfer)
kaClient-OOlo : (l : Link) → OffersOnly (peerAlpha N2N_KeepAlive lo) (KAclientA l lo)
kaClient-OOlo l = ≈DR-OO (kaClient≈DRlo l) (kaClientSpec-OffersOnly l lo)
kaServer-OOhi : (l : Link) → OffersOnly (peerAlpha N2N_KeepAlive hi) (KAserverA l hi)
kaServer-OOhi l = ≈DR-OO (kaServer≈DRhi l) (kaServerSpec-OffersOnly l hi)
csClient-OOlo : (l : Link) → OffersOnly (peerAlpha N2N_ChainSync lo) (CSclientA l lo)
csClient-OOlo l = ≈DR-OO (csClient≈DRlo l) (csClientSpec-OffersOnly l lo)
csServer-OOhi : (l : Link) → OffersOnly (peerAlpha N2N_ChainSync hi) (CSserverA l hi)
csServer-OOhi l = ≈DR-OO (csServer≈DRhi l) (csServerSpec-OffersOnly l hi)
bfClient-OOlo : (l : Link) → OffersOnly (peerAlpha N2N_BlockFetch lo) (BFclientA l lo)
bfClient-OOlo l = ≈DR-OO (bfClient≈DRlo l) (bfClientSpec-OffersOnly l lo)
bfServer-OOhi : (l : Link) → OffersOnly (peerAlpha N2N_BlockFetch hi) (BFserverA l hi)
bfServer-OOhi l = ≈DR-OO (bfServer≈DRhi l) (bfServerSpec-OffersOnly l hi)
tsClient-OOlo : (l : Link) → OffersOnly (peerAlpha N2N_TxSubmission lo) (TSclientA l lo)
tsClient-OOlo l = ≈DR-OO (tsClient≈DRlo l) (tsClientSpec-OffersOnly l lo)
tsServer-OOhi : (l : Link) → OffersOnly (peerAlpha N2N_TxSubmission hi) (TSserverA l hi)
tsServer-OOhi l = ≈DR-OO (tsServer≈DRhi l) (tsServerSpec-OffersOnly l hi)

-- the per-link flipped assembly (client dir lo, server dir hi)
module _ (l : Link) where

  -- tail-union alphabets: Uk confines the ⦀-bundle of peers k..7
  U7 : Alpha
  U7 = peerAlpha N2N_TxSubmission hi
  U6 : Alpha
  U6 at a = peerAlpha N2N_TxSubmission lo at a ⊎ U7 at a
  U5 : Alpha
  U5 at a = peerAlpha N2N_BlockFetch hi at a ⊎ U6 at a
  U4 : Alpha
  U4 at a = peerAlpha N2N_BlockFetch lo at a ⊎ U5 at a
  U3 : Alpha
  U3 at a = peerAlpha N2N_ChainSync hi at a ⊎ U4 at a
  U2 : Alpha
  U2 at a = peerAlpha N2N_ChainSync lo at a ⊎ U3 at a
  U1 : Alpha
  U1 at a = peerAlpha N2N_KeepAlive hi at a ⊎ U2 at a

  -- impl-side tail-bundle OffersOnly (fold of OffersOnly-⦀ + mono into Uk)
  ooI7 : OffersOnly U7 (TSserverA l hi)
  ooI7 = tsServer-OOhi l
  ooI6 : OffersOnly U6 (TSclientA l lo ⦀ (TSserverA l hi))
  ooI6 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (tsClient-OOlo l))
                        (OffersOnly-mono (λ _ _ → inj₂) ooI7)
  ooI5 : OffersOnly U5 (BFserverA l hi ⦀ (TSclientA l lo ⦀ (TSserverA l hi)))
  ooI5 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (bfServer-OOhi l))
                        (OffersOnly-mono (λ _ _ → inj₂) ooI6)
  ooI4 : OffersOnly U4 (BFclientA l lo ⦀ (BFserverA l hi ⦀ (TSclientA l lo ⦀ (TSserverA l hi))))
  ooI4 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (bfClient-OOlo l))
                        (OffersOnly-mono (λ _ _ → inj₂) ooI5)
  ooI3 : OffersOnly U3 (CSserverA l hi ⦀ (BFclientA l lo ⦀ (BFserverA l hi ⦀ (TSclientA l lo ⦀ (TSserverA l hi)))))
  ooI3 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (csServer-OOhi l))
                        (OffersOnly-mono (λ _ _ → inj₂) ooI4)
  ooI2 : OffersOnly U2 (CSclientA l lo ⦀ (CSserverA l hi ⦀ (BFclientA l lo ⦀ (BFserverA l hi ⦀ (TSclientA l lo ⦀ (TSserverA l hi))))))
  ooI2 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (csClient-OOlo l))
                        (OffersOnly-mono (λ _ _ → inj₂) ooI3)
  ooI1 : OffersOnly U1 (KAserverA l hi ⦀ (CSclientA l lo ⦀ (CSserverA l hi ⦀ (BFclientA l lo ⦀ (BFserverA l hi ⦀ (TSclientA l lo ⦀ (TSserverA l hi)))))))
  ooI1 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (kaServer-OOhi l))
                        (OffersOnly-mono (λ _ _ → inj₂) ooI2)

  -- spec-side tail-bundle OffersOnly
  ooS7 : OffersOnly U7 (tsServerSpec l hi)
  ooS7 = tsServerSpec-OffersOnly l hi
  ooS6 : OffersOnly U6 (tsClientSpec l lo ⦀ (tsServerSpec l hi))
  ooS6 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (tsClientSpec-OffersOnly l lo))
                        (OffersOnly-mono (λ _ _ → inj₂) ooS7)
  ooS5 : OffersOnly U5 (bfServerSpec l hi ⦀ (tsClientSpec l lo ⦀ (tsServerSpec l hi)))
  ooS5 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (bfServerSpec-OffersOnly l hi))
                        (OffersOnly-mono (λ _ _ → inj₂) ooS6)
  ooS4 : OffersOnly U4 (bfClientSpec l lo ⦀ (bfServerSpec l hi ⦀ (tsClientSpec l lo ⦀ (tsServerSpec l hi))))
  ooS4 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (bfClientSpec-OffersOnly l lo))
                        (OffersOnly-mono (λ _ _ → inj₂) ooS5)
  ooS3 : OffersOnly U3 (csServerSpec l hi ⦀ (bfClientSpec l lo ⦀ (bfServerSpec l hi ⦀ (tsClientSpec l lo ⦀ (tsServerSpec l hi)))))
  ooS3 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (csServerSpec-OffersOnly l hi))
                        (OffersOnly-mono (λ _ _ → inj₂) ooS4)
  ooS2 : OffersOnly U2 (csClientSpec l lo ⦀ (csServerSpec l hi ⦀ (bfClientSpec l lo ⦀ (bfServerSpec l hi ⦀ (tsClientSpec l lo ⦀ (tsServerSpec l hi))))))
  ooS2 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (csClientSpec-OffersOnly l lo))
                        (OffersOnly-mono (λ _ _ → inj₂) ooS3)
  ooS1 : OffersOnly U1 (kaServerSpec l hi ⦀ (csClientSpec l lo ⦀ (csServerSpec l hi ⦀ (bfClientSpec l lo ⦀ (bfServerSpec l hi ⦀ (tsClientSpec l lo ⦀ (tsServerSpec l hi)))))))
  ooS1 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (kaServerSpec-OffersOnly l hi))
                        (OffersOnly-mono (λ _ _ → inj₂) ooS2)

  -- the flipped bundle bisim: fold cong-⦀ from the innermost pair outward
  b7 : (TSserverA l hi) ≈DR (tsServerSpec l hi)
  b7 = tsServer≈DRhi l
  b6 : (TSclientA l lo ⦀ (TSserverA l hi)) ≈DR (tsClientSpec l lo ⦀ (tsServerSpec l hi))
  b6 = cong-⦀ (sep-from-OffersOnly ∅ES (λ {at} {a} _ h t → peerAlpha-Disj (λ ()) at a h t) (tsClient-OOlo l) ooI7)
                (sep-from-OffersOnly ∅ES (λ {at} {a} _ h t → peerAlpha-Disj (λ ()) at a h t) (tsClientSpec-OffersOnly l lo) ooI7)
                (sep-from-OffersOnly ∅ES (λ {at} {a} _ h t → peerAlpha-Disj (λ ()) at a h t) (tsClientSpec-OffersOnly l lo) ooS7)
                (tsClient≈DRlo l) b7
  b5 : (BFserverA l hi ⦀ (TSclientA l lo ⦀ (TSserverA l hi))) ≈DR (bfServerSpec l hi ⦀ (tsClientSpec l lo ⦀ (tsServerSpec l hi)))
  b5 = cong-⦀ (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (t)) → peerAlpha-Disj (λ ()) at a h t }) (bfServer-OOhi l) ooI6)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (t)) → peerAlpha-Disj (λ ()) at a h t }) (bfServerSpec-OffersOnly l hi) ooI6)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (t)) → peerAlpha-Disj (λ ()) at a h t }) (bfServerSpec-OffersOnly l hi) ooS6)
                (bfServer≈DRhi l) b6
  b4 : (BFclientA l lo ⦀ (BFserverA l hi ⦀ (TSclientA l lo ⦀ (TSserverA l hi)))) ≈DR (bfClientSpec l lo ⦀ (bfServerSpec l hi ⦀ (tsClientSpec l lo ⦀ (tsServerSpec l hi))))
  b4 = cong-⦀ (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (t))) → peerAlpha-Disj (λ ()) at a h t }) (bfClient-OOlo l) ooI5)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (t))) → peerAlpha-Disj (λ ()) at a h t }) (bfClientSpec-OffersOnly l lo) ooI5)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (t))) → peerAlpha-Disj (λ ()) at a h t }) (bfClientSpec-OffersOnly l lo) ooS5)
                (bfClient≈DRlo l) b5
  b3 : (CSserverA l hi ⦀ (BFclientA l lo ⦀ (BFserverA l hi ⦀ (TSclientA l lo ⦀ (TSserverA l hi))))) ≈DR (csServerSpec l hi ⦀ (bfClientSpec l lo ⦀ (bfServerSpec l hi ⦀ (tsClientSpec l lo ⦀ (tsServerSpec l hi)))))
  b3 = cong-⦀ (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (t)))) → peerAlpha-Disj (λ ()) at a h t }) (csServer-OOhi l) ooI4)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (t)))) → peerAlpha-Disj (λ ()) at a h t }) (csServerSpec-OffersOnly l hi) ooI4)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (t)))) → peerAlpha-Disj (λ ()) at a h t }) (csServerSpec-OffersOnly l hi) ooS4)
                (csServer≈DRhi l) b4
  b2 : (CSclientA l lo ⦀ (CSserverA l hi ⦀ (BFclientA l lo ⦀ (BFserverA l hi ⦀ (TSclientA l lo ⦀ (TSserverA l hi)))))) ≈DR (csClientSpec l lo ⦀ (csServerSpec l hi ⦀ (bfClientSpec l lo ⦀ (bfServerSpec l hi ⦀ (tsClientSpec l lo ⦀ (tsServerSpec l hi))))))
  b2 = cong-⦀ (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (t))))) → peerAlpha-Disj (λ ()) at a h t }) (csClient-OOlo l) ooI3)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (t))))) → peerAlpha-Disj (λ ()) at a h t }) (csClientSpec-OffersOnly l lo) ooI3)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (t))))) → peerAlpha-Disj (λ ()) at a h t }) (csClientSpec-OffersOnly l lo) ooS3)
                (csClient≈DRlo l) b3
  b1 : (KAserverA l hi ⦀ (CSclientA l lo ⦀ (CSserverA l hi ⦀ (BFclientA l lo ⦀ (BFserverA l hi ⦀ (TSclientA l lo ⦀ (TSserverA l hi))))))) ≈DR (kaServerSpec l hi ⦀ (csClientSpec l lo ⦀ (csServerSpec l hi ⦀ (bfClientSpec l lo ⦀ (bfServerSpec l hi ⦀ (tsClientSpec l lo ⦀ (tsServerSpec l hi)))))))
  b1 = cong-⦀ (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (t)))))) → peerAlpha-Disj (λ ()) at a h t }) (kaServer-OOhi l) ooI2)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (t)))))) → peerAlpha-Disj (λ ()) at a h t }) (kaServerSpec-OffersOnly l hi) ooI2)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (t)))))) → peerAlpha-Disj (λ ()) at a h t }) (kaServerSpec-OffersOnly l hi) ooS2)
                (kaServer≈DRhi l) b2
  b0 : (KAclientA l lo ⦀ (KAserverA l hi ⦀ (CSclientA l lo ⦀ (CSserverA l hi ⦀ (BFclientA l lo ⦀ (BFserverA l hi ⦀ (TSclientA l lo ⦀ (TSserverA l hi)))))))) ≈DR (kaClientSpec l lo ⦀ (kaServerSpec l hi ⦀ (csClientSpec l lo ⦀ (csServerSpec l hi ⦀ (bfClientSpec l lo ⦀ (bfServerSpec l hi ⦀ (tsClientSpec l lo ⦀ (tsServerSpec l hi))))))))
  b0 = cong-⦀ (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t)))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (t))))))) → peerAlpha-Disj (λ ()) at a h t }) (kaClient-OOlo l) ooI1)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t)))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (t))))))) → peerAlpha-Disj (λ ()) at a h t }) (kaClientSpec-OffersOnly l lo) ooI1)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t)))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (t))))))) → peerAlpha-Disj (λ ()) at a h t }) (kaClientSpec-OffersOnly l lo) ooS1)
                (kaClient≈DRlo l) b1

-- THE FLIPPED BUNDLE BISIM: miniProtocols l lo hi ≈DR specBundleFlip l
b0flip : (l : Link) → miniProtocols l lo hi ≈DR specBundleFlip l
b0flip l = b0 l
