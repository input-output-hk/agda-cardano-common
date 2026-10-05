{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- PipePairAssembly — the FourNode M1 (Part 14) ASSEMBLY: the eight
-- per-peer `≈DR` bisims (KA/CS/BF/TS × client/server, all ∀l) + the
-- verbatim driver are glued into `pipe l hi ≈DR pipeSpec l hi` by the
-- proven congruences.  The 7 inner `cong-⦀`s discharge their `Sep ∅ES`
-- side-conditions from the per-peer `OffersOnly`s via `sep-from-OffersOnly`
-- + the pairwise-disjoint peer alphabets (`peerAlpha-Disj`); the top-level
-- `cong-Par⊤ apiES` uses the asymmetric `sep-R` (the driver offers only
-- apiES events) and `drbisim-refl` for the driver leg.  goalBD/goalCD PROVED.
--
-- No postulates, holes, or `NON_TERMINATING`.  Script-generated
-- (`.superpowers/sdd/gen-assembly.py`; only the Agda is committed).
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
  using ( p; consume; apiES; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Params using (Params)
open Params p
open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.Net p

open import CSP.Examples.Cardano_network.NetworkPar p
  using ( KAclientA; KAserverA; CSclientA; CSserverA
        ; BFclientA; BFserverA; TSclientA; TSserverA; miniProtocols )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _>>_; Skip; ∅ES; EventSet )
open EventSet using ( mem )

open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _≈DR_; drbisim-refl )
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )

open import CSP.Laws.Bisim.DRCongruence (Net_Api-≟ {Payload})
  using ( Sep; cong-⦀; cong-Par⊤ )
open Sep
open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
  using ( Alpha; OffersOnly; OffersOnly-mono; OffersOnly-⦀; sep-from-OffersOnly
        ; OffersOnly->>=; OffersOnly-Prefix; OffersOnly-Prefix₀
        ; OffersOnly-Output; OffersOnly-Ret; OffersOnly-Skip )

-- the contract surface + peer alphabets + KA/BF impl OO + all spec OO + driver
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePair
-- CS/TS impl-side OffersOnly
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairPeers2
  using ( csServer-OO; csClient-OO; tsServer-OO; tsClient-OO )
-- the eight per-peer bisims
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairPeersKB
  using ( kaServer≈DR; bfServer≈DR; kaClient≈DR )
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairPeersKB2
  using ( bfClient≈DR )
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairPeers3
  using ( csServer≈DR )
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairPeers4
  using ( csClient≈DR )
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairPeers5
  using ( tsServer≈DR )
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairPeers6
  using ( tsClient≈DR )

module CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairAssembly where

-- asymmetric Sep intro: if Q offers only events inside the sync set A, then
-- Q never both-offers a non-sync event with ANY P, so `Sep A P Q` for all P.
sep-R : {A : EventSet} {β : Alpha} {Q : NetTree}
      → OffersOnly β Q → (∀ {at a} → β at a → A .mem at a)
      → (P : NetTree) → Sep A P Q
sep-R ooQ sub P .now ¬m Pst Qst = ¬m (sub (OffersOnly.now ooQ Qst))
sep-R ooQ sub P .stepL Pst = sep-R ooQ sub _
sep-R ooQ sub P .stepR Qst = sep-R (OffersOnly.step ooQ Qst) sub P

-- the api sync set viewed as an Alpha (value-blind)
apiAlpha : Alpha
apiAlpha at a = apiES .mem at a

-- the driver confines TIGHTLY to apiES (only apiCS/apiBF fire; all ∈ apiES)
consume-OO-api : (l : Link) → OffersOnly apiAlpha (consume l hi >> Skip {0ℓ})
consume-OO-api l =
  OffersOnly->>=
    (OffersOnly-Prefix₀ (λ _ → tt)
      (OffersOnly-Prefix (λ _ → tt)
        (λ { (header b , _) →
          OffersOnly-Output tt
            (OffersOnly-Prefix (λ _ → tt)
              (λ b′ →
                OffersOnly-Output tt
                  (OffersOnly-Prefix₀ (λ _ → tt) OffersOnly-Ret)))})))
    (λ _ → OffersOnly-Skip)

-- the per-link assembly (client dir hi, server dir lo = flipDir hi)
module _ (l : Link) where

  -- tail-union alphabets: Uk confines the ⦀-bundle of peers k..7
  U7 : Alpha
  U7 = peerAlpha N2N_TxSubmission lo
  U6 : Alpha
  U6 at a = peerAlpha N2N_TxSubmission hi at a ⊎ U7 at a
  U5 : Alpha
  U5 at a = peerAlpha N2N_BlockFetch lo at a ⊎ U6 at a
  U4 : Alpha
  U4 at a = peerAlpha N2N_BlockFetch hi at a ⊎ U5 at a
  U3 : Alpha
  U3 at a = peerAlpha N2N_ChainSync lo at a ⊎ U4 at a
  U2 : Alpha
  U2 at a = peerAlpha N2N_ChainSync hi at a ⊎ U3 at a
  U1 : Alpha
  U1 at a = peerAlpha N2N_KeepAlive lo at a ⊎ U2 at a

  -- impl-side tail-bundle OffersOnly (fold of OffersOnly-⦀ + mono into Uk)
  ooI7 : OffersOnly U7 (TSserverA l lo)
  ooI7 = tsServer-OO l
  ooI6 : OffersOnly U6 (TSclientA l hi ⦀ (TSserverA l lo))
  ooI6 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (tsClient-OO l))
                        (OffersOnly-mono (λ _ _ → inj₂) ooI7)
  ooI5 : OffersOnly U5 (BFserverA l lo ⦀ (TSclientA l hi ⦀ (TSserverA l lo)))
  ooI5 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (bfServer-OO l))
                        (OffersOnly-mono (λ _ _ → inj₂) ooI6)
  ooI4 : OffersOnly U4 (BFclientA l hi ⦀ (BFserverA l lo ⦀ (TSclientA l hi ⦀ (TSserverA l lo))))
  ooI4 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (bfClient-OO l))
                        (OffersOnly-mono (λ _ _ → inj₂) ooI5)
  ooI3 : OffersOnly U3 (CSserverA l lo ⦀ (BFclientA l hi ⦀ (BFserverA l lo ⦀ (TSclientA l hi ⦀ (TSserverA l lo)))))
  ooI3 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (csServer-OO l))
                        (OffersOnly-mono (λ _ _ → inj₂) ooI4)
  ooI2 : OffersOnly U2 (CSclientA l hi ⦀ (CSserverA l lo ⦀ (BFclientA l hi ⦀ (BFserverA l lo ⦀ (TSclientA l hi ⦀ (TSserverA l lo))))))
  ooI2 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (csClient-OO l))
                        (OffersOnly-mono (λ _ _ → inj₂) ooI3)
  ooI1 : OffersOnly U1 (KAserverA l lo ⦀ (CSclientA l hi ⦀ (CSserverA l lo ⦀ (BFclientA l hi ⦀ (BFserverA l lo ⦀ (TSclientA l hi ⦀ (TSserverA l lo)))))))
  ooI1 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (kaServer-OO l))
                        (OffersOnly-mono (λ _ _ → inj₂) ooI2)

  -- spec-side tail-bundle OffersOnly
  ooS7 : OffersOnly U7 (tsServerSpec l lo)
  ooS7 = tsServerSpec-OffersOnly l lo
  ooS6 : OffersOnly U6 (tsClientSpec l hi ⦀ (tsServerSpec l lo))
  ooS6 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (tsClientSpec-OffersOnly l hi))
                        (OffersOnly-mono (λ _ _ → inj₂) ooS7)
  ooS5 : OffersOnly U5 (bfServerSpec l lo ⦀ (tsClientSpec l hi ⦀ (tsServerSpec l lo)))
  ooS5 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (bfServerSpec-OffersOnly l lo))
                        (OffersOnly-mono (λ _ _ → inj₂) ooS6)
  ooS4 : OffersOnly U4 (bfClientSpec l hi ⦀ (bfServerSpec l lo ⦀ (tsClientSpec l hi ⦀ (tsServerSpec l lo))))
  ooS4 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (bfClientSpec-OffersOnly l hi))
                        (OffersOnly-mono (λ _ _ → inj₂) ooS5)
  ooS3 : OffersOnly U3 (csServerSpec l lo ⦀ (bfClientSpec l hi ⦀ (bfServerSpec l lo ⦀ (tsClientSpec l hi ⦀ (tsServerSpec l lo)))))
  ooS3 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (csServerSpec-OffersOnly l lo))
                        (OffersOnly-mono (λ _ _ → inj₂) ooS4)
  ooS2 : OffersOnly U2 (csClientSpec l hi ⦀ (csServerSpec l lo ⦀ (bfClientSpec l hi ⦀ (bfServerSpec l lo ⦀ (tsClientSpec l hi ⦀ (tsServerSpec l lo))))))
  ooS2 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (csClientSpec-OffersOnly l hi))
                        (OffersOnly-mono (λ _ _ → inj₂) ooS3)
  ooS1 : OffersOnly U1 (kaServerSpec l lo ⦀ (csClientSpec l hi ⦀ (csServerSpec l lo ⦀ (bfClientSpec l hi ⦀ (bfServerSpec l lo ⦀ (tsClientSpec l hi ⦀ (tsServerSpec l lo)))))))
  ooS1 = OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) (kaServerSpec-OffersOnly l lo))
                        (OffersOnly-mono (λ _ _ → inj₂) ooS2)

  -- the bundle bisim: fold cong-⦀ from the innermost pair outward
  b7 : (TSserverA l lo) ≈DR (tsServerSpec l lo)
  b7 = tsServer≈DR l
  b6 : (TSclientA l hi ⦀ (TSserverA l lo)) ≈DR (tsClientSpec l hi ⦀ (tsServerSpec l lo))
  b6 = cong-⦀ (sep-from-OffersOnly ∅ES (λ {at} {a} _ h t → peerAlpha-Disj (λ ()) at a h t) (tsClient-OO l) ooI7)
                (sep-from-OffersOnly ∅ES (λ {at} {a} _ h t → peerAlpha-Disj (λ ()) at a h t) (tsClientSpec-OffersOnly l hi) ooI7)
                (sep-from-OffersOnly ∅ES (λ {at} {a} _ h t → peerAlpha-Disj (λ ()) at a h t) (tsClientSpec-OffersOnly l hi) ooS7)
                (tsClient≈DR l) b7
  b5 : (BFserverA l lo ⦀ (TSclientA l hi ⦀ (TSserverA l lo))) ≈DR (bfServerSpec l lo ⦀ (tsClientSpec l hi ⦀ (tsServerSpec l lo)))
  b5 = cong-⦀ (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (t)) → peerAlpha-Disj (λ ()) at a h t }) (bfServer-OO l) ooI6)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (t)) → peerAlpha-Disj (λ ()) at a h t }) (bfServerSpec-OffersOnly l lo) ooI6)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (t)) → peerAlpha-Disj (λ ()) at a h t }) (bfServerSpec-OffersOnly l lo) ooS6)
                (bfServer≈DR l) b6
  b4 : (BFclientA l hi ⦀ (BFserverA l lo ⦀ (TSclientA l hi ⦀ (TSserverA l lo)))) ≈DR (bfClientSpec l hi ⦀ (bfServerSpec l lo ⦀ (tsClientSpec l hi ⦀ (tsServerSpec l lo))))
  b4 = cong-⦀ (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (t))) → peerAlpha-Disj (λ ()) at a h t }) (bfClient-OO l) ooI5)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (t))) → peerAlpha-Disj (λ ()) at a h t }) (bfClientSpec-OffersOnly l hi) ooI5)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (t))) → peerAlpha-Disj (λ ()) at a h t }) (bfClientSpec-OffersOnly l hi) ooS5)
                (bfClient≈DR l) b5
  b3 : (CSserverA l lo ⦀ (BFclientA l hi ⦀ (BFserverA l lo ⦀ (TSclientA l hi ⦀ (TSserverA l lo))))) ≈DR (csServerSpec l lo ⦀ (bfClientSpec l hi ⦀ (bfServerSpec l lo ⦀ (tsClientSpec l hi ⦀ (tsServerSpec l lo)))))
  b3 = cong-⦀ (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (t)))) → peerAlpha-Disj (λ ()) at a h t }) (csServer-OO l) ooI4)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (t)))) → peerAlpha-Disj (λ ()) at a h t }) (csServerSpec-OffersOnly l lo) ooI4)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (t)))) → peerAlpha-Disj (λ ()) at a h t }) (csServerSpec-OffersOnly l lo) ooS4)
                (csServer≈DR l) b4
  b2 : (CSclientA l hi ⦀ (CSserverA l lo ⦀ (BFclientA l hi ⦀ (BFserverA l lo ⦀ (TSclientA l hi ⦀ (TSserverA l lo)))))) ≈DR (csClientSpec l hi ⦀ (csServerSpec l lo ⦀ (bfClientSpec l hi ⦀ (bfServerSpec l lo ⦀ (tsClientSpec l hi ⦀ (tsServerSpec l lo))))))
  b2 = cong-⦀ (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (t))))) → peerAlpha-Disj (λ ()) at a h t }) (csClient-OO l) ooI3)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (t))))) → peerAlpha-Disj (λ ()) at a h t }) (csClientSpec-OffersOnly l hi) ooI3)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (t))))) → peerAlpha-Disj (λ ()) at a h t }) (csClientSpec-OffersOnly l hi) ooS3)
                (csClient≈DR l) b3
  b1 : (KAserverA l lo ⦀ (CSclientA l hi ⦀ (CSserverA l lo ⦀ (BFclientA l hi ⦀ (BFserverA l lo ⦀ (TSclientA l hi ⦀ (TSserverA l lo))))))) ≈DR (kaServerSpec l lo ⦀ (csClientSpec l hi ⦀ (csServerSpec l lo ⦀ (bfClientSpec l hi ⦀ (bfServerSpec l lo ⦀ (tsClientSpec l hi ⦀ (tsServerSpec l lo)))))))
  b1 = cong-⦀ (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (t)))))) → peerAlpha-Disj (λ ()) at a h t }) (kaServer-OO l) ooI2)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (t)))))) → peerAlpha-Disj (λ ()) at a h t }) (kaServerSpec-OffersOnly l lo) ooI2)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (t)))))) → peerAlpha-Disj (λ ()) at a h t }) (kaServerSpec-OffersOnly l lo) ooS2)
                (kaServer≈DR l) b2
  b0 : (KAclientA l hi ⦀ (KAserverA l lo ⦀ (CSclientA l hi ⦀ (CSserverA l lo ⦀ (BFclientA l hi ⦀ (BFserverA l lo ⦀ (TSclientA l hi ⦀ (TSserverA l lo)))))))) ≈DR (kaClientSpec l hi ⦀ (kaServerSpec l lo ⦀ (csClientSpec l hi ⦀ (csServerSpec l lo ⦀ (bfClientSpec l hi ⦀ (bfServerSpec l lo ⦀ (tsClientSpec l hi ⦀ (tsServerSpec l lo))))))))
  b0 = cong-⦀ (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t)))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (t))))))) → peerAlpha-Disj (λ ()) at a h t }) (kaClient-OO l) ooI1)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t)))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (t))))))) → peerAlpha-Disj (λ ()) at a h t }) (kaClientSpec-OffersOnly l hi) ooI1)
                (sep-from-OffersOnly ∅ES (λ { {at} {a} _ h (inj₁ t) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₁ t)) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₁ t))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₁ t)))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ t)))))) → peerAlpha-Disj (λ ()) at a h t ; {at} {a} _ h (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (t))))))) → peerAlpha-Disj (λ ()) at a h t }) (kaClientSpec-OffersOnly l hi) ooS1)
                (kaClient≈DR l) b1

  -- the top-level composition with the driver (Sep via sep-R; driver leg refl)
  pipe≈DR : pipe l hi ≈DR pipeSpec l hi
  pipe≈DR = cong-Par⊤ apiES
              (sep-R (consume-OO-api l) (λ x → x) _)
              (sep-R (consume-OO-api l) (λ x → x) _)
              (sep-R (consume-OO-api l) (λ x → x) _)
              b0 (drbisim-refl _)

-- the two M1 goal terms (BD/CD instances of the ∀l pipeline bisim)
goalBD-proof : goalBD
goalBD-proof = pipe≈DR linkBD

goalCD-proof : goalCD
goalCD-proof = pipe≈DR linkCD
