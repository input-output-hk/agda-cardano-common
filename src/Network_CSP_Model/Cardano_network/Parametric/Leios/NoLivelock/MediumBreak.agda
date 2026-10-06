{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage L: the BREAKABLE medium `NetworkLinkBreakableA`
-- (every link's cell `netLinkMediumA l △ (break l ⟶₀ Skip)`, interleaved).
-- A `break` only drops what is in flight, so every fact of the plain
-- cell survives (`TraceInterrupt`):
--   * `mediumB-relay` — delivered weight ≤ given weight, every wire weight
--   * `mediumB-io`    — every label is an io label or a `break`
--   * `mediumB-prov`  — every BlockFetch block delivered was given earlier
--   * `ΣB`            — at the system: a weight that vanishes on `break`
--                        weighs on the system what it weighs on the nodes
-- No postulate, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.NoLivelock.MediumBreak (p : Params) where

open import Level using (0ℓ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-trans; m≤m+n)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as UP
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst₂)

open import Process_Trees using (ExtI; PTree)
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.Data p using (Payload; DecEq-Payload)
open import Cardano_network.NetCommon p
  using (ιNet; ιNet⁻¹; ιNet-linv; ioES; netLinkMediumA; breakableNetLinkA; NetworkLinkBreakableA)
open import Cardano_network.Params using (module Params)
open Params p using (numLinks)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (_⦀_; Skip; ∅ES; ⦀Fin)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (Event; evLabel; Event√)
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
open import CSP.Laws.Traces.TraceLawsParallelTrace (Net_Api-≟ {Payload})
  using (ParInter; pnil; psync; psoloL; psoloR; p√; Par-trace-elim)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload})
  using (labels; Σc; AllL; []; _∷_; AllL-map; AllT; AllT-Ret; AllT-⟶; Ret-tr)
open import CSP.Laws.DivFree.CountMore (Net_Api-≟ {Payload}) using (InA; Σc-⦀; +-inter; slack0)
open import CSP.Laws.DivFree.Prov (Net_Api-≟ {Payload}) using (PA; pa; runA; PA-⦀Fin)
open import CSP.Laws.DivFree.TraceInterrupt (Net_Api-≟ {Payload}) using (AllT-△; Rl-△inert; PA-△inert)
open import CSP.Laws.DivFree.ParLabels (Net_Api-≟ {Payload}) using (AllL-⦀)
open import Cardano_network.Parametric.Leios.NoLivelock.ProvBF p using (ChS)
open import Cardano_network.Parametric.Leios.NoLivelock.MediumRelay p
  using (WireW; wO; wI; ιNet-rinv; NetOneLink-R; IoP; io; TxSide-A; RxSide-A; al-hide; al-par; al-ren; InM; Rv; chs→chm; inM)
open import Cardano_network.Parametric.Leios.NoLivelock.MediumProv p Payload (λ id → id ≡ N2N_BlockFetch)
  using (NetOneLink-PA)
open import CSP.Laws.DivFree.CountRename ιNet ιNet⁻¹ ιNet-linv ιNet-rinv (Net-≟ {Payload}) (Net_Api-≟ {Payload})
  using (ren-trace-elim-rel; Σc≤-ren; PA-ren)
open import CSP.Laws.DivFree.ProvMore (Net-≟ {Payload}) using (Prov-comap)
import CSP.Laws.DivFree.Prov (Net-≟ {Payload}) as PN
import CSP.Laws.DivFree.Count (Net-≟ {Payload}) as CN

-- the process type of the medium
ProcA : Set₁
ProcA = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (UP.⊤ {0ℓ})

-- a relay on every run of a medium process
RlA : (Event → ℕ) → (Event → ℕ) → ℕ → ProcA → Set₁
RlA c d k P = ∀ {s W} → P ⟹⟨ s ⟩ W → Σc c (labels s) ≤ Σc d (labels s) + k

-- `Skip` relays trivially
rlA-Skip : ∀ {c d} → RlA c d 0 Skip
rlA-Skip tr with Ret-tr tr
... | inj₁ refl = z≤n
... | inj₂ refl = z≤n

-- interleaving adds the slacks
rlA-⦀ : ∀ {c d k₁ k₂} {P Q : ProcA} → RlA c d k₁ P → RlA c d k₂ Q → RlA c d (k₁ + k₂) (P ⦀ Q)
rlA-⦀ {c} {d} {k₁} {k₂} {P} {Q} hp hq tr = case Par-trace-elim ∅ES _ P Q tr of λ where
  (sP , sQ , _ , _ , tP , tQ , pi) →
    subst₂ (λ x y → x ≤ y + (k₁ + k₂)) (Relation.Binary.PropositionalEquality.sym (Σc-⦀ c pi))
                                       (Relation.Binary.PropositionalEquality.sym (Σc-⦀ d pi))
      (≤-trans (Data.Nat.Properties.+-mono-≤ (hp tP) (hq tQ)) (Data.Nat.Properties.≤-reflexive (+-inter (Σc d (labels sP)) k₁ (Σc d (labels sQ)) k₂)))

-- a label fact of both sides holds of the interleaving
AllT-⦀ : ∀ {F : Event → Set} {P Q : ProcA} → AllT F P → AllT F Q → AllT F (P ⦀ Q)
AllT-⦀ {F} {P} {Q} aP aQ tr = case Par-trace-elim ∅ES _ P Q tr of λ where
  (sP , sQ , _ , _ , tP , tQ , pi) → AllL-⦀ (aP tP) (aQ tQ) pi

-- induction over `⦀Fin` (medium processes)
⦀FinA-ind : (Pr : ProcA → Set₁) → Pr Skip → (∀ {P Q} → Pr P → Pr Q → Pr (P ⦀ Q))
          → ∀ n (f : Fin n → ProcA) → (∀ i → Pr (f i)) → Pr (⦀Fin n f)
⦀FinA-ind Pr z c zero    f pf = z
⦀FinA-ind Pr z c (suc n) f pf = c (pf fzero) (⦀FinA-ind Pr z c n (λ i → f (fsuc i)) (λ i → pf (fsuc i)))

------------------------------------------------------------------------
-- one cell
------------------------------------------------------------------------

-- the plain cell relays every wire weight (across its renaming)
cellA-relay : ∀ w l → RlA (wO w) (wI w) 0 (netLinkMediumA l)
cellA-relay w l = Σc≤-ren (wO w) (wI w) 0 (λ t → ≤-trans (NetOneLink-R w l t) (m≤m+n _ 0))

-- … and so does the breakable one (`break` carries no wire weight)
cellB-relay : ∀ w l → RlA (wO w) (wI w) 0 (breakableNetLinkA l)
cellB-relay w l = Rl-△inert (cellA-relay w l) (AllT-⟶ (break l) (λ _ → refl) (λ _ → AllT-Ret))

-- a `break` label
IsBrk : Event → Set
IsBrk (evLabel _ (break _) _) = ⊤
IsBrk _                       = ⊥

-- what the breakable medium shows
IoB : Event → Set
IoB e = InA ioES e ⊎ IsBrk e

-- the plain cell shows only io labels
cellA-io : ∀ l → AllT (InA ioES) (netLinkMediumA l)
cellA-io l tr = case ren-trace-elim-rel tr of λ where
  (_ , _ , tr₁ , rl) → al-ren rl (CN.AllL-map io (al-hide (al-par inj₁ inj₂ (TxSide-A l) (RxSide-A l)) tr₁))

-- the breakable cell shows io labels and its break
cellB-io : ∀ l → AllT IoB (breakableNetLinkA l)
cellB-io l = AllT-△ (λ tr → AllL-map inj₁ (cellA-io l tr)) (AllT-⟶ (break l) (λ _ → inj₂ tt) (λ _ → AllT-Ret))

-- the plain cell's block provenance (the system instance of `MediumProv`, as `medium-prov`)
cellA-prov : ∀ l → PA ChS ChS InM (netLinkMediumA l)
cellA-prov l = PA-ren (PN.pa λ tr →
  Prov-comap Rv chs→chm (λ i r → proj₁ (inM i r)) (λ i r → proj₂ (inM i r)) (λ ()) _ (PN.runA (NetOneLink-PA l) {K = λ _ → ⊥} tr))

-- … survives the break (a `break` carries no block)
cellB-prov : ∀ l → PA ChS ChS InM (breakableNetLinkA l)
cellB-prov l = PA-△inert (cellA-prov l) (AllT-⟶ (break l) (λ _ → λ ()) (λ _ → AllT-Ret))

------------------------------------------------------------------------
-- the breakable medium
------------------------------------------------------------------------

-- THE RELAY: delivered weight never exceeds given weight, for every wire weight
mediumB-relay : (w : WireW) {s : List (Event√ (UP.⊤ {0ℓ}))} {W : ProcA}
              → NetworkLinkBreakableA ⟹⟨ s ⟩ W → Σc (wO w) (labels s) ≤ Σc (wI w) (labels s)
mediumB-relay w {s} tr =
  slack0 {wO w} {wI w} {labels s} (⦀FinA-ind (RlA (wO w) (wI w) 0) rlA-Skip rlA-⦀ numLinks breakableNetLinkA (cellB-relay w) tr)

-- THE ALPHABET: io labels and breaks
mediumB-io : AllT IoB NetworkLinkBreakableA
mediumB-io = ⦀FinA-ind (AllT IoB) AllT-Ret AllT-⦀ numLinks breakableNetLinkA cellB-io

-- THE MEDIUM HOP: every BlockFetch block delivered was given earlier
mediumB-prov : PA ChS ChS InM NetworkLinkBreakableA
mediumB-prov = PA-⦀Fin numLinks breakableNetLinkA cellB-prov

-- at the system: a weight that vanishes on `break` weighs what the nodes weigh
ΣB : ∀ (c : Event → ℕ) → (∀ {e} → IsBrk e → c e ≡ 0) → ∀ {R₁ R₂ R₀ : Set} {merge}
     {sM : List (Event√ R₁)} {sN : List (Event√ R₂)} {s : List (Event√ R₀)}
   → AllL IoB (labels sM) → ParInter ioES merge sM sN s → Σc c (labels s) ≡ Σc c (labels sN)
ΣB c z al            pnil           = refl
ΣB c z (_ ∷ al)      (psync _ pi)   = cong (c _ +_) (ΣB c z al pi)
ΣB c z (inj₁ m ∷ al) (psoloL ¬m pi) = ⊥-elim (¬m m)
ΣB c z {s = _ ∷ s′} (inj₂ b ∷ al) (psoloL ¬m pi) = trans (cong (_+ Σc c (labels s′)) (z b)) (ΣB c z al pi)
ΣB c z al            (psoloR _ pi)  = cong (c _ +_) (ΣB c z al pi)
ΣB c z al            p√             = refl
