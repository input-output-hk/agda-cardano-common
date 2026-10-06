{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C: THE TWO-NODE THEOREM (spec §3.2).
--   * the node summaries are `Logic2`'s `nodeF` (a node's bundle facts
--                 against its logic's, across `apiES`)
--   * `bound2`  — PREMISE (a): the system splits into the medium and the
--                 two nodes; the medium relays each cell-keyed wire weight
--                 (`medium-relay`), so every relay group's reports are paid
--                 by its owner's commands; the stores' read bounds come from
--                 the system provenance (`ProvSys.sys-inX`, D1-b); the
--                 linear system is solved in the order RollForward / tx
--                 replies / notifications → closure requests → closure
--                 entries → body requests, giving `F2 m = c2 * m + c2₀`
--   * `noLivelock2` — `noLivelockT` with premise (b) `Tau2.noDiv2`
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.NoLivelock.Bound2 where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; s≤s; z≤n)
import Data.Bool
import Data.Nat
open import Data.Nat.Properties
  using (≤-trans; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; *-monoʳ-≤; *-monoˡ-≤; ≤ᵇ⇒≤; +-comm; +-cancelʳ-≤; *-distribˡ-+)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (length)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Process_Trees using (ExtI)
open import Cardano_network.Base
open import Cardano_network.Parametric.Leios.LeiosInstance2 using (p2; rawSys2; H2; node2; line2)
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (U6; allV6)
open import Cardano_network.Net p2 using (Net_Api; Net_Api-≟)
open import Cardano_network.Data p2 using (Payload)
open import Cardano_network.NetCommon p2 using (ioES; NetworkLinkA)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (Event)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (_∖_; ⦀Fin⁺; ∅ES)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload}) using (Σc; labels)
open import CSP.Laws.DivFree.CountMore (Net_Api-≟ {Payload}) using (Σc-⦀; Σc-sync; χ; χ̄; #H≡Σc; Σc≤#V; AllL-parL; AllL-parR; ≤-≡; +-inter)
open import CSP.Laws.Traces.TraceLawsParallelTrace (Net_Api-≟ {Payload}) using (Par-trace-elim; ParInter)
open import Function using (case_of_)
open import Data.Unit.Polymorphic using (tt)
open import Cardano_network.Parametric.Leios.NoLivelock.MediumRelay p2 using (WireW; wO; wI; medium-relay; medium-io; medium-prov)
open import Cardano_network.Parametric.Leios.NoLivelock.StoresProv 1 2 line2 (λ n → n) U6 allV6 using (Σc-+)
open import Cardano_network.Parametric.Leios.NoLivelock.Stores 1 2 line2 (λ n → n) U6 allV6 using (cF)
open import Cardano_network.Parametric.Leios.NoLivelock.Threads 1 2 line2 (λ n → n) using (cForge; cSubmit; Σc-≤)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerAlpha 1 2 line2 (λ n → n) U6 allV6
  using (gRF; gLN; gTQ; gBT; gBQ; rep; ww; one; allL) renaming (gTS to grTS)
open import Cardano_network.Parametric.Leios.NoLivelock.Logic2 1 2 line2 (λ n → n) U6 allV6
  using (Cls; cls; TWr; KTn; CBn; NodeOut; nodeF; ΣTW)
open import CSP.Laws.DivFree.ParLabels (Net_Api-≟ {Payload}) using (labR)
open import Cardano_network.Parametric.Leios.NoLivelock.ProvSys 1 2 line2 (λ n → n) U6 allV6 using (sys-inX; fvals; cFg; length-fvals)
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
open import Semantics.FailuresDivergences {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (divergences)
open import CSP.Laws.FD.NoLivelock (Net_Api-≟ {Payload}) using (#H; #V; noLivelockT)
open import Cardano_network.Parametric.Leios.NoLivelock.Tau2 using (noDiv2)

------------------------------------------------------------------------
-- THE THEOREM
------------------------------------------------------------------------

-- the slope of the linear bound
c2 : ℕ
c2 = 92640

-- the offset of the linear bound
c2₀ : ℕ
c2₀ = 208104

-- the concrete linear bound
F2 : ℕ → ℕ
F2 m = c2 * m + c2₀

-- two nodes' group facts and the medium's relay: the reports are paid by the commands
cancel2 : ∀ {r₀ i₀ o₀ c₀ r₁ i₁ o₁ c₁} → r₀ + i₀ ≤ o₀ + c₀ → r₁ + i₁ ≤ o₁ + c₁ → o₀ + o₁ ≤ i₀ + i₁ → r₀ + r₁ ≤ c₀ + c₁
cancel2 {r₀} {i₀} {o₀} {c₀} {r₁} {i₁} {o₁} {c₁} h₀ h₁ m =
  +-cancelʳ-≤ (i₀ + i₁) (r₀ + r₁) (c₀ + c₁)
    (≤-trans (≤-≡ (+-inter r₀ r₁ i₀ i₁)) (≤-trans (+-mono-≤ h₀ h₁) (≤-trans (≤-≡ (+-inter o₀ c₀ o₁ c₁))
      (≤-trans (+-monoˡ-≤ (c₀ + c₁) m) (≤-≡ (+-comm (i₀ + i₁) (c₀ + c₁)))))))

-- the threads' constant, in closed form
KT≡ : ∀ B → KTn fzero B ≡ 20 * B + 76
KT≡ B = solve 1 (λ B → con 4 :+ ((con 2 :* B :+ con 2) :+ ((con 3 :* B :+ con 3) :+ (con 2 :+ (con 1 :+ (con 5
          :+ ((con 8 :* B :+ con 8) :+ (con 5 :+ ((con 2 :* B :+ con 2) :+ ((con 5 :* B :+ con 5) :+ ((con 2 :* con 6 :+ con 2)
          :+ (con 3 :+ (con 3 :+ (con 4 :+ (con 5 :* con 2 :+ con 5))))))))))))))
          := con 20 :* B :+ con 76) refl B
  where open +-*-Solver

-- THE LINEAR SYSTEM, solved
fin : ∀ {H V F S Xn B₀ B₁ C₀ C₁ T₀ T₁ RF LN TQ BT BQ TS : ℕ}
    → F + S ≤ V → C₀ + C₁ ≤ V → Xn ≤ V → B₀ ≤ Xn + C₀ → B₁ ≤ Xn + C₁
    → T₀ + T₁ ≤ (4 * F + (2 * S + (5 * RF + (5 * LN + (BT + (3 * BQ + (3 * TQ + 4 * TS))))))) + ((3 + KTn fzero B₀) + (3 + KTn (fsuc fzero) B₁))
    → RF ≤ 16 * (B₀ + B₁) + 32 → TS ≤ 120 → LN ≤ 24 * (B₀ + B₁) + 160 → TQ ≤ 4 * LN → BT ≤ 2 * TQ
    → BQ ≤ 10 * LN + 2 * BT + 20 → H ≤ 12 * (T₀ + T₁) + 48 → H ≤ c2 * V + c2₀
fin {H} {V} {F} {S} {Xn} {B₀} {B₁} {C₀} {C₁} {T₀} {T₁} {RF} {LN} {TQ} {BT} {BQ} {TS} hFS hC hX hB₀ hB₁ hT hRF hTS hLN hTQ hBT hBQ hH =
  ≤-trans hH (≤-trans (+-monoˡ-≤ 48 (*-monoʳ-≤ 12 tB))
    (≤-≡ (solve 1 (λ v → con 12 :* (con 7720 :* v :+ con 17338) :+ con 48 := con 92640 :* v :+ con 208104) refl V)))
  where
    open +-*-Solver
    -- both nodes' read bounds
    B = B₀ + B₁
    -- B₀'s and B₁'s own bounds via Xn, C₀, C₁ combine to bound B by 3 * V
    bB : B ≤ 3 * V
    bB = ≤-trans (+-mono-≤ hB₀ hB₁) (≤-trans (≤-≡ (solve 3 (λ x c d → (x :+ c) :+ (x :+ d) := con 2 :* x :+ (c :+ d)) refl Xn C₀ C₁))
           (≤-trans (+-mono-≤ (*-monoʳ-≤ 2 hX) hC) (≤-≡ (solve 1 (λ v → con 2 :* v :+ v := con 3 :* v) refl V))))
    -- the closure entries, then the body requests, by the notifications
    bt : BT ≤ 8 * LN
    bt = ≤-trans hBT (≤-trans (*-monoʳ-≤ 2 hTQ) (≤-≡ (solve 1 (λ l → con 2 :* (con 4 :* l) := con 8 :* l) refl LN)))
    -- BT's bound `bt` substituted into BQ's own bound, restated as a multiple of LN
    bq : BQ ≤ 26 * LN + 20
    bq = ≤-trans hBQ (≤-trans (+-monoˡ-≤ 20 (+-monoʳ-≤ (10 * LN) (*-monoʳ-≤ 2 bt)))
           (≤-≡ (solve 1 (λ l → con 10 :* l :+ con 2 :* (con 8 :* l) :+ con 20 := con 26 :* l :+ con 20) refl LN)))
    -- forges and submissions
    fs : 4 * F + 2 * S ≤ 4 * V
    fs = ≤-trans (+-monoʳ-≤ (4 * F) (*-monoˡ-≤ S {2} {4} (s≤s (s≤s z≤n))))
           (≤-trans (≤-≡ (sym (*-distribˡ-+ 4 F S))) (*-monoʳ-≤ 4 hFS))
    -- the trigger weight
    w : 4 * F + (2 * S + (5 * RF + (5 * LN + (BT + (3 * BQ + (3 * TQ + 4 * TS)))))) ≤ 4 * V + (5 * RF + (103 * LN + 540))
    w = ≤-trans (+-monoʳ-≤ (4 * F) (+-monoʳ-≤ (2 * S) (+-monoʳ-≤ (5 * RF) (+-monoʳ-≤ (5 * LN)
              (+-mono-≤ bt (+-mono-≤ (*-monoʳ-≤ 3 bq) (+-mono-≤ (*-monoʳ-≤ 3 hTQ) (*-monoʳ-≤ 4 hTS))))))))
          (≤-trans (≤-≡ (solve 4 (λ f s r l → f :+ (s :+ (con 5 :* r :+ (con 5 :* l :+ (con 8 :* l :+ (con 3 :* (con 26 :* l :+ con 20)
                                     :+ (con 3 :* (con 4 :* l) :+ con 4 :* con 120))))))
                                   := (f :+ s) :+ (con 5 :* r :+ (con 103 :* l :+ con 540))) refl (4 * F) (2 * S) RF LN))
            (+-monoˡ-≤ _ fs))
    -- the threads' events
    tB : T₀ + T₁ ≤ 7720 * V + 17338
    tB = ≤-trans hT (≤-trans (+-mono-≤ w (≤-≡ (trans (cong₂ (λ x y → (3 + x) + (3 + y)) (KT≡ B₀) (KT≡ B₁))
                                            (solve 2 (λ b c → (con 3 :+ (con 20 :* b :+ con 76)) :+ (con 3 :+ (con 20 :* c :+ con 76))
                                                            := con 20 :* (b :+ c) :+ con 158) refl B₀ B₁))))
           (≤-trans (+-monoˡ-≤ (20 * B + 158) (+-monoʳ-≤ (4 * V) (+-mono-≤ (*-monoʳ-≤ 5 hRF) (+-monoˡ-≤ 540 (*-monoʳ-≤ 103 hLN)))))
             (≤-trans (≤-≡ (solve 2 (λ v b → con 4 :* v :+ (con 5 :* (con 16 :* b :+ con 32) :+ (con 103 :* (con 24 :* b :+ con 160)
                                                :+ con 540)) :+ (con 20 :* b :+ con 158)
                                              := con 4 :* v :+ con 2572 :* b :+ con 17338) refl V B))
               (≤-trans (+-monoˡ-≤ 17338 (+-monoʳ-≤ (4 * V) (*-monoʳ-≤ 2572 bB)))
                 (≤-≡ (solve 1 (λ v → con 4 :* v :+ con 2572 :* (con 3 :* v) :+ con 17338 := con 7720 :* v :+ con 17338) refl V))))))

-- the system, split: the medium and the two nodes
sysB : ∀ {s Q sM sN s₀ s₁ M′ N₀′ N₁′} → rawSys2 ⟹⟨ s ⟩ Q → NetworkLinkA ⟹⟨ sM ⟩ M′
     → node2 fzero ⟹⟨ s₀ ⟩ N₀′ → node2 (fsuc fzero) ⟹⟨ s₁ ⟩ N₁′
     → ParInter ioES (λ _ _ → tt) sM sN s → ParInter ∅ES (λ _ _ → tt) s₀ s₁ sN → #H H2 s ≤ F2 (#V H2 s)
sysB {s} {s₀ = s₀} {s₁ = s₁} tr tM t₀ t₁ pi pn =
  subst (_≤ F2 (#V H2 s)) (sym (#H≡Σc H2 s))
    (fin {F = Σc cForge L} {S = Σc cSubmit L} {Xn = length X} {B₀ = NodeOut.nB N₀} {B₁ = NodeOut.nB N₁}
         {C₀ = Σc cF l₀} {C₁ = Σc cF l₁} {T₀ = NodeOut.nT N₀} {T₁ = NodeOut.nT N₁}
         {RF = Σc (rep gRF) L} {LN = Σc (rep gLN) L} {TQ = Σc (rep gTQ) L} {BT = Σc (rep gBT) L}
         {BQ = Σc (rep gBQ) L} {TS = Σc (rep grTS) L}
       (≤-trans (≤-≡ (sym (Σc-+ cForge cSubmit L))) (toV (λ e → proj₁ (Cls.oV (cls e)))))
       (≤-trans (≤-≡ (sym (sp cF))) (toV (λ e → proj₁ (proj₂ (Cls.oV (cls e))))))
       (≤-trans (≤-≡ (length-fvals L)) (toV (λ e → proj₂ (proj₂ (Cls.oV (cls e))))))
       (NodeOut.nB≤ N₀) (NodeOut.nB≤ N₁)
       (≤-trans (+-mono-≤ (NodeOut.nT≤ N₀) (NodeOut.nT≤ N₁))
         (≤-≡ (trans (+-inter (Σc TWr l₀) (3 + KTn fzero (NodeOut.nB N₀)) (Σc TWr l₁) (3 + KTn (fsuc fzero) (NodeOut.nB N₁))) (cong (_+ ((3 + KTn fzero (NodeOut.nB N₀)) + (3 + KTn (fsuc fzero) (NodeOut.nB N₁)))) (trans (sym (sp TWr)) (ΣTW L))))))
       (≤-trans (grp gRF) (≤-≡ (solve 2 (λ b c → con 2 :* (con 8 :* b :+ con 8) :+ con 2 :* (con 8 :* c :+ con 8)
                                              := con 16 :* (b :+ c) :+ con 32) refl (NodeOut.nB N₀) (NodeOut.nB N₁))))
       (grp grTS)
       (≤-trans (grp gLN) (≤-≡ (solve 2 (λ b c → con 2 :* (con 12 :* b :+ con 40) :+ con 2 :* (con 12 :* c :+ con 40)
                                              := con 24 :* (b :+ c) :+ con 160) refl (NodeOut.nB N₀) (NodeOut.nB N₁))))
       (≤-trans (grp gTQ) (≤-≡ (trans (solve 2 (λ a b → con 2 :* (con 2 :* a) :+ con 2 :* (con 2 :* b) := con 4 :* (a :+ b)) refl
                                         (Σc (rep gLN) l₀) (Σc (rep gLN) l₁)) (cong (4 *_) (sym (sp (rep gLN)))))))
       (≤-trans (grp gBT) (≤-≡ (trans (sym (*-distribˡ-+ 2 (Σc (rep gTQ) l₀) (Σc (rep gTQ) l₁))) (cong (2 *_) (sym (sp (rep gTQ)))))))
       (≤-trans (grp gBQ) (≤-≡ (trans (solve 4 (λ a b c d → con 2 :* (con 5 :* a :+ c :+ con 5) :+ con 2 :* (con 5 :* b :+ d :+ con 5)
                                                      := con 10 :* (a :+ b) :+ con 2 :* (c :+ d) :+ con 20) refl
                                         (Σc (rep gLN) l₀) (Σc (rep gLN) l₁) (Σc (rep gBT) l₀) (Σc (rep gBT) l₁))
                                  (cong₂ (λ x y → 10 * x + 2 * y + 20) (sym (sp (rep gLN))) (sym (sp (rep gBT)))))))
       (≤-trans (≤-≡ (sp (χ H2)))
         (≤-trans (cancel2 {Σc (χ H2) l₀} {Σc (wI one) l₀} {Σc (wO one) l₀} {12 * NodeOut.nT N₀ + 24}
                           {Σc (χ H2) l₁} {Σc (wI one) l₁} {Σc (wO one) l₁} {12 * NodeOut.nT N₁ + 24}
                           (≤-trans (NodeOut.nH N₀) (≤-≡ (solve 2 (λ t o → con 12 :* t :+ o :+ con 24 := o :+ (con 12 :* t :+ con 24)) refl
                                                                  (NodeOut.nT N₀) (Σc (wO one) l₀))))
                           (≤-trans (NodeOut.nH N₁) (≤-≡ (solve 2 (λ t o → con 12 :* t :+ o :+ con 24 := o :+ (con 12 :* t :+ con 24)) refl
                                                                  (NodeOut.nT N₁) (Σc (wO one) l₁))))
                           (med one))
           (≤-≡ (solve 2 (λ a b → (con 12 :* a :+ con 24) :+ (con 12 :* b :+ con 24) := con 12 :* (a :+ b) :+ con 48) refl
                    (NodeOut.nT N₀) (NodeOut.nT N₁))))))
  where
    open +-*-Solver
    -- the system's labels and each node's
    L = labels s
    l₀ = labels s₀
    l₁ = labels s₁
    -- the blocks forged in the trace
    X = fvals L
    -- the stores' rely, at the nodes
    rN = AllL-parR pi (sys-inX medium-prov tr)
    -- the two nodes
    N₀ = nodeF fzero X t₀ (AllL-parL pn rN)
    N₁ = nodeF (fsuc fzero) X t₁ (AllL-parR pn rN)
    -- a system weight is the two nodes' (the medium's labels are all wire labels)
    sp : ∀ c → Σc c L ≡ Σc c l₀ + Σc c l₁
    sp c = trans (cong (Σc c) (labR (medium-io tM) pi)) (Σc-⦀ c pn)
    -- an environment weight is visible
    toV : ∀ {c : Event → ℕ} → (∀ e → Data.Bool.T (c e Data.Nat.≤ᵇ χ̄ H2 e)) → Σc c L ≤ #V H2 s
    toV f = ≤-trans (Σc-≤ (allL (λ e → ≤ᵇ⇒≤ _ _ (f e)) L)) (Σc≤#V H2 s)
    -- the medium relays every wire weight, split over the two nodes
    med : ∀ w → Σc (wO w) l₀ + Σc (wO w) l₁ ≤ Σc (wI w) l₀ + Σc (wI w) l₁
    med w = subst₂ _≤_ (trans (proj₁ (Σc-sync (wO w) (λ e m → proj₂ (Cls.oI (cls e) w m)) pi)) (sp (wO w)))
                       (trans (proj₁ (Σc-sync (wI w) (λ e m → proj₁ (Cls.oI (cls e) w m)) pi)) (sp (wI w)))
                       (medium-relay w tM)
    -- a relay group: the system's reports are paid by the two nodes' commands
    grp : ∀ g → Σc (rep g) L ≤ 2 * CBn fzero g (NodeOut.nB N₀) l₀ + 2 * CBn (fsuc fzero) g (NodeOut.nB N₁) l₁
    grp g = ≤-trans (≤-≡ (sp (rep g))) (cancel2 {Σc (rep g) l₀} {Σc (wI (ww g)) l₀} {Σc (wO (ww g)) l₀} {2 * CBn fzero g (NodeOut.nB N₀) l₀}
                   {Σc (rep g) l₁} {Σc (wI (ww g)) l₁} {Σc (wO (ww g)) l₁} {2 * CBn (fsuc fzero) g (NodeOut.nB N₁) l₁} (NodeOut.nG N₀ g) (NodeOut.nG N₁ g) (med (ww g)))

-- PREMISE (a): the counting bound on every trace of the unhidden two-node system
bound2 : ∀ {s Q} → rawSys2 ⟹⟨ s ⟩ Q → #H H2 s ≤ F2 (#V H2 s)
bound2 {s} tr = case Par-trace-elim ioES _ NetworkLinkA (⦀Fin⁺ 1 node2) tr of λ where
  (_ , _ , _ , _ , tM , tN , pi) → case Par-trace-elim ∅ES _ (node2 fzero) (node2 (fsuc fzero)) tN of λ where
    (_ , _ , _ , _ , t₀ , t₁ , pn) → sysB tr tM t₀ t₁ pi pn

-- THE THEOREM (spec §3.2)
noLivelock2 : ∀ s → ¬ divergences (rawSys2 ∖ H2) s
noLivelock2 s = noLivelockT H2 F2 bound2 noDiv2 {s}
