{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage L: THE THREE-NODE COUNTING BOUND (spec §3.3).
-- The unhidden shipped system `rawL` splits into the BREAKABLE medium and
-- the three nodes of the line (A, B, C; B has two endpoints):
--   * every weight used is zero on a `break` (`zB`), so the system weighs
--     what the nodes weigh (`MediumBreak.ΣB`, then `Σc-⦀` twice);
--   * the medium relays every cell-keyed wire weight (`mediumB-relay`),
--     so the three nodes' group facts cancel (`cancel3`);
--   * the stores' read bounds come from the system provenance over the
--     breakable medium (`ProvSys.sys-inX mediumB-prov`);
--   * the linear system, with node B's doubled slacks, is solved in
--     Stage C's order (`finL`), giving `FL m = cL * m + cL₀`.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.NoLivelock.BoundL where

open import Data.Nat using (ℕ; _+_; _*_; _≤_; s≤s; z≤n)
import Data.Bool
import Data.Nat
open import Data.Nat.Properties
  using (≤-trans; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; *-monoʳ-≤; *-monoˡ-≤; m≤m+n; ≤ᵇ⇒≤; +-comm; +-cancelʳ-≤; *-distribˡ-+)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Process_Trees using (ExtI)
open import Function using (case_of_)
open import Data.Unit.Polymorphic using (tt)
import Data.Unit.Polymorphic as UP
open import Level using (0ℓ)
open import Cardano_network.Base
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (pL; lpF; U9; allV9)
open import Cardano_network.Parametric.Leios.LeiosInstanceL using (leiosLLine)
open import Cardano_network.Parametric.Leios.LeiosInstance3 using (rawL; HL)
open import Cardano_network.Net (pL 2 3)
  using (Net_Api; Net_Api-≟; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
        ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; apiLP; store; env; break)
open import Cardano_network.Data (pL 2 3) using (Payload)
open import Cardano_network.NetCommon (pL 2 3) using (ioES; NetworkLinkBreakableA)
open import Cardano_network.ApiAlphabet (pL 2 3) using (apiES)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (Event; evLabel; Event√)
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (⦀Fin⁺; ∅ES; _⦀_)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload}) using (Σc; labels)
open import CSP.Laws.DivFree.CountMore (Net_Api-≟ {Payload}) using (Σc-⦀; Σc-sync; χ; χ̄; #H≡Σc; Σc≤#V; AllL-parL; AllL-parR; ≤-≡)
open import CSP.Laws.Traces.TraceLawsParallelTrace (Net_Api-≟ {Payload}) using (Par-trace-elim; ParInter)
open import CSP.Laws.FD.NoLivelock (Net_Api-≟ {Payload}) using (#H; #V)
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open NLL.Generic (pL 2 3) (lpF 2 3) leiosLLine apiES (λ n → n) using (nodeLogicL; st₀)
open import Cardano_network.Parametric.Leios.PeersP (pL 2 3) using (Proc; nodeBundleP)
open import Cardano_network.Parametric.Node (pL 2 3) leiosLLine apiES using (nodeWith)
open import Cardano_network.Parametric.Leios.NoLivelock.MediumRelay (pL 2 3) using (wO; wI)
open import Cardano_network.Parametric.Leios.NoLivelock.MediumBreak (pL 2 3)
  using (IsBrk; ΣB; mediumB-relay; mediumB-io; mediumB-prov)
open import Cardano_network.Parametric.Leios.NoLivelock.StoresProv 2 3 leiosLLine (λ n → n) U9 allV9 using (Σc-+)
open import Cardano_network.Parametric.Leios.NoLivelock.Stores 2 3 leiosLLine (λ n → n) U9 allV9 using (cF)
open import Cardano_network.Parametric.Leios.NoLivelock.Threads 2 3 leiosLLine (λ n → n) using (cForge; cSubmit; Σc-≤)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerAlpha 2 3 leiosLLine (λ n → n) U9 allV9
  using (gRF; gLN; gTQ; gBT; gBQ; rep; ww; one; allL) renaming (gTS to grTS)
open import Cardano_network.Parametric.Leios.NoLivelock.Logic2 2 3 leiosLLine (λ n → n) U9 allV9
  using (Cls; cls; offRep; TWr; KTe; KTn; CBn; NodeOut; nodeF; ΣTW)
open import Cardano_network.Parametric.Leios.NoLivelock.ProvSys 2 3 leiosLLine (λ n → n) U9 allV9
  using (sys-inX; fvals; length-fvals)

------------------------------------------------------------------------
-- sanity (Review Focus 2): node B folds over BOTH its endpoints
------------------------------------------------------------------------

-- node B pays two endpoint slacks
KTn-B : ∀ B → KTn (fsuc fzero) B ≡ 4 + ((2 * B + 2) + ((3 * B + 3) + (2 + (1 + (KTe B + KTe B)))))
KTn-B B = refl

-- … and two ChainSync servers' RollForward commands
CBn-B : ∀ B ls → CBn (fsuc fzero) gRF B ls ≡ (8 * B + 8) + (8 * B + 8)
CBn-B B ls = refl

-- node A pays one
KTn-A : ∀ B → KTn fzero B ≡ 4 + ((2 * B + 2) + ((3 * B + 3) + (2 + (1 + KTe B))))
KTn-A B = refl

-- … and so does node C
KTn-C : ∀ B → KTn (fsuc (fsuc fzero)) B ≡ 4 + ((2 * B + 2) + ((3 * B + 3) + (2 + (1 + KTe B))))
KTn-C B = refl

------------------------------------------------------------------------
-- the nodes and the break labels
------------------------------------------------------------------------

-- a node of the line
nodeL : Fin 3 → Proc
nodeL n = nodeWith nodeBundleP n (nodeLogicL n st₀)

-- a weight that vanishes on every break label vanishes on `IsBrk`
zB : ∀ (c : Event → ℕ) → (∀ l x → c (evLabel _ (break l) x) ≡ 0) → ∀ {e} → IsBrk e → c e ≡ 0
zB c h {evLabel _ (break l) x}       _  = h l x
zB c h {evLabel _ (input _ _ _) _}  ()
zB c h {evLabel _ (output _ _ _) _} ()
zB c h {evLabel _ (sndmsg _ _ _) _} ()
zB c h {evLabel _ (rcvmsg _ _ _) _} ()
zB c h {evLabel _ (tx _ _ _) _}     ()
zB c h {evLabel _ (sndack _ _ _) _} ()
zB c h {evLabel _ (rcvack _ _ _) _} ()
zB c h {evLabel _ (ack _ _ _) _}    ()
zB c h {evLabel _ (done _ _ _) _}   ()
zB c h {evLabel _ (apiCS _ _ _) _}  ()
zB c h {evLabel _ (apiBF _ _ _) _}  ()
zB c h {evLabel _ (apiTS _ _ _) _}  ()
zB c h {evLabel _ (apiKA _ _ _) _}  ()
zB c h {evLabel _ (apiLN _ _ _) _}  ()
zB c h {evLabel _ (apiLF _ _ _) _}  ()
zB c h {evLabel _ (apiLP _ _ _) _}  ()
zB c h {evLabel _ (store _ _ _) _}  ()
zB c h {evLabel _ (env _ _ _) _}    ()

-- a group's reports vanish on a break (a break is no api label)
zr : ∀ g {e} → IsBrk e → rep g e ≡ 0
zr g = zB (rep g) (λ l x → offRep g (evLabel _ (break l) x) (λ ()))

------------------------------------------------------------------------
-- THE THEOREM
------------------------------------------------------------------------

-- the slope of the linear bound: 12 · (4 + 2572 · 6) (threads ≤ 15436 V + 44573, `finL`)
cL : ℕ
cL = 185232

-- the offset of the linear bound: 12 · 44573 + 96
cL₀ : ℕ
cL₀ = 534972

-- the concrete linear bound
FL : ℕ → ℕ
FL m = cL * m + cL₀

-- three nodes' group facts and the medium's relay: the reports are paid by the commands
cancel3 : ∀ {r₀ i₀ o₀ c₀ r₁ i₁ o₁ c₁ r₂ i₂ o₂ c₂}
        → r₀ + i₀ ≤ o₀ + c₀ → r₁ + i₁ ≤ o₁ + c₁ → r₂ + i₂ ≤ o₂ + c₂ → o₀ + (o₁ + o₂) ≤ i₀ + (i₁ + i₂)
        → r₀ + (r₁ + r₂) ≤ c₀ + (c₁ + c₂)
cancel3 {r₀} {i₀} {o₀} {c₀} {r₁} {i₁} {o₁} {c₁} {r₂} {i₂} {o₂} {c₂} h₀ h₁ h₂ m =
  +-cancelʳ-≤ (i₀ + (i₁ + i₂)) (r₀ + (r₁ + r₂)) (c₀ + (c₁ + c₂))
    (≤-trans (≤-≡ (solve 6 (λ r₀ r₁ r₂ i₀ i₁ i₂ → (r₀ :+ (r₁ :+ r₂)) :+ (i₀ :+ (i₁ :+ i₂))
                                                := (r₀ :+ i₀) :+ ((r₁ :+ i₁) :+ (r₂ :+ i₂))) refl r₀ r₁ r₂ i₀ i₁ i₂))
      (≤-trans (+-mono-≤ h₀ (+-mono-≤ h₁ h₂))
        (≤-trans (≤-≡ (solve 6 (λ o₀ o₁ o₂ c₀ c₁ c₂ → (o₀ :+ c₀) :+ ((o₁ :+ c₁) :+ (o₂ :+ c₂))
                                                    := (o₀ :+ (o₁ :+ o₂)) :+ (c₀ :+ (c₁ :+ c₂))) refl o₀ o₁ o₂ c₀ c₁ c₂))
          (≤-trans (+-monoˡ-≤ (c₀ + (c₁ + c₂)) m) (≤-≡ (+-comm (i₀ + (i₁ + i₂)) (c₀ + (c₁ + c₂))))))))
  where open +-*-Solver

-- the one-endpoint nodes' threads' constant, in closed form
KTA : ∀ B → KTn fzero B ≡ 20 * B + 82
KTA B = solve 1 (λ B → con 4 :+ ((con 2 :* B :+ con 2) :+ ((con 3 :* B :+ con 3) :+ (con 2 :+ (con 1 :+ (con 5
          :+ ((con 8 :* B :+ con 8) :+ (con 5 :+ ((con 2 :* B :+ con 2) :+ ((con 5 :* B :+ con 5) :+ ((con 2 :* con 9 :+ con 2)
          :+ (con 3 :+ (con 3 :+ (con 4 :+ (con 5 :* con 2 :+ con 5))))))))))))))
          := con 20 :* B :+ con 82) refl B
  where open +-*-Solver

-- … node C's is node A's
KTC : ∀ B → KTn (fsuc (fsuc fzero)) B ≡ 20 * B + 82
KTC = KTA

-- node B's threads' constant (two endpoints), in closed form
KTB : ∀ B → KTn (fsuc fzero) B ≡ 35 * B + 152
KTB B = solve 1 (λ B → con 4 :+ ((con 2 :* B :+ con 2) :+ ((con 3 :* B :+ con 3) :+ (con 2 :+ (con 1 :+ (kE B :+ kE B)))))
          := con 35 :* B :+ con 152) refl B
  where
    open +-*-Solver
    -- one endpoint's constant
    kE = λ B → con 5 :+ ((con 8 :* B :+ con 8) :+ (con 5 :+ ((con 2 :* B :+ con 2) :+ ((con 5 :* B :+ con 5)
               :+ ((con 2 :* con 9 :+ con 2) :+ (con 3 :+ (con 3 :+ (con 4 :+ (con 5 :* con 2 :+ con 5)))))))))

-- THE LINEAR SYSTEM, solved (W = B₀ + 2·B₁ + B₂ weighs node B's doubled slacks)
finL : ∀ {H V F S Xn B₀ B₁ B₂ C₀ C₁ C₂ T₀ T₁ T₂ RF LN TQ BT BQ TS : ℕ}
     → F + S ≤ V → C₀ + (C₁ + C₂) ≤ V → Xn ≤ V → B₀ ≤ Xn + C₀ → B₁ ≤ Xn + C₁ → B₂ ≤ Xn + C₂
     → T₀ + (T₁ + T₂) ≤ (4 * F + (2 * S + (5 * RF + (5 * LN + (BT + (3 * BQ + (3 * TQ + 4 * TS)))))))
                        + ((3 + KTn fzero B₀) + ((3 + KTn (fsuc fzero) B₁) + (3 + KTn (fsuc (fsuc fzero)) B₂)))
     → RF ≤ 16 * (B₀ + 2 * B₁ + B₂) + 64 → TS ≤ 240 → LN ≤ 24 * (B₀ + 2 * B₁ + B₂) + 416 → TQ ≤ 4 * LN → BT ≤ 2 * TQ
     → BQ ≤ 10 * LN + 2 * BT + 40 → H ≤ 12 * (T₀ + (T₁ + T₂)) + 96 → H ≤ cL * V + cL₀
finL {H} {V} {F} {S} {Xn} {B₀} {B₁} {B₂} {C₀} {C₁} {C₂} {T₀} {T₁} {T₂} {RF} {LN} {TQ} {BT} {BQ} {TS}
     hFS hC hX hB₀ hB₁ hB₂ hT hRF hTS hLN hTQ hBT hBQ hH =
  ≤-trans hH (≤-trans (+-monoˡ-≤ 96 (*-monoʳ-≤ 12 tB))
    (≤-≡ (solve 1 (λ v → con 12 :* (con 15436 :* v :+ con 44573) :+ con 96 := con 185232 :* v :+ con 534972) refl V)))
  where
    open +-*-Solver
    -- the three nodes' read bounds, node B's twice
    W = B₀ + 2 * B₁ + B₂
    -- via Xn and C₀, C₁, C₂, W is at most 6 * V
    bW : W ≤ 6 * V
    bW = ≤-trans (+-mono-≤ (+-mono-≤ hB₀ (*-monoʳ-≤ 2 hB₁)) hB₂)
           (≤-trans (≤-≡ (solve 4 (λ x c d e → (x :+ c) :+ con 2 :* (x :+ d) :+ (x :+ e) := con 4 :* x :+ (c :+ con 2 :* d :+ e))
                                  refl Xn C₀ C₁ C₂))
             (≤-trans (+-monoʳ-≤ (4 * Xn) (≤-trans (m≤m+n (C₀ + 2 * C₁ + C₂) (C₀ + C₂))
                         (≤-≡ (solve 3 (λ c d e → (c :+ con 2 :* d :+ e) :+ (c :+ e) := con 2 :* (c :+ (d :+ e))) refl C₀ C₁ C₂))))
               (≤-trans (+-mono-≤ (*-monoʳ-≤ 4 hX) (*-monoʳ-≤ 2 hC)) (≤-≡ (solve 1 (λ v → con 4 :* v :+ con 2 :* v := con 6 :* v) refl V)))))
    -- the closure entries, then the body requests, by the notifications
    bt : BT ≤ 8 * LN
    bt = ≤-trans hBT (≤-trans (*-monoʳ-≤ 2 hTQ) (≤-≡ (solve 1 (λ l → con 2 :* (con 4 :* l) := con 8 :* l) refl LN)))
    -- BT's bound `bt` substituted into BQ's own bound, restated as a multiple of LN
    bq : BQ ≤ 26 * LN + 40
    bq = ≤-trans hBQ (≤-trans (+-monoˡ-≤ 40 (+-monoʳ-≤ (10 * LN) (*-monoʳ-≤ 2 bt)))
           (≤-≡ (solve 1 (λ l → con 10 :* l :+ con 2 :* (con 8 :* l) :+ con 40 := con 26 :* l :+ con 40) refl LN)))
    -- forges and submissions
    fs : 4 * F + 2 * S ≤ 4 * V
    fs = ≤-trans (+-monoʳ-≤ (4 * F) (*-monoˡ-≤ S {2} {4} (s≤s (s≤s z≤n))))
           (≤-trans (≤-≡ (sym (*-distribˡ-+ 4 F S))) (*-monoʳ-≤ 4 hFS))
    -- the trigger weight
    w : 4 * F + (2 * S + (5 * RF + (5 * LN + (BT + (3 * BQ + (3 * TQ + 4 * TS)))))) ≤ 4 * V + (5 * RF + (103 * LN + 1080))
    w = ≤-trans (+-monoʳ-≤ (4 * F) (+-monoʳ-≤ (2 * S) (+-monoʳ-≤ (5 * RF) (+-monoʳ-≤ (5 * LN)
              (+-mono-≤ bt (+-mono-≤ (*-monoʳ-≤ 3 bq) (+-mono-≤ (*-monoʳ-≤ 3 hTQ) (*-monoʳ-≤ 4 hTS))))))))
          (≤-trans (≤-≡ (solve 4 (λ f s r l → f :+ (s :+ (con 5 :* r :+ (con 5 :* l :+ (con 8 :* l :+ (con 3 :* (con 26 :* l :+ con 40)
                                     :+ (con 3 :* (con 4 :* l) :+ con 4 :* con 240))))))
                                   := (f :+ s) :+ (con 5 :* r :+ (con 103 :* l :+ con 1080))) refl (4 * F) (2 * S) RF LN))
            (+-monoˡ-≤ _ fs))
    -- the three nodes' thread constants (node B's 35 · B₁ rounded up to 40 · B₁)
    kt : (3 + KTn fzero B₀) + ((3 + KTn (fsuc fzero) B₁) + (3 + KTn (fsuc (fsuc fzero)) B₂)) ≤ 20 * W + 325
    kt = ≤-trans (≤-≡ (cong₂ (λ x y → (3 + x) + y) (KTA B₀) (cong₂ (λ x y → (3 + x) + (3 + y)) (KTB B₁) (KTC B₂))))
           (≤-trans (m≤m+n _ (5 * B₁))
             (≤-≡ (solve 3 (λ a b c → (con 3 :+ (con 20 :* a :+ con 82)) :+ ((con 3 :+ (con 35 :* b :+ con 152)) :+ (con 3 :+ (con 20 :* c :+ con 82)))
                                       :+ con 5 :* b := con 20 :* (a :+ con 2 :* b :+ c) :+ con 325) refl B₀ B₁ B₂)))
    -- the threads' events
    tB : T₀ + (T₁ + T₂) ≤ 15436 * V + 44573
    tB = ≤-trans hT (≤-trans (+-mono-≤ w kt)
           (≤-trans (+-monoˡ-≤ (20 * W + 325) (+-monoʳ-≤ (4 * V) (+-mono-≤ (*-monoʳ-≤ 5 hRF) (+-monoˡ-≤ 1080 (*-monoʳ-≤ 103 hLN)))))
             (≤-trans (≤-≡ (solve 2 (λ v b → con 4 :* v :+ (con 5 :* (con 16 :* b :+ con 64) :+ (con 103 :* (con 24 :* b :+ con 416)
                                                :+ con 1080)) :+ (con 20 :* b :+ con 325)
                                              := con 4 :* v :+ con 2572 :* b :+ con 44573) refl V W))
               (≤-trans (+-monoˡ-≤ 44573 (+-monoʳ-≤ (4 * V) (*-monoʳ-≤ 2572 bW)))
                 (≤-≡ (solve 1 (λ v → con 4 :* v :+ con 2572 :* (con 6 :* v) :+ con 44573 := con 15436 :* v :+ con 44573) refl V))))))

-- the system, split: the breakable medium and the three nodes
sysBL : ∀ {s Q sM} {sN s₁₂ : List (Event√ (UP.⊤ {0ℓ}))} {s₀ s₁ s₂ M′ N₀′ N₁′ N₂′} → rawL ⟹⟨ s ⟩ Q → NetworkLinkBreakableA ⟹⟨ sM ⟩ M′
      → nodeL fzero ⟹⟨ s₀ ⟩ N₀′ → nodeL (fsuc fzero) ⟹⟨ s₁ ⟩ N₁′ → nodeL (fsuc (fsuc fzero)) ⟹⟨ s₂ ⟩ N₂′
      → ParInter ioES (λ _ _ → tt) sM sN s → ParInter ∅ES (λ _ _ → tt) s₀ s₁₂ sN → ParInter ∅ES (λ _ _ → tt) s₁ s₂ s₁₂
      → #H HL s ≤ FL (#V HL s)
sysBL {s} {s₀ = s₀} {s₁ = s₁} {s₂ = s₂} tr tM t₀ t₁ t₂ pi pn pn′ =
  subst (_≤ FL (#V HL s)) (sym (#H≡Σc HL s))
    (finL {F = Σc cForge L} {S = Σc cSubmit L} {Xn = length X} {B₀ = b₀} {B₁ = b₁} {B₂ = b₂}
          {C₀ = Σc cF l₀} {C₁ = Σc cF l₁} {C₂ = Σc cF l₂} {T₀ = NodeOut.nT N₀} {T₁ = NodeOut.nT N₁} {T₂ = NodeOut.nT N₂}
          {RF = Σc (rep gRF) L} {LN = Σc (rep gLN) L} {TQ = Σc (rep gTQ) L} {BT = Σc (rep gBT) L}
          {BQ = Σc (rep gBQ) L} {TS = Σc (rep grTS) L}
       (≤-trans (≤-≡ (sym (Σc-+ cForge cSubmit L))) (toV (λ e → proj₁ (Cls.oV (cls e)))))
       (≤-trans (≤-≡ (sym (sp cF (zB cF (λ _ _ → refl))))) (toV (λ e → proj₁ (proj₂ (Cls.oV (cls e))))))
       (≤-trans (≤-≡ (length-fvals L)) (toV (λ e → proj₂ (proj₂ (Cls.oV (cls e))))))
       (NodeOut.nB≤ N₀) (NodeOut.nB≤ N₁) (NodeOut.nB≤ N₂)
       (≤-trans (+-mono-≤ (NodeOut.nT≤ N₀) (+-mono-≤ (NodeOut.nT≤ N₁) (NodeOut.nT≤ N₂)))
         (≤-≡ (trans (solve 6 (λ a x b y c z → (a :+ x) :+ ((b :+ y) :+ (c :+ z)) := (a :+ (b :+ c)) :+ (x :+ (y :+ z))) refl
                             (Σc TWr l₀) k₀ (Σc TWr l₁) k₁ (Σc TWr l₂) k₂)
                     (cong (_+ (k₀ + (k₁ + k₂))) (trans (sym (sp TWr (zB TWr (λ _ _ → refl)))) (ΣTW L))))))
       (≤-trans (grp gRF) (≤-≡ (solve 3 (λ a b c → con 2 :* (con 8 :* a :+ con 8) :+ (con 2 :* ((con 8 :* b :+ con 8) :+ (con 8 :* b :+ con 8))
                                              :+ con 2 :* (con 8 :* c :+ con 8)) := con 16 :* (a :+ con 2 :* b :+ c) :+ con 64) refl b₀ b₁ b₂)))
       (grp grTS)
       (≤-trans (grp gLN) (≤-≡ (solve 3 (λ a b c → con 2 :* (con 12 :* a :+ con 52) :+ (con 2 :* ((con 12 :* b :+ con 52) :+ (con 12 :* b :+ con 52))
                                              :+ con 2 :* (con 12 :* c :+ con 52)) := con 24 :* (a :+ con 2 :* b :+ c) :+ con 416) refl b₀ b₁ b₂)))
       (≤-trans (grp gTQ) (≤-≡ (trans (solve 3 (λ a b c → con 2 :* (con 2 :* a) :+ (con 2 :* (con 2 :* b) :+ con 2 :* (con 2 :* c))
                                                    := con 4 :* (a :+ (b :+ c))) refl (Σc (rep gLN) l₀) (Σc (rep gLN) l₁) (Σc (rep gLN) l₂))
                                  (cong (4 *_) (sym (sp (rep gLN) (zr gLN)))))))
       (≤-trans (grp gBT) (≤-≡ (trans (solve 3 (λ a b c → con 2 :* a :+ (con 2 :* b :+ con 2 :* c) := con 2 :* (a :+ (b :+ c))) refl
                                         (Σc (rep gTQ) l₀) (Σc (rep gTQ) l₁) (Σc (rep gTQ) l₂))
                                  (cong (2 *_) (sym (sp (rep gTQ) (zr gTQ)))))))
       (≤-trans (grp gBQ) (≤-≡ (trans (solve 6 (λ a b c d e f → con 2 :* (con 5 :* a :+ d :+ con 5) :+ (con 2 :* (con 5 :* b :+ e :+ con 10)
                                                              :+ con 2 :* (con 5 :* c :+ f :+ con 5))
                                                      := con 10 :* (a :+ (b :+ c)) :+ con 2 :* (d :+ (e :+ f)) :+ con 40) refl
                                         (Σc (rep gLN) l₀) (Σc (rep gLN) l₁) (Σc (rep gLN) l₂) (Σc (rep gBT) l₀) (Σc (rep gBT) l₁) (Σc (rep gBT) l₂))
                                  (cong₂ (λ x y → 10 * x + 2 * y + 40) (sym (sp (rep gLN) (zr gLN))) (sym (sp (rep gBT) (zr gBT)))))))
       (≤-trans (≤-≡ (sp (χ HL) (zB (χ HL) (λ _ _ → refl))))
         (≤-trans (cancel3 {Σc (χ HL) l₀} {Σc (wI one) l₀} {Σc (wO one) l₀} {12 * NodeOut.nT N₀ + 24}
                           {Σc (χ HL) l₁} {Σc (wI one) l₁} {Σc (wO one) l₁} {12 * NodeOut.nT N₁ + 48}
                           {Σc (χ HL) l₂} {Σc (wI one) l₂} {Σc (wO one) l₂} {12 * NodeOut.nT N₂ + 24}
                           (≤-trans (NodeOut.nH N₀) (≤-≡ (solve 2 (λ t o → con 12 :* t :+ o :+ con 24 := o :+ (con 12 :* t :+ con 24)) refl
                                                                  (NodeOut.nT N₀) (Σc (wO one) l₀))))
                           (≤-trans (NodeOut.nH N₁) (≤-≡ (solve 2 (λ t o → con 12 :* t :+ o :+ con 48 := o :+ (con 12 :* t :+ con 48)) refl
                                                                  (NodeOut.nT N₁) (Σc (wO one) l₁))))
                           (≤-trans (NodeOut.nH N₂) (≤-≡ (solve 2 (λ t o → con 12 :* t :+ o :+ con 24 := o :+ (con 12 :* t :+ con 24)) refl
                                                                  (NodeOut.nT N₂) (Σc (wO one) l₂))))
                           (med one))
           (≤-≡ (solve 3 (λ a b c → (con 12 :* a :+ con 24) :+ ((con 12 :* b :+ con 48) :+ (con 12 :* c :+ con 24))
                                     := con 12 :* (a :+ (b :+ c)) :+ con 96) refl (NodeOut.nT N₀) (NodeOut.nT N₁) (NodeOut.nT N₂))))))
  where
    open +-*-Solver
    -- the system's labels and each node's
    L = labels s
    l₀ = labels s₀
    l₁ = labels s₁
    l₂ = labels s₂
    -- the blocks forged in the trace
    X = fvals L
    -- the stores' rely, at the nodes (over the breakable medium)
    rN = AllL-parR pi (sys-inX mediumB-prov tr)
    -- … at nodes B and C
    r₁₂ = AllL-parR pn rN
    -- the three nodes
    N₀ = nodeF fzero X t₀ (AllL-parL pn rN)
    N₁ = nodeF (fsuc fzero) X t₁ (AllL-parL pn′ r₁₂)
    N₂ = nodeF (fsuc (fsuc fzero)) X t₂ (AllL-parR pn′ r₁₂)
    -- their read bounds
    b₀ = NodeOut.nB N₀
    b₁ = NodeOut.nB N₁
    b₂ = NodeOut.nB N₂
    -- their threads' constants
    k₀ = 3 + KTn fzero b₀
    k₁ = 3 + KTn (fsuc fzero) b₁
    k₂ = 3 + KTn (fsuc (fsuc fzero)) b₂
    -- a system weight zero on a break is the three nodes' (the medium shows only io labels and breaks)
    sp : ∀ c → (∀ {e} → IsBrk e → c e ≡ 0) → Σc c L ≡ Σc c l₀ + (Σc c l₁ + Σc c l₂)
    sp c z = trans (ΣB c z (mediumB-io tM) pi) (trans (Σc-⦀ c pn) (cong (Σc c l₀ +_) (Σc-⦀ c pn′)))
    -- an environment weight is visible (a break only enlarges `#V`)
    toV : ∀ {c : Event → ℕ} → (∀ e → Data.Bool.T (c e Data.Nat.≤ᵇ χ̄ HL e)) → Σc c L ≤ #V HL s
    toV f = ≤-trans (Σc-≤ (allL (λ e → ≤ᵇ⇒≤ _ _ (f e)) L)) (Σc≤#V HL s)
    -- the breakable medium relays every wire weight, split over the three nodes
    med : ∀ w → Σc (wO w) l₀ + (Σc (wO w) l₁ + Σc (wO w) l₂) ≤ Σc (wI w) l₀ + (Σc (wI w) l₁ + Σc (wI w) l₂)
    med w = subst₂ _≤_ (trans (proj₁ (Σc-sync (wO w) (λ e m → proj₂ (Cls.oI (cls e) w m)) pi)) (sp (wO w) (zB (wO w) (λ _ _ → refl))))
                       (trans (proj₁ (Σc-sync (wI w) (λ e m → proj₁ (Cls.oI (cls e) w m)) pi)) (sp (wI w) (zB (wI w) (λ _ _ → refl))))
                       (mediumB-relay w tM)
    -- a relay group: the system's reports are paid by the three nodes' commands
    grp : ∀ g → Σc (rep g) L ≤ 2 * CBn fzero g b₀ l₀ + (2 * CBn (fsuc fzero) g b₁ l₁ + 2 * CBn (fsuc (fsuc fzero)) g b₂ l₂)
    grp g = ≤-trans (≤-≡ (sp (rep g) (zr g)))
              (cancel3 {Σc (rep g) l₀} {Σc (wI (ww g)) l₀} {Σc (wO (ww g)) l₀} {2 * CBn fzero g b₀ l₀}
                       {Σc (rep g) l₁} {Σc (wI (ww g)) l₁} {Σc (wO (ww g)) l₁} {2 * CBn (fsuc fzero) g b₁ l₁}
                       {Σc (rep g) l₂} {Σc (wI (ww g)) l₂} {Σc (wO (ww g)) l₂} {2 * CBn (fsuc (fsuc fzero)) g b₂ l₂}
                       (NodeOut.nG N₀ g) (NodeOut.nG N₁ g) (NodeOut.nG N₂ g) (med (ww g)))

-- PREMISE (a): the counting bound on every trace of the unhidden three-node system
boundL : ∀ {s Q} → rawL ⟹⟨ s ⟩ Q → #H HL s ≤ FL (#V HL s)
boundL {s} tr = case Par-trace-elim ioES _ NetworkLinkBreakableA (⦀Fin⁺ 2 nodeL) tr of λ where
  (_ , _ , _ , _ , tM , tN , pi) → case Par-trace-elim ∅ES _ (nodeL fzero) (nodeL (fsuc fzero) ⦀ nodeL (fsuc (fsuc fzero))) tN of λ where
    (_ , _ , _ , _ , t₀ , t₁₂ , pn) → case Par-trace-elim ∅ES _ (nodeL (fsuc fzero)) (nodeL (fsuc (fsuc fzero))) t₁₂ of λ where
      (_ , _ , _ , _ , t₁ , t₂ , pn′) → sysBL tr tM t₀ t₁ t₂ pi pn pn′
