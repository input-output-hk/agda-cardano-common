{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C: the concrete MEDIUM `NetworkLinkA`.
--   * `medium-relay` — for EVERY wire weight `w` (by cell and payload),
--     the medium never delivers (`output`) more weight than it was given
--     (`input`).  Per cell a value walks input → sndmsg → tx → rcvmsg →
--     output (stages 0–4); every leaf relays one stage on its own trace
--     (`Rl`, read off the `MediumProv` views), and each leaf's cost also
--     counts every LATER stage (`g1`–`g3`), so the pipeline joints
--     (`jointL`/`jointR`: one synchronisation, then its hiding) need no
--     alphabet fact.  Interleavings add (`Σc-⦀`); `renameMap ιNet` is
--     crossed by `CountRename`.
--   * `medium-io`    — the medium's visible alphabet is `ioES`
--   * `medium-prov`  — provenance (D1-b): every block the medium delivers
--     on a BlockFetch cell was handed to a BlockFetch cell earlier
--     (`MediumProv` at `Cl = (_≡ N2N_BlockFetch)`, payload → block)
-- No postulate, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.NoLivelock.MediumRelay (p : Params) where

open import Level using (0ℓ)
open import Data.Bool using (if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; m≤n+m; +-mono-≤; +-monoʳ-≤; +-monoˡ-≤; +-comm; +-assoc; +-identityʳ)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as UP
open import Function using (id; case_of_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Class.DecEq using (DecEq)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open Params p using (numLinks; linkConfig; Block)

open import Process_Trees using (ExtI; PTree)
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.Data p using (Payload; DecEq-Payload)
open import Cardano_network.NetCommon p using (ιNet; ιNet⁻¹; ιNet-linv; NetworkLinkA; ioES)
open import Cardano_network.Network p Payload
  using (NetProc; Menu; Input; inputMenu; outputMenu; csSR; csSR-dec; csRS; csRS-dec; csTA; csTA-dec)
import Cardano_network.Network p Payload as N
open import Cardano_network.NetworkLink p Payload
open import CSP.Operators (Net-≟ {Payload})
  using (EventSet; chanSet; Par; _∥⇘_⇙_; _⦀_; ⦀⋆; ⦀Fin; _∖_; pchoice; Output; Prefix; Ret; Skip; loop0)
import Semantics.LTS {E = Net Payload} {I = ExtI (Net Payload)} as L
import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as L₂
open import Semantics.Failures {E = Net Payload} {I = ExtI (Net Payload)} using (_⟹⟨_⟩_)
import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as F₂
open import CSP.Laws.Traces.TraceLawsBind (Net-≟ {Payload}) using (bs-live; bs-term; bind-elim-aux)
open import CSP.Laws.Traces.TraceLawsParallelTrace (Net-≟ {Payload})
  using (ParInter; pnil; psync; psoloL; psoloR; p√; Par-trace-elim)
open import CSP.Laws.Traces.TraceLawsHide (Net-≟ {Payload}) using (HideTr; hnil; hkeep; hdrop; h√; Hide-trace-elim)
open import CSP.Laws.DivFree.Loop (Net-≟ {Payload}) using (loopStep)
open import CSP.Laws.DivFree.Count (Net-≟ {Payload})
  using (labels; labels-EvlOnly; Σc; Σc-par; Σc-parL; Σc-parR; Ret-tr; out-tr; pfx-tr; AllL; []; _∷_; AllL-map;
         AllT; AllT-Ret; AllT-Output; AllT-⟶; AllT->>=; Post; post; Post->>=; Post-Ret; invLoop)
open import CSP.Laws.DivFree.CountMore (Net-≟ {Payload})
  using (InA; PfxW; Back; potIter; pch-tr; Σc-sync; Σc-⦀; +-swap; +-inter; labels-√; slack0)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload}) using () renaming (labels to labelsᴬ; Σc to Σcᴬ; AllL to AllLᴬ)
import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload}) as CA
open import CSP.Laws.DivFree.CountMore (Net_Api-≟ {Payload}) using () renaming (InA to InAᴬ; slack0 to slack0ᴬ)
open import CSP.Laws.DivFree.Prov (Net-≟ {Payload}) using (pa; runA)
open import CSP.Laws.DivFree.Prov (Net_Api-≟ {Payload}) using () renaming (PA to PAᴬ)
open import CSP.Laws.DivFree.ProvMore (Net-≟ {Payload}) using (Prov-comap)
open import Cardano_network.Parametric.Leios.NoLivelock.ProvBF p using (ChS; msgBlk)

------------------------------------------------------------------------
-- the renaming pulls back exactly its images (`CountRename`'s `ι-rinv`)
------------------------------------------------------------------------

-- `ιNet⁻¹` pulls back only `ιNet`-images (as `BlockProvenanceMedium.ιNet⁻¹-sound`)
ιNet-rinv : ∀ {A} {e₂ : Net_Api Payload A} {e : Net Payload A} → ιNet⁻¹ e₂ ≡ just e → e₂ ≡ ιNet e
ιNet-rinv {e₂ = input  _ _ _} refl = refl
ιNet-rinv {e₂ = output _ _ _} refl = refl
ιNet-rinv {e₂ = sndmsg _ _ _} refl = refl
ιNet-rinv {e₂ = rcvmsg _ _ _} refl = refl
ιNet-rinv {e₂ = tx     _ _ _} refl = refl
ιNet-rinv {e₂ = sndack _ _ _} refl = refl
ιNet-rinv {e₂ = rcvack _ _ _} refl = refl
ιNet-rinv {e₂ = ack    _ _ _} refl = refl
ιNet-rinv {e₂ = done   _ _ _} ()
ιNet-rinv {e₂ = apiCS  _ _ _} ()
ιNet-rinv {e₂ = apiBF  _ _ _} ()
ιNet-rinv {e₂ = apiTS  _ _ _} ()
ιNet-rinv {e₂ = apiKA  _ _ _} ()
ιNet-rinv {e₂ = apiLN  _ _ _} ()
ιNet-rinv {e₂ = apiLF  _ _ _} ()
ιNet-rinv {e₂ = apiLP  _ _ _} ()
ιNet-rinv {e₂ = store  _ _ _} ()
ιNet-rinv {e₂ = env    _ _ _} ()
ιNet-rinv {e₂ = break  _}     ()

open import CSP.Laws.DivFree.CountRename ιNet ιNet⁻¹ ιNet-linv ιNet-rinv (Net-≟ {Payload}) (Net_Api-≟ {Payload})
  using (renE; RenL; rnil; rcons; ren-trace-elim-rel; Σc≤-ren; PA-ren)

-- the medium's chain is the BlockFetch cells' (the system instance of `MediumProv`)
open import Cardano_network.Parametric.Leios.NoLivelock.MediumProv p Payload (λ id → id ≡ N2N_BlockFetch)
  using (InV; iv; inV; TrV; tv; trV; RaV; rv; raV; OutV; ov; outV; RvV; rvv; rvV; SaV; sav; saV; ChM; InIn; NetworkLink-PA)

-- the three internal channel sets
SR RS TA : EventSet
SR = chanSet csSR csSR-dec
RS = chanSet csRS csRS-dec
TA = chanSet csTA csTA-dec

------------------------------------------------------------------------
-- §1. Wire weights and the stage weights of a cell
------------------------------------------------------------------------

-- a weight on a wire message, by its cell and payload
WireW : Set
WireW = Link → Dir → IDs → Payload → ℕ

-- the weight an output / an input label carries (0 on every other channel)
wO wI : WireW → L₂.Event → ℕ
wO w (L₂.evLabel _ (output l d id) x) = w l d id x
wO w _                                = 0
wI w (L₂.evLabel _ (input l d id) x)  = w l d id x
wI w _                                = 0

-- stages 0 (input) and 4 (output), pulled back to the medium's own labels
a0 a4 : WireW → L.Event → ℕ
a0 w e = wI w (renE e)
a4 w e = wO w (renE e)

-- a weight kept only inside an event set
mask : EventSet → (L.Event → ℕ) → L.Event → ℕ
mask A c (L.evLabel B e a) = if ⌊ EventSet.dec A (B , e) a ⌋ then c (L.evLabel B e a) else 0

-- the raw weights of the inner stages 1 (sndmsg), 2 (tx), 3 (rcvmsg)
r1 r2 r3 : WireW → L.Event → ℕ
r1 w (L.evLabel _ (sndmsg l d id) x) = w l d id x
r1 w _                               = 0
r2 w (L.evLabel _ (tx l d id) x)     = w l d id x
r2 w _                               = 0
r3 w (L.evLabel _ (rcvmsg l d id) x) = w l d id x
r3 w _                               = 0

-- the inner stages, each kept inside the set it is synchronised on
a1 a2 a3 : WireW → L.Event → ℕ
a1 w = mask SR (r1 w)
a2 w = mask TA (r2 w)
a3 w = mask RS (r3 w)

-- a stage and every later one (what a relay of that stage may at most pass on)
g3 g2 g1 : WireW → L.Event → ℕ
g3 w e = a4 w e + a3 w e
g2 w e = g3 w e + a2 w e
g1 w e = g2 w e + a1 w e

-- a masked weight vanishes outside its set
mask-out : ∀ {A c} e → ¬ InA A e → mask A c e ≡ 0
mask-out {A} (L.evLabel B e a) ¬m with EventSet.dec A (B , e) a
... | yes m = ⊥-elim (¬m m)
... | no _  = refl

-- the input stage vanishes on a set that holds no input
a0-on : ∀ {w A} → (∀ {l d id x} → ¬ InA A (L.evLabel _ (input l d id) x)) → ∀ e → InA A e → a0 w e ≡ 0
a0-on h (L.evLabel _ (input _ _ _) _)  m = ⊥-elim (h m)
a0-on h (L.evLabel _ (output _ _ _) _) _ = refl
a0-on h (L.evLabel _ (sndmsg _ _ _) _) _ = refl
a0-on h (L.evLabel _ (rcvmsg _ _ _) _) _ = refl
a0-on h (L.evLabel _ (tx _ _ _) _)     _ = refl
a0-on h (L.evLabel _ (sndack _ _ _) _) _ = refl
a0-on h (L.evLabel _ (rcvack _ _ _) _) _ = refl
a0-on h (L.evLabel _ (ack _ _ _) _)    _ = refl

-- stage 2 vanishes on the Rx side's internal set
a2-RS : ∀ w e → InA RS e → a2 w e ≡ 0
a2-RS w (L.evLabel _ (rcvmsg _ _ _) _) _ = refl
a2-RS w (L.evLabel _ (sndack _ _ _) _) _ = refl
a2-RS w (L.evLabel _ (input _ _ _) _)  ()
a2-RS w (L.evLabel _ (output _ _ _) _) ()
a2-RS w (L.evLabel _ (sndmsg _ _ _) _) ()
a2-RS w (L.evLabel _ (tx _ _ _) _)     ()
a2-RS w (L.evLabel _ (rcvack _ _ _) _) ()
a2-RS w (L.evLabel _ (ack _ _ _) _)    ()

------------------------------------------------------------------------
-- §2. Relays: weights on every trace prefix
------------------------------------------------------------------------

-- a process relays `d` to `c`: on every trace it never passed on more than it was given
Rl : (L.Event → ℕ) → (L.Event → ℕ) → NetProc → Set₁
Rl c d P = ∀ {s W} → P ⟹⟨ s ⟩ W → Σc c (labels s) ≤ Σc d (labels s)

-- paying one event out of the slack
pw-step : ∀ c₁ d₁ m n C D → c₁ + m ≤ d₁ + n → C ≤ D + m → c₁ + C ≤ (d₁ + D) + n
pw-step c₁ d₁ m n C D h q =
  ≤-trans (+-monoʳ-≤ c₁ q) (≤-trans (≤-reflexive (+-swap c₁ D m)) (≤-trans (+-monoʳ-≤ D h)
    (≤-reflexive (trans (+-swap D d₁ n) (sym (+-assoc d₁ D n))))))

-- a return relays nothing
pw-Ret : ∀ {c d n} {ℓr} {R : Set ℓr} {x : R} → PfxW c d n (Ret x)
pw-Ret tr = case Ret-tr tr of λ { (inj₁ refl) → z≤n ; (inj₂ refl) → z≤n }

-- an output pays its event out of the slack
pw-Out : ∀ {c d m n} {A : Set} ⦃ _ : DecEq A ⦄ {e : Net Payload A} {v : A} {P : NetProc}
       → c (L.evLabel A e v) + m ≤ d (L.evLabel A e v) + n → PfxW c d m P → PfxW c d n (Output e v P)
pw-Out {c} {d} {m} {n} h q tr = case out-tr tr of λ where
  (inj₁ refl)               → z≤n
  (inj₂ (s′ , refl , rest)) → pw-step (c _) (d _) m n (Σc c (labels s′)) (Σc d (labels s′)) h (q rest)

-- a prefix pays its event (any value) out of the slack
pw-⟶ : ∀ {c d m n} {A : Set} {e : Net Payload A} {P : A → NetProc}
     → (∀ x → c (L.evLabel A e x) + m ≤ d (L.evLabel A e x) + n) → (∀ x → PfxW c d m (P x)) → PfxW c d n (Prefix e P)
pw-⟶ {c} {d} {m} {n} h q tr = case pfx-tr tr of λ where
  (inj₁ refl)                   → z≤n
  (inj₂ (x , s′ , refl , rest)) → pw-step (c _) (d _) m n (Σc c (labels s′)) (Σc d (labels s′)) (h x) (q x rest)

-- a menu, from its steps
pw-pch : ∀ {c d n} {v : Menu}
       → (∀ {x t′} → pchoice v L.─[ L.ev (L.evl x) ]─► t′ → Σ[ m ∈ ℕ ] ((c x + m ≤ d x + n) × PfxW c d m t′))
       → PfxW c d n (pchoice v)
pw-pch {c} {d} {n} f tr = case pch-tr tr of λ where
  (inj₁ refl)                            → z≤n
  (inj₂ (x , _ , s′ , st , refl , rest)) → case f st of λ where
    (m , h , q) → pw-step (c x) (d x) m n (Σc c (labels s′)) (Σc d (labels s′)) h (q rest)

-- a loop round: the body, then a silent loop-back
pw-round : ∀ {c d n} {b : NetProc} → PfxW c d n b → PfxW c d n (loopStep {R = UP.⊤ {0ℓ}} (λ _ → b) UP.tt)
pw-round {c} {d} {n} {b} pb tr with bind-elim-aux b (λ a′ → Ret (inj₁ a′)) tr
... | bs-live tb eo = subst (λ ls → Σc c ls ≤ Σc d ls + n) (labels-EvlOnly eo) (pb tb)
... | bs-term {sS = sS} tb fr eo (_ , kt) refl with Ret-tr kt
...   | inj₁ refl = subst (λ ls → Σc c ls ≤ Σc d ls + n)
                      (trans (labels-EvlOnly eo) (sym (cong labels (++-identityʳ sS)))) (pb tb)
...   | inj₂ refl = subst (λ ls → Σc c ls ≤ Σc d ls + n) (trans (labels-EvlOnly eo) (sym (labels-√ sS))) (pb tb)

-- a round that never outweighs its credit pays the (zero) potential drop
pw-post : ∀ {c d} {A Rx : Set} {a : A} {t : PTree (Net Payload) (ExtI (Net Payload)) (A ⊎ Rx)}
        → PfxW c d 0 t → Post (Back (λ _ → 0) c d a) t
pw-post {c} {d} pt = post λ {s} {x} tr → bk x (subst (λ ls → Σc c ls ≤ Σc d ls + 0) (labels-√ s) (pt tr))
  where
    -- by the round's return
    bk : ∀ {A Rx : Set} {a : A} {ls} (x : A ⊎ Rx) → Σc c ls ≤ Σc d ls + 0 → Back (λ _ → 0) c d a ls x
    bk (inj₁ _) h = ≤-trans (≤-reflexive (+-identityʳ _)) h
    bk (inj₂ _) _ = tt

-- a loop of a body that never outweighs its credit never does either
pw-loop0 : ∀ {c d} {b : NetProc} → PfxW c d 0 b → Rl c d (loop0 b)
pw-loop0 {c} {d} {b} pb {s} tr =
  slack0 {c} {d} {labels s} (potIter {k = loopStep (λ _ → b)} (λ _ → 0) c d 0 (λ _ → pw-round pb , pw-post (pw-round pb)) UP.tt tr)

-- a return relays
rl-Ret : ∀ {c d} → Rl c d Skip
rl-Ret tr = case Ret-tr tr of λ { (inj₁ refl) → z≤n ; (inj₂ refl) → z≤n }

-- an interleaving relays what both sides relay
rl-⦀ : ∀ {c d} {P Q : NetProc} → Rl c d P → Rl c d Q → Rl c d (P ⦀ Q)
rl-⦀ {c} {d} {P} {Q} rP rQ tr = case Par-trace-elim _ _ P Q tr of λ where
  (_ , _ , _ , _ , tP , tQ , pi) → subst₂ _≤_ (sym (Σc-⦀ c pi)) (sym (Σc-⦀ d pi)) (+-mono-≤ (rP tP) (rQ tQ))

-- a property closed under `⦀` from `Skip` holds of every interleaving of a mapped list
⦀⋆-ind : (Pr : NetProc → Set₁) → Pr Skip → (∀ {P Q} → Pr P → Pr Q → Pr (P ⦀ Q))
       → ∀ {X : Set} (f : X → NetProc) → (∀ x → Pr (f x)) → ∀ xs → Pr (⦀⋆ (map f xs))
⦀⋆-ind Pr z c f pf []       = z
⦀⋆-ind Pr z c f pf (x ∷ xs) = c (pf x) (⦀⋆-ind Pr z c f pf xs)

-- … and of every finite interleaving
⦀Fin-ind : (Pr : NetProc → Set₁) → Pr Skip → (∀ {P Q} → Pr P → Pr Q → Pr (P ⦀ Q))
         → ∀ n (f : Fin n → NetProc) → (∀ i → Pr (f i)) → Pr (⦀Fin n f)
⦀Fin-ind Pr z c zero    f pf = z
⦀Fin-ind Pr z c (suc n) f pf = c (pf fzero) (⦀Fin-ind Pr z c n (λ i → f (fsuc i)) (λ i → pf (fsuc i)))

------------------------------------------------------------------------
-- §3. Pipeline joints: synchronise on the middle stage, then hide it
------------------------------------------------------------------------

-- hiding only drops labels
Σc-hide≤ : ∀ (c : L.Event → ℕ) {A} {s′ s : List (L.Event√ (UP.⊤ {0ℓ}))} → HideTr A s′ s → Σc c (labels s) ≤ Σc c (labels s′)
Σc-hide≤ c hnil        = z≤n
Σc-hide≤ c (hkeep _ h) = +-monoʳ-≤ (c _) (Σc-hide≤ c h)
Σc-hide≤ c (hdrop _ h) = ≤-trans (Σc-hide≤ c h) (m≤n+m _ (c _))
Σc-hide≤ c h√          = z≤n

-- a weight that vanishes on the hidden set is unchanged by hiding
Σc-hide≡ : ∀ {c : L.Event → ℕ} {A} {s′ s : List (L.Event√ (UP.⊤ {0ℓ}))}
         → (∀ e → InA A e → c e ≡ 0) → HideTr A s′ s → Σc c (labels s′) ≡ Σc c (labels s)
Σc-hide≡ z hnil            = refl
Σc-hide≡ {c} z (hkeep _ h) = cong (c _ +_) (Σc-hide≡ z h)
Σc-hide≡ {c} {s′ = L.evl (L.evLabel _ _ _) ∷ s′} z (hdrop m h) = trans (cong (_+ Σc c (labels s′)) (z (L.evLabel _ _ _) m)) (Σc-hide≡ z h)
Σc-hide≡ z h√              = refl

-- a pointwise split, summed
Σc-split : ∀ {f g h : L.Event → ℕ} → (∀ e → f e + g e ≤ h e) → ∀ ls → Σc f ls + Σc g ls ≤ Σc h ls
Σc-split sp []                   = z≤n
Σc-split {f} {g} sp (e ∷ ls) =
  ≤-trans (≤-reflexive (+-inter (f e) (Σc f ls) (g e) (Σc g ls))) (+-mono-≤ (sp e) (Σc-split sp ls))

-- the arithmetic of a joint: the downstream cost passes the middle weight on to the upstream credit
jt : ∀ gu {gd mu md hu iu i} → gd ≤ md → md ≡ mu → gu + mu ≤ hu → hu ≤ iu → iu ≤ i → gu + gd ≤ i
jt _ q e r s t = ≤-trans (+-monoʳ-≤ _ (≤-trans q (≤-reflexive e))) (≤-trans r (≤-trans s t))

-- A JOINT, upstream on the left: `U` relays its credit to stage-m-and-later, `D` relays stage m
-- (synchronised, then hidden) to its cost
jointL : ∀ {A} {gU gD aI aM : L.Event → ℕ} {U D : NetProc}
       → (∀ e → gD e + aM e ≤ gU e) → (∀ e → ¬ InA A e → aM e ≡ 0) → (∀ e → InA A e → aI e ≡ 0)
       → Rl gU aI U → Rl gD aM D → Rl gD aI ((U ∥⇘ A ⇙ D) ∖ A)
jointL {A} {gU} {gD} {aI} {aM} {U} {D} sp zo zi rU rD tr = case Hide-trace-elim A _ tr of λ where
  (_ , _ , tr′ , h) → case Par-trace-elim A _ U D tr′ of λ where
    (sP , _ , _ , _ , tP , tQ , pi) →
      ≤-trans (Σc-hide≤ gD h) (≤-trans (Σc-par gD pi)
        (jt (Σc gD (labels sP)) (rD tQ) (trans (proj₂ (Σc-sync aM zo pi)) (sym (proj₁ (Σc-sync aM zo pi))))
            (Σc-split {gD} {aM} {gU} sp (labels sP))
            (rU tP) (≤-trans (Σc-parL aI pi) (≤-reflexive (Σc-hide≡ zi h)))))

-- … upstream on the right
jointR : ∀ {A} {gU gD aI aM : L.Event → ℕ} {U D : NetProc}
       → (∀ e → gD e + aM e ≤ gU e) → (∀ e → ¬ InA A e → aM e ≡ 0) → (∀ e → InA A e → aI e ≡ 0)
       → Rl gU aI U → Rl gD aM D → Rl gD aI ((D ∥⇘ A ⇙ U) ∖ A)
jointR {A} {gU} {gD} {aI} {aM} {U} {D} sp zo zi rU rD tr = case Hide-trace-elim A _ tr of λ where
  (_ , _ , tr′ , h) → case Par-trace-elim A _ D U tr′ of λ where
    (sP , sQ , _ , _ , tP , tQ , pi) →
      ≤-trans (Σc-hide≤ gD h) (≤-trans (Σc-par gD pi) (≤-trans (≤-reflexive (+-comm (Σc gD (labels sP)) (Σc gD (labels sQ))))
        (jt (Σc gD (labels sQ)) (rD tP) (trans (proj₁ (Σc-sync aM zo pi)) (sym (proj₂ (Σc-sync aM zo pi))))
            (Σc-split {gD} {aM} {gU} sp (labels sQ))
            (rU tQ) (≤-trans (Σc-parR aI pi) (≤-reflexive (Σc-hide≡ zi h))))))

------------------------------------------------------------------------
-- §4. Alphabets
------------------------------------------------------------------------

-- the Tx side's channels
TxA : L.Event → Set
TxA (L.evLabel _ (input _ _ _) _)  = ⊤
TxA (L.evLabel _ (sndmsg _ _ _) _) = ⊤
TxA (L.evLabel _ (rcvack _ _ _) _) = ⊤
TxA (L.evLabel _ (tx _ _ _) _)     = ⊤
TxA (L.evLabel _ (ack _ _ _) _)    = ⊤
TxA _                              = ⊥

-- the Rx side's channels
RxA : L.Event → Set
RxA (L.evLabel _ (rcvmsg _ _ _) _) = ⊤
RxA (L.evLabel _ (output _ _ _) _) = ⊤
RxA (L.evLabel _ (sndack _ _ _) _) = ⊤
RxA (L.evLabel _ (tx _ _ _) _)     = ⊤
RxA (L.evLabel _ (ack _ _ _) _)    = ⊤
RxA _                              = ⊥

-- a loop of a body that stays in the alphabet stays there
al-loop0 : ∀ {P} {b : NetProc} → AllT P b → AllT P (loop0 {R = UP.⊤ {0ℓ}} b)
al-loop0 {P} {b} ab tr =
  invLoop {body = λ _ → b} (λ _ _ → ⊤) (λ _ → 0) (λ _ → P) (λ _ q → q) (λ _ → AllT->>= ab (λ _ → AllT-Ret))
          (λ _ → Post->>= {Q₁ = λ _ _ → ⊤} (post λ _ → tt) (λ _ → Post-Ret tt)) {m = 0} tt tr

-- a menu stays in the alphabet if every step does
al-pch : ∀ {P} {v : Menu} → (∀ {x t′} → pchoice v L.─[ L.ev (L.evl x) ]─► t′ → P x × AllT P t′) → AllT P (pchoice v)
al-pch f tr = case pch-tr tr of λ where
  (inj₁ refl)                           → []
  (inj₂ (_ , _ , _ , st , refl , rest)) → proj₁ (f st) ∷ proj₂ (f st) rest

-- the labels of a parallel trace come from its sides
all-par : ∀ {P Q R : L.Event → Set} {A merge} {sP sQ s : List (L.Event√ (UP.⊤ {0ℓ}))}
        → (∀ {e} → P e → R e) → (∀ {e} → Q e → R e)
        → ParInter A merge sP sQ s → AllL P (labels sP) → AllL Q (labels sQ) → AllL R (labels s)
all-par f g pnil          _       _       = []
all-par f g (psync _ pi)  (p ∷ a) (_ ∷ b) = f p ∷ all-par f g pi a b
all-par f g (psoloL _ pi) (p ∷ a) b       = f p ∷ all-par f g pi a b
all-par f g (psoloR _ pi) a       (q ∷ b) = g q ∷ all-par f g pi a b
all-par f g p√            _       _       = []

-- a parallel composition stays in (the union of) its sides' alphabets
al-par : ∀ {P Q R : L.Event → Set} {A merge} {U D : NetProc}
       → (∀ {e} → P e → R e) → (∀ {e} → Q e → R e) → AllT P U → AllT Q D → AllT R (Par A merge U D)
al-par {A = A} {merge} {U} {D} f g aU aD tr = case Par-trace-elim A merge U D tr of λ where
  (_ , _ , _ , _ , tU , tD , pi) → all-par f g pi (aU tU) (aD tD)

-- the labels a hiding keeps lie outside the hidden set
all-hide : ∀ {P : L.Event → Set} {A} {s′ s : List (L.Event√ (UP.⊤ {0ℓ}))}
         → HideTr A s′ s → AllL P (labels s′) → AllL (λ e → P e × ¬ InA A e) (labels s)
all-hide hnil         _       = []
all-hide (hkeep ¬m h) (p ∷ a) = (p , ¬m) ∷ all-hide h a
all-hide (hdrop _ h)  (_ ∷ a) = all-hide h a
all-hide h√           _       = []

-- hiding leaves only labels outside the hidden set
al-hide : ∀ {P} {A} {U : NetProc} → AllT P U → AllT (λ e → P e × ¬ InA A e) (U ∖ A)
al-hide {A = A} {U} aU tr = case Hide-trace-elim A U tr of λ where
  (_ , _ , tU , h) → all-hide h (aU tU)

------------------------------------------------------------------------
-- §5. The leaves, read off the `MediumProv` views
------------------------------------------------------------------------

-- what a leaf step owes: its label and the rest lie in the alphabet `P`, and it relays
StepS : (L.Event → Set) → (L.Event → ℕ) → (L.Event → ℕ) → L.Event → NetProc → Set₁
StepS P c d x t′ = (P x × AllT P t′) × Σ[ m ∈ ℕ ] ((c x + m ≤ d x + 0) × PfxW c d m t′)

-- a leaf: a loop of a menu whose every step pays its way
leaf : ∀ {P c d} {v : Menu} → (∀ {x t′} → pchoice v L.─[ L.ev (L.evl x) ]─► t′ → StepS P c d x t′)
     → AllT P (loop0 {R = UP.⊤ {0ℓ}} (pchoice v)) × Rl c d (loop0 (pchoice v))
leaf f = al-loop0 (al-pch (λ st → proj₁ (f st))) , pw-loop0 (pw-pch (λ st → proj₂ (f st)))

-- an Input step: stage 0 in, stage 1 out
inS : ∀ {w l d id x t′} → InV l d id x t′ → StepS TxA (g1 w) (a0 w) x t′
inS {w} {l} {d} {id} (iv x) =
    (tt , AllT-Output _ x tt (AllT-⟶ _ (λ _ → tt) (λ _ → AllT-Ret)))
  , (w l d id x , m≤m+n _ 0 , pw-Out (≤-reflexive (+-identityʳ _)) (pw-⟶ (λ _ → ≤-refl) (λ _ → pw-Ret)))

-- a transmitter step: stage 1 in, stage 2 out
trS : ∀ {w l x t′} → TrV l x t′ → StepS TxA (g2 w) (a1 w) x t′
trS {w} {l} (tv d id x) =
  (tt , AllT-Output _ x tt AllT-Ret) , (w l d id x , m≤m+n _ 0 , pw-Out (≤-reflexive (+-identityʳ _)) pw-Ret)

-- an ack-relay step: weightless
raS : ∀ {w l x t′} → RaV l x t′ → StepS TxA (g2 w) (a1 w) x t′
raS (rv d id u) = (tt , AllT-⟶ _ (λ _ → tt) (λ _ → AllT-Ret)) , (0 , ≤-refl , pw-⟶ (λ _ → ≤-refl) (λ _ → pw-Ret))

-- an Output step: stage 3 in, stage 4 out
ouS : ∀ {w l d id x t′} → OutV l d id x t′ → StepS RxA (a4 w) (a3 w) x t′
ouS {w} {l} {d} {id} (ov x) =
    (tt , AllT-Output _ x tt (AllT-⟶ _ (λ _ → tt) (λ _ → AllT-Ret)))
  , (w l d id x , m≤m+n _ 0 , pw-Out (≤-reflexive (+-identityʳ _)) (pw-⟶ (λ _ → ≤-refl) (λ _ → pw-Ret)))

-- a receiver step: stage 2 in, stage 3 out
rvS : ∀ {w l x t′} → RvV l x t′ → StepS RxA (g3 w) (a2 w) x t′
rvS {w} {l} (rvv d id x) =
  (tt , AllT-Output _ x tt AllT-Ret) , (w l d id x , m≤m+n _ 0 , pw-Out (≤-reflexive (+-identityʳ _)) pw-Ret)

-- an ack-sender step: weightless
saS : ∀ {w l x t′} → SaV l x t′ → StepS RxA (g3 w) (a2 w) x t′
saS (sav d id u) = (tt , AllT-⟶ _ (λ _ → tt) (λ _ → AllT-Ret)) , (0 , ≤-refl , pw-⟶ (λ _ → ≤-refl) (λ _ → pw-Ret))

-- THE LEAVES (alphabet, relay)
Input-L : ∀ w l d id → AllT TxA (Input l d id) × Rl (g1 w) (a0 w) (Input l d id)
Input-L w l d id = leaf (λ st → inS {w} (inV st))

-- the transmitter
Tr-L : ∀ w l → AllT TxA (Transmitterₗ l) × Rl (g2 w) (a1 w) (Transmitterₗ l)
Tr-L w l = leaf (λ st → trS {w} (trV st))

-- the ack relay
Ra-L : ∀ w l → AllT TxA (RcvAckₗ l) × Rl (g2 w) (a1 w) (RcvAckₗ l)
Ra-L w l = leaf (λ st → raS {w} (raV st))

-- an output cell
Out-L : ∀ w l d id → AllT RxA (N.Output l d id) × Rl (a4 w) (a3 w) (N.Output l d id)
Out-L w l d id = leaf (λ st → ouS {w} (outV st))

-- the receiver
Rv-L : ∀ w l → AllT RxA (Receiverₗ l) × Rl (g3 w) (a2 w) (Receiverₗ l)
Rv-L w l = leaf (λ st → rvS {w} (rvV st))

-- the ack sender
Sa-L : ∀ w l → AllT RxA (SndAckₗ l) × Rl (g3 w) (a2 w) (SndAckₗ l)
Sa-L w l = leaf (λ st → saS {w} (saV st))

------------------------------------------------------------------------
-- §6. THE RELAY
------------------------------------------------------------------------

-- the Tx side relays stage 0 to stages 2–4
TxSide-R : ∀ w l → Rl (g2 w) (a0 w) (TxSideₗ l)
TxSide-R w l = jointL (λ _ → ≤-refl) (mask-out {SR} {r1 w}) (a0-on {w} {SR} (λ ()))
  (⦀⋆-ind (Rl (g1 w) (a0 w)) (rl-Ret {g1 w} {a0 w}) (rl-⦀ {g1 w} {a0 w}) _ (λ { (d , id) → proj₂ (Input-L w l d id) }) (linkConfig l))
  (rl-⦀ (proj₂ (Tr-L w l)) (proj₂ (Ra-L w l)))

-- the Rx side relays stage 2 to stage 4
RxSide-R : ∀ w l → Rl (a4 w) (a2 w) (RxSideₗ l)
RxSide-R w l = jointR (λ _ → ≤-refl) (mask-out {RS} {r3 w}) (a2-RS w)
  (rl-⦀ (proj₂ (Rv-L w l)) (proj₂ (Sa-L w l)))
  (⦀⋆-ind (Rl (a4 w) (a3 w)) (rl-Ret {a4 w} {a3 w}) (rl-⦀ {a4 w} {a3 w}) _ (λ { (d , id) → proj₂ (Out-L w l d id) }) (linkConfig l))

-- one link relays stage 0 to stage 4
NetOneLink-R : ∀ w l → Rl (a4 w) (a0 w) (NetOneLink l)
NetOneLink-R w l = jointL (λ e → +-monoˡ-≤ (a2 w e) (m≤m+n (a4 w e) (a3 w e))) (mask-out {TA} {r2 w}) (a0-on {w} {TA} (λ ()))
  (TxSide-R w l) (RxSide-R w l)

-- THE RELAY: what the medium delivers never outweighs what it was given, for EVERY weight
medium-relay : (w : WireW) {s : List (L₂.Event√ (UP.⊤ {0ℓ}))} {W : _}
             → NetworkLinkA F₂.⟹⟨ s ⟩ W → Σcᴬ (wO w) (labelsᴬ s) ≤ Σcᴬ (wI w) (labelsᴬ s)
medium-relay w {s} tr =
  slack0ᴬ {wO w} {wI w} {labelsᴬ s} (Σc≤-ren (wO w) (wI w) 0
    (λ t → ≤-trans (⦀Fin-ind (Rl (a4 w) (a0 w)) (rl-Ret {a4 w} {a0 w}) (rl-⦀ {a4 w} {a0 w}) numLinks NetOneLink (NetOneLink-R w) t) (m≤m+n _ 0)) tr)

------------------------------------------------------------------------
-- §7. The visible alphabet
------------------------------------------------------------------------

-- the Tx side shows only its own non-internal channels
TxSide-A : ∀ l → AllT (λ e → TxA e × ¬ InA SR e) (TxSideₗ l)
TxSide-A l = al-hide (al-par id id
  (⦀⋆-ind (AllT TxA) AllT-Ret (al-par id id) _ (λ { (d , id) → proj₁ (Input-L (λ _ _ _ _ → 0) l d id) }) (linkConfig l))
  (al-par id id (proj₁ (Tr-L (λ _ _ _ _ → 0) l)) (proj₁ (Ra-L (λ _ _ _ _ → 0) l))))

-- the Rx side shows only its own non-internal channels
RxSide-A : ∀ l → AllT (λ e → RxA e × ¬ InA RS e) (RxSideₗ l)
RxSide-A l = al-hide (al-par id id
  (⦀⋆-ind (AllT RxA) AllT-Ret (al-par id id) _ (λ { (d , id) → proj₁ (Out-L (λ _ _ _ _ → 0) l d id) }) (linkConfig l))
  (al-par id id (proj₁ (Rv-L (λ _ _ _ _ → 0) l)) (proj₁ (Sa-L (λ _ _ _ _ → 0) l))))

-- what one link can show
IoP : L.Event → Set
IoP e = ((TxA e × ¬ InA SR e) ⊎ (RxA e × ¬ InA RS e)) × ¬ InA TA e

-- what survives every hiding of a link is an io label
io : ∀ {e} → IoP e → InAᴬ ioES (renE e)
io {L.evLabel _ (input _ _ _) _}  _                    = UP.tt
io {L.evLabel _ (output _ _ _) _} _                    = UP.tt
io {L.evLabel _ (sndmsg _ _ _) _} (inj₁ (_ , ¬m) , _)  = ⊥-elim (¬m UP.tt)
io {L.evLabel _ (sndmsg _ _ _) _} (inj₂ (() , _) , _)
io {L.evLabel _ (rcvack _ _ _) _} (inj₁ (_ , ¬m) , _)  = ⊥-elim (¬m UP.tt)
io {L.evLabel _ (rcvack _ _ _) _} (inj₂ (() , _) , _)
io {L.evLabel _ (rcvmsg _ _ _) _} (inj₁ (() , _) , _)
io {L.evLabel _ (rcvmsg _ _ _) _} (inj₂ (_ , ¬m) , _)  = ⊥-elim (¬m UP.tt)
io {L.evLabel _ (sndack _ _ _) _} (inj₁ (() , _) , _)
io {L.evLabel _ (sndack _ _ _) _} (inj₂ (_ , ¬m) , _)  = ⊥-elim (¬m UP.tt)
io {L.evLabel _ (tx _ _ _) _}     (_ , ¬m)             = ⊥-elim (¬m UP.tt)
io {L.evLabel _ (ack _ _ _) _}    (_ , ¬m)             = ⊥-elim (¬m UP.tt)

-- a renamed trace keeps the alphabet its source was pulled back to
al-ren : ∀ {P : L₂.Event → Set} {ls ls′} → RenL ls ls′ → AllL (λ e → P (renE e)) ls → AllLᴬ P ls′
al-ren rnil      []      = CA.[]
al-ren (rcons r) (p ∷ a) = p CA.∷ al-ren r a

-- THE ALPHABET: the medium's visible alphabet is `ioES`
medium-io : ∀ {s W} → NetworkLinkA F₂.⟹⟨ s ⟩ W → AllLᴬ (InAᴬ ioES) (labelsᴬ s)
medium-io tr = case ren-trace-elim-rel tr of λ where
  (_ , _ , tr₁ , rl) → al-ren rl (AllL-map io
    (⦀Fin-ind (AllT IoP) AllT-Ret (al-par id id) numLinks NetOneLink
      (λ l → al-hide (al-par inj₁ inj₂ (TxSide-A l) (RxSide-A l))) tr₁))

------------------------------------------------------------------------
-- §8. THE MEDIUM HOP of the block chain (D1-b)
------------------------------------------------------------------------

-- a BlockFetch-cell input carrying the block: the medium's only rely
InM : L₂.Event → Block → Set
InM (L₂.evLabel _ (input _ _ N2N_BlockFetch) pl) y = msgBlk pl ≡ just y
InM _                                            y = ⊥

-- the payload carries the block
Rv : Payload → Block → Set
Rv pl b = msgBlk pl ≡ just b

-- a system chain label on the medium carries a block whose payload the medium chain carries
chs→chm : ∀ {e y′} → ChS (renE e) y′ → Σ[ y ∈ Payload ] (ChM e y × Rv y y′)
chs→chm {L.evLabel _ (input _ _ N2N_BlockFetch) pl}   c = pl , (refl , refl) , c
chs→chm {L.evLabel _ (output _ _ N2N_BlockFetch) pl}  c = pl , (refl , refl) , c
chs→chm {L.evLabel _ (input _ _ N2N_ChainSync) _}     ()
chs→chm {L.evLabel _ (input _ _ N2N_TxSubmission) _}  ()
chs→chm {L.evLabel _ (input _ _ N2N_KeepAlive) _}     ()
chs→chm {L.evLabel _ (input _ _ N2N_LeiosNotify) _}   ()
chs→chm {L.evLabel _ (input _ _ N2N_LeiosFetch) _}    ()
chs→chm {L.evLabel _ (output _ _ N2N_ChainSync) _}    ()
chs→chm {L.evLabel _ (output _ _ N2N_TxSubmission) _} ()
chs→chm {L.evLabel _ (output _ _ N2N_KeepAlive) _}    ()
chs→chm {L.evLabel _ (output _ _ N2N_LeiosNotify) _}  ()
chs→chm {L.evLabel _ (output _ _ N2N_LeiosFetch) _}   ()
chs→chm {L.evLabel _ (sndmsg _ _ _) _}                ()
chs→chm {L.evLabel _ (rcvmsg _ _ _) _}                ()
chs→chm {L.evLabel _ (tx _ _ _) _}                    ()
chs→chm {L.evLabel _ (sndack _ _ _) _}                ()
chs→chm {L.evLabel _ (rcvack _ _ _) _}                ()
chs→chm {L.evLabel _ (ack _ _ _) _}                   ()

-- a medium rely (a BlockFetch input) is a system rely, and a system chain label
inM : ∀ {e y y′} → InIn e y → Rv y y′ → InM (renE e) y′ × ChS (renE e) y′
inM {L.evLabel _ (input _ _ _) _}  (refl , refl) r = r , r
inM {L.evLabel _ (output _ _ _) _} ()
inM {L.evLabel _ (sndmsg _ _ _) _} ()
inM {L.evLabel _ (rcvmsg _ _ _) _} ()
inM {L.evLabel _ (tx _ _ _) _}     ()
inM {L.evLabel _ (sndack _ _ _) _} ()
inM {L.evLabel _ (rcvack _ _ _) _} ()
inM {L.evLabel _ (ack _ _ _) _}    ()

-- THE MEDIUM HOP on the system alphabet: every BF-cell block the medium delivers was BF-cell input earlier
medium-prov : PAᴬ ChS ChS InM NetworkLinkA
medium-prov = PA-ren (pa λ tr →
  Prov-comap Rv chs→chm (λ i r → proj₁ (inM i r)) (λ i r → proj₂ (inM i r)) (λ ())
    _ (runA NetworkLink-PA {K = λ _ → ⊥} tr))
