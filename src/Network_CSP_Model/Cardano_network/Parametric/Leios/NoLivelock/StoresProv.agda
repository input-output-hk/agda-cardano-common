{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C (D1-b, shipped route): the RB store under VALUE
-- PROVENANCE.
--   * `blockStore-prov`  — THE STORE HOP: every block the store hands out
--     (`stGet`/`stGetAt`) was deposited or forged into it before
--     (stateful: `provInv` with "every held block is known")
--   * `blockStore-readsX` — THE BOUND: if every deposited block lies in a
--     list X (provenance: X = the blocks forged anywhere in the system
--     trace), every read index stays below |X| + (forges here); deposits
--     outside X are paid for by the weight `cB X`, which provenance zeroes
--   * D1-a is the instance X = the three values of `Maybe Bool`.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Cardano_network.Parametric.Topology using (Topology; module Topology)
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (pL; lpF; VB; AllV; HP)

module Cardano_network.Parametric.Leios.NoLivelock.StoresProv
  (k m : ℕ) (tP : Topology (pL k m)) (vo : Topology.Node tP → Fin m) (U : List (VB m)) (allV : AllV m U) where

-- the family member this module is about
pP = pL k m
-- its Leios parameters
lpP = lpF k m
open Topology tP using (Node)


open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; reverse; length)
open import Data.List.Properties using (length-reverse; ++-identityʳ)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Base using (reverseAcc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; +-mono-≤; +-suc; +-identityʳ; +-comm; +-assoc)
open import Data.Product using (_,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (0ℓ)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Class.DecEq using (DecEq; _≟_)
open import Data.Fin using (Fin)

open import Process_Trees using (PTree; ExtI)
open import Cardano_network.Base
open import Cardano_network.Parametric.Leios.NoLivelock.Threads k m tP vo using (IsGetAt)
open import Cardano_network.Parametric.Leios.NoLivelock.Stores k m tP vo U allV
  using (mem; mem≤1; mem-cons; cF; AllT-mono; oi-reads; forge-cases)
open import Cardano_network.Parametric.Leios.NoLivelock.ProvBF pP using (ChS)
open import Cardano_network.Net pP
open import Cardano_network.Data pP using (Payload)
open import Cardano_network.ApiAlphabet pP using (apiES)
open import Cardano_network.Params using (module Params)
open Params pP using (decBlock)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (Event; evLabel)
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
open import CSP.Laws.DivFree.Loop (Net_Api-≟ {Payload}) using (loopStep)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload})
open import CSP.Laws.DivFree.Prov (Net_Api-≟ {Payload})
  using (Prov; Kn; ProvT; ProvT-Ret; ProvT-Stop; ProvT-⟶; ProvT-Output; ProvT-□; ProvT->>=; provInv; JAt)
import Cardano_network.Parametric.NodeLogic as NL
open NL.Generic pP tP apiES using (offerHeld; Held; forgeEv; putEv; getEv)
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open NLL.Generic pP lpP tP apiES vo
  using (storeStepL; blockStoreL; offerIx; getAtEv; memberOf; acceptForgeL)

-- (Task 8, the five stores together)
open import Data.Product using (proj₁)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (_⦀_)
open import CSP.Laws.DivFree.Prov (Net_Api-≟ {Payload}) using (InA; PA; pa; PA-par≡)
open import CSP.Laws.DivFree.ProvMore (Net_Api-≟ {Payload}) using (AllT→PA)
open import Cardano_network.Parametric.Leios.NoLivelock.Threads k m tP vo using (loopAll)
open import Cardano_network.Parametric.Leios.NoLivelock.Stores k m tP vo U allV
  using (oiAll; eb-All; body-All; mem-All; vote-All)
open NL.Generic pP tP apiES using (storeES)
open NLL.Generic pP lpP tP apiES vo using (ebStore; bodyStore; mempool; voteStore; voteStep)

------------------------------------------------------------------------
-- the store bound, relative to a list X of admissible blocks
------------------------------------------------------------------------

-- how many blocks of X are held (D1-a's `D3` is X = the three values)
cnt : List (Maybe Bool) → Held → ℕ
cnt []      hs = 0
cnt (x ∷ X) hs = mem x hs + cnt X hs

-- at most |X|
cnt≤ : ∀ X hs → cnt X hs ≤ length X
cnt≤ []      hs = z≤n
cnt≤ (x ∷ X) hs = +-mono-≤ (mem≤1 x hs) (cnt≤ X hs)

-- never drops when a block is prepended
cnt-cons : ∀ X b hs → cnt X hs ≤ cnt X (b ∷ hs)
cnt-cons []      b hs = z≤n
cnt-cons (x ∷ X) b hs = +-mono-≤ (mem-cons x b hs) (cnt-cons X b hs)

-- a decision of `b ≡ b` says yes
dt : ∀ {b : Maybe Bool} (d : Dec (b ≡ b)) → ⌊ d ⌋ ≡ true
dt (yes _) = refl
dt (no ¬p) = ⊥-elim (¬p refl)

-- a block is held right after it is prepended
memHit : ∀ b hs → mem b (b ∷ hs) ≡ 1
memHit b hs = cong (λ z → if z ∨ memberOf ⦃ decBlock ⦄ b hs then 1 else 0) (dt (DecEq._≟_ decBlock b b))

-- a block not held counts zero
memMiss : ∀ b hs → memberOf ⦃ decBlock ⦄ b hs ≡ false → mem b hs ≡ 0
memMiss b hs eq = cong (λ z → if z then 1 else 0) eq

-- grows when a fresh block of X is prepended
cnt-fresh : ∀ X b hs → memberOf ⦃ decBlock ⦄ b X ≡ true → memberOf ⦃ decBlock ⦄ b hs ≡ false
          → suc (cnt X hs) ≤ cnt X (b ∷ hs)
cnt-fresh (x ∷ X) b hs inX fresh with DecEq._≟_ decBlock x b
... | yes refl = subst (λ z → suc (mem x hs + cnt X hs) ≤ z + cnt X (x ∷ hs)) (sym (memHit x hs))
                   (subst (λ z → suc (z + cnt X hs) ≤ suc (cnt X (x ∷ hs))) (sym (memMiss x hs fresh))
                     (s≤s (cnt-cons X x hs)))
... | no _ = subst (_≤ mem x (b ∷ hs) + cnt X (b ∷ hs)) (+-suc (mem x hs) (cnt X hs))
               (+-mono-≤ (mem-cons x b hs) (cnt-fresh X b hs inX fresh))

-- a deposit outside X costs one unit of budget
cB : List (Maybe Bool) → Event → ℕ
cB X (evLabel _ (store _ _ stPut) b) = if memberOf ⦃ decBlock ⦄ b X then 0 else 1
cB X _                                = 0

-- the budget: forges here plus deposits outside X
cFB : List (Maybe Bool) → Event → ℕ
cFB X e = cF e + cB X e

-- the store invariant relative to X
SInvX : List (Maybe Bool) → Held → ℕ → Set
SInvX X hs m = length hs ≤ cnt X hs + m

-- a read stays below |X| + budget
ROkX : List (Maybe Bool) → ℕ → Event → Set
ROkX X m e = ∀ j → IsGetAt j e → j < length X + m

module _ (n : Node) (X : List (Maybe Bool)) where

  -- the hand-over menu reads no index
  ohX : ∀ {m} hs bs → AllT (ROkX X m) (offerHeld n hs bs)
  ohX hs []       = AllT-Stop
  ohX hs (b ∷ bs) = AllT-□ (AllT-Output _ _ (λ j ()) AllT-Ret) (ohX hs bs)

  -- every read of a round is below |X| + budget
  rOkX : ∀ {hs m} → SInvX X hs m → AllT (ROkX X m) (loopStep {R = ⊤ {0ℓ}} (storeStepL n) hs)
  rOkX {hs} {m} i =
    AllT->>= (AllT-□ (AllT-⟶ _ (λ _ j ()) (λ _ → AllT-Ret))
               (AllT-□ (AllT-⟶ _ (λ _ j ()) (λ _ → AllT-Ret))
                 (AllT-□ (ohX hs hs)
                   (AllT-mono (λ f j r → ≤-trans (f j r)
                                 (≤-trans (subst (_≤ cnt X hs + m) (sym (length-reverse hs)) i)
                                          (+-mono-≤ (cnt≤ X hs) ≤-refl)))
                              (oi-reads n hs (reverse hs) 0)))))
             (λ _ → AllT-Ret)

  -- the budget never shrinks the invariant
  keepX : ∀ {hs m k} → SInvX X hs m → SInvX X hs (m + k)
  keepX {hs} {m} {k} i = ≤-trans i (+-mono-≤ (≤-refl {cnt X hs}) (m≤m+n m k))

  -- the menus that hand blocks out leave the state alone
  oh-postX : ∀ {m} hs bs → SInvX X hs m → Post (λ ls h′ → SInvX X h′ (m + Σc (cFB X) ls)) (offerHeld n hs bs)
  oh-postX hs []       i = Post-Stop
  oh-postX {m} hs (b ∷ bs) i = Post-□ (Post-Output _ _ (Post-Ret (keepX {hs} {m} i))) (oh-postX hs bs i)

  -- … the read-pointer menu too
  oi-postX : ∀ {m} hs xs k₀ → SInvX X hs m
           → Post (λ ls h′ → SInvX X h′ (m + Σc (cFB X) ls)) (offerIx (getAtEv n) xs k₀ hs)
  oi-postX hs []       k₀ i = Post-Stop
  oi-postX {m} hs (x ∷ xs) k₀ i = Post-□ (Post-Output _ _ (Post-Ret (keepX {hs} {m} i))) (oi-postX hs xs (suc k₀) i)

  -- a forge pays one unit
  forge-invX : ∀ {hs m} mb → SInvX X hs m → SInvX X (acceptForgeL mb hs) (m + 1)
  forge-invX {hs} {m} mb i with forge-cases n mb hs
  ... | inj₁ eq rewrite eq = keepX {hs} {m} i
  ... | inj₂ eq rewrite eq =
        subst (λ z → suc (length hs) ≤ cnt X (proj₂ mb ∷ hs) + z) (+-comm 1 m)
          (subst (suc (length hs) ≤_) (sym (+-suc (cnt X (proj₂ mb ∷ hs)) m))
             (s≤s (≤-trans i (+-mono-≤ (cnt-cons X (proj₂ mb) hs) ≤-refl))))

  -- a deposit: a held block changes nothing, a fresh one of X raises the count, one outside X is paid
  put-invX : ∀ {hs m} b → SInvX X hs m
           → SInvX X (if memberOf ⦃ decBlock ⦄ b hs then hs else b ∷ hs) (m + (cB X (evLabel _ (putEv n) b) + 0))
  put-invX {hs} {m} b i with memberOf ⦃ decBlock ⦄ b hs in eh
  ... | true = keepX {hs} {m} i
  ... | false with memberOf ⦃ decBlock ⦄ b X in ex
  ...   | true  = subst (suc (length hs) ≤_) (cong (cnt X (b ∷ hs) +_) (sym (+-identityʳ m)))
                    (≤-trans (s≤s i) (+-mono-≤ (cnt-fresh X b hs ex eh) (≤-refl {m})))
  ...   | false = subst (suc (length hs) ≤_) (cong (cnt X (b ∷ hs) +_) (sym (+-comm m 1)))
                    (subst (suc (length hs) ≤_) (sym (+-suc (cnt X (b ∷ hs)) m))
                      (s≤s (≤-trans i (+-mono-≤ (cnt-cons X b hs) ≤-refl))))

  -- every completed round re-establishes the invariant at the grown budget
  rInvX : ∀ {hs m} → SInvX X hs m
        → Post (λ ls x → InvAt (SInvX X) x (m + Σc (cFB X) ls)) (loopStep {R = ⊤ {0ℓ}} (storeStepL n) hs)
  rInvX {hs} {m} i =
    Post->>= {Q₁ = λ ls h′ → SInvX X h′ (m + Σc (cFB X) ls)}
      (Post-□ (Post-⟶ _ (λ mb → Post-Ret (forge-invX {hs} {m} mb i)))
        (Post-□ (Post-⟶ _ (λ b → Post-Ret (put-invX {hs} {m} b i)))
          (Post-□ (oh-postX hs hs i) (oi-postX hs (reverse hs) 0 i))))
      (λ {ls₁} {r} q → Post-Ret (subst (λ ls → SInvX X r (m + Σc (cFB X) ls)) (sym (++-identityʳ ls₁)) q))

  -- THE STORE BOUND RELATIVE TO X: every read index stays below |X| + forges + deposits outside X
  blockStore-readsX : ∀ {s W} → blockStoreL n [] ⟹⟨ s ⟩ W → AllL (ROkX X (Σc (cFB X) (labels s))) (labels s)
  blockStore-readsX tr = invLoop (SInvX X) (cFB X) (ROkX X) ROkX-mono rOkX rInvX {m = 0} z≤n tr
    where
      -- monotone in the budget
      ROkX-mono : ∀ {m m′ e} → m ≤ m′ → ROkX X m e → ROkX X m′ e
      ROkX-mono m≤ ok j r = ≤-trans (ok j r) (+-mono-≤ (≤-refl {length X}) m≤)

------------------------------------------------------------------------
-- the store's own hop: what it hands out was put or forged into it
------------------------------------------------------------------------

-- the RB store relies on deposits and forges
InSt : Event → Maybe Bool → Set
InSt (evLabel _ (store _ _ stPut) b)        y = b ≡ y
InSt (evLabel _ (env _ _ envForge) (_ , b)) y = b ≡ y
InSt _                                      y = ⊥

-- `All` survives the accumulator reversal
All-revAcc : ∀ {K : Maybe Bool → Set} acc xs → All K acc → All K xs → All K (reverseAcc acc xs)
All-revAcc acc []       a []      = a
All-revAcc acc (x ∷ xs) a (k ∷ b) = All-revAcc (x ∷ acc) xs (k ∷ a) b

module _ (n : Node) where

  -- the hand-over menu: each block it offers is known
  ohP : ∀ {K} (hs bs : Held) → All K bs → ProvT ChS ChS InSt K (offerHeld n hs bs)
  ohP hs []       []       = ProvT-Stop
  ohP hs (b ∷ bs) (k ∷ a)  = ProvT-□ (ProvT-Output (getEv n) b (λ { refl → inj₂ k }) ProvT-Ret) (ohP hs bs a)

  -- the read-pointer menu likewise
  oiP : ∀ {K} (hs xs : Held) k₀ → All K xs → ProvT ChS ChS InSt K (offerIx (getAtEv n) xs k₀ hs)
  oiP hs []       k₀ []      = ProvT-Stop
  oiP hs (x ∷ xs) k₀ (k ∷ a) = ProvT-□ (ProvT-Output (getAtEv n k₀) x (λ { refl → inj₂ k }) ProvT-Ret) (oiP hs xs (suc k₀) a)

  -- a round from a known store
  rP : ∀ {hs K} → All K hs → ProvT ChS ChS InSt K (loopStep {R = ⊤ {0ℓ}} (storeStepL n) hs)
  rP {hs} a =
    ProvT->>= (ProvT-□ (ProvT-⟶ (forgeEv n) (λ _ → inj₁) (λ _ → ProvT-Ret))
                (ProvT-□ (ProvT-⟶ (putEv n) (λ _ → inj₁) (λ _ → ProvT-Ret))
                  (ProvT-□ (ohP hs hs a) (oiP hs (reverse hs) 0 (All-revAcc [] hs [] a)))))
              (λ _ → ProvT-Ret)

  -- knowledge only grows
  grow : ∀ {K : Maybe Bool → Set} {ls hs} → All K hs → All (λ y → K y ⊎ Kn ChS ls y) hs
  grow = All.map inj₁

  -- every completed round leaves a known store
  rJ : ∀ {hs K} → All K hs
     → Post (λ ls x → JAt (λ h K′ → All K′ h) x (λ y → K y ⊎ Kn ChS ls y))
            (loopStep {R = ⊤ {0ℓ}} (storeStepL n) hs)
  rJ {hs} {K} a =
    Post->>= {Q₁ = λ ls h′ → All (λ y → K y ⊎ Kn ChS ls y) h′}
      (Post-□ (Post-⟶ (forgeEv n) (λ mb → Post-Ret (forged mb)))
        (Post-□ (Post-⟶ (putEv n) (λ b → Post-Ret (put b)))
          (Post-□ (ohJ hs) (oiJ (reverse hs) 0))))
      (λ {ls₁} {r} q → Post-Ret (subst (λ ls → All (λ y → K y ⊎ Kn ChS ls y) r) (sym (++-identityʳ ls₁)) q))
    where
      -- a forge: the forged block is known from its own label
      forged : ∀ mb → All (λ y → K y ⊎ Kn ChS (evLabel _ (forgeEv n) mb ∷ []) y) (acceptForgeL mb hs)
      forged mb with forge-cases n mb hs
      ... | inj₁ eq rewrite eq = grow {ls = evLabel _ (forgeEv n) mb ∷ []} a
      ... | inj₂ eq rewrite eq = inj₂ (inj₁ refl) ∷ grow {ls = evLabel _ (forgeEv n) mb ∷ []} a
      -- a deposit: the deposited block is known from its own label
      put : ∀ b → All (λ y → K y ⊎ Kn ChS (evLabel _ (putEv n) b ∷ []) y)
                      (if memberOf ⦃ decBlock ⦄ b hs then hs else b ∷ hs)
      put b with memberOf ⦃ decBlock ⦄ b hs
      ... | true  = grow {ls = evLabel _ (putEv n) b ∷ []} a
      ... | false = inj₂ (inj₁ refl) ∷ grow {ls = evLabel _ (putEv n) b ∷ []} a
      -- the hand-over menu keeps the store
      ohJ : ∀ bs → Post (λ ls h′ → All (λ y → K y ⊎ Kn ChS ls y) h′) (offerHeld n hs bs)
      ohJ []       = Post-Stop
      ohJ (b ∷ bs) = Post-□ (Post-Output (getEv n) b (Post-Ret (grow {ls = evLabel _ (getEv n) b ∷ []} a))) (ohJ bs)
      -- the read-pointer menu keeps the store
      oiJ : ∀ (xs : Held) k₀ → Post (λ ls h′ → All (λ y → K y ⊎ Kn ChS ls y) h′) (offerIx (getAtEv n) xs k₀ hs)
      oiJ []       k₀ = Post-Stop
      oiJ (x ∷ xs) k₀ = Post-□ (Post-Output (getAtEv n k₀) x (Post-Ret (grow {ls = evLabel _ (getAtEv n k₀) x ∷ []} a))) (oiJ xs (suc k₀))

  -- THE STORE HOP: every block the store hands out was put or forged into it before
  blockStore-prov : ∀ {K s W} → blockStoreL n [] ⟹⟨ s ⟩ W → Prov ChS ChS InSt K (labels s)
  blockStore-prov tr = provInv (loopStep {R = ⊤ {0ℓ}} (storeStepL n)) (λ h K′ → All K′ h) rP rJ [] tr

------------------------------------------------------------------------
-- the store bound FROM PROVENANCE: deposits inside X cost nothing
------------------------------------------------------------------------

-- the sum of two weights
Σc-+ : ∀ (c d : Event → ℕ) ls → Σc (λ e → c e + d e) ls ≡ Σc c ls + Σc d ls
Σc-+ c d []       = refl
Σc-+ c d (e ∷ ls) rewrite Σc-+ c d ls =
  trans (+-assoc (c e) (d e) _) (trans (cong (c e +_) (sym (+-assoc (d e) (Σc c ls) (Σc d ls))))
    (trans (cong (λ z → c e + (z + Σc d ls)) (+-comm (d e) (Σc c ls)))
      (trans (cong (c e +_) (+-assoc (Σc c ls) (d e) (Σc d ls))) (sym (+-assoc (c e) (Σc c ls) _)))))

-- a weight that vanishes on every label sums to zero
Σc-0 : ∀ (c : Event → ℕ) {ls} → AllL (λ e → c e ≡ 0) ls → Σc c ls ≡ 0
Σc-0 c []        = refl
Σc-0 c (z ∷ a) rewrite z | Σc-0 c a = refl

-- the rely: every block the label carries lies in X
InX : List (Maybe Bool) → Event → Set
InX X e = ∀ {y} → ChS e y → memberOf ⦃ decBlock ⦄ y X ≡ true

module _ (n : Node) (X : List (Maybe Bool)) where

  -- the label's own deposit lies in X, so it costs nothing
  OkB : Event → Set
  OkB e = InX X e → cB X e ≡ 0

  -- a held-or-indexed hand-over costs nothing
  ohB : ∀ (hs bs : Held) → AllT OkB (offerHeld n hs bs)
  ohB hs []       = AllT-Stop
  ohB hs (b ∷ bs) = AllT-□ (AllT-Output _ _ (λ _ → refl) AllT-Ret) (ohB hs bs)

  -- … the read-pointer menu too
  oiB : ∀ (hs xs : Held) k₀ → AllT OkB (offerIx (getAtEv n) xs k₀ hs)
  oiB hs []       k₀ = AllT-Stop
  oiB hs (x ∷ xs) k₀ = AllT-□ (AllT-Output _ _ (λ _ → refl) AllT-Ret) (oiB hs xs (suc k₀))

  -- one round: a deposit in X is free
  rB : ∀ {hs : Held} {m : ℕ} → ⊤ {0ℓ} → AllT (λ e → OkB e) (loopStep {R = ⊤ {0ℓ}} (storeStepL n) hs)
  rB {hs} _ =
    AllT->>= (AllT-□ (AllT-⟶ (forgeEv n) (λ _ _ → refl) (λ _ → AllT-Ret))
               (AllT-□ (AllT-⟶ (putEv n) (λ b h → cong (λ z → if z then 0 else 1) (h refl)) (λ _ → AllT-Ret))
                 (AllT-□ (ohB hs hs) (oiB hs (reverse hs) 0))))
             (λ _ → AllT-Ret)

  -- THE STORE BOUND FROM PROVENANCE: if every block on the store's trace lies in X, every
  -- read index stays below |X| + the forges here
  blockStore-reads-prov : ∀ {s W} → blockStoreL n [] ⟹⟨ s ⟩ W → AllL (InX X) (labels s)
                        → AllL (ROkX X (Σc cF (labels s))) (labels s)
  blockStore-reads-prov {s} tr rely =
    subst (λ m → AllL (ROkX X m) (labels s)) eq (blockStore-readsX n X tr)
    where
      -- every label of the trace is free
      free : AllL (λ e → cB X e ≡ 0) (labels s)
      free = zipB (invLoop (λ _ _ → ⊤ {0ℓ}) (λ _ → 0) (λ _ → OkB) (λ _ ok → ok) (λ {a} {m} t → rB {a} {m} t)
                      (λ {a} _ → Post->>= {Q₁ = λ _ _ → ⊤ {0ℓ}} {P = storeStepL n a}
                                     (post λ _ → tt) (λ _ → Post-Ret tt)) {m = 0} tt tr) rely
        where
          -- pair the per-label fact with the rely
          zipB : ∀ {ms} → AllL OkB ms → AllL (InX X) ms → AllL (λ e → cB X e ≡ 0) ms
          zipB []       []       = []
          zipB (o ∷ os) (r ∷ rs) = o r ∷ zipB os rs
      -- so the budget is the forges alone
      eq : Σc (cFB X) (labels s) ≡ Σc cF (labels s)
      eq = trans (Σc-+ cF (cB X) (labels s))
             (trans (cong (Σc cF (labels s) +_) (Σc-0 (cB X) free)) (+-identityʳ _))

------------------------------------------------------------------------
-- the five stores together: alphabet, chain-freedom, provenance
------------------------------------------------------------------------

-- every label of an RB-store round is in the store alphabet
rb-alph : ∀ n held → AllT (InA storeES) (storeStepL n held)
rb-alph n held =
  AllT-□ (AllT-⟶ (forgeEv n) (λ _ → _) (λ _ → AllT-Ret))
    (AllT-□ (AllT-⟶ (putEv n) (λ _ → _) (λ _ → AllT-Ret))
      (AllT-□ (ohA held) (oiAll (getAtEv n) (reverse held) 0 held (λ _ _ _ → _))))
  where
    -- the hand-over menu
    ohA : ∀ bs → AllT (InA storeES) (offerHeld n held bs)
    ohA []       = AllT-Stop
    ohA (b ∷ bs) = AllT-□ (AllT-Output (getEv n) b _ AllT-Ret) (ohA bs)

-- every label of every RB-store trace is in the store alphabet
blockStoreL-alph : ∀ n held {s W} → blockStoreL n held ⟹⟨ s ⟩ W → AllL (InA storeES) (labels s)
blockStoreL-alph n = loopAll (rb-alph n)

-- … of the EB-entry store
ebStore-alph : ∀ n es {s W} → ebStore n es ⟹⟨ s ⟩ W → AllL (InA storeES) (labels s)
ebStore-alph n = loopAll (λ es → eb-All n es (λ _ → _) (λ _ _ → _))

-- … of the EB-body store
bodyStore-alph : ∀ n bs {s W} → bodyStore n bs ⟹⟨ s ⟩ W → AllL (InA storeES) (labels s)
bodyStore-alph n = loopAll (λ bs → body-All n bs (λ _ → _) (λ _ _ → _))

-- … of the mempool
mempool-alph : ∀ n ts {s W} → mempool n ts ⟹⟨ s ⟩ W → AllL (InA storeES) (labels s)
mempool-alph n = loopAll (λ ts → mem-All n ts (λ _ → _) (λ _ → _) (λ _ _ _ → _) (λ _ _ → _))

-- … of the vote store
voteStore-alph : ∀ n vs {s W} → voteStore n vs ⟹⟨ s ⟩ W → AllL (InA storeES) (labels s)
voteStore-alph n = loopAll {body = voteStep n} (λ v → vote-All n (proj₁ v) (proj₂ v) (λ _ → _) (λ _ → _) (λ _ _ _ → _) (λ _ _ → _))

-- the label carries no block on any chain kind
NoCh : Event → Set
NoCh e = ∀ {x} → ChS e x → ⊥

-- the EB-entry store touches no chain label
ebStore-noCh : ∀ n es {s W} → ebStore n es ⟹⟨ s ⟩ W → AllL NoCh (labels s)
ebStore-noCh n = loopAll (λ es → eb-All n es (λ _ ()) (λ _ _ ()))

-- … nor the EB-body store
bodyStore-noCh : ∀ n bs {s W} → bodyStore n bs ⟹⟨ s ⟩ W → AllL NoCh (labels s)
bodyStore-noCh n = loopAll (λ bs → body-All n bs (λ _ ()) (λ _ _ ()))

-- … nor the mempool
mempool-noCh : ∀ n ts {s W} → mempool n ts ⟹⟨ s ⟩ W → AllL NoCh (labels s)
mempool-noCh n = loopAll (λ ts → mem-All n ts (λ _ ()) (λ _ ()) (λ _ _ _ ()) (λ _ _ ()))

-- … nor the vote store
voteStore-noCh : ∀ n vs {s W} → voteStore n vs ⟹⟨ s ⟩ W → AllL NoCh (labels s)
voteStore-noCh n = loopAll {body = voteStep n} (λ v → vote-All n (proj₁ v) (proj₂ v) (λ _ ()) (λ _ ()) (λ _ _ _ ()) (λ _ _ ()))

-- a chain-free process guarantees provenance under the store rely
noCh→PA : ∀ {R : Set} {P : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R} → AllT NoCh P → PA ChS ChS InSt P
noCh→PA a = AllT→PA (AllT-mono (λ f {_} ox → ⊥-elim (f ox)) a)

-- the EB-entry store's provenance (chain-free)
ebStore-PA : ∀ n es → PA ChS ChS InSt (ebStore n es)
ebStore-PA n es = noCh→PA (ebStore-noCh n es)

-- … the EB-body store's
bodyStore-PA : ∀ n bs → PA ChS ChS InSt (bodyStore n bs)
bodyStore-PA n bs = noCh→PA (bodyStore-noCh n bs)

-- … the mempool's
mempool-PA : ∀ n ts → PA ChS ChS InSt (mempool n ts)
mempool-PA n ts = noCh→PA (mempool-noCh n ts)

-- … the vote store's
voteStore-PA : ∀ n vs → PA ChS ChS InSt (voteStore n vs)
voteStore-PA n vs = noCh→PA (voteStore-noCh n vs)

-- THE STORES' PROVENANCE: the RB store's hop, interleaved with the four chain-free stores
storesL-PA : ∀ n → PA ChS ChS InSt (blockStoreL n [] ⦀ (ebStore n [] ⦀ (bodyStore n [] ⦀ (mempool n [] ⦀ voteStore n ([] , [])))))
storesL-PA n =
  PA-par≡ (pa (blockStore-prov n))
    (PA-par≡ (ebStore-PA n []) (PA-par≡ (bodyStore-PA n []) (PA-par≡ (mempool-PA n []) (voteStore-PA n ([] , [])))))
