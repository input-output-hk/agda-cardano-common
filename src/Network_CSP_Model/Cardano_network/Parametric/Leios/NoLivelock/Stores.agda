{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C, premise (a): the STORE summaries.  The RB
-- store holds at most 3 distinct blocks (`Block = Maybe Bool`, put-dedup)
-- plus one duplicate per forge, so every block read it serves names an
-- index below 3 + (forges so far) (`blockStore-reads`) — the D1-a
-- alternative (finite-`Block`) route, kept for reference; `Bound2` uses
-- the D1-b provenance route (`StoresProv.blockStore-reads-prov`) instead,
-- so `blockStore-reads` is unused here.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Cardano_network.Parametric.Topology using (Topology; module Topology)
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (pL; lpF; VB; AllV; HP)

module Cardano_network.Parametric.Leios.NoLivelock.Stores
  (k m : ℕ) (tP : Topology (pL k m)) (vo : Topology.Node tP → Fin m) (U : List (VB m)) (allV : AllV m U) where

-- the family member this module is about
pP = pL k m
-- its Leios parameters
lpP = lpF k m
open Topology tP using (Node)


open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.List using (List; []; _∷_; reverse; length)
open import Data.List.Properties using (length-reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; m≤m+n; +-mono-≤; +-identityʳ; +-suc; +-comm)
open import Data.Product using (_,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (0ℓ)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (PTree; ExtI)
open import Data.Fin using (Fin)
open import Data.List.Properties using (++-identityʳ)
open import Cardano_network.Base
open import Cardano_network.Parametric.Leios.NoLivelock.Threads k m tP vo using (IsGetAt)
open import Cardano_network.Net pP
open import Cardano_network.Data pP using (Payload)
open import Cardano_network.ApiAlphabet pP using (apiES)
open import Cardano_network.Params using (module Params)
open Params pP using (decBlock)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (_□_)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (Event; evLabel)
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
open import CSP.Laws.DivFree.Loop (Net_Api-≟ {Payload}) using (loopStep)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload})
import Cardano_network.Parametric.NodeLogic as NL
open NL.Generic pP tP apiES using (offerHeld; Held)
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open NLL.Generic pP lpP tP apiES vo
  using (storeStepL; blockStoreL; offerIx; getAtEv; memberOf; acceptForgeL)

-- (Task 8, the other stores)
open import Data.Bool using (_∧_; not)
open import Data.Bool.Properties using (∨-identityʳ; ∨-zeroʳ; ∨-assoc)
open import Data.Empty using (⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (_++_; map)
open import Data.List.Properties using (length-++; map-++)
open import Data.Nat using (_∸_)
open import Data.Nat.Properties using (≤-reflexive; +-∸-assoc; +-monoʳ-≤)
open import Data.Product using (proj₁)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (subst₂)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (Prefix; Output; Ret; _>>=_)
open import CSP.Laws.DivFree.CountMore (Net_Api-≟ {Payload}) using (Σc-0; potIter; Back; AllT-if)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono (Net_Api-≟ {Payload}) using (□-trace-elim)
open import CSP.Laws.Traces.TraceLawsBind (Net_Api-≟ {Payload}) using (bind-elim-aux; bs-live; bs-term)
open import Cardano_network.Parametric.Leios.NoLivelock.Threads k m tP vo
  using (IsGetTxAt; IsGetVoteAt; cCert; Tr; Σc-≤)
open Params pP using (Tx; VoteBlob; txHash; decTx; decTxHash; decVoteBlob; decRbHash; decEB)
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
open LeiosP.LeiosParams lpP using (certifies; blobRb)
open LeiosP pP using (DecEq-LeiosPoint)
open NLL.Generic pP lpP tP apiES vo
  using ( Votes; memStep; mempool; voteStep; voteStore; ebStep; ebStore; bodyStep; bodyStore
        ; insertU; certify; offerCerts; offerTxs; offerBodies; getTxAtEv; getVoteAtEv; putTxEv
        ; putVoteEv; certEv; hasCertEv; getTxEv; submitEv; putEBEv; getEBAtEv; putBodyEv; getBodyEv
        ; DecEq-Votes )

------------------------------------------------------------------------
-- the RB store: at most 3 distinct blocks, plus one duplicate per forge
------------------------------------------------------------------------

-- 1 if the block is held, else 0
mem : Maybe Bool → Held → ℕ
mem x hs = if memberOf ⦃ decBlock ⦄ x hs then 1 else 0

-- the number of DISTINCT blocks held (`Block = Maybe Bool` has three values)
D3 : Held → ℕ
D3 hs = mem nothing hs + (mem (just true) hs + mem (just false) hs)

-- each indicator is at most one
mem≤1 : ∀ x hs → mem x hs ≤ 1
mem≤1 x hs with memberOf ⦃ decBlock ⦄ x hs
... | true  = s≤s z≤n
... | false = z≤n

-- so at most three distinct blocks
D3≤3 : ∀ hs → D3 hs ≤ 3
D3≤3 hs = +-mono-≤ (mem≤1 nothing hs) (+-mono-≤ (mem≤1 (just true) hs) (mem≤1 (just false) hs))

-- an indicator never drops when a block is prepended
mem-cons : ∀ x b hs → mem x hs ≤ mem x (b ∷ hs)
mem-cons x b hs with DecEq._≟_ decBlock b x
... | yes _ = mem≤1 x hs
... | no  _ = ≤-refl

-- so the distinct count never drops either
D3-cons : ∀ b hs → D3 hs ≤ D3 (b ∷ hs)
D3-cons b hs = +-mono-≤ (mem-cons nothing b hs) (+-mono-≤ (mem-cons (just true) b hs) (mem-cons (just false) b hs))

-- prepending a block not yet held raises the distinct count by one
D3-fresh : ∀ b hs → memberOf ⦃ decBlock ⦄ b hs ≡ false → D3 (b ∷ hs) ≡ suc (D3 hs)
D3-fresh nothing      hs eq rewrite eq = refl
D3-fresh (just true)  hs eq rewrite eq = +-suc (mem nothing hs) _
D3-fresh (just false) hs eq rewrite eq =
  trans (cong (mem nothing hs +_) (+-suc (mem (just true) hs) 0′)) (+-suc (mem nothing hs) _)
  where 0′ = 0

-- the store invariant: length ≤ distinct + forges so far
SInv : Held → ℕ → Set
SInv hs m = length hs ≤ D3 hs + m

-- forge events weigh one
cF : Event → ℕ
cF (evLabel _ (env _ _ envForge) _) = 1
cF _                                = 0

-- a read stays below 3 + forges
ROk : ℕ → Event → Set
ROk m e = ∀ j → IsGetAt j e → j < 3 + m

-- … monotonically in the budget
ROk-mono : ∀ {m m′ e} → m ≤ m′ → ROk m e → ROk m′ e
ROk-mono m≤ ok j r = ≤-trans (ok j r) (+-mono-≤ (≤-refl {3}) m≤)

-- a weaker per-label predicate
AllT-mono : ∀ {R : Set} {P Q : Event → Set} {t : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R} → (∀ {e} → P e → Q e) → AllT P t → AllT Q t
AllT-mono f a tr = AllL-map f (a tr)

module _ (n : Node) where

  -- the "hand over any held block" menu reads no index
  oh-ok : ∀ {m} hs bs → AllT (ROk m) (offerHeld n hs bs)
  oh-ok hs []       = AllT-Stop
  oh-ok hs (b ∷ bs) = AllT-□ (AllT-Output _ _ (λ j ()) AllT-Ret) (oh-ok hs bs)

  -- the read-pointer menu from k₀ reads only indices below k₀ + |xs|
  oi-reads : (hs : Held) (xs : Held) (k₀ : ℕ)
           → AllT (λ e → ∀ j → IsGetAt j e → j < k₀ + length xs) (offerIx (getAtEv n) xs k₀ hs)
  oi-reads hs []       k₀ = AllT-Stop
  oi-reads hs (x ∷ xs) k₀ =
    AllT-□ (AllT-Output _ _ (λ { j refl → subst (k₀ <_) (sym (+-suc k₀ (length xs))) (s≤s (m≤m+n k₀ (length xs))) }) AllT-Ret)
           (AllT-mono (λ f j r → subst (j <_) (sym (+-suc k₀ (length xs))) (f j r)) (oi-reads hs xs (suc k₀)))

  -- every read of a round is below 3 + forges so far
  rOk : ∀ {hs m} → SInv hs m → AllT (ROk m) (loopStep {R = ⊤ {0ℓ}} (storeStepL n) hs)
  rOk {hs} {m} i =
    AllT->>= (AllT-□ (AllT-⟶ _ (λ _ j ()) (λ _ → AllT-Ret))
               (AllT-□ (AllT-⟶ _ (λ _ j ()) (λ _ → AllT-Ret))
                 (AllT-□ (oh-ok hs hs)
                   (AllT-mono (λ f j r → ≤-trans (f j r)
                                 (≤-trans (subst (_≤ D3 hs + m) (sym (length-reverse hs)) i)
                                          (+-mono-≤ (D3≤3 hs) ≤-refl)))
                              (oi-reads hs (reverse hs) 0)))))
             (λ _ → AllT-Ret)

  -- a non-forge round keeps the invariant at the same budget
  keep : ∀ {hs m} → SInv hs m → SInv hs (m + 0)
  keep {hs} {m} i = subst (λ z → length hs ≤ D3 hs + z) (sym (+-identityʳ m)) i

  -- the hand-over menus return the state untouched
  oh-post : ∀ {m} hs bs → SInv hs m → Post (λ ls h′ → SInv h′ (m + Σc cF ls)) (offerHeld n hs bs)
  oh-post hs []       i = Post-Stop
  oh-post {m} hs (b ∷ bs) i = Post-□ (Post-Output _ _ (Post-Ret (keep {hs} {m} i))) (oh-post hs bs i)

  -- … the read-pointer menu too
  oi-post : ∀ {m} hs xs k₀ → SInv hs m
          → Post (λ ls h′ → SInv h′ (m + Σc cF ls)) (offerIx (getAtEv n) xs k₀ hs)
  oi-post hs []       k₀ i = Post-Stop
  oi-post {m} hs (x ∷ xs) k₀ i = Post-□ (Post-Output _ _ (Post-Ret (keep {hs} {m} i))) (oi-post hs xs (suc k₀) i)

  -- a forge leaves the store as it was or prepends the forged block
  forge-cases : ∀ mb hs → (acceptForgeL mb hs ≡ hs) ⊎ (acceptForgeL mb hs ≡ proj₂ mb ∷ hs)
  forge-cases (nothing     , nothing)      hs = inj₂ refl
  forge-cases (nothing     , just true)    hs = inj₁ refl
  forge-cases (nothing     , just false)   hs = inj₁ refl
  forge-cases (just true   , nothing)      hs = inj₁ refl
  forge-cases (just true   , just true)    hs = inj₂ refl
  forge-cases (just true   , just false)   hs = inj₁ refl
  forge-cases (just false  , nothing)      hs = inj₁ refl
  forge-cases (just false  , just true)    hs = inj₁ refl
  forge-cases (just false  , just false)   hs = inj₁ refl

  -- a forge round pays one unit of budget
  forge-inv : ∀ {hs m} mb → SInv hs m → SInv (acceptForgeL mb hs) (m + 1)
  forge-inv {hs} {m} mb i with forge-cases mb hs
  ... | inj₁ eq rewrite eq = ≤-trans i (+-mono-≤ (≤-refl {D3 hs}) (m≤m+n m 1))
  ... | inj₂ eq rewrite eq =
        subst (λ z → suc (length hs) ≤ D3 (proj₂ mb ∷ hs) + z) (+-comm 1 m)
          (subst (suc (length hs) ≤_) (sym (+-suc (D3 (proj₂ mb ∷ hs)) m))
             (s≤s (≤-trans i (+-mono-≤ (D3-cons (proj₂ mb) hs) ≤-refl))))

  -- a deposit keeps the invariant (dedup: a fresh block raises the distinct count too)
  put-inv : ∀ {hs m} b → SInv hs m → SInv (if memberOf ⦃ decBlock ⦄ b hs then hs else b ∷ hs) (m + 0)
  put-inv {hs} {m} b i with memberOf ⦃ decBlock ⦄ b hs in eq
  ... | true  = keep {hs} {m} i
  ... | false =
        subst (λ z → suc (length hs) ≤ z) (sym (cong (_+ (m + 0)) (D3-fresh b hs eq)))
          (s≤s (keep {hs} {m} i))

  -- every completed round re-establishes the invariant at the grown budget
  rInv : ∀ {hs m} → SInv hs m → Post (λ ls x → InvAt SInv x (m + Σc cF ls)) (loopStep {R = ⊤ {0ℓ}} (storeStepL n) hs)
  rInv {hs} {m} i =
    Post->>= {Q₁ = λ ls h′ → SInv h′ (m + Σc cF ls)}
      (Post-□ (Post-⟶ _ (λ mb → Post-Ret (forge-inv {hs} {m} mb i)))
        (Post-□ (Post-⟶ _ (λ b → Post-Ret (put-inv {hs} {m} b i)))
          (Post-□ (oh-post hs hs i) (oi-post hs (reverse hs) 0 i))))
      (λ {ls₁} {r} q → Post-Ret (subst (λ ls → SInv r (m + Σc cF ls)) (sym (++-identityʳ ls₁)) q))

  -- THE STORE-SIZE LEMMA: from the empty store, every read index stays below 3 + forges
  blockStore-reads : ∀ {s W} → blockStoreL n [] ⟹⟨ s ⟩ W → AllL (ROk (Σc cF (labels s))) (labels s)
  blockStore-reads tr = invLoop SInv cF ROk ROk-mono rOk rInv {m = 0} z≤n tr

------------------------------------------------------------------------
-- generic menu and weight lemmas (the read-pointer menu, conditionals,
-- the weight of every trace of a round)
------------------------------------------------------------------------

-- every label of a read-pointer menu from k₀ is a read below k₀ + |xs|
oiAll : ∀ {A S : Set} {dA : DecEq A} {dS : DecEq S} {P : Event → Set} (e : ℕ → Net_Api Payload A)
        (xs : List A) (k₀ : ℕ) (s : S)
      → (∀ k x → k < k₀ + length xs → P (evLabel A (e k) x)) → AllT P (offerIx ⦃ dA ⦄ ⦃ dS ⦄ e xs k₀ s)
oiAll e []       k₀ s p = AllT-Stop
oiAll {dA = dA} {dS} e (x ∷ xs) k₀ s p =
  AllT-□ ⦃ dS ⦄
    (AllT-Output ⦃ dA ⦄ (e k₀) x (p k₀ x (subst (k₀ <_) (sym (+-suc k₀ (length xs))) (s≤s (m≤m+n k₀ (length xs))))) AllT-Ret)
    (oiAll e xs (suc k₀) s (λ k y lt → p k y (subst (k <_) (sym (+-suc k₀ (length xs))) lt)))

-- a read-pointer menu returns its state after one label
oiPost : ∀ {A S : Set} {dA : DecEq A} {dS : DecEq S} {Q : List Event → S → Set} (e : ℕ → Net_Api Payload A)
         (xs : List A) (k₀ : ℕ) (s : S)
       → (∀ k x → Q (evLabel A (e k) x ∷ []) s) → Post Q (offerIx ⦃ dA ⦄ ⦃ dS ⦄ e xs k₀ s)
oiPost e []       k₀ s q = Post-Stop
oiPost {dA = dA} {dS} e (x ∷ xs) k₀ s q =
  Post-□ ⦃ dS ⦄ (Post-Output ⦃ dA ⦄ (e k₀) x (Post-Ret (q k₀ x))) (oiPost e xs (suc k₀) s q)

-- a conditional whose true branch may use its condition
Post-ifT : ∀ {R : Set} {Q : List Event → R → Set} {P P′ : Tr R} b → (b ≡ true → Post Q P) → Post Q P′
         → Post Q (if b then P else P′)
Post-ifT true  p q = p refl
Post-ifT false p q = q

-- a condition `x ∧ not y` that holds refutes `y`
∧-not : ∀ x y → x ∧ not y ≡ true → y ≡ false
∧-not true  false _ = refl
∧-not true  true  ()
∧-not false _     ()

-- every trace of `t` weighs at most `k` under `c`
Wt : ∀ {R : Set} → (Event → ℕ) → ℕ → Tr R → Set₁
Wt c k t = ∀ {s W} → t ⟹⟨ s ⟩ W → Σc c (labels s) ≤ k

-- a larger bound
Wt-mono : ∀ {R : Set} {c k k′} {t : Tr R} → k ≤ k′ → Wt c k t → Wt c k′ t
Wt-mono le w tr = ≤-trans (w tr) le

-- a return weighs nothing
Wt-Ret : ∀ {R : Set} {c k} {x : R} → Wt c k (Ret x)
Wt-Ret tr with Ret-tr tr
... | inj₁ refl = z≤n
... | inj₂ refl = z≤n

-- a traversal of weightless labels weighs nothing
Wt-AllT : ∀ {R : Set} {c k} {t : Tr R} → AllT (λ e → c e ≤ 0) t → Wt c k t
Wt-AllT {c = c} a {s} tr = ≤-trans (Σc-≤ {c = c} {d = λ _ → 0} (a tr)) (subst (_≤ _) (sym (Σc-0 (labels s))) z≤n)

-- a choice weighs no more than its heavier branch
Wt-□ : ∀ {R : Set} ⦃ _ : DecEq R ⦄ {c k} {P Q : Tr R} → Wt c k P → Wt c k Q → Wt c k (P □ Q)
Wt-□ {P = P} {Q} wp wq tr with □-trace-elim P Q tr
... | inj₁ (_ , t₁) = wp t₁
... | inj₂ (_ , t₂) = wq t₂

-- a weightless prefix
Wt-⟶ : ∀ {R A : Set} {c k} (e : Net_Api Payload A) {P : A → Tr R}
     → (∀ x → c (evLabel A e x) ≡ 0) → (∀ x → Wt c k (P x)) → Wt c k (e ⟶ P)
Wt-⟶ {c = c} e z w tr with pfx-tr tr
... | inj₁ refl                   = z≤n
... | inj₂ (x , s′ , refl , rest) = subst (_≤ _) (sym (cong (_+ Σc c (labels s′)) (z x))) (w x rest)

-- an output adds its own weight
Wt-Output : ∀ {R A : Set} {c k} ⦃ _ : DecEq A ⦄ (e : Net_Api Payload A) (v : A) {P : Tr R}
          → Wt c k P → Wt c (c (evLabel A e v) + k) (e ! v ⟶ P)
Wt-Output e v w tr with out-tr tr
... | inj₁ refl               = z≤n
... | inj₂ (s′ , refl , rest) = +-monoʳ-≤ _ (w rest)

-- a bind adds the weights of its halves
Wt->>= : ∀ {R S : Set} {c m n} {P : Tr R} {k : R → Tr S} → Wt c m P → (∀ r → Wt c n (k r)) → Wt c (m + n) (P >>= k)
Wt->>= {c = c} {m} {n} {P} {k} wp wk tr with bind-elim-aux P k tr
... | bs-live d eo = ≤-trans (subst (λ ls → Σc c ls ≤ m) (labels-EvlOnly eo) (wp d)) (m≤m+n m n)
... | bs-term {sS = sS} {s_k = s_k} d fr eo (_ , kt) refl =
      subst (_≤ m + n) (sym (trans (cong (Σc c) (labels-++ sS s_k)) (Σc-++ c (labels sS) (labels s_k))))
        (+-mono-≤ (subst (λ ls → Σc c ls ≤ m) (labels-EvlOnly eo) (wp d)) (wk _ kt))

-- a conditional whose true branch may use its condition
Wt-ifT : ∀ {R : Set} {c k} {P P′ : Tr R} b → (b ≡ true → Wt c k P) → Wt c k P′ → Wt c k (if b then P else P′)
Wt-ifT true  p q = p refl
Wt-ifT false p q = q

------------------------------------------------------------------------
-- a distinct-count over an explicit enumeration U (the APPEND-dedup
-- stores: `insertU`, `insertTx`)
------------------------------------------------------------------------

-- 1 if `x` is in `xs`, under the decision `d`
memD : ∀ {A : Set} → DecEq A → A → List A → ℕ
memD d x xs = if memberOf ⦃ d ⦄ x xs then 1 else 0

-- how many of the values `U` are in `xs`
cntD : ∀ {A : Set} → DecEq A → List A → List A → ℕ
cntD d []      xs = 0
cntD d (u ∷ U) xs = memD d u xs + cntD d U xs

-- an indicator is at most one
ind≤1 : ∀ b → (if b then 1 else 0) ≤ 1
ind≤1 true  = s≤s z≤n
ind≤1 false = z≤n

-- so the count is at most |U|
cntD≤ : ∀ {A : Set} (d : DecEq A) U xs → cntD d U xs ≤ length U
cntD≤ d []      xs = z≤n
cntD≤ d (u ∷ U) xs = +-mono-≤ (ind≤1 (memberOf ⦃ d ⦄ u xs)) (cntD≤ d U xs)

-- membership after appending one value
mem-snoc : ∀ {A : Set} (d : DecEq A) u y xs
         → memberOf ⦃ d ⦄ u (xs ++ y ∷ []) ≡ memberOf ⦃ d ⦄ u xs ∨ ⌊ DecEq._≟_ d y u ⌋
mem-snoc d u y []       = ∨-identityʳ _
mem-snoc d u y (x ∷ xs) =
  trans (cong (⌊ DecEq._≟_ d x u ⌋ ∨_) (mem-snoc d u y xs)) (sym (∨-assoc ⌊ DecEq._≟_ d x u ⌋ _ _))

-- an indicator never drops when its condition is widened
ind-∨ : ∀ a b → (if a then 1 else 0) ≤ (if a ∨ b then 1 else 0)
ind-∨ true  b = s≤s z≤n
ind-∨ false b = z≤n

-- an indicator never drops when a value is appended
memD-snoc : ∀ {A : Set} (d : DecEq A) u y xs → memD d u xs ≤ memD d u (xs ++ y ∷ [])
memD-snoc d u y xs = subst (λ z → memD d u xs ≤ (if z then 1 else 0)) (sym (mem-snoc d u y xs)) (ind-∨ _ _)

-- nor does the count
cntD-snoc : ∀ {A : Set} (d : DecEq A) U xs y → cntD d U xs ≤ cntD d U (xs ++ y ∷ [])
cntD-snoc d []      xs y = z≤n
cntD-snoc d (u ∷ U) xs y = +-mono-≤ (memD-snoc d u y xs) (cntD-snoc d U xs y)

-- a decision of `y ≡ y` says yes
dtD : ∀ {A : Set} {y : A} (q : Dec (y ≡ y)) → ⌊ q ⌋ ≡ true
dtD (yes _) = refl
dtD (no ¬p) = ⊥-elim (¬p refl)

-- an appended value is held
memD-hit : ∀ {A : Set} (d : DecEq A) y xs → memD d y (xs ++ y ∷ []) ≡ 1
memD-hit d y xs = cong (λ z → if z then 1 else 0)
  (trans (mem-snoc d y y xs) (trans (cong (memberOf ⦃ d ⦄ y xs ∨_) (dtD (DecEq._≟_ d y y))) (∨-zeroʳ _)))

-- appending a value of U not yet held raises the count (THE DEDUP STEP)
cntD-fresh : ∀ {A : Set} (d : DecEq A) U xs y → memberOf ⦃ d ⦄ y U ≡ true → memberOf ⦃ d ⦄ y xs ≡ false
           → suc (cntD d U xs) ≤ cntD d U (xs ++ y ∷ [])
cntD-fresh d (u ∷ U) xs y inU fresh with DecEq._≟_ d u y
... | yes refl = subst (λ z → suc (memD d u xs + cntD d U xs) ≤ z + cntD d U (xs ++ u ∷ [])) (sym (memD-hit d u xs))
                   (subst (λ z → suc (z + cntD d U xs) ≤ suc (cntD d U (xs ++ u ∷ [])))
                          (sym (cong (λ z → if z then 1 else 0) fresh))
                     (s≤s (cntD-snoc d U xs u)))
... | no _ = subst (_≤ memD d u (xs ++ y ∷ []) + cntD d U (xs ++ y ∷ [])) (+-suc (memD d u xs) (cntD d U xs))
               (+-mono-≤ (memD-snoc d u y xs) (cntD-fresh d U xs y inU fresh))

-- an append grows the length by one
length-snoc : ∀ {A : Set} (xs : List A) y → length (xs ++ y ∷ []) ≡ suc (length xs)
length-snoc xs y = trans (length-++ xs) (+-comm (length xs) 1)

------------------------------------------------------------------------
-- the mempool: at most one transaction per hash, `TxHash = Bool`
------------------------------------------------------------------------

-- the two transaction hashes
UB : List Bool
UB = true ∷ false ∷ []

-- every hash is one of them
allB : ∀ h → memberOf ⦃ decTxHash ⦄ h UB ≡ true
allB true  = refl
allB false = refl

-- the mempool invariant: no more transactions than distinct hashes held
MInv : List Tx → Set
MInv ts = length ts ≤ cntD decTxHash UB (map txHash ts)

-- a deposit keeps it (key-dedup: a fresh hash raises the count too)
insTx-inv : ∀ t₀ ts → MInv ts
          → MInv (if memberOf ⦃ decTxHash ⦄ (txHash t₀) (map txHash ts) then ts else ts ++ t₀ ∷ [])
insTx-inv t₀ ts i with memberOf ⦃ decTxHash ⦄ (txHash t₀) (map txHash ts) in eq
... | true  = i
... | false = subst₂ _≤_ (sym (length-snoc ts t₀)) (cong (cntD decTxHash UB) (sym (map-++ txHash ts (t₀ ∷ []))))
                (≤-trans (s≤s i) (cntD-fresh decTxHash UB (map txHash ts) (txHash t₀) (allB (txHash t₀)) eq))

-- every label of a mempool round is one of its four channels, its reads below |ts|
mem-All : ∀ {P : Event → Set} n ts
        → (∀ t₀ → P (evLabel _ (putTxEv n) t₀)) → (∀ t₀ → P (evLabel _ (submitEv n) t₀))
        → (∀ k t₀ → k < length ts → P (evLabel _ (getTxAtEv n k) t₀)) → (∀ h t₀ → P (evLabel _ (getTxEv n h) t₀))
        → AllT P (memStep n ts)
mem-All {P} n ts pp ps pa pg =
  AllT-□ (AllT-⟶ (putTxEv n) pp (λ _ → AllT-Ret))
    (AllT-□ (AllT-⟶ (submitEv n) ps (λ _ → AllT-Ret)) (AllT-□ (oiAll (getTxAtEv n) ts 0 ts pa) (otA ts)))
  where
    -- the keyed menu
    otA : ∀ xs → AllT P (offerTxs n ts xs)
    otA []         = AllT-Stop
    otA (t₀ ∷ ts′′) = AllT-□ (AllT-Output ⦃ decTx ⦄ (getTxEv n (txHash t₀)) t₀ (pg _ t₀) AllT-Ret) (otA ts′′)

-- every mempool round re-establishes the invariant
mem-Post : ∀ n ts → MInv ts → Post (λ _ ts′ → MInv ts′) (memStep n ts)
mem-Post n ts i =
  Post-□ (Post-⟶ (putTxEv n) (λ t₀ → Post-Ret (insTx-inv t₀ ts i)))
    (Post-□ (Post-⟶ (submitEv n) (λ _ → Post-Ret i)) (Post-□ (oiPost (getTxAtEv n) ts 0 ts (λ _ _ → i)) (otP ts)))
  where
    -- the keyed menu
    otP : ∀ xs → Post (λ _ ts′ → MInv ts′) (offerTxs n ts xs)
    otP []         = Post-Stop
    otP (t₀ ∷ ts′′) = Post-□ (Post-Output ⦃ decTx ⦄ (getTxEv n (txHash t₀)) t₀ (Post-Ret i)) (otP ts′′)

-- THE MEMPOOL BOUND: from the empty mempool, every read index is below 2
mempool-reads : ∀ n {s W} → mempool n [] ⟹⟨ s ⟩ W → AllL (λ e → ∀ j → IsGetTxAt j e → j < 2) (labels s)
mempool-reads n tr =
  invLoop {body = memStep n} (λ ts _ → MInv ts) (λ _ → 0) (λ _ e → ∀ j → IsGetTxAt j e → j < 2) (λ _ ok → ok)
    (λ {ts} i → AllT->>= (mem-All n ts (λ _ j ()) (λ _ j ())
                            (λ k _ lt j eq → subst (_< 2) eq (≤-trans lt (≤-trans i (cntD≤ decTxHash UB (map txHash ts)))))
                            (λ _ _ j ()))
                          (λ _ → AllT-Ret))
    (λ {ts} i → Post->>= {Q₁ = λ _ ts′ → MInv ts′} (mem-Post n ts i) (λ q → Post-Ret q)) {a = []} {m = 0} z≤n tr

------------------------------------------------------------------------
-- the vote store: at most one copy of each blob of `U`, and one
-- certificate per RB hash (`RbHash = Maybe Bool`)
------------------------------------------------------------------------

-- the vote-store invariant: no more blobs than distinct blobs held
VInv : Votes → Set
VInv v = length (proj₁ v) ≤ cntD decVoteBlob U (proj₁ v)

-- a deposit keeps it (dedup: a fresh blob raises the count too)
insU-inv : ∀ v bs → length bs ≤ cntD decVoteBlob U bs
         → length (if memberOf ⦃ decVoteBlob ⦄ v bs then bs else bs ++ v ∷ [])
           ≤ cntD decVoteBlob U (if memberOf ⦃ decVoteBlob ⦄ v bs then bs else bs ++ v ∷ [])
insU-inv v bs i with memberOf ⦃ decVoteBlob ⦄ v bs in eq
... | true  = i
... | false = subst (_≤ cntD decVoteBlob U (bs ++ v ∷ [])) (sym (length-snoc bs v))
                (≤-trans (s≤s i) (cntD-fresh decVoteBlob U bs v (allV v) eq))

-- every label of a vote-store round is one of its four channels, its reads below |bs|
vote-All : ∀ {P : Event → Set} n bs cs
         → (∀ v → P (evLabel _ (putVoteEv n) v)) → (∀ r → P (evLabel _ (certEv n) r))
         → (∀ k v → k < length bs → P (evLabel _ (getVoteAtEv n k) v)) → (∀ r x → P (evLabel _ (hasCertEv n r) x))
         → AllT P (voteStep n (bs , cs))
vote-All {P} n bs cs pp pc pa ph =
  AllT-□ (AllT-⟶ (putVoteEv n) pp (λ v → cA (insertU ⦃ decVoteBlob ⦄ v bs) (blobRb v)))
    (AllT-□ (oiAll (getVoteAtEv n) bs 0 (bs , cs) pa) (ocA cs))
  where
    -- the certification step
    cA : ∀ bs′ r → AllT P (certify n bs′ cs r)
    cA bs′ r = AllT-if (certifies bs′ r ∧ not (memberOf ⦃ decRbHash ⦄ r cs))
                 (AllT-Output ⦃ decRbHash ⦄ (certEv n) r (pc r) AllT-Ret) AllT-Ret
    -- the certificate-query menu
    ocA : ∀ rs → AllT P (offerCerts n (bs , cs) rs)
    ocA []       = AllT-Stop
    ocA (r ∷ rs) = AllT-□ (AllT-⟶ (hasCertEv n r) (ph r) (λ _ → AllT-Ret)) (ocA rs)

-- each vote-store round returns the blobs it deposited, and a certificate only when fresh
vote-Post : ∀ {Q : List Event → Votes → Set} n bs cs
          → (∀ v → memberOf ⦃ decRbHash ⦄ (blobRb v) cs ≡ false
               → Q (evLabel _ (putVoteEv n) v ∷ evLabel _ (certEv n) (blobRb v) ∷ [])
                   (insertU ⦃ decVoteBlob ⦄ v bs , blobRb v ∷ cs))
          → (∀ v → Q (evLabel _ (putVoteEv n) v ∷ []) (insertU ⦃ decVoteBlob ⦄ v bs , cs))
          → (∀ k v → Q (evLabel _ (getVoteAtEv n k) v ∷ []) (bs , cs))
          → (∀ r x → Q (evLabel _ (hasCertEv n r) x ∷ []) (bs , cs))
          → Post Q (voteStep n (bs , cs))
vote-Post {Q} n bs cs qc qp qa qh =
  Post-□ (Post-⟶ (putVoteEv n) cP) (Post-□ (oiPost (getVoteAtEv n) bs 0 (bs , cs) qa) (ocP cs))
  where
    -- the certification step after a deposit
    cP : ∀ v → Post (λ ls r → Q (evLabel _ (putVoteEv n) v ∷ ls) r) (certify n (insertU ⦃ decVoteBlob ⦄ v bs) cs (blobRb v))
    cP v = Post-ifT (certifies (insertU ⦃ decVoteBlob ⦄ v bs) (blobRb v) ∧ not (memberOf ⦃ decRbHash ⦄ (blobRb v) cs))
             (λ eq → Post-Output ⦃ decRbHash ⦄ (certEv n) (blobRb v)
                       (Post-Ret (qc v (∧-not (certifies (insertU ⦃ decVoteBlob ⦄ v bs) (blobRb v))
                                              (memberOf ⦃ decRbHash ⦄ (blobRb v) cs) eq))))
             (Post-Ret (qp v))
    -- the certificate-query menu
    ocP : ∀ rs → Post Q (offerCerts n (bs , cs) rs)
    ocP []       = Post-Stop
    ocP (r ∷ rs) = Post-□ (Post-⟶ (hasCertEv n r) (λ x → Post-Ret (qh r x))) (ocP rs)

-- THE VOTE-STORE BOUND: from the empty vote store, every blob read index is below `length U`
voteStore-reads : ∀ n {s W} → voteStore n ([] , []) ⟹⟨ s ⟩ W → AllL (λ e → ∀ j → IsGetVoteAt j e → j < length U) (labels s)
voteStore-reads n tr =
  invLoop {body = voteStep n} (λ v _ → VInv v) (λ _ → 0) (λ _ e → ∀ j → IsGetVoteAt j e → j < length U) (λ _ ok → ok)
    (λ {v} i → AllT->>= (vote-All n (proj₁ v) (proj₂ v) (λ _ j ()) (λ _ j ())
                           (λ k _ lt j eq → subst (_< length U) eq (≤-trans lt (≤-trans i (cntD≤ decVoteBlob U (proj₁ v)))))
                           (λ _ _ j ()))
                         (λ _ → AllT-Ret))
    (λ {v} i → Post->>= {Q₁ = λ _ v′ → VInv v′}
                 (vote-Post n (proj₁ v) (proj₂ v) (λ u _ → insU-inv u (proj₁ v) i) (λ u → insU-inv u (proj₁ v) i)
                            (λ _ _ → i) (λ _ _ → i))
                 (λ q → Post-Ret q))
    {a = [] , []} {m = 0} z≤n tr

-- the certificate potential: how many of the three RB hashes are still uncertified
Φc : Votes → ℕ
Φc v = 3 ∸ D3 (proj₂ v)

-- a fresh certificate spends one unit of it (dedup: `D3-fresh`)
potDrop : ∀ r cs → memberOf ⦃ decBlock ⦄ r cs ≡ false → suc (3 ∸ D3 (r ∷ cs)) ≤ 3 ∸ D3 cs
potDrop r cs eq rewrite D3-fresh r cs eq =
  ≤-reflexive (sym (+-∸-assoc 1 (subst (_≤ 3) (D3-fresh r cs eq) (D3≤3 (r ∷ cs)))))

-- a certification step weighs one only when the certificate is fresh
certW : ∀ n bs cs r → Wt cCert (3 ∸ D3 cs) (certify n bs cs r)
certW n bs cs r =
  Wt-ifT (certifies bs r ∧ not (memberOf ⦃ decRbHash ⦄ r cs))
    (λ eq → Wt-mono (≤-trans (s≤s z≤n) (potDrop r cs (∧-not (certifies bs r) (memberOf ⦃ decRbHash ⦄ r cs) eq)))
                    (Wt-Output ⦃ decRbHash ⦄ (certEv n) r Wt-Ret))
    Wt-Ret

-- a vote-store round weighs at most the potential
vote-Wt : ∀ n bs cs → Wt cCert (Φc (bs , cs)) (voteStep n (bs , cs))
vote-Wt n bs cs =
  Wt-□ (Wt-⟶ (putVoteEv n) (λ _ → refl) (λ v → certW n (insertU ⦃ decVoteBlob ⦄ v bs) cs (blobRb v)))
       (Wt-AllT (AllT-□ (oiAll (getVoteAtEv n) bs 0 (bs , cs) (λ _ _ _ → z≤n)) (ocW cs)))
  where
    -- the certificate-query menu certifies nothing
    ocW : ∀ rs → AllT (λ e → cCert e ≤ 0) (offerCerts n (bs , cs) rs)
    ocW []       = AllT-Stop
    ocW (r ∷ rs) = AllT-□ (AllT-⟶ (hasCertEv n r) (λ _ → z≤n) (λ _ → AllT-Ret)) (ocW rs)

-- THE CERTIFICATE BOUND: from the empty vote store, at most three certificates
voteStore-certs : ∀ n {s W} → voteStore n ([] , []) ⟹⟨ s ⟩ W → Σc cCert (labels s) ≤ 3
voteStore-certs n {s} tr =
  subst (λ z → Σc cCert (labels s) ≤ z + 3) (Σc-0 (labels s))
    (potIter {k = loopStep {R = ⊤ {0ℓ}} (voteStep n)} Φc cCert (λ _ → 0) 0 rp ([] , []) tr)
  where
    -- every round pays its certificate from the potential
    rp : ∀ v → _
    rp (bs , cs) =
        (λ {s′} tr′ → subst (λ z → Σc cCert (labels s′) ≤ z + (Φc (bs , cs) + 0)) (sym (Σc-0 (labels s′)))
                        (Wt->>= (vote-Wt n bs cs) (λ _ → Wt-Ret) tr′))
      , Post->>= {Q₁ = λ ls v′ → Σc cCert ls + Φc v′ ≤ Σc (λ _ → 0) ls + Φc (bs , cs)}
          (vote-Post n bs cs (λ v fr → potDrop (blobRb v) cs fr) (λ _ → ≤-refl) (λ _ _ → ≤-refl) (λ _ _ → ≤-refl))
          (λ {ls₁} {r} q → Post-Ret (subst (λ ls → Σc cCert ls + Φc r ≤ Σc (λ _ → 0) ls + Φc (bs , cs))
                                           (sym (++-identityʳ ls₁)) q))

------------------------------------------------------------------------
-- the EB-entry and EB-body stores (no bound needed: no thread reads them
-- by pointer — only their alphabet and chain-freedom, `StoresProv`)
------------------------------------------------------------------------

-- every label of an EB-store round is a deposit or a read
eb-All : ∀ {P : Event → Set} n es → (∀ e → P (evLabel _ (putEBEv n) e)) → (∀ k e → P (evLabel _ (getEBAtEv n k) e))
       → AllT P (ebStep n es)
eb-All n es pp pa = AllT-□ (AllT-⟶ (putEBEv n) pp (λ _ → AllT-Ret)) (oiAll (getEBAtEv n) es 0 es (λ k e _ → pa k e))

-- every label of a body-store round is a deposit or a keyed read
body-All : ∀ {P : Event → Set} n bs → (∀ eb → P (evLabel _ (putBodyEv n) eb)) → (∀ h eb → P (evLabel _ (getBodyEv n h) eb))
         → AllT P (bodyStep n bs)
body-All {P} n bs pp pg = AllT-□ (AllT-⟶ (putBodyEv n) pp (λ _ → AllT-Ret)) (obA bs)
  where
    -- the keyed menu
    obA : ∀ xs → AllT P (offerBodies n bs xs)
    obA []         = AllT-Stop
    obA (eb ∷ ebs) = AllT-□ (AllT-Output ⦃ decEB ⦄ (getBodyEv n _) eb (pg _ eb) AllT-Ret) (obA ebs)
