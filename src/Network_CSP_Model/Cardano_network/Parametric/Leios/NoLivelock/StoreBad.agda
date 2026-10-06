{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C — THE NEGATIVE CONTROL (owner decision D2-b):
-- the RB-echo dedup is load-bearing for the store bound the proof uses.
--
-- `badStore` is `NodeLogicL.blockStoreL` with the PRE-FIX deposit arm
-- `Ret (b ∷ held)` (no `memberOf` test).  Fed only the block `nothing` —
-- so the provenance rely `InX (nothing ∷ [])` HOLDS on its trace — and
-- never forged into, it still serves EVERY read index k
-- (`storeBad-unbounded`), so the bound `StoresProv.blockStore-reads-prov`
-- proves for the real store, `j < |X| + forges = 1`, FAILS for it
-- (`storeBad-refutes`).
--
-- LEVEL: the STORE, not `rawSys2`.  Store level, by owner decision D2-b; it
-- deviates from spec §7's system-level wording ("a finite trace of the
-- two-node system") WITH OWNER APPROVAL, following the
-- `Negative/Chatter.agda` precedent ("LEVEL: the THREAD/STORE PAIR, not
-- `systemOf`").  Nothing here is a claim about `rawSys2`.
--
-- Import-by-nobody.  Built with the trace-INTRO lemmas only (`□-introL`/
-- `□-introR`, the bind and iter lifts): a menu over a VARIABLE `held` list
-- never normalises, so no step of the store is computed by `refl`.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.NoLivelock.StoreBad where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Fin using (Fin) renaming (zero to fzero)
import Data.List
open import Data.List using (List; []; _∷_; reverse; replicate; _∷ʳ_; length)
open import Data.List.Properties using (unfold-reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-suc; +-identityʳ; <-irrefl)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (0ℓ)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI

open import Process_Trees using (PTree; ExtI; ret; sil; react; AnyTypes)
open PTree
open import Cardano_network.Parametric.Leios.LeiosInstance2 using (p2; lp2; line2)
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (U6; allV6)
open import Cardano_network.Net p2
open import Cardano_network.Data p2 using (Payload)
open import Cardano_network.ApiAlphabet p2 using (apiES)
open import Cardano_network.Params using (module Params)
open Params p2 using (decBlock)
open import Cardano_network.Parametric.Node p2 line2 apiES using (Proc)
import Cardano_network.Parametric.NodeLogic as NL
open NL.Generic p2 line2 apiES using (Held; StoreProc; forgeEv; putEv; offerHeld)
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open NLL.Generic p2 lp2 line2 apiES (λ n → n) using (acceptForgeL; offerIx; getAtEv; memberOf)

open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload})
  using (_□_; Ret; Prefix; Output; Output-cont; _>>=_; loop; iter; iter-bind; iterV; iterT; viewV; viewT; Stop)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import CSP.Laws.Traces.TraceLaws (Net_Api-≟ {Payload}) using (Prefix-cont-just)
open import CSP.Laws.Traces.TraceLawsExtChoice (Net_Api-≟ {Payload}) using (□-introL; □-introR)
open import CSP.Laws.Traces.TraceLawsBind (Net_Api-≟ {Payload}) using (⟹-split-√)
open import CSP.Laws.FD.BindFD (Net_Api-≟ {Payload}) using (lift-bind-bigstep; bind-force-ret; ⟹-trans)
open import CSP.Laws.DivFree.Loop (Net_Api-≟ {Payload}) using (loopStep)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload}) using (labels; Σc; AllL; []; _∷_; AnyE; IsE)
open import Data.List.Relation.Unary.Any using (here; there)
open import Cardano_network.Parametric.Leios.NoLivelock.Threads 1 2 line2 (λ n → n) using (IsGetAt)
open import Cardano_network.Parametric.Leios.NoLivelock.Stores 1 2 line2 (λ n → n) U6 allV6 using (cF)
open import Cardano_network.Parametric.Leios.NoLivelock.StoresProv 1 2 line2 (λ n → n) U6 allV6 using (InX; ROkX; dt)

------------------------------------------------------------------------
-- The pre-fix store
------------------------------------------------------------------------

-- the forge arm, verbatim from `storeStepL`
fArm : Fin 2 → Held → StoreProc
fArm n held = forgeEv n ⟶ (λ mb → Ret (acceptForgeL mb held))

-- THE PRE-FIX DEPOSIT ARM: a block already held is prepended again (no RB-echo dedup)
pArm : Fin 2 → Held → StoreProc
pArm n held = putEv n ⟶ (λ b → Ret (b ∷ held))

-- the two hand-over menus, verbatim from `storeStepL`
rArm : Fin 2 → Held → StoreProc
rArm n held = offerHeld n held held □ offerIx (getAtEv n) (reverse held) 0 held

-- one round of the PRE-FIX RB store: `NodeLogicL.storeStepL` with `pArm` for its deposit arm
badStep : Fin 2 → Held → StoreProc
badStep n held = fArm n held □ (pArm n held □ rArm n held)

-- the pre-fix RB store holding `held`
badStore : Fin 2 → Held → Proc
badStore n held = loop (badStep n) held

------------------------------------------------------------------------
-- The trace
------------------------------------------------------------------------

-- the deposit of the block `nothing` at node `n`
putE : ∀ {ℓr} {R : Set ℓr} → Fin 2 → Event√ R
putE n = evl (evLabel _ (putEv n) nothing)

-- the read of index `k` at node `n`, handing out `nothing`
getE : ∀ {ℓr} {R : Set ℓr} → Fin 2 → ℕ → Event√ R
getE n k = evl (evLabel _ (getAtEv n k) nothing)

-- `nothing` lies in the one-block X
mem1 : memberOf ⦃ decBlock ⦄ nothing (nothing ∷ []) ≡ true
mem1 = cong (_∨ false) (dt (DecEq._≟_ decBlock nothing nothing))

-- an `Output`'s menu answers its own event and value (no decision computed on a variable)
out-just : ∀ {ℓr} {A : Set} {R : Set ℓr} ⦃ _ : DecEq A ⦄ (e : Net_Api Payload A) (v : A)
             (P : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R)
         → Output-cont e v P (A , e) v ≡ just P
out-just {A = A} e v P with Net_Api-≟ {Payload} (A , e) (A , e)
... | no ¬p = ⊥-elim (¬p refl)
... | yes refl with v ≟ v
...   | yes _ = refl
...   | no ¬p = ⊥-elim (¬p refl)

-- the iteration loops back once a round has returned its new state
ib : ∀ {A : Set} {R : Set} (t : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (A ⊎ R))
       (k : A → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (A ⊎ R)) {a : A}
   → force t ≡ ret (inj₁ a) → force (iter-bind t k) ≡ sil (iter k a)
ib t k eq with force t | eq
... | ret (inj₁ _) | refl = refl

-- the iteration is silent when its current round is
ibS : ∀ {A : Set} (t : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (A ⊎ ⊤ {0ℓ}))
        (k : A → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (A ⊎ ⊤ {0ℓ})) {c}
    → force t ≡ sil c → force (iter-bind t k) ≡ sil (iter-bind c k)
ibS t k eq with force t | eq
... | sil _ | refl = refl

-- the iteration reacts as its current round does
ibR : ∀ {A : Set} (t : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (A ⊎ ⊤ {0ℓ}))
        (k : A → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (A ⊎ ⊤ {0ℓ})) {v τc}
    → force t ≡ react v τc → force (iter-bind t k) ≡ react (iterV k (react v τc)) (iterT k (react v τc))
ibR t k eq with force t | eq
... | react _ _ | refl = refl

-- the iteration's offers follow its current round's
ivJ : ∀ {A : Set} (k : A → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (A ⊎ ⊤ {0ℓ})) nP {at a t′}
    → viewV nP at a ≡ just t′ → iterV k nP at a ≡ just (iter-bind t′ k)
ivJ k nP {at} {a} eq with viewV nP at a | eq
... | just _ | refl = refl

-- the iteration's τ-branches follow its current round's
itJ : ∀ {A : Set} (k : A → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (A ⊎ ⊤ {0ℓ})) nP {i a t′}
    → viewT nP i a ≡ just t′ → iterT k nP i a ≡ just (iter-bind t′ k)
itJ k nP {i} {a} eq with viewT nP i a | eq
... | just _ | refl = refl

-- a visible-only run of an iteration's current round is a run of the iteration
liftIter : ∀ {A : Set} {t t′ : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (A ⊎ ⊤ {0ℓ})}
             {k : A → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (A ⊎ ⊤ {0ℓ})} (vs : List Event)
         → t ⟹⟨ Data.List.map evl vs ⟩ t′ → iter-bind t k ⟹⟨ Data.List.map evl vs ⟩ iter-bind t′ k
liftIter []       ⟹-refl      = ⟹-refl
liftIter {k = k} vs (⟹-τ (sSil {p = t} eq) r) = ⟹-τ (sSil (ibS t k eq)) (liftIter vs r)
liftIter {k = k} vs (⟹-τ (sTau {p = t} {v = v} {τc = τc} eq br) r) =
  ⟹-τ (sTau (ibR t k eq) (itJ k (react v τc) br)) (liftIter vs r)
liftIter {k = k} (_ ∷ vs) (⟹-ev (sVis {p = t} {v = v} {τc = τc} eq br) r) =
  ⟹-ev (sVis (ibR t k eq) (ivJ k (react v τc) br)) (liftIter vs r)

-- the store's iteration continuation (`loop` is `iter` of it, by `refl`)
K : Fin 2 → Held → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (Held ⊎ ⊤ {0ℓ})
K n = loopStep {R = ⊤ {0ℓ}} (badStep n)

-- a round's return into the iteration
ret₁ : Held → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (Held ⊎ ⊤ {0ℓ})
ret₁ a′ = Ret (inj₁ a′)

-- a deposit round, up to its return: `nothing` is prepended
putArm : (n : Fin 2) (hs : Held) → traces (badStep n hs) (putE n ∷ √ (nothing ∷ hs) ∷ [])
putArm n hs =
  □-introR (fArm n hs) (pArm n hs □ rArm n hs)
    (proj₂ (□-introL (pArm n hs) (rArm n hs)
      (⟹-ev (sVis refl (Prefix-cont-just (putEv n) (λ b → Ret (b ∷ hs)) nothing))
        (⟹-ev (sRet refl) ⟹-refl))))

-- one deposit round of the store, in front of any run of the grown store
putR : (n : Fin 2) (hs : Held) {s : List (Event√ (⊤ {0ℓ}))} → traces (badStore n (nothing ∷ hs)) s → traces (badStore n hs) (putE n ∷ s)
putR n hs (W , tr) with ⟹-split-√ (badStep n hs) (putE n ∷ []) (proj₂ (putArm n hs))
... | P‴ , w , fr =
  W , ⟹-trans (liftIter {k = K n} (evLabel _ (putEv n) nothing ∷ [])
                 (lift-bind-bigstep _ _ ret₁ (evLabel _ (putEv n) nothing ∷ []) w))
              (⟹-τ (sSil (ib (P‴ >>= ret₁) (K n) (bind-force-ret P‴ ret₁ fr))) tr)

-- appending one more copy is prepending it
rep-snoc : ∀ m → replicate m (nothing {A = Bool}) ∷ʳ nothing ≡ nothing ∷ replicate m nothing
rep-snoc zero    = refl
rep-snoc (suc m) = cong (nothing ∷_) (rep-snoc m)

-- reversing copies of one value changes nothing
rev-rep : ∀ m → reverse (replicate m (nothing {A = Bool})) ≡ replicate m nothing
rev-rep zero    = refl
rev-rep (suc m) = trans (unfold-reverse nothing (replicate m nothing))
                        (trans (cong (_∷ʳ nothing) (rev-rep m)) (rep-snoc m))

-- the read-pointer menu over `m + 1` copies of `nothing`, from pointer `j`, serves index `m + j`
oiTr : (n : Fin 2) (hs : Held) (m j : ℕ) → traces (offerIx (getAtEv n) (replicate (suc m) nothing) j hs) (getE n (m + j) ∷ [])
oiTr n hs zero    j =
  □-introL (getAtEv n j ! nothing ⟶ Ret hs) (offerIx (getAtEv n) [] (suc j) hs)
    (⟹-ev (sVis refl (out-just (getAtEv n j) nothing (Ret hs))) ⟹-refl)
oiTr n hs (suc m) j =
  □-introR (getAtEv n j ! nothing ⟶ Ret hs) (offerIx (getAtEv n) (replicate (suc m) nothing) (suc j) hs)
    (proj₂ (subst (λ i → traces (offerIx (getAtEv n) (replicate (suc m) nothing) (suc j) hs) (getE n i ∷ []))
                  (+-suc m j) (oiTr n hs m (suc j))))

-- a read round over `k + 1` held copies of `nothing` serves index `k`
getR : (n : Fin 2) (k : ℕ) → traces (badStore n (replicate (suc k) nothing)) (getE n k ∷ [])
getR n k =
  _ , liftIter {k = K n} (evLabel _ (getAtEv n k) nothing ∷ [])
        (lift-bind-bigstep _ _ ret₁ (evLabel _ (getAtEv n k) nothing ∷ []) (proj₂ tr))
  where
    -- the held list
    hs : Held
    hs = replicate (suc k) nothing
    -- the read menu, over `reverse hs`
    oi : traces (offerIx (getAtEv n) (reverse hs) 0 hs) (getE n k ∷ [])
    oi = subst (λ xs → traces (offerIx (getAtEv n) xs 0 hs) (getE n k ∷ [])) (sym (rev-rep (suc k)))
           (subst (λ i → traces (offerIx (getAtEv n) hs 0 hs) (getE n i ∷ [])) (+-identityʳ k) (oiTr n hs k 0))
    -- … inside the round's menu
    tr : traces (badStep n hs) (getE n k ∷ [])
    tr = □-introR (fArm n hs) (pArm n hs □ rArm n hs)
           (proj₂ (□-introR (pArm n hs) (rArm n hs)
             (proj₂ (□-introR (offerHeld n hs hs) (offerIx (getAtEv n) (reverse hs) 0 hs) (proj₂ oi)))))

-- `j` deposits of `nothing`, then the read of index `k`
run : Fin 2 → ℕ → ℕ → List (Event√ (⊤ {0ℓ}))
run n zero    k = getE n k ∷ []
run n (suc j) k = putE n ∷ run n j k

-- `j` deposits from `m` held copies, reaching `k + 1` copies, then the read of index `k`
go : (n : Fin 2) (k j m : ℕ) → j + m ≡ suc k → traces (badStore n (replicate m nothing)) (run n j k)
go n k zero    m eq = subst (λ m′ → traces (badStore n (replicate m′ nothing)) (getE n k ∷ [])) (sym eq) (getR n k)
go n k (suc j) m eq = putR n (replicate m nothing) (go n k j (suc m) (trans (+-suc j m) eq))

-- THE NEGATIVE CONTROL: from the empty pre-fix store, given only the block `nothing` (the
-- rely `InX (nothing ∷ [])` holds) and no forge, every read index `k` is served
storeBad-unbounded : ∀ k → Σ[ s ∈ List (Event√ (⊤ {0ℓ})) ] traces (badStore fzero []) s
                       × AllL (InX (nothing ∷ [])) (labels s)
                       × (Σc cF (labels s) ≡ 0) × AnyE (IsGetAt k) s
storeBad-unbounded k =
  run fzero (suc k) k , go fzero k (suc k) 0 (cong suc (+-identityʳ k)) , allX (suc k) , cf0 (suc k) , anyG (suc k)
  where
    -- every label carries only `nothing`, which lies in X
    allX : ∀ j → AllL (InX (nothing ∷ [])) (labels (run fzero j k))
    allX zero    = (λ { refl → mem1 }) ∷ []
    allX (suc j) = (λ { refl → mem1 }) ∷ allX j
    -- no label is a forge
    cf0 : ∀ j → Σc cF (labels (run fzero j k)) ≡ 0
    cf0 zero    = refl
    cf0 (suc j) = cf0 j
    -- the last label reads index `k`
    anyG : ∀ j → AnyE (IsGetAt k) (run fzero j k)
    anyG zero    = here refl
    anyG (suc j) = there (anyG j)

------------------------------------------------------------------------
-- The refutation of the provenance-relative store bound
------------------------------------------------------------------------

-- a label kept by an `AllL` and picked by an `AnyE` satisfies both
pick : ∀ {P Q : Event → Set} (s : List (Event√ (⊤ {0ℓ}))) → AllL P (labels s) → AnyE Q s
     → Σ Event (λ e → P e × Q e)
pick (evl e ∷ s) (p ∷ a) (here q)  = e , p , q
pick (evl e ∷ s) (p ∷ a) (there y) = pick s a y
pick (√ _ ∷ s)   a       (here ())
pick (√ _ ∷ s)   a       (there y) = pick s a y

-- THE DEDUP IS LOAD-BEARING: `StoresProv.blockStore-reads-prov`'s conclusion, stated for
-- the pre-fix store at X = [ nothing ], is FALSE — index 1 is read although |X| + forges = 1
storeBad-refutes : ¬ (∀ {s W} → badStore fzero [] ⟹⟨ s ⟩ W → AllL (InX (nothing ∷ [])) (labels s)
                      → AllL (ROkX (nothing ∷ []) (Σc cF (labels s))) (labels s))
storeBad-refutes bound with storeBad-unbounded 1
... | s , (W , tr) , rely , cf , g with pick s (bound tr rely) g
...   | e , ok , isg = <-irrefl refl (subst (λ m → 1 < 1 + m) cf (ok 1 isg))
