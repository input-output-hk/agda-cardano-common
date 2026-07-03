{-# OPTIONS --guardedness #-}

-- WORK IN PROGRESS (uncommitted): generalising DeadlockFree SYSTEMasym to arbitrary
-- n = suc (suc m).  Foundation: general per-component reach-closure via explicit
-- `loopTail` position terms + `with E-≟` step-inversion (abstracts the whole event
-- decision, sidestepping the green-slime that blocks `i Fin.≟ i` for abstract i).

module CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_DeadlockFreeN where

open import Level using (lift) renaming (zero to lzero)
open import Data.Nat using (ℕ; suc; zero; _<_; _≤_; s≤s; z≤n; _<?_)
open import Data.Nat.Properties using (n<1+n; 1+n≢n; ≮⇒≥; ≤-antisym; suc-injective)
open import Data.Fin using (Fin; toℕ; fromℕ<; inject₁) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ-inject₁; toℕ-injective; toℕ<n)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; concatMap; drop; map; _++_; [_])
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.Vec.Base as VB
import Data.List.Base as LB
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (allFin⁺)
open import Data.List.Relation.Unary.AllPairs using () renaming (_∷_ to _∷ᵖ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Function using (case_of_)

open import Process_Trees
open import Semantics.LTS
open import Semantics.Failures using (_⟹⟨_⟩_; ⟹-refl; ⟹-ev; ⟹-τ)
open import Semantics.Deadlock using (IsStuck; DeadlockFree)
open PTree

open import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP

module N (m : ℕ) where
  open Sys m
  import CSP.Operators {E = DP} as Ops
  open Ops DP-AnyTypes-≟
  open EventSet
  import CSP.Laws.AlphaParallel {E = DP} as AParL
  open AParL DP-AnyTypes-≟ using (αpar-reach; AlphaParReachSplit; in-progress; done
    ; αpar-vis-step-inv; αpar-τ-step-inv; αpar-√-step-inv; vSync; vSoloL; vSoloR; v√)

  -- loop0's internal step: body >>= (inject into the loop sum), as a named function.
  gret : ⊤ {lzero} → PTree DP (ExtI DP) (⊤ {lzero} ⊎ ⊥)
  gret a = Ret (inj₁ a)
  gstep : (first second : Phil → Fork) → Phil → ⊤ {lzero} → PTree DP (ExtI DP) (⊤ {lzero} ⊎ ⊥)
  gstep first second i _ = PHILbody first second i >>= gret
    where
      PHILbody : (first second : Phil → Fork) → Phil → PTree DP (ExtI DP) (⊤ {lzero})
      PHILbody f s j = picks j (f j) ⟶₀ (picks j (s j) ⟶₀ (putsdown j (s j) ⟶₀ (putsdown j (f j) ⟶₀ Skip)))

  -- the philosopher body (matches the model's PHIL)
  Pbody : (first second : Phil → Fork) → Phil → PTree DP (ExtI DP) (⊤ {lzero})
  Pbody f s i = picks i (f i) ⟶₀ (picks i (s i) ⟶₀ (putsdown i (s i) ⟶₀ (putsdown i (f i) ⟶₀ Skip)))
  Psuf1 Psuf2 Psuf3 : (first second : Phil → Fork) → Phil → PTree DP (ExtI DP) (⊤ {lzero})
  Psuf1 f s i = picks i (s i) ⟶₀ (putsdown i (s i) ⟶₀ (putsdown i (f i) ⟶₀ Skip))
  Psuf2 f s i = putsdown i (s i) ⟶₀ (putsdown i (f i) ⟶₀ Skip)
  Psuf3 f s i = putsdown i (f i) ⟶₀ Skip

  -- a loop0 residual sitting at suffix `suf` (think = whole body = the real PHIL).
  loopTail : (first second : Phil → Fork) → Phil → PTree DP (ExtI DP) (⊤ {lzero}) → PTree DP (ExtI DP) ⊥
  loopTail f s i suf = iter-bind (suf >>= gret) (gstep f s i)

  data PhilPos : Set where think one eat down1 reloop : PhilPos
  philSt : (first second : Phil → Fork) → Phil → PhilPos → PTree DP (ExtI DP) ⊥
  philSt f s i think  = loopTail f s i (Pbody f s i)
  philSt f s i one    = loopTail f s i (Psuf1 f s i)
  philSt f s i eat    = loopTail f s i (Psuf2 f s i)
  philSt f s i down1  = loopTail f s i (Psuf3 f s i)
  philSt f s i reloop = loopTail f s i Skip

  -- VALIDATION 1: think IS the real PHIL process (definitionally).
  philSt-think≡ : ∀ f s i → philSt f s i think ≡ PHIL f s i
  philSt-think≡ f s i = refl

  -- VALIDATION 2: think is react-headed-and-stable for ABSTRACT i (no green-slime).
  think-VisHead : ∀ f s i → Σ[ v ∈ _ ] Σ[ τc ∈ _ ]
                  ((philSt f s i think) .force ≡ react v τc × (∀ j a → τc j a ≡ nothing))
  think-VisHead f s i = _ , _ , refl , (λ _ _ → refl)

  -- VALIDATION 3: reloop is sil-headed back to think, for abstract i.
  reloop-sil : ∀ f s i → (philSt f s i reloop) .force ≡ sil (philSt f s i think)
  reloop-sil f s i = refl

  ----------------------------------------------------------------------------------
  -- General PHIL reach-closure.  Step-inversion via `with E-≟ (whole event)` — this
  -- abstracts the buried DP-AnyTypes-≟ decision, so it works for ABSTRACT i (the
  -- green-slime that blocks `i Fin.≟ i` never surfaces).
  data PhilReach (f s : Phil → Fork) (i : Phil) : PTree DP (ExtI DP) ⊥ → Set where
    rp : (p : PhilPos) → PhilReach f s i (philSt f s i p)

  phil-step : ∀ {f s i t l t″} → PhilReach f s i t → t ─[ l ]─► t″ → PhilReach f s i t″
  phil-step (rp think) (sRet eq) = case eq of λ ()
  phil-step (rp think) (sSil eq) = case eq of λ ()
  phil-step (rp think) (sTau refl br) = case br of λ ()
  phil-step {f}{s}{i} (rp think) (sVis {at = at} refl br) with DP-AnyTypes-≟ (⊤ {lzero} , picks i (f i)) at
  ... | yes refl = subst (PhilReach f s i) (just-injective br) (rp one)
  ... | no ¬p    = case br of λ ()
  phil-step (rp one) (sRet eq) = case eq of λ ()
  phil-step (rp one) (sSil eq) = case eq of λ ()
  phil-step (rp one) (sTau refl br) = case br of λ ()
  phil-step {f}{s}{i} (rp one) (sVis {at = at} refl br) with DP-AnyTypes-≟ (⊤ {lzero} , picks i (s i)) at
  ... | yes refl = subst (PhilReach f s i) (just-injective br) (rp eat)
  ... | no ¬p    = case br of λ ()
  phil-step (rp eat) (sRet eq) = case eq of λ ()
  phil-step (rp eat) (sSil eq) = case eq of λ ()
  phil-step (rp eat) (sTau refl br) = case br of λ ()
  phil-step {f}{s}{i} (rp eat) (sVis {at = at} refl br) with DP-AnyTypes-≟ (⊤ {lzero} , putsdown i (s i)) at
  ... | yes refl = subst (PhilReach f s i) (just-injective br) (rp down1)
  ... | no ¬p    = case br of λ ()
  phil-step (rp down1) (sRet eq) = case eq of λ ()
  phil-step (rp down1) (sSil eq) = case eq of λ ()
  phil-step (rp down1) (sTau refl br) = case br of λ ()
  phil-step {f}{s}{i} (rp down1) (sVis {at = at} refl br) with DP-AnyTypes-≟ (⊤ {lzero} , putsdown i (f i)) at
  ... | yes refl = subst (PhilReach f s i) (just-injective br) (rp reloop)
  ... | no ¬p    = case br of λ ()
  phil-step (rp reloop) (sSil refl) = rp think
  phil-step (rp reloop) (sRet eq) = case eq of λ ()
  phil-step (rp reloop) (sTau eq br) = case eq of λ ()
  phil-step (rp reloop) (sVis eq br) = case eq of λ ()

  phil-reach : ∀ {f s i s′ t′} → PHIL f s i ⟹⟨ s′ ⟩ t′ → PhilReach f s i t′
  phil-reach {f}{s}{i} = go (rp think)
    where
      go : ∀ {t s′ t′} → PhilReach f s i t → t ⟹⟨ s′ ⟩ t′ → PhilReach f s i t′
      go r ⟹-refl         = r
      go r (⟹-τ  st rest) = go (phil-step r st) rest
      go r (⟹-ev st rest) = go (phil-step r st) rest

  ----------------------------------------------------------------------------------
  -- General FORK reach-closure.  FORK j = loop0((picks j j → putsdown j j → Skip) □
  -- (picks (j⊖1) j → putsdown (j⊖1) j → Skip)).  The `free` position is the □ entry
  -- (offers own picks j j and nbr picks (j⊖1) j); its τ-map needs the structured
  -- index-shape stability.  Step-inversion uses the own/nbr event decisions; the □
  -- offer is own-first, so the (own-yes, _) / (own-no, nbr-yes) / (no,no) split works
  -- without needing the ring fact j⊖1 ≢ j.
  Fbody : Fork → PTree DP (ExtI DP) (⊤ {lzero})
  Fbody j = (picks j j ⟶₀ (putsdown j j ⟶₀ Skip)) □ (picks (j ⊖1) j ⟶₀ (putsdown (j ⊖1) j ⟶₀ Skip))
  gstepF : Fork → ⊤ {lzero} → PTree DP (ExtI DP) (⊤ {lzero} ⊎ ⊥)
  gstepF j _ = Fbody j >>= gret
  loopTailF : Fork → PTree DP (ExtI DP) (⊤ {lzero}) → PTree DP (ExtI DP) ⊥
  loopTailF j suf = iter-bind (suf >>= gret) (gstepF j)

  data ForkPos : Set where free heldOwn heldNbr freloop : ForkPos
  forkSt : Fork → ForkPos → PTree DP (ExtI DP) ⊥
  forkSt j free    = loopTailF j (Fbody j)
  forkSt j heldOwn = loopTailF j (putsdown j j ⟶₀ Skip)
  forkSt j heldNbr = loopTailF j (putsdown (j ⊖1) j ⟶₀ Skip)
  forkSt j freloop = loopTailF j Skip

  forkSt-free≡ : ∀ j → forkSt j free ≡ FORK j
  forkSt-free≡ j = refl
  freloop-sil : ∀ j → (forkSt j freloop) .force ≡ sil (forkSt j free)
  freloop-sil j = refl

  -- the free position's τ-map (the □ merge) is everywhere nothing — structured on the
  -- ExtI index shape (independent of j), mirroring DeadlockReachable.probeFst.
  fork-free-force : ∀ j → Σ[ v ∈ _ ] Σ[ τc ∈ _ ] (forkSt j free) .force ≡ react v τc
  fork-free-force j = _ , _ , refl
  fork-free-τc : ∀ j → (i : AnyTypes (ExtI DP)) → ContinueType i (Maybe (PTree DP (ExtI DP) ⊥))
  fork-free-τc j = let (_ , τc , _) = fork-free-force j in τc
  st-free : ∀ j i a → fork-free-τc j i a ≡ nothing
  st-free j (_ , base _)            _ = refl
  st-free j (_ , fin)               _ = refl
  st-free j (_ , pair (base _) _)   _ = refl
  st-free j (_ , pair (pair _ _) _) _ = refl
  st-free j (_ , pair fin i) (lift fzero , a)           = refl
  st-free j (_ , pair fin i) (lift (fsuc fzero) , a)    = refl
  st-free j (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = refl

  -- ring fact: the predecessor differs from the index (n = suc (suc m) ≥ 2).
  ⊖≢ : ∀ (j : Fork) → j ⊖1 ≢ j
  ⊖≢ fzero eq = case trans (sym (toℕ-fromℕ< (n<1+n (suc m)))) (cong toℕ eq) of λ ()
  ⊖≢ (fsuc i) eq = 1+n≢n (sym (trans (sym (toℕ-inject₁ i)) (cong toℕ eq)))

  -- extract the philosopher index of a DP event (for the (yes,yes) refutation).
  philOf : AnyTypes DP → Fork
  philOf (_ , picks i _)    = i
  philOf (_ , putsdown i _) = i

  data ForkReach (j : Fork) : PTree DP (ExtI DP) ⊥ → Set where
    rf : (p : ForkPos) → ForkReach j (forkSt j p)

  fork-step : ∀ {j t l t″} → ForkReach j t → t ─[ l ]─► t″ → ForkReach j t″
  fork-step (rf free) (sRet eq) = case eq of λ ()
  fork-step (rf free) (sSil eq) = case eq of λ ()
  fork-step {j} (rf free) (sTau {i = i} {a = a} refl br) = case trans (sym (st-free j i a)) br of λ ()
  fork-step {j} (rf free) (sVis {at = at} refl br)
    with DP-AnyTypes-≟ (⊤ {lzero} , picks j j) at | DP-AnyTypes-≟ (⊤ {lzero} , picks (j ⊖1) j) at
  ... | yes refl | no ¬q    = subst (ForkReach j) (just-injective br) (rf heldOwn)
  ... | yes refl | yes p    = ⊥-elim (⊖≢ j (cong philOf p))
  ... | no ¬p    | yes refl = subst (ForkReach j) (just-injective br) (rf heldNbr)
  ... | no ¬p    | no ¬q    = case br of λ ()
  fork-step (rf heldOwn) (sRet eq) = case eq of λ ()
  fork-step (rf heldOwn) (sSil eq) = case eq of λ ()
  fork-step (rf heldOwn) (sTau refl br) = case br of λ ()
  fork-step {j} (rf heldOwn) (sVis {at = at} refl br) with DP-AnyTypes-≟ (⊤ {lzero} , putsdown j j) at
  ... | yes refl = subst (ForkReach j) (just-injective br) (rf freloop)
  ... | no ¬p    = case br of λ ()
  fork-step (rf heldNbr) (sRet eq) = case eq of λ ()
  fork-step (rf heldNbr) (sSil eq) = case eq of λ ()
  fork-step (rf heldNbr) (sTau refl br) = case br of λ ()
  fork-step {j} (rf heldNbr) (sVis {at = at} refl br) with DP-AnyTypes-≟ (⊤ {lzero} , putsdown (j ⊖1) j) at
  ... | yes refl = subst (ForkReach j) (just-injective br) (rf freloop)
  ... | no ¬p    = case br of λ ()
  fork-step (rf freloop) (sSil refl) = rf free
  fork-step (rf freloop) (sRet eq) = case eq of λ ()
  fork-step (rf freloop) (sTau eq br) = case eq of λ ()
  fork-step (rf freloop) (sVis eq br) = case eq of λ ()

  fork-reach : ∀ {j s′ t′} → FORK j ⟹⟨ s′ ⟩ t′ → ForkReach j t′
  fork-reach {j} = go (rf free)
    where
      go : ∀ {t s′ t′} → ForkReach j t → t ⟹⟨ s′ ⟩ t′ → ForkReach j t′
      go r ⟹-refl         = r
      go r (⟹-τ  st rest) = go (fork-step r st) rest
      go r (⟹-ev st rest) = go (fork-step r st) rest

  ----------------------------------------------------------------------------------
  -- System-state framework: a Config assigns each philosopher a PhilPos and each fork
  -- a ForkPos; sysState folds the per-component position-residuals in the model's
  -- component order.  SYSTEMasym ≡ sysState cfg0 (all think/free) — since philSt think
  -- ≡ PHIL and forkSt free ≡ FORK.
  Config : Set
  Config = (Phil → PhilPos) × (Fork → ForkPos)

  philComp* : (f s : Phil → Fork) → Config → Phil → Comp DP ⊥
  philComp* f s cfg i = comp (AlphaP i) (philSt f s i (proj₁ cfg i))
  forkComp* : Config → Fork → Comp DP ⊥
  forkComp* cfg j = comp (AlphaF j) (forkSt j (proj₂ cfg j))

  sysComps0 : (f s : Phil → Fork) → Config → Comp DP ⊥
  sysComps0 f s cfg = philComp* f s cfg fzero
  sysCompsRest : (f s : Phil → Fork) → Config → List (Comp DP ⊥)
  sysCompsRest f s cfg =
    forkComp* cfg fzero ∷ concatMap (λ i → philComp* f s cfg i ∷ forkComp* cfg i ∷ []) (drop 1 allPhils)

  sysState : (f s : Phil → Fork) (cfg : Config)
           → PTree DP (ExtI DP) (RetOf⁺ (sysComps0 f s cfg) (sysCompsRest f s cfg))
  sysState f s cfg = ∥ₐ⁺ (sysComps0 f s cfg) (sysCompsRest f s cfg)

  cfg0 : Config
  cfg0 = (λ _ → think) , (λ _ → free)

  sys≡ : SYSTEMasym ≡ sysState asymFirst asymSecond cfg0
  sys≡ = refl

  ----------------------------------------------------------------------------------
  -- Uniform per-component reach interface (packages PHIL/FORK reach-closures), so the
  -- n-ary system decomposition can treat the heterogeneous component list uniformly.
  record CompReachI (c : Comp DP ⊥) : Set₁ where
    field
      Pos     : Set
      pst     : Pos → PTree DP (ExtI DP) ⊥
      pinit   : Pos
      pinit≡  : pst pinit ≡ Comp.proc c
      psing   : ∀ {p l t″} → pst p ─[ l ]─► t″ → Σ[ p′ ∈ Pos ] (t″ ≡ pst p′)
      pno-ret : ∀ p {x} → pst p .force ≢ ret x

  -- tag extractors from the reach datatypes
  phil-tag : ∀ {f s i t} → PhilReach f s i t → Σ[ p ∈ PhilPos ] (t ≡ philSt f s i p)
  phil-tag (rp p) = p , refl
  fork-tag : ∀ {j t} → ForkReach j t → Σ[ p ∈ ForkPos ] (t ≡ forkSt j p)
  fork-tag (rf p) = p , refl

  phil-never-ret : ∀ f s i p {x} → philSt f s i p .force ≢ ret x
  phil-never-ret f s i think  ()
  phil-never-ret f s i one    ()
  phil-never-ret f s i eat    ()
  phil-never-ret f s i down1  ()
  phil-never-ret f s i reloop ()
  fork-never-ret : ∀ j p {x} → forkSt j p .force ≢ ret x
  fork-never-ret j free    ()
  fork-never-ret j heldOwn ()
  fork-never-ret j heldNbr ()
  fork-never-ret j freloop ()

  philReachI : (f s : Phil → Fork) (i : Phil) → CompReachI (philComp f s i)
  philReachI f s i = record
    { Pos = PhilPos ; pst = philSt f s i ; pinit = think ; pinit≡ = refl
    ; psing = λ {p} st → phil-tag (phil-step (rp p) st)
    ; pno-ret = phil-never-ret f s i }
  forkReachI : (j : Fork) → CompReachI (forkComp j)
  forkReachI j = record
    { Pos = ForkPos ; pst = forkSt j ; pinit = free ; pinit≡ = refl
    ; psing = λ {p} st → fork-tag (fork-step (rf p) st)
    ; pno-ret = fork-never-ret j }

  -- big-step per-component reach: from the initial position, any ⟹-reachable residual
  -- is again a position.  (Derived from pinit + psing.)
  pbig : ∀ {c} (rc : CompReachI c) {s′ t′}
       → Comp.proc c ⟹⟨ s′ ⟩ t′ → Σ[ p ∈ CompReachI.Pos rc ] (t′ ≡ CompReachI.pst rc p)
  pbig {c} rc bs = go (CompReachI.pinit rc) (sym (CompReachI.pinit≡ rc)) bs
    where
      open CompReachI rc
      go : ∀ {t s′ t′} (p : Pos) → t ≡ pst p → t ⟹⟨ s′ ⟩ t′ → Σ[ p′ ∈ Pos ] (t′ ≡ pst p′)
      go p eq ⟹-refl = p , eq
      go p refl (⟹-τ  st rest) = let (p′ , eq′) = psing st in go p′ eq′ rest
      go p refl (⟹-ev st rest) = let (p′ , eq′) = psing st in go p′ eq′ rest

  ----------------------------------------------------------------------------------
  -- A component never ticks (√): positions are never ret-headed, so no √-labelled step
  -- and no √-ending big-step.  Used to refute αpar-reach's `done` case.
  pos-no-tick : ∀ {c}(rc : CompReachI c){p t″ r} → CompReachI.pst rc p ─[ ev (√ r) ]─► t″ → ⊥
  pos-no-tick rc (sRet feq) = CompReachI.pno-ret rc _ feq

  no-tick : ∀ {c}(rc : CompReachI c){t t′}(p : CompReachI.Pos rc){s r}
          → t ≡ CompReachI.pst rc p → t ⟹⟨ map evl s ++ [ √ r ] ⟩ t′ → ⊥
  no-tick rc p {[]}    refl (⟹-ev st rest) = pos-no-tick rc st
  no-tick rc p {[]}    refl (⟹-τ  st rest) = let (p′ , eq′) = CompReachI.psing rc st in no-tick rc p′ {[]}    eq′ rest
  no-tick rc p {e ∷ s} refl (⟹-ev st rest) = let (p′ , eq′) = CompReachI.psing rc st in no-tick rc p′ {s}     eq′ rest
  no-tick rc p {e ∷ s} refl (⟹-τ  st rest) = let (p′ , eq′) = CompReachI.psing rc st in no-tick rc p′ {e ∷ s} eq′ rest

  ----------------------------------------------------------------------------------
  -- The n-ary system decomposition.  FoldReach keeps the ORIGINAL alphabets (so the
  -- αpar equation is definitional) while recording each component's reached position.
  data FoldReach : (c : Comp DP ⊥) (xs : List (Comp DP ⊥))
                 → CompReachI c → All CompReachI xs → PTree DP (ExtI DP) (RetOf⁺ c xs) → Set₁ where
    fr-nil  : ∀ {c} {rc : CompReachI c} (p : CompReachI.Pos rc)
            → FoldReach c [] rc [] (CompReachI.pst rc p)
    fr-cons : ∀ {c d ds} {rc : CompReachI c} {rcd : CompReachI d} {rcds : All CompReachI ds}
                (p : CompReachI.Pos rc) {tail : PTree DP (ExtI DP) (RetOf⁺ d ds)}
            → FoldReach d ds rcd rcds tail
            → FoldReach c (d ∷ ds) rc (rcd ∷ rcds)
                (CompReachI.pst rc p ⟦ Comp.alpha c ∥ unionα (d ∷ ds) ⟧ tail)

  ∥ₐ⁺-foldReach : ∀ {c xs} (rc : CompReachI c) (rcs : All CompReachI xs) {s′ t′}
                → ∥ₐ⁺ c xs ⟹⟨ s′ ⟩ t′ → FoldReach c xs rc rcs t′
  ∥ₐ⁺-foldReach {c} {[]} rc [] bs =
    let (p , eq) = pbig rc bs in subst (FoldReach c [] rc []) (sym eq) (fr-nil p)
  ∥ₐ⁺-foldReach {c} {d ∷ ds} rc (rcd ∷ rcds) bs
    with αpar-reach (Comp.proc c) (∥ₐ⁺ d ds) (Comp.alpha c) (unionα (d ∷ ds)) bs
  ... | in-progress {P′ = P′} {Q′ = Q′} _ bsP bsQ =
        let (p , eqP) = pbig rc bsP
        in subst (λ z → FoldReach c (d ∷ ds) rc (rcd ∷ rcds) (z ⟦ Comp.alpha c ∥ unionα (d ∷ ds) ⟧ Q′))
                 (sym eqP) (fr-cons p (∥ₐ⁺-foldReach rcd rcds bsQ))
  ... | done _ bsP√ _ = ⊥-elim (no-tick rc (CompReachI.pinit rc) (sym (CompReachI.pinit≡ rc)) bsP√)

  ----------------------------------------------------------------------------------
  -- Instantiate the decomposition for SYSTEMasym's component list.
  allRest : (xs : List Phil)
          → All CompReachI (concatMap (λ i → philComp asymFirst asymSecond i ∷ forkComp i ∷ []) xs)
  allRest []       = []
  allRest (i ∷ xs) = philReachI asymFirst asymSecond i ∷ forkReachI i ∷ allRest xs

  allComps : All CompReachI (compsRest asymFirst asymSecond)
  allComps = forkReachI fzero ∷ allRest (drop 1 allPhils)

  sys-foldReach : ∀ {s′ t′} → SYSTEMasym ⟹⟨ s′ ⟩ t′
                → FoldReach (comps0 asymFirst asymSecond) (compsRest asymFirst asymSecond)
                            (philReachI asymFirst asymSecond fzero) allComps t′
  sys-foldReach bs = ∥ₐ⁺-foldReach (philReachI asymFirst asymSecond fzero) allComps bs

  ----------------------------------------------------------------------------------
  -- NATIVE consistency layer (toward generic-rank progress for flipped-phil-0).
  -- holdings: which fork-slots a philosopher position occupies.
  holdsF holdsS : PhilPos → Bool
  holdsF think = false ; holdsF one = true ; holdsF eat = true ; holdsF down1 = true ; holdsF reloop = false
  holdsS think = false ; holdsS one = false ; holdsS eat = true ; holdsS down1 = false ; holdsS reloop = false

  -- philosopher i holds fork k (its first slot if held, or its second slot if eating).
  phil-holds : Config → Phil → Fork → Set
  phil-holds cfg i k =
      (asymFirst i ≡ k × holdsF (proj₁ cfg i) ≡ true)
    ⊎ (asymSecond i ≡ k × holdsS (proj₁ cfg i) ≡ true)

  -- the consistency invariant: a fork's recorded position matches its actual holder
  -- (own = phil j picked it; nbr = phil (j⊖1) picked it), and a held fork has a unique
  -- consistent holder (mutual exclusion).
  ForkConsistent : Config → Set
  ForkConsistent cfg = ∀ (j : Fork) →
      (proj₂ cfg j ≡ heldOwn → phil-holds cfg j j)
    × (proj₂ cfg j ≡ heldNbr → phil-holds cfg (j ⊖1) j)
    × (∀ i → phil-holds cfg i j →
         (i ≡ j × proj₂ cfg j ≡ heldOwn) ⊎ (i ≡ (j ⊖1) × proj₂ cfg j ≡ heldNbr))

  -- the initial config (all think / all free) is consistent.
  cons0-FC : ForkConsistent cfg0
  cons0-FC j = (λ ()) , (λ ()) , holders
    where
      holders : ∀ i → phil-holds cfg0 i j
               → (i ≡ j × proj₂ cfg0 j ≡ heldOwn) ⊎ (i ≡ (j ⊖1) × proj₂ cfg0 j ≡ heldNbr)
      holders i (inj₁ (_ , ()))
      holders i (inj₂ (_ , ()))

  ----------------------------------------------------------------------------------
  -- Native config-transition relation _⊳_ (no relational module).  Each pick/putsdown
  -- co-updates a philosopher and a fork; reloops are τ.  The fork's new position is
  -- own/nbr per whether the fork's index equals the philosopher's.
  asymForks-Sys : ∀ i → (asymFirst i ≡ i × asymSecond i ≡ i ⊕1)
                       ⊎ (asymFirst i ≡ i ⊕1 × asymSecond i ≡ i)
  asymForks-Sys i with i Fin.≟ fzero
  ... | yes refl = inj₂ (refl , refl)
  ... | no  _    = inj₁ (refl , refl)

  ownNbr : Phil → Fork → ForkPos
  ownNbr i k = if ⌊ k Fin.≟ i ⌋ then heldOwn else heldNbr
  setP : Config → Phil → PhilPos → Config
  setP cfg i p = (λ k → if ⌊ k Fin.≟ i ⌋ then p else proj₁ cfg k) , proj₂ cfg
  setF : Config → Fork → ForkPos → Config
  setF cfg j q = proj₁ cfg , (λ k → if ⌊ k Fin.≟ j ⌋ then q else proj₂ cfg k)

  data _⊳_ : Config → Config → Set where
    ⊳pk1 : ∀ {cfg} (i : Phil) → proj₁ cfg i ≡ think → proj₂ cfg (asymFirst i) ≡ free
         → cfg ⊳ setF (setP cfg i one) (asymFirst i) (ownNbr i (asymFirst i))
    ⊳pk2 : ∀ {cfg} (i : Phil) → proj₁ cfg i ≡ one → proj₂ cfg (asymSecond i) ≡ free
         → cfg ⊳ setF (setP cfg i eat) (asymSecond i) (ownNbr i (asymSecond i))
    ⊳pd2 : ∀ {cfg} (i : Phil) → proj₁ cfg i ≡ eat
         → cfg ⊳ setF (setP cfg i down1) (asymSecond i) freloop
    ⊳pd1 : ∀ {cfg} (i : Phil) → proj₁ cfg i ≡ down1
         → cfg ⊳ setF (setP cfg i reloop) (asymFirst i) freloop
    ⊳τp  : ∀ {cfg} (i : Phil) → proj₁ cfg i ≡ reloop → cfg ⊳ setP cfg i think
    ⊳τf  : ∀ {cfg} (j : Fork) → proj₂ cfg j ≡ freloop → cfg ⊳ setF cfg j free

  ----------------------------------------------------------------------------------
  -- ForkConsistent preservation.  Helper lemmas for the pointwise updates.
  setP-at : ∀ cfg i p → proj₁ (setP cfg i p) i ≡ p
  setP-at cfg i p with i Fin.≟ i
  ... | yes _  = refl
  ... | no ¬q = ⊥-elim (¬q refl)
  setP-≢ : ∀ cfg i p k → ¬ (k ≡ i) → proj₁ (setP cfg i p) k ≡ proj₁ cfg k
  setP-≢ cfg i p k ¬eq with k Fin.≟ i
  ... | yes eq = ⊥-elim (¬eq eq)
  ... | no  _  = refl
  setF-at : ∀ cfg j q → proj₂ (setF cfg j q) j ≡ q
  setF-at cfg j q with j Fin.≟ j
  ... | yes _  = refl
  ... | no ¬q = ⊥-elim (¬q refl)
  setF-≢ : ∀ cfg j q k → ¬ (k ≡ j) → proj₂ (setF cfg j q) k ≡ proj₂ cfg k
  setF-≢ cfg j q k ¬eq with k Fin.≟ j
  ... | yes eq = ⊥-elim (¬eq eq)
  ... | no  _  = refl

  -- a position that holds neither slot can't hold any fork.
  no-hold : ∀ cfg i k → holdsF (proj₁ cfg i) ≡ false → holdsS (proj₁ cfg i) ≡ false
          → phil-holds cfg i k → ⊥
  no-hold cfg i k hf hs (inj₁ (_ , ht)) = case trans (sym hf) ht of λ ()
  no-hold cfg i k hf hs (inj₂ (_ , ht)) = case trans (sym hs) ht of λ ()

  -- phil-holds is insensitive to setF (it reads only proj₁) and to setP away from i.
  ph-setF : ∀ cfg j q i k → phil-holds (setF cfg j q) i k ≡ phil-holds cfg i k
  ph-setF cfg j q i k = refl
  ph-setP-≢ : ∀ cfg i p i′ k → ¬ (i′ ≡ i) → phil-holds (setP cfg i p) i′ k ≡ phil-holds cfg i′ k
  ph-setP-≢ cfg i p i′ k ¬eq =
    cong (λ x → (asymFirst i′ ≡ k × holdsF x ≡ true) ⊎ (asymSecond i′ ≡ k × holdsS x ≡ true))
         (setP-≢ cfg i p i′ ¬eq)

  -- preservation, fork-reloop step (⊳τf): fork j freloop → free, nothing held there.
  cons-pres-τf : ∀ {cfg j} → ForkConsistent cfg → proj₂ cfg j ≡ freloop
               → ForkConsistent (setF cfg j free)
  cons-pres-τf {cfg} {j} fc eq j′ with j′ Fin.≟ j
  ... | yes refl =
          (λ ())
        , (λ ())
        , (λ i h → case proj₂ (proj₂ (fc j)) i h of
                     λ { (inj₁ (_ , ho)) → case trans (sym eq) ho of λ ()
                       ; (inj₂ (_ , hn)) → case trans (sym eq) hn of λ () })
  ... | no ¬eq = fc j′

  -- preservation, phil-reloop step (⊳τp): phil i reloop → think.  proj₂ unchanged;
  -- phil-holds is equivalent before/after (both reloop and think hold nothing).
  cons-pres-τp : ∀ {cfg i} → ForkConsistent cfg → proj₁ cfg i ≡ reloop
               → ForkConsistent (setP cfg i think)
  cons-pres-τp {cfg} {i} fc eq j′ =
      (λ ho → ph← j′       j′ (proj₁ (fc j′) ho))
    , (λ hn → ph← (j′ ⊖1)  j′ (proj₁ (proj₂ (fc j′)) hn))
    , (λ i′ h → proj₂ (proj₂ (fc j′)) i′ (ph→ i′ j′ h))
    where
      ph→ : ∀ i′ k → phil-holds (setP cfg i think) i′ k → phil-holds cfg i′ k
      ph→ i′ k h with i′ Fin.≟ i
      ph→ i′ k (inj₁ (_ , ht)) | yes p = case ht of λ ()
      ph→ i′ k (inj₂ (_ , ht)) | yes p = case ht of λ ()
      ph→ i′ k h               | no ¬e = h
      ph← : ∀ i′ k → phil-holds cfg i′ k → phil-holds (setP cfg i think) i′ k
      ph← i′ k h with i′ Fin.≟ i
      ph← i′ k (inj₁ (_ , ht)) | yes p = case subst (λ z → holdsF z ≡ true) (trans (cong (proj₁ cfg) p) eq) ht of λ ()
      ph← i′ k (inj₂ (_ , ht)) | yes p = case subst (λ z → holdsS z ≡ true) (trans (cong (proj₁ cfg) p) eq) ht of λ ()
      ph← i′ k h               | no ¬e = h

  ----------------------------------------------------------------------------------
  -- Ring facts for the own/nbr analysis (proved natively, no relational import).
  toℕ-⊖1-suc : ∀ (k : Fork) r → toℕ k ≡ suc r → toℕ (k ⊖1) ≡ r
  toℕ-⊖1-suc fzero     r ()
  toℕ-⊖1-suc (fsuc k′) r eq = trans (toℕ-inject₁ k′) (suc-injective eq)

  ⊕1≢ : ∀ (i : Phil) → i ⊕1 ≢ i
  ⊕1≢ i eq with suc (toℕ i) <? suc (suc m)
  ... | yes p = 1+n≢n (trans (sym (toℕ-fromℕ< p)) (cong toℕ eq))
  ... | no ¬p = ¬p (subst (λ z → suc (toℕ z) < suc (suc m)) eq (s≤s (s≤s z≤n)))

  ⊕1-⊖1 : ∀ (i : Phil) → (i ⊕1) ⊖1 ≡ i
  ⊕1-⊖1 i with suc (toℕ i) <? suc (suc m)
  ... | yes p = toℕ-injective (toℕ-⊖1-suc (fromℕ< p) (toℕ i) (toℕ-fromℕ< p))
  ... | no ¬p with ≮⇒≥ ¬p | toℕ<n i
  ...            | s≤s q | s≤s r =
                   toℕ-injective (trans (toℕ-fromℕ< (n<1+n (suc m))) (sym (≤-antisym r q)))

  ----------------------------------------------------------------------------------
  -- Shared consistency helpers for the pick/putsdown preservation cases.
  -- A held fork has a unique holder (mutual exclusion from ForkConsistent).
  unique-holder : ∀ {cfg} → ForkConsistent cfg → ∀ {a b j}
                → phil-holds cfg a j → phil-holds cfg b j → a ≡ b
  unique-holder fc {a}{b}{j} ha hb with proj₂ (proj₂ (fc j)) a ha | proj₂ (proj₂ (fc j)) b hb
  ... | inj₁ (a≡j , _)  | inj₁ (b≡j , _)  = trans a≡j (sym b≡j)
  ... | inj₁ (_ , ho)   | inj₂ (_ , hn)   = ⊥-elim (case trans (sym ho) hn of λ ())
  ... | inj₂ (_ , hn)   | inj₁ (_ , ho)   = ⊥-elim (case trans (sym hn) ho of λ ())
  ... | inj₂ (a≡j′ , _) | inj₂ (b≡j′ , _) = trans a≡j′ (sym b≡j′)

  -- a position whose first/second slot is held does hold that fork.
  holds-first  : ∀ {cfg i} → holdsF (proj₁ cfg i) ≡ true → phil-holds cfg i (asymFirst i)
  holds-first  hf = inj₁ (refl , hf)
  holds-second : ∀ {cfg i} → holdsS (proj₁ cfg i) ≡ true → phil-holds cfg i (asymSecond i)
  holds-second hs = inj₂ (refl , hs)

  -- preservation, putsdown-first step (⊳pd1): phil i down1 → reloop, releases its
  -- first fork (asymFirst i) → freloop.
  cons-pres-pd1 : ∀ {cfg i} → ForkConsistent cfg → proj₁ cfg i ≡ down1
                → ForkConsistent (setF (setP cfg i reloop) (asymFirst i) freloop)
  cons-pres-pd1 {cfg} {i} fc eq j′ with j′ Fin.≟ asymFirst i
  ... | yes p = (λ ()) , (λ ()) , c3
    where
      piF : phil-holds cfg i (asymFirst i)
      piF = holds-first {cfg} {i} (cong holdsF eq)
      c3 : ∀ i′ → phil-holds (setF (setP cfg i reloop) (asymFirst i) freloop) i′ j′
         → (i′ ≡ j′ × freloop ≡ heldOwn) ⊎ (i′ ≡ (j′ ⊖1) × freloop ≡ heldNbr)
      c3 i′ h with i′ Fin.≟ i
      c3 i′ (inj₁ (_ , ht)) | yes q = case ht of λ ()
      c3 i′ (inj₂ (_ , ht)) | yes q = case ht of λ ()
      c3 i′ h               | no ¬q = ⊥-elim (¬q (unique-holder fc h (subst (phil-holds cfg i) (sym p) piF)))
  ... | no ¬e = (λ ho → ph← j′ (proj₁ (fc j′) ho))
              , (λ hn → ph← (j′ ⊖1) (proj₁ (proj₂ (fc j′)) hn))
              , (λ i′ h → proj₂ (proj₂ (fc j′)) i′ (ph→ i′ h))
    where
      ph→ : ∀ i′ → phil-holds (setF (setP cfg i reloop) (asymFirst i) freloop) i′ j′ → phil-holds cfg i′ j′
      ph→ i′ h with i′ Fin.≟ i
      ph→ i′ (inj₁ (_ , ht)) | yes q = case ht of λ ()
      ph→ i′ (inj₂ (_ , ht)) | yes q = case ht of λ ()
      ph→ i′ h               | no ¬q = h
      ph← : ∀ i′ → phil-holds cfg i′ j′ → phil-holds (setF (setP cfg i reloop) (asymFirst i) freloop) i′ j′
      ph← i′ h with i′ Fin.≟ i
      ph← i′ (inj₁ (af≡j′ , _)) | yes q = ⊥-elim (¬e (sym (trans (cong asymFirst (sym q)) af≡j′)))
      ph← i′ (inj₂ (_ , hs))    | yes q = case trans (sym (cong holdsS (trans (cong (proj₁ cfg) q) eq))) hs of λ ()
      ph← i′ h                  | no ¬q = h

  -- a philosopher's two forks are distinct.
  first≢second : ∀ i → asymFirst i ≢ asymSecond i
  first≢second i e with asymForks-Sys i
  ... | inj₁ (af≡i  , as≡i⊕1) = ⊕1≢ i (sym (trans (sym af≡i) (trans e as≡i⊕1)))
  ... | inj₂ (af≡i⊕1 , as≡i ) = ⊕1≢ i (trans (sym af≡i⊕1) (trans e as≡i))

  -- preservation, putsdown-second step (⊳pd2): phil i eat → down1, releases its
  -- second fork (asymSecond i) → freloop; still holds its first fork.
  cons-pres-pd2 : ∀ {cfg i} → ForkConsistent cfg → proj₁ cfg i ≡ eat
                → ForkConsistent (setF (setP cfg i down1) (asymSecond i) freloop)
  cons-pres-pd2 {cfg} {i} fc eq j′ with j′ Fin.≟ asymSecond i
  ... | yes p = (λ ()) , (λ ()) , c3
    where
      piS : phil-holds cfg i (asymSecond i)
      piS = holds-second {cfg} {i} (cong holdsS eq)
      c3 : ∀ i′ → phil-holds (setF (setP cfg i down1) (asymSecond i) freloop) i′ j′
         → (i′ ≡ j′ × freloop ≡ heldOwn) ⊎ (i′ ≡ (j′ ⊖1) × freloop ≡ heldNbr)
      c3 i′ h with i′ Fin.≟ i
      c3 i′ (inj₁ (af≡j′ , _)) | yes q = ⊥-elim (first≢second i (trans (trans (cong asymFirst (sym q)) af≡j′) p))
      c3 i′ (inj₂ (_ , ht))    | yes q = case ht of λ ()
      c3 i′ h                  | no ¬q = ⊥-elim (¬q (unique-holder fc h (subst (phil-holds cfg i) (sym p) piS)))
  ... | no ¬e = (λ ho → ph← j′ (proj₁ (fc j′) ho))
              , (λ hn → ph← (j′ ⊖1) (proj₁ (proj₂ (fc j′)) hn))
              , (λ i′ h → proj₂ (proj₂ (fc j′)) i′ (ph→ i′ h))
    where
      ph→ : ∀ i′ → phil-holds (setF (setP cfg i down1) (asymSecond i) freloop) i′ j′ → phil-holds cfg i′ j′
      ph→ i′ h with i′ Fin.≟ i
      ph→ i′ (inj₁ (af≡j′ , _)) | yes q = inj₁ (af≡j′ , cong holdsF (trans (cong (proj₁ cfg) q) eq))
      ph→ i′ (inj₂ (_ , ht))    | yes q = case ht of λ ()
      ph→ i′ h                  | no ¬q = h
      ph← : ∀ i′ → phil-holds cfg i′ j′ → phil-holds (setF (setP cfg i down1) (asymSecond i) freloop) i′ j′
      ph← i′ h with i′ Fin.≟ i
      ph← i′ (inj₁ (af≡j′ , _)) | yes q = inj₁ (af≡j′ , refl)
      ph← i′ (inj₂ (as≡j′ , _)) | yes q = ⊥-elim (¬e (sym (trans (cong asymSecond (sym q)) as≡j′)))
      ph← i′ h                  | no ¬q = h

  -- a free fork has no holder.
  free-no-holder : ∀ {cfg} → ForkConsistent cfg → ∀ {j} → proj₂ cfg j ≡ free
                 → ∀ a → phil-holds cfg a j → ⊥
  free-no-holder fc {j} fr a h with proj₂ (proj₂ (fc j)) a h
  ... | inj₁ (_ , ho) = case trans (sym fr) ho of λ ()
  ... | inj₂ (_ , hn) = case trans (sym fr) hn of λ ()

  -- preservation, pick-first step (⊳pk1): phil i think → one, acquires its first
  -- fork (asymFirst i): free → ownNbr i (asymFirst i).
  cons-pres-pk1 : ∀ {cfg i} → ForkConsistent cfg → proj₁ cfg i ≡ think
                → proj₂ cfg (asymFirst i) ≡ free
                → ForkConsistent (setF (setP cfg i one) (asymFirst i) (ownNbr i (asymFirst i)))
  cons-pres-pk1 {cfg} {i} fc eq eq2 j′ with j′ Fin.≟ asymFirst i
  ... | no ¬e = (λ ho → ph← j′ (proj₁ (fc j′) ho))
              , (λ hn → ph← (j′ ⊖1) (proj₁ (proj₂ (fc j′)) hn))
              , (λ i′ h → proj₂ (proj₂ (fc j′)) i′ (ph→ i′ h))
    where
      ph→ : ∀ i′ → phil-holds (setF (setP cfg i one) (asymFirst i) (ownNbr i (asymFirst i))) i′ j′ → phil-holds cfg i′ j′
      ph→ i′ h with i′ Fin.≟ i
      ph→ i′ (inj₁ (af≡j′ , _)) | yes q = ⊥-elim (¬e (sym (trans (cong asymFirst (sym q)) af≡j′)))
      ph→ i′ (inj₂ (_ , ht))    | yes q = case ht of λ ()
      ph→ i′ h                  | no ¬q = h
      ph← : ∀ i′ → phil-holds cfg i′ j′ → phil-holds (setF (setP cfg i one) (asymFirst i) (ownNbr i (asymFirst i))) i′ j′
      ph← i′ h with i′ Fin.≟ i
      ph← i′ (inj₁ (_ , hf)) | yes q = case trans (sym (cong holdsF (trans (cong (proj₁ cfg) q) eq))) hf of λ ()
      ph← i′ (inj₂ (_ , hs)) | yes q = case trans (sym (cong holdsS (trans (cong (proj₁ cfg) q) eq))) hs of λ ()
      ph← i′ h               | no ¬q = h
  ... | yes p with asymFirst i Fin.≟ i
  ...   | yes o = (λ _ → holderF) , (λ ()) , c3own
    where
      cfg′ = setF (setP cfg i one) (asymFirst i) (ownNbr i (asymFirst i))
      piF′ : phil-holds cfg′ i (asymFirst i)
      piF′ = holds-first {cfg′} {i} (cong holdsF (setP-at cfg i one))
      holderF : phil-holds cfg′ j′ j′
      holderF = subst (λ z → phil-holds cfg′ z j′) (sym (trans p o)) (subst (phil-holds cfg′ i) (sym p) piF′)
      c3own : ∀ i′ → phil-holds cfg′ i′ j′ → (i′ ≡ j′ × heldOwn ≡ heldOwn) ⊎ (i′ ≡ (j′ ⊖1) × heldOwn ≡ heldNbr)
      c3own i′ h with i′ Fin.≟ i
      ... | yes q = inj₁ (trans q (sym (trans p o)) , refl)
      ... | no ¬q = ⊥-elim (free-no-holder fc (subst (λ z → proj₂ cfg z ≡ free) (sym p) eq2) i′ h)
  ...   | no ¬o = (λ ()) , (λ _ → holderF) , c3nbr
    where
      cfg′ = setF (setP cfg i one) (asymFirst i) (ownNbr i (asymFirst i))
      nbr-F≡ : asymFirst i ≡ i ⊕1
      nbr-F≡ with asymForks-Sys i
      ... | inj₁ (af≡i , _)   = ⊥-elim (¬o af≡i)
      ... | inj₂ (af≡i⊕1 , _) = af≡i⊕1
      jp : j′ ≡ i ⊕1
      jp = trans p nbr-F≡
      j′⊖1≡i : (j′ ⊖1) ≡ i
      j′⊖1≡i = trans (cong (λ z → z ⊖1) jp) (⊕1-⊖1 i)
      piF′ : phil-holds cfg′ i (asymFirst i)
      piF′ = holds-first {cfg′} {i} (cong holdsF (setP-at cfg i one))
      holderF : phil-holds cfg′ (j′ ⊖1) j′
      holderF = subst (λ z → phil-holds cfg′ z j′) (sym j′⊖1≡i) (subst (phil-holds cfg′ i) (sym p) piF′)
      c3nbr : ∀ i′ → phil-holds cfg′ i′ j′ → (i′ ≡ j′ × heldNbr ≡ heldOwn) ⊎ (i′ ≡ (j′ ⊖1) × heldNbr ≡ heldNbr)
      c3nbr i′ h with i′ Fin.≟ i
      ... | yes q = inj₂ (trans q (sym j′⊖1≡i) , refl)
      ... | no ¬q = ⊥-elim (free-no-holder fc (subst (λ z → proj₂ cfg z ≡ free) (sym p) eq2) i′ h)

  -- preservation, pick-second step (⊳pk2): phil i one → eat, acquires its second
  -- fork (asymSecond i): free → ownNbr i (asymSecond i); still holds its first fork.
  cons-pres-pk2 : ∀ {cfg i} → ForkConsistent cfg → proj₁ cfg i ≡ one
                → proj₂ cfg (asymSecond i) ≡ free
                → ForkConsistent (setF (setP cfg i eat) (asymSecond i) (ownNbr i (asymSecond i)))
  cons-pres-pk2 {cfg} {i} fc eq eq2 j′ with j′ Fin.≟ asymSecond i
  ... | no ¬e = (λ ho → ph← j′ (proj₁ (fc j′) ho))
              , (λ hn → ph← (j′ ⊖1) (proj₁ (proj₂ (fc j′)) hn))
              , (λ i′ h → proj₂ (proj₂ (fc j′)) i′ (ph→ i′ h))
    where
      ph→ : ∀ i′ → phil-holds (setF (setP cfg i eat) (asymSecond i) (ownNbr i (asymSecond i))) i′ j′ → phil-holds cfg i′ j′
      ph→ i′ h with i′ Fin.≟ i
      ph→ i′ (inj₁ (af≡j′ , _)) | yes q = inj₁ (af≡j′ , cong holdsF (trans (cong (proj₁ cfg) q) eq))
      ph→ i′ (inj₂ (as≡j′ , _)) | yes q = ⊥-elim (¬e (sym (trans (cong asymSecond (sym q)) as≡j′)))
      ph→ i′ h                  | no ¬q = h
      ph← : ∀ i′ → phil-holds cfg i′ j′ → phil-holds (setF (setP cfg i eat) (asymSecond i) (ownNbr i (asymSecond i))) i′ j′
      ph← i′ h with i′ Fin.≟ i
      ph← i′ (inj₁ (af≡j′ , _)) | yes q = inj₁ (af≡j′ , refl)
      ph← i′ (inj₂ (as≡j′ , _)) | yes q = ⊥-elim (¬e (sym (trans (cong asymSecond (sym q)) as≡j′)))
      ph← i′ h                  | no ¬q = h
  ... | yes p with asymSecond i Fin.≟ i
  ...   | yes o = (λ _ → holderS) , (λ ()) , c3own
    where
      cfg′ = setF (setP cfg i eat) (asymSecond i) (ownNbr i (asymSecond i))
      piS′ : phil-holds cfg′ i (asymSecond i)
      piS′ = holds-second {cfg′} {i} (cong holdsS (setP-at cfg i eat))
      holderS : phil-holds cfg′ j′ j′
      holderS = subst (λ z → phil-holds cfg′ z j′) (sym (trans p o)) (subst (phil-holds cfg′ i) (sym p) piS′)
      c3own : ∀ i′ → phil-holds cfg′ i′ j′ → (i′ ≡ j′ × heldOwn ≡ heldOwn) ⊎ (i′ ≡ (j′ ⊖1) × heldOwn ≡ heldNbr)
      c3own i′ h with i′ Fin.≟ i
      ... | yes q = inj₁ (trans q (sym (trans p o)) , refl)
      ... | no ¬q = ⊥-elim (free-no-holder fc (subst (λ z → proj₂ cfg z ≡ free) (sym p) eq2) i′ h)
  ...   | no ¬o = (λ ()) , (λ _ → holderS) , c3nbr
    where
      cfg′ = setF (setP cfg i eat) (asymSecond i) (ownNbr i (asymSecond i))
      nbr-S≡ : asymSecond i ≡ i ⊕1
      nbr-S≡ with asymForks-Sys i
      ... | inj₁ (_ , as≡i⊕1) = as≡i⊕1
      ... | inj₂ (_ , as≡i)   = ⊥-elim (¬o as≡i)
      jp : j′ ≡ i ⊕1
      jp = trans p nbr-S≡
      j′⊖1≡i : (j′ ⊖1) ≡ i
      j′⊖1≡i = trans (cong (λ z → z ⊖1) jp) (⊕1-⊖1 i)
      piS′ : phil-holds cfg′ i (asymSecond i)
      piS′ = holds-second {cfg′} {i} (cong holdsS (setP-at cfg i eat))
      holderS : phil-holds cfg′ (j′ ⊖1) j′
      holderS = subst (λ z → phil-holds cfg′ z j′) (sym j′⊖1≡i) (subst (phil-holds cfg′ i) (sym p) piS′)
      c3nbr : ∀ i′ → phil-holds cfg′ i′ j′ → (i′ ≡ j′ × heldNbr ≡ heldOwn) ⊎ (i′ ≡ (j′ ⊖1) × heldNbr ≡ heldNbr)
      c3nbr i′ h with i′ Fin.≟ i
      ... | yes q = inj₂ (trans q (sym j′⊖1≡i) , refl)
      ... | no ¬q = ⊥-elim (free-no-holder fc (subst (λ z → proj₂ cfg z ≡ free) (sym p) eq2) i′ h)

  ----------------------------------------------------------------------------------
  -- ForkConsistent preservation under any config transition.
  cons-pres : ∀ {cfg cfg′} → ForkConsistent cfg → cfg ⊳ cfg′ → ForkConsistent cfg′
  cons-pres fc (⊳pk1 i e1 e2) = cons-pres-pk1 fc e1 e2
  cons-pres fc (⊳pk2 i e1 e2) = cons-pres-pk2 fc e1 e2
  cons-pres fc (⊳pd2 i e1)    = cons-pres-pd2 fc e1
  cons-pres fc (⊳pd1 i e1)    = cons-pres-pd1 fc e1
  cons-pres fc (⊳τp  i e1)    = cons-pres-τp  fc e1
  cons-pres fc (⊳τf  j e1)    = cons-pres-τf  fc e1

  ----------------------------------------------------------------------------------
  -- ════ sysState → ⊳ STEP-INVERSION ════
  -- Event-indexed refined per-component steps: a component step exposes the DP event
  -- (or nothing for the τ loop-back) plus the position transition.
  DPEvent : Set₁
  DPEvent = Event {E = DP} {I = ExtI DP}
  evt : DP (⊤ {lzero}) → Maybe DPEvent
  evt e = just (evLabel (⊤ {lzero}) e tt)
  evOf : ∀ {ℓr} {R : Set ℓr} → Label {E = DP} {I = ExtI DP} R → Maybe DPEvent
  evOf (ev (evl e)) = just e
  evOf (ev (√ _))   = nothing
  evOf τ            = nothing

  data PhilTr (f s : Phil → Fork) (i : Phil) : PhilPos → PhilPos → Maybe DPEvent → Set where
    tp-pk1 : PhilTr f s i think  one    (evt (picks i (f i)))
    tp-pk2 : PhilTr f s i one    eat    (evt (picks i (s i)))
    tp-pd2 : PhilTr f s i eat    down1  (evt (putsdown i (s i)))
    tp-pd1 : PhilTr f s i down1  reloop (evt (putsdown i (f i)))
    tp-lp  : PhilTr f s i reloop think  nothing
  data ForkTr (j : Fork) : ForkPos → ForkPos → Maybe DPEvent → Set where
    tf-own : ForkTr j free    heldOwn (evt (picks j j))
    tf-nbr : ForkTr j free    heldNbr (evt (picks (j ⊖1) j))
    tf-po  : ForkTr j heldOwn freloop (evt (putsdown j j))
    tf-pn  : ForkTr j heldNbr freloop (evt (putsdown (j ⊖1) j))
    tf-lp  : ForkTr j freloop free    nothing

  phil-step′ : ∀ {f s i} (p : PhilPos) {l t′} → philSt f s i p ─[ l ]─► t′
             → Σ[ p′ ∈ PhilPos ] (t′ ≡ philSt f s i p′ × PhilTr f s i p p′ (evOf l))
  phil-step′ think (sRet eq) = case eq of λ ()
  phil-step′ think (sSil eq) = case eq of λ ()
  phil-step′ think (sTau refl br) = case br of λ ()
  phil-step′ {f}{s}{i} think (sVis {at = at} refl br) with DP-AnyTypes-≟ (⊤ {lzero} , picks i (f i)) at
  ... | yes refl = one , sym (just-injective br) , tp-pk1
  ... | no ¬p = case br of λ ()
  phil-step′ one (sRet eq) = case eq of λ ()
  phil-step′ one (sSil eq) = case eq of λ ()
  phil-step′ one (sTau refl br) = case br of λ ()
  phil-step′ {f}{s}{i} one (sVis {at = at} refl br) with DP-AnyTypes-≟ (⊤ {lzero} , picks i (s i)) at
  ... | yes refl = eat , sym (just-injective br) , tp-pk2
  ... | no ¬p = case br of λ ()
  phil-step′ eat (sRet eq) = case eq of λ ()
  phil-step′ eat (sSil eq) = case eq of λ ()
  phil-step′ eat (sTau refl br) = case br of λ ()
  phil-step′ {f}{s}{i} eat (sVis {at = at} refl br) with DP-AnyTypes-≟ (⊤ {lzero} , putsdown i (s i)) at
  ... | yes refl = down1 , sym (just-injective br) , tp-pd2
  ... | no ¬p = case br of λ ()
  phil-step′ down1 (sRet eq) = case eq of λ ()
  phil-step′ down1 (sSil eq) = case eq of λ ()
  phil-step′ down1 (sTau refl br) = case br of λ ()
  phil-step′ {f}{s}{i} down1 (sVis {at = at} refl br) with DP-AnyTypes-≟ (⊤ {lzero} , putsdown i (f i)) at
  ... | yes refl = reloop , sym (just-injective br) , tp-pd1
  ... | no ¬p = case br of λ ()
  phil-step′ reloop (sSil refl) = think , refl , tp-lp
  phil-step′ reloop (sRet eq) = case eq of λ ()
  phil-step′ reloop (sTau eq br) = case eq of λ ()
  phil-step′ reloop (sVis eq br) = case eq of λ ()

  fork-step′ : ∀ {j} (p : ForkPos) {l t′} → forkSt j p ─[ l ]─► t′
             → Σ[ p′ ∈ ForkPos ] (t′ ≡ forkSt j p′ × ForkTr j p p′ (evOf l))
  fork-step′ free (sRet eq) = case eq of λ ()
  fork-step′ free (sSil eq) = case eq of λ ()
  fork-step′ {j} free (sTau {i = i} {a = a} refl br) = case trans (sym (st-free j i a)) br of λ ()
  fork-step′ {j} free (sVis {at = at} refl br)
    with DP-AnyTypes-≟ (⊤ {lzero} , picks j j) at | DP-AnyTypes-≟ (⊤ {lzero} , picks (j ⊖1) j) at
  ... | yes refl | no ¬q = heldOwn , sym (just-injective br) , tf-own
  ... | yes refl | yes p = ⊥-elim (⊖≢ j (cong philOf p))
  ... | no ¬p | yes refl = heldNbr , sym (just-injective br) , tf-nbr
  ... | no ¬p | no ¬q = case br of λ ()
  fork-step′ heldOwn (sRet eq) = case eq of λ ()
  fork-step′ heldOwn (sSil eq) = case eq of λ ()
  fork-step′ heldOwn (sTau refl br) = case br of λ ()
  fork-step′ {j} heldOwn (sVis {at = at} refl br) with DP-AnyTypes-≟ (⊤ {lzero} , putsdown j j) at
  ... | yes refl = freloop , sym (just-injective br) , tf-po
  ... | no ¬p = case br of λ ()
  fork-step′ heldNbr (sRet eq) = case eq of λ ()
  fork-step′ heldNbr (sSil eq) = case eq of λ ()
  fork-step′ heldNbr (sTau refl br) = case br of λ ()
  fork-step′ {j} heldNbr (sVis {at = at} refl br) with DP-AnyTypes-≟ (⊤ {lzero} , putsdown (j ⊖1) j) at
  ... | yes refl = freloop , sym (just-injective br) , tf-pn
  ... | no ¬p = case br of λ ()
  fork-step′ freloop (sSil refl) = free , refl , tf-lp
  fork-step′ freloop (sRet eq) = case eq of λ ()
  fork-step′ freloop (sTau eq br) = case eq of λ ()
  fork-step′ freloop (sVis eq br) = case eq of λ ()

  -- Fold congruence: componentwise position equality ⇒ sysState equality (needed
  -- because setP/setF projections are stuck on the green-slime, so t′ ≡ sysState cfg′
  -- only holds propositionally).
  concatMap-cong : ∀ {f g : Phil → List (Comp DP ⊥)} (xs : List Phil)
                 → (∀ i → f i ≡ g i) → concatMap f xs ≡ concatMap g xs
  concatMap-cong []       e = refl
  concatMap-cong (x ∷ xs) e = cong₂ _++_ (e x) (concatMap-cong xs e)

  philComp*-cong : ∀ {cfg cfg′} i → proj₁ cfg i ≡ proj₁ cfg′ i
                 → philComp* asymFirst asymSecond cfg i ≡ philComp* asymFirst asymSecond cfg′ i
  philComp*-cong i e = cong (λ p → comp (AlphaP i) (philSt asymFirst asymSecond i p)) e
  forkComp*-cong : ∀ {cfg cfg′} j → proj₂ cfg j ≡ proj₂ cfg′ j
                 → forkComp* cfg j ≡ forkComp* cfg′ j
  forkComp*-cong j e = cong (λ p → comp (AlphaF j) (forkSt j p)) e

  -- NOTE: a homogeneous fold congruence `sysState cfg ≡ sysState cfg′` is NOT statable:
  -- RetOf⁺ (…cfg) is stuck on the abstract `concatMap`/`tabulate` over `allPhils`, so the
  -- two PTree types are not definitionally equal (the n=2 file avoids this with a concrete
  -- tuple config; the general-n proof needs the legacy SystemP `ii-c` source-carrier
  -- recursion to keep the carrier type fixed).  The `*-cong` helpers above are the
  -- per-component building blocks for that.

  ----------------------------------------------------------------------------------
  -- Source-carrier discipline: stay at the FIXED carrier RetOf⁺ c xs (never rebuild
  -- sysState cfg′).  fold-step = FoldReach closed under a single LTS step, by recursion
  -- on the chain (generic over xs) using the binary αpar inversions + CompReachI.psing.
  fold-step : ∀ {c xs} {rc : CompReachI c} {rcs : All CompReachI xs} {t l t′}
            → FoldReach c xs rc rcs t → t ─[ l ]─► t′ → FoldReach c xs rc rcs t′
  fold-step {rc = rc} (fr-nil p) st =
    let (p′ , eq) = CompReachI.psing rc st in subst (FoldReach _ [] rc []) (sym eq) (fr-nil p′)
  fold-step {c} {d ∷ ds} {rc} (fr-cons p tail) (sRet feq) with αpar-√-step-inv feq
  ... | v√ peq _ = ⊥-elim (CompReachI.pno-ret rc p peq)
  fold-step {c} {d ∷ ds} {rc} (fr-cons p tail) (sSil feq) with αpar-τ-step-inv (sSil feq)
  ... | inj₁ (P′ , pτ , refl) =
          let (p′ , eq) = CompReachI.psing rc pτ
          in subst (λ z → FoldReach c (d ∷ ds) rc _ (z ⟦ Comp.alpha c ∥ unionα (d ∷ ds) ⟧ _)) (sym eq) (fr-cons p′ tail)
  ... | inj₂ (Q′ , qτ , refl) = fr-cons p (fold-step tail qτ)
  fold-step {c} {d ∷ ds} {rc} (fr-cons p tail) (sTau feq br) with αpar-τ-step-inv (sTau feq br)
  ... | inj₁ (P′ , pτ , refl) =
          let (p′ , eq) = CompReachI.psing rc pτ
          in subst (λ z → FoldReach c (d ∷ ds) rc _ (z ⟦ Comp.alpha c ∥ unionα (d ∷ ds) ⟧ _)) (sym eq) (fr-cons p′ tail)
  ... | inj₂ (Q′ , qτ , refl) = fr-cons p (fold-step tail qτ)
  fold-step {c} {d ∷ ds} {rc} (fr-cons p tail) (sVis feq br) with αpar-vis-step-inv feq br
  ... | vSync _ _ pst qst =
          let (p′ , eq) = CompReachI.psing rc pst
          in subst (λ z → FoldReach c (d ∷ ds) rc _ (z ⟦ Comp.alpha c ∥ unionα (d ∷ ds) ⟧ _)) (sym eq) (fr-cons p′ (fold-step tail qst))
  ... | vSoloL _ _ pst =
          let (p′ , eq) = CompReachI.psing rc pst
          in subst (λ z → FoldReach c (d ∷ ds) rc _ (z ⟦ Comp.alpha c ∥ unionα (d ∷ ds) ⟧ _)) (sym eq) (fr-cons p′ tail)
  ... | vSoloR _ _ qst = fr-cons p (fold-step tail qst)

  ----------------------------------------------------------------------------------
  -- Config extraction via INDEX-PAIRED recursion (the legacy ii-c move).  Recurse the
  -- FoldReach chain in lockstep with the index list S (head index separated), reading
  -- each (phil i, fork i) position into a Config accumulator.  The recursion is on S;
  -- applied to the abstract `drop 1 allPhils` it is a valid (stuck) term.
  pairF : Phil → List (Comp DP ⊥)
  pairF i = philComp asymFirst asymSecond i ∷ forkComp i ∷ []

  extractPairs : (i : Phil) (S : List Phil) {t : PTree DP (ExtI DP) (RetOf⁺ (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S))}
               → FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S)
                           (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest S) t
               → Config → Config
  extractPairs i []       (fr-cons p (fr-nil q))       acc = setF (setP acc i p) i q
  extractPairs i (j ∷ S′) (fr-cons p (fr-cons q rest)) acc = extractPairs j S′ rest (setF (setP acc i p) i q)

  sysCfg : ∀ {t} → FoldReach (comps0 asymFirst asymSecond) (compsRest asymFirst asymSecond)
                             (philReachI asymFirst asymSecond fzero) allComps t → Config
  sysCfg fr = extractPairs fzero (drop 1 allPhils) fr cfg0

  ----------------------------------------------------------------------------------
  -- ForkConsistent respects POINTWISE config equality (sysCfg builds setP/setF
  -- functions, never definitionally cfg0, so reach-cons must transport up to ≐).
  phil-holds-cong : ∀ {cfg cfg′} → (∀ i → proj₁ cfg i ≡ proj₁ cfg′ i)
                  → ∀ i j → phil-holds cfg i j ≡ phil-holds cfg′ i j
  phil-holds-cong ph i j =
    cong (λ p → (asymFirst i ≡ j × holdsF p ≡ true) ⊎ (asymSecond i ≡ j × holdsS p ≡ true)) (ph i)

  FC-cong : ∀ {cfg cfg′} → (∀ i → proj₁ cfg i ≡ proj₁ cfg′ i) → (∀ j → proj₂ cfg j ≡ proj₂ cfg′ j)
          → ForkConsistent cfg → ForkConsistent cfg′
  FC-cong {cfg} {cfg′} ph pf fc j = c1 , c2 , c3
    where
      c1 : proj₂ cfg′ j ≡ heldOwn → phil-holds cfg′ j j
      c1 ho = subst (λ (S : Set) → S) (phil-holds-cong {cfg} {cfg′} ph j j) (proj₁ (fc j) (trans (pf j) ho))
      c2 : proj₂ cfg′ j ≡ heldNbr → phil-holds cfg′ (j ⊖1) j
      c2 hn = subst (λ (S : Set) → S) (phil-holds-cong {cfg} {cfg′} ph (j ⊖1) j) (proj₁ (proj₂ (fc j)) (trans (pf j) hn))
      c3 : ∀ i → phil-holds cfg′ i j → (i ≡ j × proj₂ cfg′ j ≡ heldOwn) ⊎ (i ≡ (j ⊖1) × proj₂ cfg′ j ≡ heldNbr)
      c3 i h with proj₂ (proj₂ (fc j)) i (subst (λ (S : Set) → S) (sym (phil-holds-cong {cfg} {cfg′} ph i j)) h)
      ... | inj₁ (e , ho) = inj₁ (e , trans (sym (pf j)) ho)
      ... | inj₂ (e , hn) = inj₂ (e , trans (sym (pf j)) hn)

  ----------------------------------------------------------------------------------
  -- ════ step-⊳ : a fold step is a ⊳ on the extracted config ════
  -- Sub-piece 1: allPhils is duplicate-free (needed so extractPairs's later setP/setF
  -- don't clobber earlier indices).  Bridge toList∘Vec.tabulate ≡ List.tabulate, then
  -- reuse stdlib `allFin⁺`.
  toList-tab : ∀ {ℓ} {A : Set ℓ} {k} (f : Fin k → A) → VB.toList (VB.tabulate f) ≡ LB.tabulate f
  toList-tab {k = zero}  f = refl
  toList-tab {k = suc k} f = cong (f fzero ∷_) (toList-tab (λ x → f (fsuc x)))

  allPhils-unique : Unique allPhils
  allPhils-unique = subst Unique (sym (toList-tab (λ (i : Phil) → i))) (allFin⁺ n)

  -- Sub-piece 2: extraction correctness.  `ep-*-other`: extractPairs leaves proj₁/proj₂
  -- unchanged at indices outside {i}∪S.  `ep-*-head`: it reads the head position at i.
  headPhilPos : ∀ {i S t}
              → FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S)
                          (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest S) t → PhilPos
  headPhilPos (fr-cons p _) = p
  headForkPos : ∀ (i : Phil) (S : List Phil) {t}
              → FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S)
                          (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest S) t → ForkPos
  headForkPos i []       (fr-cons _ (fr-nil q))    = q
  headForkPos i (j ∷ S′) (fr-cons _ (fr-cons q _)) = q

  ep-phil-other : ∀ (i : Phil) (S : List Phil) {t}
                    (fr : FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S)
                                    (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest S) t)
                    (acc : Config) (k : Phil)
                → All (λ x → k ≢ x) (i ∷ S) → proj₁ (extractPairs i S fr acc) k ≡ proj₁ acc k
  ep-phil-other i []       (fr-cons p (fr-nil q))     acc k (k≢i ∷ _)    = setP-≢ acc i p k k≢i
  ep-phil-other i (j ∷ S′) (fr-cons p (fr-cons q rest)) acc k (k≢i ∷ aS) =
    trans (ep-phil-other j S′ rest (setF (setP acc i p) i q) k aS) (setP-≢ acc i p k k≢i)

  ep-fork-other : ∀ (i : Phil) (S : List Phil) {t}
                    (fr : FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S)
                                    (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest S) t)
                    (acc : Config) (k : Fork)
                → All (λ x → k ≢ x) (i ∷ S) → proj₂ (extractPairs i S fr acc) k ≡ proj₂ acc k
  ep-fork-other i []       (fr-cons p (fr-nil q))     acc k (k≢i ∷ _)    = setF-≢ (setP acc i p) i q k k≢i
  ep-fork-other i (j ∷ S′) (fr-cons p (fr-cons q rest)) acc k (k≢i ∷ aS) =
    trans (ep-fork-other j S′ rest (setF (setP acc i p) i q) k aS) (setF-≢ (setP acc i p) i q k k≢i)

  ep-phil-head : ∀ (i : Phil) (S : List Phil) {t}
                   (fr : FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S)
                                   (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest S) t)
                   (acc : Config)
               → All (λ x → i ≢ x) S → proj₁ (extractPairs i S fr acc) i ≡ headPhilPos fr
  ep-phil-head i []       (fr-cons p (fr-nil q))     acc _  = setP-at acc i p
  ep-phil-head i (j ∷ S′) (fr-cons p (fr-cons q rest)) acc aS =
    trans (ep-phil-other j S′ rest (setF (setP acc i p) i q) i aS) (setP-at acc i p)

  ep-fork-head : ∀ (i : Phil) (S : List Phil) {t}
                   (fr : FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S)
                                   (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest S) t)
                   (acc : Config)
               → All (λ x → i ≢ x) S → proj₂ (extractPairs i S fr acc) i ≡ headForkPos i S fr
  ep-fork-head i []       (fr-cons p (fr-nil q))     acc _  = setF-at (setP acc i p) i q
  ep-fork-head i (j ∷ S′) (fr-cons p (fr-cons q rest)) acc aS =
    trans (ep-fork-other j S′ rest (setF (setP acc i p) i q) i aS) (setF-at (setP acc i p) i q)

  -- Sub-piece 3a: accumulator irrelevance.  extractPairs's proj₁ at k depends on acc only
  -- through indices ≢ bad (so changing the head position ⇔ changing acc at i is local).
  setP-ag : ∀ {acc acc′ : Config} (i : Phil) (p : PhilPos) (bad : Phil)
          → (∀ x → ¬ (x ≡ bad) → proj₁ acc x ≡ proj₁ acc′ x)
          → ∀ x → ¬ (x ≡ bad) → proj₁ (setP acc i p) x ≡ proj₁ (setP acc′ i p) x
  setP-ag i p bad ag x x≢bad with x Fin.≟ i
  ... | yes _ = refl
  ... | no _  = ag x x≢bad

  ep-acc-phil : ∀ (i : Phil) (S : List Phil) {t}
                  (fr : FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S)
                                  (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest S) t)
                  (acc acc′ : Config) (bad k : Phil)
              → ¬ (k ≡ bad) → (∀ x → ¬ (x ≡ bad) → proj₁ acc x ≡ proj₁ acc′ x)
              → proj₁ (extractPairs i S fr acc) k ≡ proj₁ (extractPairs i S fr acc′) k
  ep-acc-phil i []       (fr-cons p (fr-nil q))     acc acc′ bad k k≢bad ag with k Fin.≟ i
  ... | yes _ = refl
  ... | no _  = ag k k≢bad
  ep-acc-phil i (j ∷ S′) (fr-cons p (fr-cons q rest)) acc acc′ bad k k≢bad ag =
    ep-acc-phil j S′ rest (setF (setP acc i p) i q) (setF (setP acc′ i p) i q) bad k k≢bad
                (setP-ag {acc} {acc′} i p bad ag)

  -- fork analogue of accumulator irrelevance.
  setF-ag : ∀ {acc acc′ : Config} (i : Fork) (q : ForkPos) (bad : Fork)
          → (∀ x → ¬ (x ≡ bad) → proj₂ acc x ≡ proj₂ acc′ x)
          → ∀ x → ¬ (x ≡ bad) → proj₂ (setF acc i q) x ≡ proj₂ (setF acc′ i q) x
  setF-ag i q bad ag x x≢bad with x Fin.≟ i
  ... | yes _ = refl
  ... | no _  = ag x x≢bad

  ep-acc-fork : ∀ (i : Phil) (S : List Phil) {t}
                  (fr : FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S)
                                  (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest S) t)
                  (acc acc′ : Config) (bad k : Fork)
              → ¬ (k ≡ bad) → (∀ x → ¬ (x ≡ bad) → proj₂ acc x ≡ proj₂ acc′ x)
              → proj₂ (extractPairs i S fr acc) k ≡ proj₂ (extractPairs i S fr acc′) k
  ep-acc-fork i []       (fr-cons p (fr-nil q))     acc acc′ bad k k≢bad ag with k Fin.≟ i
  ... | yes _ = refl
  ... | no _  = ag k k≢bad
  ep-acc-fork i (j ∷ S′) (fr-cons p (fr-cons q rest)) acc acc′ bad k k≢bad ag =
    ep-acc-fork j S′ rest (setF (setP acc i p) i q) (setF (setP acc′ i p) i q) bad k k≢bad
                (setF-ag {setP acc i p} {setP acc′ i p} i q bad ag)

  -- Sub-piece 3b: head commutations.  Changing the head phil position ⇔ setP on the
  -- extracted config (pointwise).  Helpers first.
  setF-full-ag : ∀ {acc acc′ : Config} (i : Fork) (q : ForkPos)
               → (∀ x → proj₂ acc x ≡ proj₂ acc′ x)
               → ∀ x → proj₂ (setF acc i q) x ≡ proj₂ (setF acc′ i q) x
  setF-full-ag i q ag x with x Fin.≟ i
  ... | yes _ = refl
  ... | no _  = ag x

  ep-acc-fork-full : ∀ (i : Phil) (S : List Phil) {t}
                       (fr : FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S)
                                       (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest S) t)
                       (acc acc′ : Config)
                   → (∀ x → proj₂ acc x ≡ proj₂ acc′ x)
                   → ∀ k → proj₂ (extractPairs i S fr acc) k ≡ proj₂ (extractPairs i S fr acc′) k
  ep-acc-fork-full i []       (fr-cons p (fr-nil q))     acc acc′ ag k with k Fin.≟ i
  ... | yes _ = refl
  ... | no _  = ag k
  ep-acc-fork-full i (j ∷ S′) (fr-cons p (fr-cons q rest)) acc acc′ ag k =
    ep-acc-fork-full j S′ rest (setF (setP acc i p) i q) (setF (setP acc′ i p) i q)
                     (setF-full-ag {setP acc i p} {setP acc′ i p} i q ag) k

  ep-head-irrel-phil : ∀ (i : Phil) (S : List Phil) (p p′ : PhilPos) {ts}
                         (tail : FoldReach (forkComp i) (concatMap pairF S) (forkReachI i) (allRest S) ts)
                         (acc : Config) (k : Phil) → ¬ (k ≡ i)
                     → proj₁ (extractPairs i S (fr-cons p′ tail) acc) k ≡ proj₁ (extractPairs i S (fr-cons p tail) acc) k
  ep-head-irrel-phil i []       p p′ (fr-nil q)      acc k k≢i =
    trans (setP-≢ acc i p′ k k≢i) (sym (setP-≢ acc i p k k≢i))
  ep-head-irrel-phil i (j ∷ S′) p p′ (fr-cons q rest) acc k k≢i =
    ep-acc-phil j S′ rest (setF (setP acc i p′) i q) (setF (setP acc i p) i q) i k k≢i
                (λ x x≢i → trans (setP-≢ acc i p′ x x≢i) (sym (setP-≢ acc i p x x≢i)))

  commute-phil-1 : ∀ (i : Phil) (S : List Phil) (p p′ : PhilPos) {ts}
                     (tail : FoldReach (forkComp i) (concatMap pairF S) (forkReachI i) (allRest S) ts)
                     (acc : Config) (k : Phil) → All (λ x → i ≢ x) S
                 → proj₁ (extractPairs i S (fr-cons p′ tail) acc) k
                 ≡ proj₁ (setP (extractPairs i S (fr-cons p tail) acc) i p′) k
  commute-phil-1 i S p p′ tail acc k aS with k Fin.≟ i
  ... | yes q = trans (cong (λ z → proj₁ (extractPairs i S (fr-cons p′ tail) acc) z) q)
                      (ep-phil-head i S (fr-cons p′ tail) acc aS)
  ... | no ¬e = ep-head-irrel-phil i S p p′ tail acc k ¬e

  commute-phil-2 : ∀ (i : Phil) (S : List Phil) (p p′ : PhilPos) {ts}
                     (tail : FoldReach (forkComp i) (concatMap pairF S) (forkReachI i) (allRest S) ts)
                     (acc : Config) (k : Fork)
                 → proj₂ (extractPairs i S (fr-cons p′ tail) acc) k
                 ≡ proj₂ (setP (extractPairs i S (fr-cons p tail) acc) i p′) k
  commute-phil-2 i []       p p′ (fr-nil q)      acc k = refl
  commute-phil-2 i (j ∷ S′) p p′ (fr-cons q rest) acc k =
    ep-acc-fork-full j S′ rest (setF (setP acc i p′) i q) (setF (setP acc i p) i q) (λ x → refl) k

  -- proj₁ full-agreement engine (mirror of ep-acc-fork-full), for the fork commutations.
  setP-full-ag : ∀ {acc acc′ : Config} (i : Phil) (p : PhilPos)
               → (∀ x → proj₁ acc x ≡ proj₁ acc′ x)
               → ∀ x → proj₁ (setP acc i p) x ≡ proj₁ (setP acc′ i p) x
  setP-full-ag i p ag x with x Fin.≟ i
  ... | yes _ = refl
  ... | no _  = ag x

  ep-acc-phil-full : ∀ (i : Phil) (S : List Phil) {t}
                       (fr : FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S)
                                       (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest S) t)
                       (acc acc′ : Config)
                   → (∀ x → proj₁ acc x ≡ proj₁ acc′ x)
                   → ∀ k → proj₁ (extractPairs i S fr acc) k ≡ proj₁ (extractPairs i S fr acc′) k
  ep-acc-phil-full i []       (fr-cons p (fr-nil q))     acc acc′ ag k with k Fin.≟ i
  ... | yes _ = refl
  ... | no _  = ag k
  ep-acc-phil-full i (j ∷ S′) (fr-cons p (fr-cons q rest)) acc acc′ ag k =
    ep-acc-phil-full j S′ rest (setF (setP acc i p) i q) (setF (setP acc′ i p) i q)
                     (setP-full-ag {acc} {acc′} i p ag) k

  -- Sub-piece 3b (forks): changing the fork-i (2nd component) position ⇔ setF on the
  -- extracted config (pointwise).  Split by S (concrete structures; no chHead needed).
  commute-fork-nil-1 : ∀ (i : Phil) (p : PhilPos) (q q′ : ForkPos) (acc : Config) (k : Phil)
                     → proj₁ (extractPairs i [] (fr-cons p (fr-nil q′)) acc) k
                     ≡ proj₁ (setF (extractPairs i [] (fr-cons p (fr-nil q)) acc) i q′) k
  commute-fork-nil-1 i p q q′ acc k = refl

  commute-fork-nil-2 : ∀ (i : Phil) (p : PhilPos) (q q′ : ForkPos) (acc : Config) (k : Fork)
                     → proj₂ (extractPairs i [] (fr-cons p (fr-nil q′)) acc) k
                     ≡ proj₂ (setF (extractPairs i [] (fr-cons p (fr-nil q)) acc) i q′) k
  commute-fork-nil-2 i p q q′ acc k with k Fin.≟ i
  ... | yes _ = refl
  ... | no _  = refl

  commute-fork-cons-1 : ∀ (i j : Phil) (S′ : List Phil) (p : PhilPos) (q q′ : ForkPos) {ts}
                          (rest : FoldReach (philComp asymFirst asymSecond j) (forkComp j ∷ concatMap pairF S′)
                                            (philReachI asymFirst asymSecond j) (forkReachI j ∷ allRest S′) ts)
                          (acc : Config) (k : Phil)
                      → proj₁ (extractPairs i (j ∷ S′) (fr-cons p (fr-cons q′ rest)) acc) k
                      ≡ proj₁ (setF (extractPairs i (j ∷ S′) (fr-cons p (fr-cons q rest)) acc) i q′) k
  commute-fork-cons-1 i j S′ p q q′ rest acc k =
    ep-acc-phil-full j S′ rest (setF (setP acc i p) i q′) (setF (setP acc i p) i q) (λ x → refl) k

  commute-fork-cons-2 : ∀ (i j : Phil) (S′ : List Phil) (p : PhilPos) (q q′ : ForkPos) {ts}
                          (rest : FoldReach (philComp asymFirst asymSecond j) (forkComp j ∷ concatMap pairF S′)
                                            (philReachI asymFirst asymSecond j) (forkReachI j ∷ allRest S′) ts)
                          (acc : Config) (k : Fork)
                      → All (λ x → i ≢ x) (j ∷ S′)
                      → proj₂ (extractPairs i (j ∷ S′) (fr-cons p (fr-cons q′ rest)) acc) k
                      ≡ proj₂ (setF (extractPairs i (j ∷ S′) (fr-cons p (fr-cons q rest)) acc) i q′) k
  commute-fork-cons-2 i j S′ p q q′ rest acc k aS with k Fin.≟ i
  ... | yes qe = trans (cong (λ z → proj₂ (extractPairs j S′ rest (setF (setP acc i p) i q′)) z) qe)
                       (trans (ep-fork-other j S′ rest (setF (setP acc i p) i q′) i aS)
                              (setF-at (setP acc i p) i q′))
  ... | no ¬e = ep-acc-fork j S′ rest (setF (setP acc i p) i q′) (setF (setP acc i p) i q) i k ¬e
                  (λ x x≢i → trans (setF-≢ (setP acc i p) i q′ x x≢i) (sym (setF-≢ (setP acc i p) i q x x≢i)))

  -- Sub-piece 3c: the routing.  τ-step inversions specialised to philSt/forkSt: a τ from
  -- a component is its reloop (the only silent move), giving the position + successor.
  phil-τ-step : ∀ {i p P′} → philSt asymFirst asymSecond i p ─[ τ ]─► P′
              → (p ≡ reloop) × (P′ ≡ philSt asymFirst asymSecond i think)
  phil-τ-step {p = think}  (sSil eq)     = case eq of λ ()
  phil-τ-step {p = think}  (sTau refl br) = case br of λ ()
  phil-τ-step {p = one}    (sSil eq)     = case eq of λ ()
  phil-τ-step {p = one}    (sTau refl br) = case br of λ ()
  phil-τ-step {p = eat}    (sSil eq)     = case eq of λ ()
  phil-τ-step {p = eat}    (sTau refl br) = case br of λ ()
  phil-τ-step {p = down1}  (sSil eq)     = case eq of λ ()
  phil-τ-step {p = down1}  (sTau refl br) = case br of λ ()
  phil-τ-step {p = reloop} (sSil refl)   = refl , refl
  phil-τ-step {p = reloop} (sTau eq br)  = case eq of λ ()

  fork-τ-step : ∀ {i q Q′} → forkSt i q ─[ τ ]─► Q′
              → (q ≡ freloop) × (Q′ ≡ forkSt i free)
  fork-τ-step {q = free}    (sSil eq)     = case eq of λ ()
  fork-τ-step {i = i} {q = free} (sTau {i = i′} {a = a} refl br) = case trans (sym (st-free i i′ a)) br of λ ()
  fork-τ-step {q = heldOwn} (sSil eq)     = case eq of λ ()
  fork-τ-step {q = heldOwn} (sTau refl br) = case br of λ ()
  fork-τ-step {q = heldNbr} (sSil eq)     = case eq of λ ()
  fork-τ-step {q = heldNbr} (sTau refl br) = case br of λ ()
  fork-τ-step {q = freloop} (sSil refl)   = refl , refl
  fork-τ-step {q = freloop} (sTau eq br)  = case eq of λ ()

  -- the phil-τ case of the routing, factored (cases p so the successor unifies
  -- definitionally; only reloop→think is productive).  Returns the new FoldReach +
  -- the ForkConsistent-preservation for the extracted config.
  route-τ-phil : ∀ (i : Phil) (S : List Phil) (p : PhilPos) {ts}
                   (ftail : FoldReach (forkComp i) (concatMap pairF S) (forkReachI i) (allRest S) ts)
                   {P′} (pτ : philSt asymFirst asymSecond i p ─[ τ ]─► P′) (acc : Config)
               → All (λ x → i ≢ x) S
               → Σ[ fr′ ∈ FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S)
                                     (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest S)
                                     (P′ ⟦ Comp.alpha (philComp asymFirst asymSecond i)
                                         ∥ unionα (forkComp i ∷ concatMap pairF S) ⟧ ts) ]
                   (ForkConsistent (extractPairs i S (fr-cons p ftail) acc)
                  → ForkConsistent (extractPairs i S fr′ acc))
  route-τ-phil i S think  ftail (sSil eq)      acc aS = case eq of λ ()
  route-τ-phil i S think  ftail (sTau refl br) acc aS = case br of λ ()
  route-τ-phil i S one    ftail (sSil eq)      acc aS = case eq of λ ()
  route-τ-phil i S one    ftail (sTau refl br) acc aS = case br of λ ()
  route-τ-phil i S eat    ftail (sSil eq)      acc aS = case eq of λ ()
  route-τ-phil i S eat    ftail (sTau refl br) acc aS = case br of λ ()
  route-τ-phil i S down1  ftail (sSil eq)      acc aS = case eq of λ ()
  route-τ-phil i S down1  ftail (sTau refl br) acc aS = case br of λ ()
  route-τ-phil i S reloop ftail (sTau eq br)   acc aS = case eq of λ ()
  route-τ-phil i S reloop ftail (sSil refl)    acc aS =
    fr-cons think ftail ,
    (λ fc → FC-cong (λ k → sym (commute-phil-1 i S reloop think ftail acc k aS))
                    (λ k → sym (commute-phil-2 i S reloop think ftail acc k))
                    (cons-pres fc (⊳τp i (ep-phil-head i S (fr-cons reloop ftail) acc aS))))

  -- the fork-τ cases of the routing (fork i = 2nd component), split by S.
  route-τ-fork-nil : ∀ (i : Phil) (p : PhilPos) (q : ForkPos) {Q′}
                       (qτ : forkSt i q ─[ τ ]─► Q′) (acc : Config)
                   → Σ[ fr′ ∈ FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ [])
                                         (philReachI asymFirst asymSecond i) (forkReachI i ∷ [])
                                         (philSt asymFirst asymSecond i p
                                           ⟦ Comp.alpha (philComp asymFirst asymSecond i) ∥ unionα (forkComp i ∷ []) ⟧ Q′) ]
                       (ForkConsistent (extractPairs i [] (fr-cons p (fr-nil q)) acc)
                      → ForkConsistent (extractPairs i [] fr′ acc))
  route-τ-fork-nil i p free    (sSil eq) acc = case eq of λ ()
  route-τ-fork-nil i p free    (sTau {i = i′} {a = a} refl br) acc = case trans (sym (st-free i i′ a)) br of λ ()
  route-τ-fork-nil i p heldOwn (sSil eq) acc = case eq of λ ()
  route-τ-fork-nil i p heldOwn (sTau refl br) acc = case br of λ ()
  route-τ-fork-nil i p heldNbr (sSil eq) acc = case eq of λ ()
  route-τ-fork-nil i p heldNbr (sTau refl br) acc = case br of λ ()
  route-τ-fork-nil i p freloop (sTau eq br) acc = case eq of λ ()
  route-τ-fork-nil i p freloop (sSil refl) acc =
    fr-cons p (fr-nil free) ,
    (λ fc → FC-cong (λ k → sym (commute-fork-nil-1 i p freloop free acc k))
                    (λ k → sym (commute-fork-nil-2 i p freloop free acc k))
                    (cons-pres fc (⊳τf i (ep-fork-head i [] (fr-cons p (fr-nil freloop)) acc []))))

  route-τ-fork-cons : ∀ (i j : Phil) (S′ : List Phil) (p : PhilPos) (q : ForkPos) {ts}
                        (rest : FoldReach (philComp asymFirst asymSecond j) (forkComp j ∷ concatMap pairF S′)
                                          (philReachI asymFirst asymSecond j) (forkReachI j ∷ allRest S′) ts)
                        {Q1} (fτ : forkSt i q ─[ τ ]─► Q1) (acc : Config)
                    → All (λ x → i ≢ x) (j ∷ S′)
                    → Σ[ fr′ ∈ FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF (j ∷ S′))
                                          (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest (j ∷ S′))
                                          (philSt asymFirst asymSecond i p
                                            ⟦ Comp.alpha (philComp asymFirst asymSecond i) ∥ unionα (forkComp i ∷ concatMap pairF (j ∷ S′)) ⟧
                                            (Q1 ⟦ Comp.alpha (forkComp i) ∥ unionα (concatMap pairF (j ∷ S′)) ⟧ ts)) ]
                        (ForkConsistent (extractPairs i (j ∷ S′) (fr-cons p (fr-cons q rest)) acc)
                       → ForkConsistent (extractPairs i (j ∷ S′) fr′ acc))
  route-τ-fork-cons i j S′ p free    rest (sSil eq) acc aS = case eq of λ ()
  route-τ-fork-cons i j S′ p free    rest (sTau {i = i′} {a = a} refl br) acc aS = case trans (sym (st-free i i′ a)) br of λ ()
  route-τ-fork-cons i j S′ p heldOwn rest (sSil eq) acc aS = case eq of λ ()
  route-τ-fork-cons i j S′ p heldOwn rest (sTau refl br) acc aS = case br of λ ()
  route-τ-fork-cons i j S′ p heldNbr rest (sSil eq) acc aS = case eq of λ ()
  route-τ-fork-cons i j S′ p heldNbr rest (sTau refl br) acc aS = case br of λ ()
  route-τ-fork-cons i j S′ p freloop rest (sTau eq br) acc aS = case eq of λ ()
  route-τ-fork-cons i j S′ p freloop rest (sSil refl) acc aS =
    fr-cons p (fr-cons free rest) ,
    (λ fc → FC-cong (λ k → sym (commute-fork-cons-1 i j S′ p freloop free rest acc k))
                    (λ k → sym (commute-fork-cons-2 i j S′ p freloop free rest acc k aS))
                    (cons-pres fc (⊳τf i (ep-fork-head i (j ∷ S′) (fr-cons p (fr-cons freloop rest)) acc aS))))

  -- the τ routing: invert the system τ-step, dispatch to phil/fork cases, recurse deep.
  route-τ : ∀ (i : Phil) (S : List Phil) {t}
              (fr : FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S)
                              (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest S) t)
              {t′} (st : t ─[ τ ]─► t′) (acc : Config) → Unique (i ∷ S)
          → Σ[ fr′ ∈ FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S)
                                (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest S) t′ ]
              (ForkConsistent (extractPairs i S fr acc) → ForkConsistent (extractPairs i S fr′ acc))
  route-τ i []       (fr-cons p (fr-nil q))     st acc _ with αpar-τ-step-inv st
  ... | inj₁ (P′ , pτ , refl) = route-τ-phil i [] p (fr-nil q) pτ acc []
  ... | inj₂ (Q′ , qτ , refl) = route-τ-fork-nil i p q qτ acc
  route-τ i (j ∷ S′) (fr-cons p (fr-cons q rest)) st acc (allS ∷ᵖ uStl) with αpar-τ-step-inv st
  ... | inj₁ (P′ , pτ , refl) = route-τ-phil i (j ∷ S′) p (fr-cons q rest) pτ acc allS
  ... | inj₂ (Q′ , qτ , refl) with αpar-τ-step-inv qτ
  ...   | inj₁ (Q1 , fτ , refl) = route-τ-fork-cons i j S′ p q rest fτ acc allS
  ...   | inj₂ (R′ , rτ , refl) =
            let (rest′ , fc-impl) = route-τ j S′ rest rτ (setF (setP acc i p) i q) uStl
            in fr-cons p (fr-cons q rest′) , fc-impl

  -- Event matching for route-vis: a vSync forces the phil's and fork's events equal,
  -- which correlates their indices (so the synced fork is exactly the phil's f i / s i).
  dp-phil dp-fork : ∀ {X} → DP X → Fin (suc (suc m))
  dp-phil (picks i _)    = i
  dp-phil (putsdown i _) = i
  dp-fork (picks _ k)    = k
  dp-fork (putsdown _ k) = k

  dp-phil-of dp-fork-of : Maybe DPEvent → Fin (suc (suc m))
  dp-phil-of (just evn) = dp-phil (Event.e evn)
  dp-phil-of nothing    = fzero
  dp-fork-of (just evn) = dp-fork (Event.e evn)
  dp-fork-of nothing    = fzero

  evt-match : ∀ {e₁ e₂ : DP (⊤ {lzero})} → evt e₁ ≡ evt e₂
            → (dp-phil e₁ ≡ dp-phil e₂) × (dp-fork e₁ ≡ dp-fork e₂)
  evt-match eq = cong dp-phil-of eq , cong dp-fork-of eq

  -- route-vis prep: setP/setF respect pointwise config equality (to COMPOSE the phil
  -- and fork head commutes for a single vis step, which changes both components).
  setP-pcong-1 : ∀ {X Y : Config} (i : Phil) (p : PhilPos)
               → (∀ k → proj₁ X k ≡ proj₁ Y k) → ∀ k → proj₁ (setP X i p) k ≡ proj₁ (setP Y i p) k
  setP-pcong-1 i p ag k with k Fin.≟ i
  ... | yes _ = refl
  ... | no _  = ag k

  setF-pcong-2 : ∀ {X Y : Config} (i : Fork) (q : ForkPos)
               → (∀ k → proj₂ X k ≡ proj₂ Y k) → ∀ k → proj₂ (setF X i q) k ≡ proj₂ (setF Y i q) k
  setF-pcong-2 i q ag k with k Fin.≟ i
  ... | yes _ = refl
  ... | no _  = ag k

  -- combined commute (own pick: phil i AND adjacent fork i both change at the head level).
  -- Composes commute-phil + commute-fork-cons via the pcong helpers.  Representative of
  -- the two-component vSync commute that route-vis's FC-impl needs.
  commute-pk-own-1 : ∀ (i j : Phil) (S′ : List Phil) (p p′ : PhilPos) (q q′ : ForkPos) {ts}
                       (rest : FoldReach (philComp asymFirst asymSecond j) (forkComp j ∷ concatMap pairF S′)
                                         (philReachI asymFirst asymSecond j) (forkReachI j ∷ allRest S′) ts)
                       (acc : Config) (k : Phil) → All (λ x → i ≢ x) (j ∷ S′)
                   → proj₁ (extractPairs i (j ∷ S′) (fr-cons p′ (fr-cons q′ rest)) acc) k
                   ≡ proj₁ (setF (setP (extractPairs i (j ∷ S′) (fr-cons p (fr-cons q rest)) acc) i p′) i q′) k
  commute-pk-own-1 i j S′ p p′ q q′ rest acc k aS =
    trans (commute-fork-cons-1 i j S′ p′ q q′ rest acc k)
          (commute-phil-1 i (j ∷ S′) p p′ (fr-cons q rest) acc k aS)

  commute-pk-own-2 : ∀ (i j : Phil) (S′ : List Phil) (p p′ : PhilPos) (q q′ : ForkPos) {ts}
                       (rest : FoldReach (philComp asymFirst asymSecond j) (forkComp j ∷ concatMap pairF S′)
                                         (philReachI asymFirst asymSecond j) (forkReachI j ∷ allRest S′) ts)
                       (acc : Config) (k : Fork) → All (λ x → i ≢ x) (j ∷ S′)
                   → proj₂ (extractPairs i (j ∷ S′) (fr-cons p′ (fr-cons q′ rest)) acc) k
                   ≡ proj₂ (setF (setP (extractPairs i (j ∷ S′) (fr-cons p (fr-cons q rest)) acc) i p′) i q′) k
  commute-pk-own-2 i j S′ p p′ q q′ rest acc k aS =
    trans (commute-fork-cons-2 i j S′ p′ q q′ rest acc k aS)
          (setF-pcong-2 {extractPairs i (j ∷ S′) (fr-cons p′ (fr-cons q rest)) acc}
                        {setP (extractPairs i (j ∷ S′) (fr-cons p (fr-cons q rest)) acc) i p′}
                        i q′ (λ k′ → commute-phil-2 i (j ∷ S′) p p′ (fr-cons q rest) acc k′) k)

  -- end-to-end vis combine, representative case (own pick-1: phil i think→one + adjacent
  -- fork i free→heldOwn).  Ties ⊳pk1 + cons-pres + combined commute + FC-cong + own-bridge.
  ownNbr-self : ∀ (i : Phil) → ownNbr i i ≡ heldOwn
  ownNbr-self i with i Fin.≟ i
  ... | yes _  = refl
  ... | no ¬p = ⊥-elim (¬p refl)

  route-vis-pk1-own : ∀ (i j : Phil) (S′ : List Phil) {ts}
                        (rest : FoldReach (philComp asymFirst asymSecond j) (forkComp j ∷ concatMap pairF S′)
                                          (philReachI asymFirst asymSecond j) (forkReachI j ∷ allRest S′) ts)
                        (acc : Config) → All (λ x → i ≢ x) (j ∷ S′) → asymFirst i ≡ i
                    → ForkConsistent (extractPairs i (j ∷ S′) (fr-cons think (fr-cons free rest)) acc)
                    → ForkConsistent (extractPairs i (j ∷ S′) (fr-cons one (fr-cons heldOwn rest)) acc)
  route-vis-pk1-own i j S′ rest acc aS own fc =
    FC-cong (λ k → sym (commute-pk-own-1 i j S′ think one free heldOwn rest acc k aS))
            (λ k → sym (commute-pk-own-2 i j S′ think one free heldOwn rest acc k aS))
            (subst ForkConsistent
                   (cong₂ (setF (setP cfg i one)) own (trans (cong (ownNbr i) own) (ownNbr-self i)))
                   (cons-pres fc (⊳pk1 i (ep-phil-head i (j ∷ S′) (fr-cons think (fr-cons free rest)) acc aS)
                                        (subst (λ z → proj₂ cfg z ≡ free) (sym own)
                                               (ep-fork-head i (j ∷ S′) (fr-cons think (fr-cons free rest)) acc aS)))))
    where cfg = extractPairs i (j ∷ S′) (fr-cons think (fr-cons free rest)) acc

  -- the other own (adjacent-fork) vis combine cases (analogous to route-vis-pk1-own,
  -- reusing the generic commute-pk-own).  pk2: pick second; pd1/pd2: putsdown (fork→freloop,
  -- no fork premise, target fork value is the constant freloop so no ownNbr).
  route-vis-pk2-own : ∀ (i j : Phil) (S′ : List Phil) {ts}
                        (rest : FoldReach (philComp asymFirst asymSecond j) (forkComp j ∷ concatMap pairF S′)
                                          (philReachI asymFirst asymSecond j) (forkReachI j ∷ allRest S′) ts)
                        (acc : Config) → All (λ x → i ≢ x) (j ∷ S′) → asymSecond i ≡ i
                    → ForkConsistent (extractPairs i (j ∷ S′) (fr-cons one (fr-cons free rest)) acc)
                    → ForkConsistent (extractPairs i (j ∷ S′) (fr-cons eat (fr-cons heldOwn rest)) acc)
  route-vis-pk2-own i j S′ rest acc aS own fc =
    FC-cong (λ k → sym (commute-pk-own-1 i j S′ one eat free heldOwn rest acc k aS))
            (λ k → sym (commute-pk-own-2 i j S′ one eat free heldOwn rest acc k aS))
            (subst ForkConsistent
                   (cong₂ (setF (setP cfg i eat)) own (trans (cong (ownNbr i) own) (ownNbr-self i)))
                   (cons-pres fc (⊳pk2 i (ep-phil-head i (j ∷ S′) (fr-cons one (fr-cons free rest)) acc aS)
                                        (subst (λ z → proj₂ cfg z ≡ free) (sym own)
                                               (ep-fork-head i (j ∷ S′) (fr-cons one (fr-cons free rest)) acc aS)))))
    where cfg = extractPairs i (j ∷ S′) (fr-cons one (fr-cons free rest)) acc

  route-vis-pd1-own : ∀ (i j : Phil) (S′ : List Phil) {ts}
                        (rest : FoldReach (philComp asymFirst asymSecond j) (forkComp j ∷ concatMap pairF S′)
                                          (philReachI asymFirst asymSecond j) (forkReachI j ∷ allRest S′) ts)
                        (acc : Config) → All (λ x → i ≢ x) (j ∷ S′) → asymFirst i ≡ i
                    → ForkConsistent (extractPairs i (j ∷ S′) (fr-cons down1 (fr-cons heldOwn rest)) acc)
                    → ForkConsistent (extractPairs i (j ∷ S′) (fr-cons reloop (fr-cons freloop rest)) acc)
  route-vis-pd1-own i j S′ rest acc aS own fc =
    FC-cong (λ k → sym (commute-pk-own-1 i j S′ down1 reloop heldOwn freloop rest acc k aS))
            (λ k → sym (commute-pk-own-2 i j S′ down1 reloop heldOwn freloop rest acc k aS))
            (subst ForkConsistent
                   (cong (λ z → setF (setP cfg i reloop) z freloop) own)
                   (cons-pres fc (⊳pd1 i (ep-phil-head i (j ∷ S′) (fr-cons down1 (fr-cons heldOwn rest)) acc aS))))
    where cfg = extractPairs i (j ∷ S′) (fr-cons down1 (fr-cons heldOwn rest)) acc

  route-vis-pd2-own : ∀ (i j : Phil) (S′ : List Phil) {ts}
                        (rest : FoldReach (philComp asymFirst asymSecond j) (forkComp j ∷ concatMap pairF S′)
                                          (philReachI asymFirst asymSecond j) (forkReachI j ∷ allRest S′) ts)
                        (acc : Config) → All (λ x → i ≢ x) (j ∷ S′) → asymSecond i ≡ i
                    → ForkConsistent (extractPairs i (j ∷ S′) (fr-cons eat (fr-cons heldOwn rest)) acc)
                    → ForkConsistent (extractPairs i (j ∷ S′) (fr-cons down1 (fr-cons freloop rest)) acc)
  route-vis-pd2-own i j S′ rest acc aS own fc =
    FC-cong (λ k → sym (commute-pk-own-1 i j S′ eat down1 heldOwn freloop rest acc k aS))
            (λ k → sym (commute-pk-own-2 i j S′ eat down1 heldOwn freloop rest acc k aS))
            (subst ForkConsistent
                   (cong (λ z → setF (setP cfg i down1) z freloop) own)
                   (cons-pres fc (⊳pd2 i (ep-phil-head i (j ∷ S′) (fr-cons eat (fr-cons heldOwn rest)) acc aS))))
    where cfg = extractPairs i (j ∷ S′) (fr-cons eat (fr-cons heldOwn rest)) acc

  -- nbr (deep-fork) combined commute: change phil i (head) + fork j (the (j)-level fork,
  -- j = head S = i⊕1).  Composes commute-fork-cons/nil at the j-level (reached by the
  -- DEFINITIONAL extractPairs peel of phil i + spectator fork i) with commute-phil at i —
  -- structurally identical to commute-pk-own, one peel deeper.  Split on the tail after fork j.
  ownNbr-nbr : ∀ (i j : Phil) → i ≢ j → ownNbr i j ≡ heldNbr
  ownNbr-nbr i j i≢j with j Fin.≟ i
  ... | yes e = ⊥-elim (i≢j (sym e))
  ... | no  _ = refl

  commute-pk-nbr-cons-1 : ∀ (i j k′ : Phil) (S‴ : List Phil) (p p′ : PhilPos)
                            (q-i : ForkPos) (p-j : PhilPos) (q q′ : ForkPos) {ts}
                            (rest2 : FoldReach (philComp asymFirst asymSecond k′) (forkComp k′ ∷ concatMap pairF S‴)
                                               (philReachI asymFirst asymSecond k′) (forkReachI k′ ∷ allRest S‴) ts)
                            (acc : Config) (k : Phil) → All (λ x → i ≢ x) (j ∷ k′ ∷ S‴)
                        → proj₁ (extractPairs i (j ∷ k′ ∷ S‴) (fr-cons p′ (fr-cons q-i (fr-cons p-j (fr-cons q′ rest2)))) acc) k
                        ≡ proj₁ (setF (setP (extractPairs i (j ∷ k′ ∷ S‴) (fr-cons p (fr-cons q-i (fr-cons p-j (fr-cons q rest2)))) acc) i p′) j q′) k
  commute-pk-nbr-cons-1 i j k′ S‴ p p′ q-i p-j q q′ rest2 acc k aS =
    trans (commute-fork-cons-1 j k′ S‴ p-j q q′ rest2 (setF (setP acc i p′) i q-i) k)
          (commute-phil-1 i (j ∷ k′ ∷ S‴) p p′ (fr-cons q-i (fr-cons p-j (fr-cons q rest2))) acc k aS)

  commute-pk-nbr-cons-2 : ∀ (i j k′ : Phil) (S‴ : List Phil) (p p′ : PhilPos)
                            (q-i : ForkPos) (p-j : PhilPos) (q q′ : ForkPos) {ts}
                            (rest2 : FoldReach (philComp asymFirst asymSecond k′) (forkComp k′ ∷ concatMap pairF S‴)
                                               (philReachI asymFirst asymSecond k′) (forkReachI k′ ∷ allRest S‴) ts)
                            (acc : Config) (k : Fork) → All (λ x → i ≢ x) (j ∷ k′ ∷ S‴) → All (λ x → j ≢ x) (k′ ∷ S‴)
                        → proj₂ (extractPairs i (j ∷ k′ ∷ S‴) (fr-cons p′ (fr-cons q-i (fr-cons p-j (fr-cons q′ rest2)))) acc) k
                        ≡ proj₂ (setF (setP (extractPairs i (j ∷ k′ ∷ S‴) (fr-cons p (fr-cons q-i (fr-cons p-j (fr-cons q rest2)))) acc) i p′) j q′) k
  commute-pk-nbr-cons-2 i j k′ S‴ p p′ q-i p-j q q′ rest2 acc k aS aSj =
    trans (commute-fork-cons-2 j k′ S‴ p-j q q′ rest2 (setF (setP acc i p′) i q-i) k aSj)
          (setF-pcong-2 {extractPairs i (j ∷ k′ ∷ S‴) (fr-cons p′ (fr-cons q-i (fr-cons p-j (fr-cons q rest2)))) acc}
                        {setP (extractPairs i (j ∷ k′ ∷ S‴) (fr-cons p (fr-cons q-i (fr-cons p-j (fr-cons q rest2)))) acc) i p′}
                        j q′ (λ k′′ → commute-phil-2 i (j ∷ k′ ∷ S‴) p p′ (fr-cons q-i (fr-cons p-j (fr-cons q rest2))) acc k′′) k)

  commute-pk-nbr-nil-1 : ∀ (i j : Phil) (p p′ : PhilPos) (q-i : ForkPos) (p-j : PhilPos) (q q′ : ForkPos)
                           (acc : Config) (k : Phil) → All (λ x → i ≢ x) (j ∷ [])
                       → proj₁ (extractPairs i (j ∷ []) (fr-cons p′ (fr-cons q-i (fr-cons p-j (fr-nil q′)))) acc) k
                       ≡ proj₁ (setF (setP (extractPairs i (j ∷ []) (fr-cons p (fr-cons q-i (fr-cons p-j (fr-nil q)))) acc) i p′) j q′) k
  commute-pk-nbr-nil-1 i j p p′ q-i p-j q q′ acc k aS =
    trans (commute-fork-nil-1 j p-j q q′ (setF (setP acc i p′) i q-i) k)
          (commute-phil-1 i (j ∷ []) p p′ (fr-cons q-i (fr-cons p-j (fr-nil q))) acc k aS)

  commute-pk-nbr-nil-2 : ∀ (i j : Phil) (p p′ : PhilPos) (q-i : ForkPos) (p-j : PhilPos) (q q′ : ForkPos)
                           (acc : Config) (k : Fork) → All (λ x → i ≢ x) (j ∷ [])
                       → proj₂ (extractPairs i (j ∷ []) (fr-cons p′ (fr-cons q-i (fr-cons p-j (fr-nil q′)))) acc) k
                       ≡ proj₂ (setF (setP (extractPairs i (j ∷ []) (fr-cons p (fr-cons q-i (fr-cons p-j (fr-nil q)))) acc) i p′) j q′) k
  commute-pk-nbr-nil-2 i j p p′ q-i p-j q q′ acc k aS =
    trans (commute-fork-nil-2 j p-j q q′ (setF (setP acc i p′) i q-i) k)
          (setF-pcong-2 {extractPairs i (j ∷ []) (fr-cons p′ (fr-cons q-i (fr-cons p-j (fr-nil q)))) acc}
                        {setP (extractPairs i (j ∷ []) (fr-cons p (fr-cons q-i (fr-cons p-j (fr-nil q)))) acc) i p′}
                        j q′ (λ k′′ → commute-phil-2 i (j ∷ []) p p′ (fr-cons q-i (fr-cons p-j (fr-nil q))) acc k′′) k)

  -- nbr (deep-fork) vis combine cases.  Same shape as the own cases but with the nbr fork at
  -- the (j)-level (j = head S = asymFirst/Second i), using commute-pk-nbr + the nbr-bridge
  -- (ownNbr i j ≡ heldNbr via i≢j).  Split cons/nil on the tail after fork j.  pk: fork
  -- free→heldNbr (fork premise via ep-fork-head at j); pd: fork heldNbr→freloop (no premise).
  route-vis-pk1-nbr-cons : ∀ (i j k′ : Phil) (S‴ : List Phil) (q-i : ForkPos) (p-j : PhilPos) {ts}
                             (rest2 : FoldReach (philComp asymFirst asymSecond k′) (forkComp k′ ∷ concatMap pairF S‴)
                                                (philReachI asymFirst asymSecond k′) (forkReachI k′ ∷ allRest S‴) ts)
                             (acc : Config) → All (λ x → i ≢ x) (j ∷ k′ ∷ S‴) → All (λ x → j ≢ x) (k′ ∷ S‴)
                         → asymFirst i ≡ j → i ≢ j
                         → ForkConsistent (extractPairs i (j ∷ k′ ∷ S‴) (fr-cons think (fr-cons q-i (fr-cons p-j (fr-cons free   rest2)))) acc)
                         → ForkConsistent (extractPairs i (j ∷ k′ ∷ S‴) (fr-cons one   (fr-cons q-i (fr-cons p-j (fr-cons heldNbr rest2)))) acc)
  route-vis-pk1-nbr-cons i j k′ S‴ q-i p-j rest2 acc aS aSj nbr i≢j fc =
    FC-cong (λ k → sym (commute-pk-nbr-cons-1 i j k′ S‴ think one q-i p-j free heldNbr rest2 acc k aS))
            (λ k → sym (commute-pk-nbr-cons-2 i j k′ S‴ think one q-i p-j free heldNbr rest2 acc k aS aSj))
            (subst ForkConsistent
                   (cong₂ (setF (setP cfg i one)) nbr (trans (cong (ownNbr i) nbr) (ownNbr-nbr i j i≢j)))
                   (cons-pres fc (⊳pk1 i (ep-phil-head i (j ∷ k′ ∷ S‴) (fr-cons think (fr-cons q-i (fr-cons p-j (fr-cons free rest2)))) acc aS)
                                        (subst (λ z → proj₂ cfg z ≡ free) (sym nbr)
                                               (ep-fork-head j (k′ ∷ S‴) (fr-cons p-j (fr-cons free rest2)) (setF (setP acc i think) i q-i) aSj)))))
    where cfg = extractPairs i (j ∷ k′ ∷ S‴) (fr-cons think (fr-cons q-i (fr-cons p-j (fr-cons free rest2)))) acc

  route-vis-pk2-nbr-cons : ∀ (i j k′ : Phil) (S‴ : List Phil) (q-i : ForkPos) (p-j : PhilPos) {ts}
                             (rest2 : FoldReach (philComp asymFirst asymSecond k′) (forkComp k′ ∷ concatMap pairF S‴)
                                                (philReachI asymFirst asymSecond k′) (forkReachI k′ ∷ allRest S‴) ts)
                             (acc : Config) → All (λ x → i ≢ x) (j ∷ k′ ∷ S‴) → All (λ x → j ≢ x) (k′ ∷ S‴)
                         → asymSecond i ≡ j → i ≢ j
                         → ForkConsistent (extractPairs i (j ∷ k′ ∷ S‴) (fr-cons one (fr-cons q-i (fr-cons p-j (fr-cons free   rest2)))) acc)
                         → ForkConsistent (extractPairs i (j ∷ k′ ∷ S‴) (fr-cons eat (fr-cons q-i (fr-cons p-j (fr-cons heldNbr rest2)))) acc)
  route-vis-pk2-nbr-cons i j k′ S‴ q-i p-j rest2 acc aS aSj nbr i≢j fc =
    FC-cong (λ k → sym (commute-pk-nbr-cons-1 i j k′ S‴ one eat q-i p-j free heldNbr rest2 acc k aS))
            (λ k → sym (commute-pk-nbr-cons-2 i j k′ S‴ one eat q-i p-j free heldNbr rest2 acc k aS aSj))
            (subst ForkConsistent
                   (cong₂ (setF (setP cfg i eat)) nbr (trans (cong (ownNbr i) nbr) (ownNbr-nbr i j i≢j)))
                   (cons-pres fc (⊳pk2 i (ep-phil-head i (j ∷ k′ ∷ S‴) (fr-cons one (fr-cons q-i (fr-cons p-j (fr-cons free rest2)))) acc aS)
                                        (subst (λ z → proj₂ cfg z ≡ free) (sym nbr)
                                               (ep-fork-head j (k′ ∷ S‴) (fr-cons p-j (fr-cons free rest2)) (setF (setP acc i one) i q-i) aSj)))))
    where cfg = extractPairs i (j ∷ k′ ∷ S‴) (fr-cons one (fr-cons q-i (fr-cons p-j (fr-cons free rest2)))) acc

  route-vis-pd1-nbr-cons : ∀ (i j k′ : Phil) (S‴ : List Phil) (q-i : ForkPos) (p-j : PhilPos) {ts}
                             (rest2 : FoldReach (philComp asymFirst asymSecond k′) (forkComp k′ ∷ concatMap pairF S‴)
                                                (philReachI asymFirst asymSecond k′) (forkReachI k′ ∷ allRest S‴) ts)
                             (acc : Config) → All (λ x → i ≢ x) (j ∷ k′ ∷ S‴) → All (λ x → j ≢ x) (k′ ∷ S‴)
                         → asymFirst i ≡ j
                         → ForkConsistent (extractPairs i (j ∷ k′ ∷ S‴) (fr-cons down1  (fr-cons q-i (fr-cons p-j (fr-cons heldNbr rest2)))) acc)
                         → ForkConsistent (extractPairs i (j ∷ k′ ∷ S‴) (fr-cons reloop (fr-cons q-i (fr-cons p-j (fr-cons freloop rest2)))) acc)
  route-vis-pd1-nbr-cons i j k′ S‴ q-i p-j rest2 acc aS aSj nbr fc =
    FC-cong (λ k → sym (commute-pk-nbr-cons-1 i j k′ S‴ down1 reloop q-i p-j heldNbr freloop rest2 acc k aS))
            (λ k → sym (commute-pk-nbr-cons-2 i j k′ S‴ down1 reloop q-i p-j heldNbr freloop rest2 acc k aS aSj))
            (subst ForkConsistent
                   (cong (λ z → setF (setP cfg i reloop) z freloop) nbr)
                   (cons-pres fc (⊳pd1 i (ep-phil-head i (j ∷ k′ ∷ S‴) (fr-cons down1 (fr-cons q-i (fr-cons p-j (fr-cons heldNbr rest2)))) acc aS))))
    where cfg = extractPairs i (j ∷ k′ ∷ S‴) (fr-cons down1 (fr-cons q-i (fr-cons p-j (fr-cons heldNbr rest2)))) acc

  route-vis-pd2-nbr-cons : ∀ (i j k′ : Phil) (S‴ : List Phil) (q-i : ForkPos) (p-j : PhilPos) {ts}
                             (rest2 : FoldReach (philComp asymFirst asymSecond k′) (forkComp k′ ∷ concatMap pairF S‴)
                                                (philReachI asymFirst asymSecond k′) (forkReachI k′ ∷ allRest S‴) ts)
                             (acc : Config) → All (λ x → i ≢ x) (j ∷ k′ ∷ S‴) → All (λ x → j ≢ x) (k′ ∷ S‴)
                         → asymSecond i ≡ j
                         → ForkConsistent (extractPairs i (j ∷ k′ ∷ S‴) (fr-cons eat   (fr-cons q-i (fr-cons p-j (fr-cons heldNbr rest2)))) acc)
                         → ForkConsistent (extractPairs i (j ∷ k′ ∷ S‴) (fr-cons down1 (fr-cons q-i (fr-cons p-j (fr-cons freloop rest2)))) acc)
  route-vis-pd2-nbr-cons i j k′ S‴ q-i p-j rest2 acc aS aSj nbr fc =
    FC-cong (λ k → sym (commute-pk-nbr-cons-1 i j k′ S‴ eat down1 q-i p-j heldNbr freloop rest2 acc k aS))
            (λ k → sym (commute-pk-nbr-cons-2 i j k′ S‴ eat down1 q-i p-j heldNbr freloop rest2 acc k aS aSj))
            (subst ForkConsistent
                   (cong (λ z → setF (setP cfg i down1) z freloop) nbr)
                   (cons-pres fc (⊳pd2 i (ep-phil-head i (j ∷ k′ ∷ S‴) (fr-cons eat (fr-cons q-i (fr-cons p-j (fr-cons heldNbr rest2)))) acc aS))))
    where cfg = extractPairs i (j ∷ k′ ∷ S‴) (fr-cons eat (fr-cons q-i (fr-cons p-j (fr-cons heldNbr rest2)))) acc

  route-vis-pk1-nbr-nil : ∀ (i j : Phil) (q-i : ForkPos) (p-j : PhilPos) (acc : Config)
                        → All (λ x → i ≢ x) (j ∷ []) → asymFirst i ≡ j → i ≢ j
                        → ForkConsistent (extractPairs i (j ∷ []) (fr-cons think (fr-cons q-i (fr-cons p-j (fr-nil free)))) acc)
                        → ForkConsistent (extractPairs i (j ∷ []) (fr-cons one   (fr-cons q-i (fr-cons p-j (fr-nil heldNbr)))) acc)
  route-vis-pk1-nbr-nil i j q-i p-j acc aS nbr i≢j fc =
    FC-cong (λ k → sym (commute-pk-nbr-nil-1 i j think one q-i p-j free heldNbr acc k aS))
            (λ k → sym (commute-pk-nbr-nil-2 i j think one q-i p-j free heldNbr acc k aS))
            (subst ForkConsistent
                   (cong₂ (setF (setP cfg i one)) nbr (trans (cong (ownNbr i) nbr) (ownNbr-nbr i j i≢j)))
                   (cons-pres fc (⊳pk1 i (ep-phil-head i (j ∷ []) (fr-cons think (fr-cons q-i (fr-cons p-j (fr-nil free)))) acc aS)
                                        (subst (λ z → proj₂ cfg z ≡ free) (sym nbr)
                                               (ep-fork-head j [] (fr-cons p-j (fr-nil free)) (setF (setP acc i think) i q-i) [])))))
    where cfg = extractPairs i (j ∷ []) (fr-cons think (fr-cons q-i (fr-cons p-j (fr-nil free)))) acc

  route-vis-pk2-nbr-nil : ∀ (i j : Phil) (q-i : ForkPos) (p-j : PhilPos) (acc : Config)
                        → All (λ x → i ≢ x) (j ∷ []) → asymSecond i ≡ j → i ≢ j
                        → ForkConsistent (extractPairs i (j ∷ []) (fr-cons one (fr-cons q-i (fr-cons p-j (fr-nil free)))) acc)
                        → ForkConsistent (extractPairs i (j ∷ []) (fr-cons eat (fr-cons q-i (fr-cons p-j (fr-nil heldNbr)))) acc)
  route-vis-pk2-nbr-nil i j q-i p-j acc aS nbr i≢j fc =
    FC-cong (λ k → sym (commute-pk-nbr-nil-1 i j one eat q-i p-j free heldNbr acc k aS))
            (λ k → sym (commute-pk-nbr-nil-2 i j one eat q-i p-j free heldNbr acc k aS))
            (subst ForkConsistent
                   (cong₂ (setF (setP cfg i eat)) nbr (trans (cong (ownNbr i) nbr) (ownNbr-nbr i j i≢j)))
                   (cons-pres fc (⊳pk2 i (ep-phil-head i (j ∷ []) (fr-cons one (fr-cons q-i (fr-cons p-j (fr-nil free)))) acc aS)
                                        (subst (λ z → proj₂ cfg z ≡ free) (sym nbr)
                                               (ep-fork-head j [] (fr-cons p-j (fr-nil free)) (setF (setP acc i one) i q-i) [])))))
    where cfg = extractPairs i (j ∷ []) (fr-cons one (fr-cons q-i (fr-cons p-j (fr-nil free)))) acc

  route-vis-pd1-nbr-nil : ∀ (i j : Phil) (q-i : ForkPos) (p-j : PhilPos) (acc : Config)
                        → All (λ x → i ≢ x) (j ∷ []) → asymFirst i ≡ j
                        → ForkConsistent (extractPairs i (j ∷ []) (fr-cons down1  (fr-cons q-i (fr-cons p-j (fr-nil heldNbr)))) acc)
                        → ForkConsistent (extractPairs i (j ∷ []) (fr-cons reloop (fr-cons q-i (fr-cons p-j (fr-nil freloop)))) acc)
  route-vis-pd1-nbr-nil i j q-i p-j acc aS nbr fc =
    FC-cong (λ k → sym (commute-pk-nbr-nil-1 i j down1 reloop q-i p-j heldNbr freloop acc k aS))
            (λ k → sym (commute-pk-nbr-nil-2 i j down1 reloop q-i p-j heldNbr freloop acc k aS))
            (subst ForkConsistent
                   (cong (λ z → setF (setP cfg i reloop) z freloop) nbr)
                   (cons-pres fc (⊳pd1 i (ep-phil-head i (j ∷ []) (fr-cons down1 (fr-cons q-i (fr-cons p-j (fr-nil heldNbr)))) acc aS))))
    where cfg = extractPairs i (j ∷ []) (fr-cons down1 (fr-cons q-i (fr-cons p-j (fr-nil heldNbr)))) acc

  route-vis-pd2-nbr-nil : ∀ (i j : Phil) (q-i : ForkPos) (p-j : PhilPos) (acc : Config)
                        → All (λ x → i ≢ x) (j ∷ []) → asymSecond i ≡ j
                        → ForkConsistent (extractPairs i (j ∷ []) (fr-cons eat   (fr-cons q-i (fr-cons p-j (fr-nil heldNbr)))) acc)
                        → ForkConsistent (extractPairs i (j ∷ []) (fr-cons down1 (fr-cons q-i (fr-cons p-j (fr-nil freloop)))) acc)
  route-vis-pd2-nbr-nil i j q-i p-j acc aS nbr fc =
    FC-cong (λ k → sym (commute-pk-nbr-nil-1 i j eat down1 q-i p-j heldNbr freloop acc k aS))
            (λ k → sym (commute-pk-nbr-nil-2 i j eat down1 q-i p-j heldNbr freloop acc k aS))
            (subst ForkConsistent
                   (cong (λ z → setF (setP cfg i down1) z freloop) nbr)
                   (cons-pres fc (⊳pd2 i (ep-phil-head i (j ∷ []) (fr-cons eat (fr-cons q-i (fr-cons p-j (fr-nil heldNbr)))) acc aS))))
    where cfg = extractPairs i (j ∷ []) (fr-cons eat (fr-cons q-i (fr-cons p-j (fr-nil heldNbr)))) acc

  -- own-nil vis combine (S=[], fork i is the LAST component, fr-nil): phil n-1's own pick
  -- of the last fork.  commute-pk-own-nil = commute-fork-nil ∘ commute-phil (S=[]).
  commute-pk-own-nil-1 : ∀ (i : Phil) (p p′ : PhilPos) (q q′ : ForkPos) (acc : Config) (k : Phil)
                       → proj₁ (extractPairs i [] (fr-cons p′ (fr-nil q′)) acc) k
                       ≡ proj₁ (setF (setP (extractPairs i [] (fr-cons p (fr-nil q)) acc) i p′) i q′) k
  commute-pk-own-nil-1 i p p′ q q′ acc k =
    trans (commute-fork-nil-1 i p′ q q′ acc k)
          (commute-phil-1 i [] p p′ (fr-nil q) acc k [])

  commute-pk-own-nil-2 : ∀ (i : Phil) (p p′ : PhilPos) (q q′ : ForkPos) (acc : Config) (k : Fork)
                       → proj₂ (extractPairs i [] (fr-cons p′ (fr-nil q′)) acc) k
                       ≡ proj₂ (setF (setP (extractPairs i [] (fr-cons p (fr-nil q)) acc) i p′) i q′) k
  commute-pk-own-nil-2 i p p′ q q′ acc k =
    trans (commute-fork-nil-2 i p′ q q′ acc k)
          (setF-pcong-2 {extractPairs i [] (fr-cons p′ (fr-nil q)) acc}
                        {setP (extractPairs i [] (fr-cons p (fr-nil q)) acc) i p′}
                        i q′ (λ k′ → commute-phil-2 i [] p p′ (fr-nil q) acc k′) k)

  route-vis-pk1-own-nil : ∀ (i : Phil) (acc : Config) → asymFirst i ≡ i
                        → ForkConsistent (extractPairs i [] (fr-cons think (fr-nil free))    acc)
                        → ForkConsistent (extractPairs i [] (fr-cons one   (fr-nil heldOwn)) acc)
  route-vis-pk1-own-nil i acc own fc =
    FC-cong (λ k → sym (commute-pk-own-nil-1 i think one free heldOwn acc k))
            (λ k → sym (commute-pk-own-nil-2 i think one free heldOwn acc k))
            (subst ForkConsistent
                   (cong₂ (setF (setP cfg i one)) own (trans (cong (ownNbr i) own) (ownNbr-self i)))
                   (cons-pres fc (⊳pk1 i (ep-phil-head i [] (fr-cons think (fr-nil free)) acc [])
                                        (subst (λ z → proj₂ cfg z ≡ free) (sym own)
                                               (ep-fork-head i [] (fr-cons think (fr-nil free)) acc [])))))
    where cfg = extractPairs i [] (fr-cons think (fr-nil free)) acc

  route-vis-pk2-own-nil : ∀ (i : Phil) (acc : Config) → asymSecond i ≡ i
                        → ForkConsistent (extractPairs i [] (fr-cons one (fr-nil free))    acc)
                        → ForkConsistent (extractPairs i [] (fr-cons eat (fr-nil heldOwn)) acc)
  route-vis-pk2-own-nil i acc own fc =
    FC-cong (λ k → sym (commute-pk-own-nil-1 i one eat free heldOwn acc k))
            (λ k → sym (commute-pk-own-nil-2 i one eat free heldOwn acc k))
            (subst ForkConsistent
                   (cong₂ (setF (setP cfg i eat)) own (trans (cong (ownNbr i) own) (ownNbr-self i)))
                   (cons-pres fc (⊳pk2 i (ep-phil-head i [] (fr-cons one (fr-nil free)) acc [])
                                        (subst (λ z → proj₂ cfg z ≡ free) (sym own)
                                               (ep-fork-head i [] (fr-cons one (fr-nil free)) acc [])))))
    where cfg = extractPairs i [] (fr-cons one (fr-nil free)) acc

  route-vis-pd1-own-nil : ∀ (i : Phil) (acc : Config) → asymFirst i ≡ i
                        → ForkConsistent (extractPairs i [] (fr-cons down1  (fr-nil heldOwn)) acc)
                        → ForkConsistent (extractPairs i [] (fr-cons reloop (fr-nil freloop)) acc)
  route-vis-pd1-own-nil i acc own fc =
    FC-cong (λ k → sym (commute-pk-own-nil-1 i down1 reloop heldOwn freloop acc k))
            (λ k → sym (commute-pk-own-nil-2 i down1 reloop heldOwn freloop acc k))
            (subst ForkConsistent
                   (cong (λ z → setF (setP cfg i reloop) z freloop) own)
                   (cons-pres fc (⊳pd1 i (ep-phil-head i [] (fr-cons down1 (fr-nil heldOwn)) acc []))))
    where cfg = extractPairs i [] (fr-cons down1 (fr-nil heldOwn)) acc

  route-vis-pd2-own-nil : ∀ (i : Phil) (acc : Config) → asymSecond i ≡ i
                        → ForkConsistent (extractPairs i [] (fr-cons eat   (fr-nil heldOwn)) acc)
                        → ForkConsistent (extractPairs i [] (fr-cons down1 (fr-nil freloop)) acc)
  route-vis-pd2-own-nil i acc own fc =
    FC-cong (λ k → sym (commute-pk-own-nil-1 i eat down1 heldOwn freloop acc k))
            (λ k → sym (commute-pk-own-nil-2 i eat down1 heldOwn freloop acc k))
            (subst ForkConsistent
                   (cong (λ z → setF (setP cfg i down1) z freloop) own)
                   (cons-pres fc (⊳pd2 i (ep-phil-head i [] (fr-cons eat (fr-nil heldOwn)) acc []))))
    where cfg = extractPairs i [] (fr-cons eat (fr-nil heldOwn)) acc

  -- route-vis returns its own (tree-index-subst'd) fr′ (phil-step′/fork-step′ give
  -- PROPOSITIONAL successor eqs, so fr′ is subst-wrapped on the tree).  extractPairs reads
  -- only POSITIONS, not the tree, so it commutes past the tree-subst.
  extractPairs-subst : ∀ (i : Phil) (S : List Phil) {acc : Config}
                         {t t′ : PTree DP (ExtI DP) (RetOf⁺ (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S))}
                         (eq : t ≡ t′)
                         (fr : FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S)
                                         (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest S) t)
                     → extractPairs i S (subst (FoldReach (philComp asymFirst asymSecond i) (forkComp i ∷ concatMap pairF S)
                                                          (philReachI asymFirst asymSecond i) (forkReachI i ∷ allRest S)) eq fr) acc
                     ≡ extractPairs i S fr acc
  extractPairs-subst i S refl fr = refl








