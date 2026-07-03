{-# OPTIONS --guardedness #-}

-- Deadlock-freedom of the asymmetric dining-philosophers system, built with the
-- *compositional* alphabetised-parallel operator `∥ₐ⁺`, at the concrete instance
-- m = 0 (n = 2).  This is the deadlock-free counterpart of the reachable symmetric
-- deadlock `dp-csp-deadlock-reachable` (same file's `DeadlockReachable` module).
--
-- Strategy (see the session design):
--   * `∥ₐ⁺-reach` decomposes a reachable system state into per-component residuals,
--     pinning `t′ ≡ ∥ₐ⁺ (residuals)`.
--   * Each `loop0` component residual is either sil-headed (a loop-back ⇒ the system
--     has a τ-move ⇒ not stuck) or react-headed-stable (a finite set of "positions").
--   * The all-vis-headed states correspond to relational configs; the asymmetric
--     resource order guarantees some synchronisation is always enabled.

module CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_DeadlockFree where

open import Level using (lift) renaming (zero to lzero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin as Fin
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)

open import Process_Trees
open import Semantics.LTS
open import Semantics.Failures using (_⟹⟨_⟩_; ⟹-refl; ⟹-ev; ⟹-τ)
open import Semantics.Deadlock using (IsStuck; HasDeadlock; DeadlockFree; embed∖√)
open PTree

open import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP

open Sys 0
import CSP.Operators {E = DP} as Ops
open Ops DP-AnyTypes-≟
open EventSet
import CSP.Laws.AlphaParallel {E = DP} as AParLaws
open AParLaws DP-AnyTypes-≟
import CSP.Laws.AlphaParallelList {E = DP} as AParList
open AParList DP-AnyTypes-≟

-- The asymmetric components at n = 2.
--   phil0 grabs fork 1 (asymFirst 0 = 0⊕1 = 1) then fork 0 (asymSecond 0 = 0).
--   phil1 grabs fork 1 (asymFirst 1 = 1)        then fork 0 (asymSecond 1 = 1⊕1 = 0).
philA : Phil → PTree DP (ExtI DP) ⊥
philA i = PHIL asymFirst asymSecond i

forkA : Fork → PTree DP (ExtI DP) ⊥
forkA j = FORK j

-- Probe: phil0 (asym) is react-headed-and-stable, offering picks 0 1 first.
probe-phil0 : VisHead (philA fzero)
probe-phil0 = _ , _ , refl , (λ _ _ → refl)

phil0-v : (at : AnyTypes DP) → ContinueType at (Maybe (PTree DP (ExtI DP) ⊥))
phil0-v = let (v , _ , _ , _) = probe-phil0 in v

-- phil0 offers picks 0 1 (= picks 0 (asymFirst 0)).
probe-phil0-off : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (phil0-v (_ , picks fzero (fsuc fzero)) tt ≡ just t)
probe-phil0-off = _ , refl

------------------------------------------------------------------------------------
-- phil0 reachable positions (asym, i = 0): think → one → eat → down1 → reloop → think.
--   think  offers picks 0 1   (asymFirst 0 = 1)
--   one    offers picks 0 0   (asymSecond 0 = 0)
--   eat    offers putsdown 0 0
--   down1  offers putsdown 0 1
--   reloop is sil-headed back to think.
p0-think : PTree DP (ExtI DP) ⊥
p0-think = philA fzero
p0-one : PTree DP (ExtI DP) ⊥
p0-one = proj₁ probe-phil0-off

probe-p0-one : VisHead p0-one
probe-p0-one = _ , _ , refl , (λ _ _ → refl)
p0-one-v = let (v , _ , _ , _) = probe-p0-one in v
probe-p0-one-off : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (p0-one-v (_ , picks fzero fzero) tt ≡ just t)
probe-p0-one-off = _ , refl
p0-eat : PTree DP (ExtI DP) ⊥
p0-eat = proj₁ probe-p0-one-off

probe-p0-eat : VisHead p0-eat
probe-p0-eat = _ , _ , refl , (λ _ _ → refl)
p0-eat-v = let (v , _ , _ , _) = probe-p0-eat in v
probe-p0-eat-off : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (p0-eat-v (_ , putsdown fzero fzero) tt ≡ just t)
probe-p0-eat-off = _ , refl
p0-down1 : PTree DP (ExtI DP) ⊥
p0-down1 = proj₁ probe-p0-eat-off

probe-p0-down1 : VisHead p0-down1
probe-p0-down1 = _ , _ , refl , (λ _ _ → refl)
p0-down1-v = let (v , _ , _ , _) = probe-p0-down1 in v
probe-p0-down1-off : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (p0-down1-v (_ , putsdown fzero (fsuc fzero)) tt ≡ just t)
probe-p0-down1-off = _ , refl
p0-reloop : PTree DP (ExtI DP) ⊥
p0-reloop = proj₁ probe-p0-down1-off

-- reloop is sil-headed, looping back to think.
probe-p0-reloop : p0-reloop .force ≡ sil p0-think
probe-p0-reloop = refl

-- Closure predicate: the reachable states of phil0.
data Phil0 : PTree DP (ExtI DP) ⊥ → Set where
  is-think  : Phil0 p0-think
  is-one    : Phil0 p0-one
  is-eat    : Phil0 p0-eat
  is-down1  : Phil0 p0-down1
  is-reloop : Phil0 p0-reloop

-- A single LTS step from any phil0 position lands on a phil0 position.  Each vis
-- position has its force ≡ react v τc by refl and τc i a ≡ nothing definitionally,
-- so sRet/sSil/sTau are refuted directly; the 8-way event split leaves exactly one
-- productive offer.  reloop is sil-headed, stepping (sSil) back to think.
phil0-step : ∀ {t l t″} → Phil0 t → t ─[ l ]─► t″ → Phil0 t″
-- think: only picks 0 1 fires, → one.
phil0-step is-think (sRet eq) = case eq of λ ()
phil0-step is-think (sSil eq) = case eq of λ ()
phil0-step is-think (sTau refl br) = case br of λ ()
phil0-step is-think (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
phil0-step is-think (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = subst Phil0 (just-injective br) is-one
phil0-step is-think (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
phil0-step is-think (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil0-step is-think (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
phil0-step is-think (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
phil0-step is-think (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
phil0-step is-think (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
-- one: only picks 0 0 fires, → eat.
phil0-step is-one (sRet eq) = case eq of λ ()
phil0-step is-one (sSil eq) = case eq of λ ()
phil0-step is-one (sTau refl br) = case br of λ ()
phil0-step is-one (sVis {at = _ , picks fzero fzero}                refl br) = subst Phil0 (just-injective br) is-eat
phil0-step is-one (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
phil0-step is-one (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
phil0-step is-one (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil0-step is-one (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
phil0-step is-one (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
phil0-step is-one (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
phil0-step is-one (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
-- eat: only putsdown 0 0 fires, → down1.
phil0-step is-eat (sRet eq) = case eq of λ ()
phil0-step is-eat (sSil eq) = case eq of λ ()
phil0-step is-eat (sTau refl br) = case br of λ ()
phil0-step is-eat (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
phil0-step is-eat (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
phil0-step is-eat (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
phil0-step is-eat (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil0-step is-eat (sVis {at = _ , putsdown fzero fzero}                refl br) = subst Phil0 (just-injective br) is-down1
phil0-step is-eat (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
phil0-step is-eat (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
phil0-step is-eat (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
-- down1: only putsdown 0 1 fires, → reloop.
phil0-step is-down1 (sRet eq) = case eq of λ ()
phil0-step is-down1 (sSil eq) = case eq of λ ()
phil0-step is-down1 (sTau refl br) = case br of λ ()
phil0-step is-down1 (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
phil0-step is-down1 (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
phil0-step is-down1 (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
phil0-step is-down1 (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil0-step is-down1 (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
phil0-step is-down1 (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = subst Phil0 (just-injective br) is-reloop
phil0-step is-down1 (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
phil0-step is-down1 (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
-- reloop: sil-headed, → think.
phil0-step is-reloop (sSil refl) = is-think
phil0-step is-reloop (sRet eq) = case eq of λ ()
phil0-step is-reloop (sTau eq br) = case eq of λ ()
phil0-step is-reloop (sVis eq br) = case eq of λ ()

-- Closure of phil0's reachable states under the τ-absorbing big-step.
phil0-reach : ∀ {s t′} → p0-think ⟹⟨ s ⟩ t′ → Phil0 t′
phil0-reach = go is-think
  where
    go : ∀ {t s t′} → Phil0 t → t ⟹⟨ s ⟩ t′ → Phil0 t′
    go p ⟹-refl          = p
    go p (⟹-τ  st rest)  = go (phil0-step p st) rest
    go p (⟹-ev st rest)  = go (phil0-step p st) rest

------------------------------------------------------------------------------------
-- phil1 reachable positions (asym, i = 1): asymFirst 1 = 1, asymSecond 1 = 1⊕1 = 0.
--   think offers picks 1 1 → one offers picks 1 0 → eat offers putsdown 1 0
--   → down1 offers putsdown 1 1 → reloop.
p1-think : PTree DP (ExtI DP) ⊥
p1-think = philA (fsuc fzero)
probe-phil1 : VisHead p1-think
probe-phil1 = _ , _ , refl , (λ _ _ → refl)
phil1-v = let (v , _ , _ , _) = probe-phil1 in v
probe-phil1-off : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (phil1-v (_ , picks (fsuc fzero) (fsuc fzero)) tt ≡ just t)
probe-phil1-off = _ , refl
p1-one : PTree DP (ExtI DP) ⊥
p1-one = proj₁ probe-phil1-off

probe-p1-one : VisHead p1-one
probe-p1-one = _ , _ , refl , (λ _ _ → refl)
p1-one-v = let (v , _ , _ , _) = probe-p1-one in v
probe-p1-one-off : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (p1-one-v (_ , picks (fsuc fzero) fzero) tt ≡ just t)
probe-p1-one-off = _ , refl
p1-eat : PTree DP (ExtI DP) ⊥
p1-eat = proj₁ probe-p1-one-off

probe-p1-eat : VisHead p1-eat
probe-p1-eat = _ , _ , refl , (λ _ _ → refl)
p1-eat-v = let (v , _ , _ , _) = probe-p1-eat in v
probe-p1-eat-off : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (p1-eat-v (_ , putsdown (fsuc fzero) fzero) tt ≡ just t)
probe-p1-eat-off = _ , refl
p1-down1 : PTree DP (ExtI DP) ⊥
p1-down1 = proj₁ probe-p1-eat-off

probe-p1-down1 : VisHead p1-down1
probe-p1-down1 = _ , _ , refl , (λ _ _ → refl)
p1-down1-v = let (v , _ , _ , _) = probe-p1-down1 in v
probe-p1-down1-off : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (p1-down1-v (_ , putsdown (fsuc fzero) (fsuc fzero)) tt ≡ just t)
probe-p1-down1-off = _ , refl
p1-reloop : PTree DP (ExtI DP) ⊥
p1-reloop = proj₁ probe-p1-down1-off
probe-p1-reloop : p1-reloop .force ≡ sil p1-think
probe-p1-reloop = refl

data Phil1 : PTree DP (ExtI DP) ⊥ → Set where
  is-think  : Phil1 p1-think
  is-one    : Phil1 p1-one
  is-eat    : Phil1 p1-eat
  is-down1  : Phil1 p1-down1
  is-reloop : Phil1 p1-reloop

phil1-step : ∀ {t l t″} → Phil1 t → t ─[ l ]─► t″ → Phil1 t″
phil1-step is-think (sRet eq) = case eq of λ ()
phil1-step is-think (sSil eq) = case eq of λ ()
phil1-step is-think (sTau refl br) = case br of λ ()
phil1-step is-think (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
phil1-step is-think (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
phil1-step is-think (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
phil1-step is-think (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = subst Phil1 (just-injective br) is-one
phil1-step is-think (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
phil1-step is-think (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
phil1-step is-think (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
phil1-step is-think (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil1-step is-one (sRet eq) = case eq of λ ()
phil1-step is-one (sSil eq) = case eq of λ ()
phil1-step is-one (sTau refl br) = case br of λ ()
phil1-step is-one (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
phil1-step is-one (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
phil1-step is-one (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = subst Phil1 (just-injective br) is-eat
phil1-step is-one (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil1-step is-one (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
phil1-step is-one (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
phil1-step is-one (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
phil1-step is-one (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil1-step is-eat (sRet eq) = case eq of λ ()
phil1-step is-eat (sSil eq) = case eq of λ ()
phil1-step is-eat (sTau refl br) = case br of λ ()
phil1-step is-eat (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
phil1-step is-eat (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
phil1-step is-eat (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
phil1-step is-eat (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil1-step is-eat (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
phil1-step is-eat (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
phil1-step is-eat (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = subst Phil1 (just-injective br) is-down1
phil1-step is-eat (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil1-step is-down1 (sRet eq) = case eq of λ ()
phil1-step is-down1 (sSil eq) = case eq of λ ()
phil1-step is-down1 (sTau refl br) = case br of λ ()
phil1-step is-down1 (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
phil1-step is-down1 (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
phil1-step is-down1 (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
phil1-step is-down1 (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil1-step is-down1 (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
phil1-step is-down1 (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
phil1-step is-down1 (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
phil1-step is-down1 (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = subst Phil1 (just-injective br) is-reloop
phil1-step is-reloop (sSil refl) = is-think
phil1-step is-reloop (sRet eq) = case eq of λ ()
phil1-step is-reloop (sTau eq br) = case eq of λ ()
phil1-step is-reloop (sVis eq br) = case eq of λ ()

phil1-reach : ∀ {s t′} → p1-think ⟹⟨ s ⟩ t′ → Phil1 t′
phil1-reach = go is-think
  where
    go : ∀ {t s t′} → Phil1 t → t ⟹⟨ s ⟩ t′ → Phil1 t′
    go p ⟹-refl         = p
    go p (⟹-τ  st rest) = go (phil1-step p st) rest
    go p (⟹-ev st rest) = go (phil1-step p st) rest

------------------------------------------------------------------------------------
-- fork0 reachable positions (j = 0; 0⊖1 = 1).  The free position is the □ entry,
-- offering BOTH picks 0 0 (own) and picks 1 0 (nbr).  Its τ-map needs the structured
-- index case-split for stability (the □ merge), copied from DeadlockReachable.probeFst.
f0-free : PTree DP (ExtI DP) ⊥
f0-free = forkA fzero
probe-f0-force : Σ[ v ∈ _ ] Σ[ τc ∈ _ ] f0-free .force ≡ react v τc
probe-f0-force = _ , _ , refl
f0-free-v  = let (v , _ , _) = probe-f0-force in v
f0-free-τc = let (_ , τc , _) = probe-f0-force in τc
st-f0-free : ∀ i a → f0-free-τc i a ≡ nothing
st-f0-free (_ , base _)            _ = refl
st-f0-free (_ , fin)               _ = refl
st-f0-free (_ , pair (base _) _)   _ = refl
st-f0-free (_ , pair (pair _ _) _) _ = refl
st-f0-free (_ , pair fin i) (lift fzero , a)           = refl
st-f0-free (_ , pair fin i) (lift (fsuc fzero) , a)    = refl
st-f0-free (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = refl

probe-f0-own : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (f0-free-v (_ , picks fzero fzero) tt ≡ just t)
probe-f0-own = _ , refl
f0-heldOwn : PTree DP (ExtI DP) ⊥
f0-heldOwn = proj₁ probe-f0-own
probe-f0-nbr : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (f0-free-v (_ , picks (fsuc fzero) fzero) tt ≡ just t)
probe-f0-nbr = _ , refl
f0-heldNbr : PTree DP (ExtI DP) ⊥
f0-heldNbr = proj₁ probe-f0-nbr

probe-f0-heldOwn : VisHead f0-heldOwn
probe-f0-heldOwn = _ , _ , refl , (λ _ _ → refl)
f0-heldOwn-v = let (v , _ , _ , _) = probe-f0-heldOwn in v
probe-f0-heldOwn-off : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (f0-heldOwn-v (_ , putsdown fzero fzero) tt ≡ just t)
probe-f0-heldOwn-off = _ , refl
f0-reloop : PTree DP (ExtI DP) ⊥
f0-reloop = proj₁ probe-f0-heldOwn-off

probe-f0-heldNbr : VisHead f0-heldNbr
probe-f0-heldNbr = _ , _ , refl , (λ _ _ → refl)
f0-heldNbr-v = let (v , _ , _ , _) = probe-f0-heldNbr in v
-- heldNbr's putsdown 1 0 residual is the SAME reloop (both iter-bind (Ret (inj₁ tt)) step).
probe-f0-heldNbr-off : f0-heldNbr-v (_ , putsdown (fsuc fzero) fzero) tt ≡ just f0-reloop
probe-f0-heldNbr-off = refl
probe-f0-reloop : f0-reloop .force ≡ sil f0-free
probe-f0-reloop = refl

data Fork0 : PTree DP (ExtI DP) ⊥ → Set where
  is-free    : Fork0 f0-free
  is-heldOwn : Fork0 f0-heldOwn
  is-heldNbr : Fork0 f0-heldNbr
  is-reloop  : Fork0 f0-reloop

fork0-step : ∀ {t l t″} → Fork0 t → t ─[ l ]─► t″ → Fork0 t″
-- free: picks 0 0 → heldOwn, picks 1 0 → heldNbr.  (structured sTau refutation)
fork0-step is-free (sRet eq) = case eq of λ ()
fork0-step is-free (sSil eq) = case eq of λ ()
fork0-step is-free (sTau {i = i} {a = a} refl br) = case trans (sym (st-f0-free i a)) br of λ ()
fork0-step is-free (sVis {at = _ , picks fzero fzero}                refl br) = subst Fork0 (just-injective br) is-heldOwn
fork0-step is-free (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
fork0-step is-free (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = subst Fork0 (just-injective br) is-heldNbr
fork0-step is-free (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork0-step is-free (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
fork0-step is-free (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
fork0-step is-free (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
fork0-step is-free (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
-- heldOwn: only putsdown 0 0 fires, → reloop.
fork0-step is-heldOwn (sRet eq) = case eq of λ ()
fork0-step is-heldOwn (sSil eq) = case eq of λ ()
fork0-step is-heldOwn (sTau refl br) = case br of λ ()
fork0-step is-heldOwn (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
fork0-step is-heldOwn (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
fork0-step is-heldOwn (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
fork0-step is-heldOwn (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork0-step is-heldOwn (sVis {at = _ , putsdown fzero fzero}                refl br) = subst Fork0 (just-injective br) is-reloop
fork0-step is-heldOwn (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
fork0-step is-heldOwn (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
fork0-step is-heldOwn (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
-- heldNbr: only putsdown 1 0 fires, → reloop.
fork0-step is-heldNbr (sRet eq) = case eq of λ ()
fork0-step is-heldNbr (sSil eq) = case eq of λ ()
fork0-step is-heldNbr (sTau refl br) = case br of λ ()
fork0-step is-heldNbr (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
fork0-step is-heldNbr (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
fork0-step is-heldNbr (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
fork0-step is-heldNbr (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork0-step is-heldNbr (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
fork0-step is-heldNbr (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
fork0-step is-heldNbr (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = subst Fork0 (just-injective br) is-reloop
fork0-step is-heldNbr (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
-- reloop: sil-headed, → free.
fork0-step is-reloop (sSil refl) = is-free
fork0-step is-reloop (sRet eq) = case eq of λ ()
fork0-step is-reloop (sTau eq br) = case eq of λ ()
fork0-step is-reloop (sVis eq br) = case eq of λ ()

fork0-reach : ∀ {s t′} → f0-free ⟹⟨ s ⟩ t′ → Fork0 t′
fork0-reach = go is-free
  where
    go : ∀ {t s t′} → Fork0 t → t ⟹⟨ s ⟩ t′ → Fork0 t′
    go p ⟹-refl         = p
    go p (⟹-τ  st rest) = go (fork0-step p st) rest
    go p (⟹-ev st rest) = go (fork0-step p st) rest

------------------------------------------------------------------------------------
-- fork1 reachable positions (j = 1; 1⊖1 = 0).  free offers picks 1 1 (own) and
-- picks 0 1 (nbr); heldOwn → putsdown 1 1; heldNbr → putsdown 0 1.
f1-free : PTree DP (ExtI DP) ⊥
f1-free = forkA (fsuc fzero)
probe-f1-force : Σ[ v ∈ _ ] Σ[ τc ∈ _ ] f1-free .force ≡ react v τc
probe-f1-force = _ , _ , refl
f1-free-v  = let (v , _ , _) = probe-f1-force in v
f1-free-τc = let (_ , τc , _) = probe-f1-force in τc
st-f1-free : ∀ i a → f1-free-τc i a ≡ nothing
st-f1-free (_ , base _)            _ = refl
st-f1-free (_ , fin)               _ = refl
st-f1-free (_ , pair (base _) _)   _ = refl
st-f1-free (_ , pair (pair _ _) _) _ = refl
st-f1-free (_ , pair fin i) (lift fzero , a)           = refl
st-f1-free (_ , pair fin i) (lift (fsuc fzero) , a)    = refl
st-f1-free (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = refl

probe-f1-own : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (f1-free-v (_ , picks (fsuc fzero) (fsuc fzero)) tt ≡ just t)
probe-f1-own = _ , refl
f1-heldOwn : PTree DP (ExtI DP) ⊥
f1-heldOwn = proj₁ probe-f1-own
probe-f1-nbr : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (f1-free-v (_ , picks fzero (fsuc fzero)) tt ≡ just t)
probe-f1-nbr = _ , refl
f1-heldNbr : PTree DP (ExtI DP) ⊥
f1-heldNbr = proj₁ probe-f1-nbr

probe-f1-heldOwn : VisHead f1-heldOwn
probe-f1-heldOwn = _ , _ , refl , (λ _ _ → refl)
f1-heldOwn-v = let (v , _ , _ , _) = probe-f1-heldOwn in v
probe-f1-heldOwn-off : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (f1-heldOwn-v (_ , putsdown (fsuc fzero) (fsuc fzero)) tt ≡ just t)
probe-f1-heldOwn-off = _ , refl
f1-reloop : PTree DP (ExtI DP) ⊥
f1-reloop = proj₁ probe-f1-heldOwn-off

probe-f1-heldNbr : VisHead f1-heldNbr
probe-f1-heldNbr = _ , _ , refl , (λ _ _ → refl)
f1-heldNbr-v = let (v , _ , _ , _) = probe-f1-heldNbr in v
probe-f1-heldNbr-off : f1-heldNbr-v (_ , putsdown fzero (fsuc fzero)) tt ≡ just f1-reloop
probe-f1-heldNbr-off = refl
probe-f1-reloop : f1-reloop .force ≡ sil f1-free
probe-f1-reloop = refl

data Fork1 : PTree DP (ExtI DP) ⊥ → Set where
  is-free    : Fork1 f1-free
  is-heldOwn : Fork1 f1-heldOwn
  is-heldNbr : Fork1 f1-heldNbr
  is-reloop  : Fork1 f1-reloop

fork1-step : ∀ {t l t″} → Fork1 t → t ─[ l ]─► t″ → Fork1 t″
fork1-step is-free (sRet eq) = case eq of λ ()
fork1-step is-free (sSil eq) = case eq of λ ()
fork1-step is-free (sTau {i = i} {a = a} refl br) = case trans (sym (st-f1-free i a)) br of λ ()
fork1-step is-free (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
fork1-step is-free (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = subst Fork1 (just-injective br) is-heldNbr
fork1-step is-free (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
fork1-step is-free (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = subst Fork1 (just-injective br) is-heldOwn
fork1-step is-free (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
fork1-step is-free (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
fork1-step is-free (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
fork1-step is-free (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork1-step is-heldOwn (sRet eq) = case eq of λ ()
fork1-step is-heldOwn (sSil eq) = case eq of λ ()
fork1-step is-heldOwn (sTau refl br) = case br of λ ()
fork1-step is-heldOwn (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
fork1-step is-heldOwn (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
fork1-step is-heldOwn (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
fork1-step is-heldOwn (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork1-step is-heldOwn (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
fork1-step is-heldOwn (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
fork1-step is-heldOwn (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
fork1-step is-heldOwn (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = subst Fork1 (just-injective br) is-reloop
fork1-step is-heldNbr (sRet eq) = case eq of λ ()
fork1-step is-heldNbr (sSil eq) = case eq of λ ()
fork1-step is-heldNbr (sTau refl br) = case br of λ ()
fork1-step is-heldNbr (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
fork1-step is-heldNbr (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
fork1-step is-heldNbr (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
fork1-step is-heldNbr (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork1-step is-heldNbr (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
fork1-step is-heldNbr (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = subst Fork1 (just-injective br) is-reloop
fork1-step is-heldNbr (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
fork1-step is-heldNbr (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork1-step is-reloop (sSil refl) = is-free
fork1-step is-reloop (sRet eq) = case eq of λ ()
fork1-step is-reloop (sTau eq br) = case eq of λ ()
fork1-step is-reloop (sVis eq br) = case eq of λ ()

fork1-reach : ∀ {s t′} → f1-free ⟹⟨ s ⟩ t′ → Fork1 t′
fork1-reach = go is-free
  where
    go : ∀ {t s t′} → Fork1 t → t ⟹⟨ s ⟩ t′ → Fork1 t′
    go p ⟹-refl         = p
    go p (⟹-τ  st rest) = go (fork1-step p st) rest
    go p (⟹-ev st rest) = go (fork1-step p st) rest

------------------------------------------------------------------------------------
-- Stage 3 scaffolding: the system state as a fold of per-component position trees.
-- The four SYSTEMasym components and the system tree:
--   SYSTEMasym = ∥ₐ⁺ cP0 [cF0, cP1, cF1]
--              = proc cP0 ⟦αP0 ∥ U1⟧ (proc cF0 ⟦αF0 ∥ U2⟧ (proc cP1 ⟦αP1 ∥ U3⟧ proc cF1))
cP0 cF0 cP1 cF1 : Comp DP ⊥
cP0 = philComp asymFirst asymSecond fzero
cF0 = forkComp fzero
cP1 = philComp asymFirst asymSecond (fsuc fzero)
cF1 = forkComp (fsuc fzero)

-- Position tags.
data PPos : Set where pT pO pE pD pR : PPos
data FPos : Set where fF fHO fHN fR : FPos

p0tree : PPos → PTree DP (ExtI DP) ⊥
p0tree pT = p0-think
p0tree pO = p0-one
p0tree pE = p0-eat
p0tree pD = p0-down1
p0tree pR = p0-reloop
p1tree : PPos → PTree DP (ExtI DP) ⊥
p1tree pT = p1-think
p1tree pO = p1-one
p1tree pE = p1-eat
p1tree pD = p1-down1
p1tree pR = p1-reloop
f0tree : FPos → PTree DP (ExtI DP) ⊥
f0tree fF  = f0-free
f0tree fHO = f0-heldOwn
f0tree fHN = f0-heldNbr
f0tree fR  = f0-reloop
f1tree : FPos → PTree DP (ExtI DP) ⊥
f1tree fF  = f1-free
f1tree fHO = f1-heldOwn
f1tree fHN = f1-heldNbr
f1tree fR  = f1-reloop

SCfg : Set
SCfg = PPos × FPos × PPos × FPos

sysState : SCfg → PTree DP (ExtI DP) (RetOf⁺ cP0 (cF0 ∷ cP1 ∷ cF1 ∷ []))
sysState (p0 , f0 , p1 , f1) =
  p0tree p0 ⟦ Comp.alpha cP0 ∥ unionα (cF0 ∷ cP1 ∷ cF1 ∷ []) ⟧
  (f0tree f0 ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧
  (p1tree p1 ⟦ Comp.alpha cP1 ∥ unionα (cF1 ∷ []) ⟧
   f1tree f1))

cfg0 : SCfg
cfg0 = pT , fF , pT , fF

-- SYSTEMasym is the initial system state.
sys≡ : SYSTEMasym ≡ sysState cfg0
sys≡ = refl

------------------------------------------------------------------------------------
-- Evidence ↔ tag conversions, and "never returns" (phils/forks never reach ret).
phil0-of : (p : PPos) → Phil0 (p0tree p)
phil0-of pT = is-think
phil0-of pO = is-one
phil0-of pE = is-eat
phil0-of pD = is-down1
phil0-of pR = is-reloop
phil0-tag : ∀ {t} → Phil0 t → Σ[ p ∈ PPos ] (t ≡ p0tree p)
phil0-tag is-think  = pT , refl
phil0-tag is-one    = pO , refl
phil0-tag is-eat    = pE , refl
phil0-tag is-down1  = pD , refl
phil0-tag is-reloop = pR , refl
phil1-of : (p : PPos) → Phil1 (p1tree p)
phil1-of pT = is-think
phil1-of pO = is-one
phil1-of pE = is-eat
phil1-of pD = is-down1
phil1-of pR = is-reloop
phil1-tag : ∀ {t} → Phil1 t → Σ[ p ∈ PPos ] (t ≡ p1tree p)
phil1-tag is-think  = pT , refl
phil1-tag is-one    = pO , refl
phil1-tag is-eat    = pE , refl
phil1-tag is-down1  = pD , refl
phil1-tag is-reloop = pR , refl
fork0-of : (f : FPos) → Fork0 (f0tree f)
fork0-of fF  = is-free
fork0-of fHO = is-heldOwn
fork0-of fHN = is-heldNbr
fork0-of fR  = is-reloop
fork0-tag : ∀ {t} → Fork0 t → Σ[ f ∈ FPos ] (t ≡ f0tree f)
fork0-tag is-free    = fF  , refl
fork0-tag is-heldOwn = fHO , refl
fork0-tag is-heldNbr = fHN , refl
fork0-tag is-reloop  = fR  , refl
fork1-of : (f : FPos) → Fork1 (f1tree f)
fork1-of fF  = is-free
fork1-of fHO = is-heldOwn
fork1-of fHN = is-heldNbr
fork1-of fR  = is-reloop
fork1-tag : ∀ {t} → Fork1 t → Σ[ f ∈ FPos ] (t ≡ f1tree f)
fork1-tag is-free    = fF  , refl
fork1-tag is-heldOwn = fHO , refl
fork1-tag is-heldNbr = fHN , refl
fork1-tag is-reloop  = fR  , refl

p0tree-not-ret : ∀ p {x} → p0tree p .force ≡ ret x → ⊥
p0tree-not-ret pT () ; p0tree-not-ret pO () ; p0tree-not-ret pE ()
p0tree-not-ret pD () ; p0tree-not-ret pR ()
p1tree-not-ret : ∀ p {x} → p1tree p .force ≡ ret x → ⊥
p1tree-not-ret pT () ; p1tree-not-ret pO () ; p1tree-not-ret pE ()
p1tree-not-ret pD () ; p1tree-not-ret pR ()
f0tree-not-ret : ∀ f {x} → f0tree f .force ≡ ret x → ⊥
f0tree-not-ret fF () ; f0tree-not-ret fHO () ; f0tree-not-ret fHN () ; f0tree-not-ret fR ()

------------------------------------------------------------------------------------
-- Level 3 (innermost): L3 = phil1 ⟦∥⟧ fork1.  Invert one step into new positions.
L3-tree : PPos → FPos → PTree DP (ExtI DP) (RetOf⁺ cP1 (cF1 ∷ []))
L3-tree p1 f1 = p1tree p1 ⟦ Comp.alpha cP1 ∥ unionα (cF1 ∷ []) ⟧ f1tree f1

L3-step : ∀ p1 f1 {l t′} → L3-tree p1 f1 ─[ l ]─► t′
        → Σ[ p1′ ∈ PPos ] Σ[ f1′ ∈ FPos ] (t′ ≡ L3-tree p1′ f1′)
L3-step p1 f1 (sRet feq) with αpar-√-step-inv feq
... | v√ peq _ = ⊥-elim (p1tree-not-ret p1 peq)
L3-step p1 f1 (sSil feq) with αpar-τ-step-inv (sSil feq)
... | inj₁ (P′ , pτ , refl) =
      let (p1′ , eq) = phil1-tag (phil1-step (phil1-of p1) pτ)
      in p1′ , f1 , cong (λ z → z ⟦ Comp.alpha cP1 ∥ unionα (cF1 ∷ []) ⟧ f1tree f1) eq
... | inj₂ (Q′ , qτ , refl) =
      let (f1′ , eq) = fork1-tag (fork1-step (fork1-of f1) qτ)
      in p1 , f1′ , cong (λ z → p1tree p1 ⟦ Comp.alpha cP1 ∥ unionα (cF1 ∷ []) ⟧ z) eq
L3-step p1 f1 (sTau feq br) with αpar-τ-step-inv (sTau feq br)
... | inj₁ (P′ , pτ , refl) =
      let (p1′ , eq) = phil1-tag (phil1-step (phil1-of p1) pτ)
      in p1′ , f1 , cong (λ z → z ⟦ Comp.alpha cP1 ∥ unionα (cF1 ∷ []) ⟧ f1tree f1) eq
... | inj₂ (Q′ , qτ , refl) =
      let (f1′ , eq) = fork1-tag (fork1-step (fork1-of f1) qτ)
      in p1 , f1′ , cong (λ z → p1tree p1 ⟦ Comp.alpha cP1 ∥ unionα (cF1 ∷ []) ⟧ z) eq
L3-step p1 f1 (sVis feq br) with αpar-vis-step-inv feq br
... | vSync _ _ pst qst =
      let (p1′ , eqp) = phil1-tag (phil1-step (phil1-of p1) pst)
          (f1′ , eqq) = fork1-tag (fork1-step (fork1-of f1) qst)
      in p1′ , f1′ , cong₂ (λ y z → y ⟦ Comp.alpha cP1 ∥ unionα (cF1 ∷ []) ⟧ z) eqp eqq
... | vSoloL _ _ pst =
      let (p1′ , eq) = phil1-tag (phil1-step (phil1-of p1) pst)
      in p1′ , f1 , cong (λ z → z ⟦ Comp.alpha cP1 ∥ unionα (cF1 ∷ []) ⟧ f1tree f1) eq
... | vSoloR _ _ qst =
      let (f1′ , eq) = fork1-tag (fork1-step (fork1-of f1) qst)
      in p1 , f1′ , cong (λ z → p1tree p1 ⟦ Comp.alpha cP1 ∥ unionα (cF1 ∷ []) ⟧ z) eq

------------------------------------------------------------------------------------
-- Level 2: L2 = fork0 ⟦∥⟧ L3.  Invert one step, recursing into L3-step on the right.
L2-tree : FPos → PPos → FPos → PTree DP (ExtI DP) (RetOf⁺ cF0 (cP1 ∷ cF1 ∷ []))
L2-tree f0 p1 f1 = f0tree f0 ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧ L3-tree p1 f1

L2-step : ∀ f0 p1 f1 {l t′} → L2-tree f0 p1 f1 ─[ l ]─► t′
        → Σ[ f0′ ∈ FPos ] Σ[ p1′ ∈ PPos ] Σ[ f1′ ∈ FPos ] (t′ ≡ L2-tree f0′ p1′ f1′)
L2-step f0 p1 f1 (sRet feq) with αpar-√-step-inv feq
... | v√ peq _ = ⊥-elim (f0tree-not-ret f0 peq)
L2-step f0 p1 f1 (sSil feq) with αpar-τ-step-inv (sSil feq)
... | inj₁ (P′ , pτ , refl) =
      let (f0′ , eq) = fork0-tag (fork0-step (fork0-of f0) pτ)
      in f0′ , p1 , f1 , cong (λ z → z ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧ L3-tree p1 f1) eq
... | inj₂ (Q′ , qτ , refl) =
      let (p1′ , f1′ , eq) = L3-step p1 f1 qτ
      in f0 , p1′ , f1′ , cong (λ z → f0tree f0 ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧ z) eq
L2-step f0 p1 f1 (sTau feq br) with αpar-τ-step-inv (sTau feq br)
... | inj₁ (P′ , pτ , refl) =
      let (f0′ , eq) = fork0-tag (fork0-step (fork0-of f0) pτ)
      in f0′ , p1 , f1 , cong (λ z → z ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧ L3-tree p1 f1) eq
... | inj₂ (Q′ , qτ , refl) =
      let (p1′ , f1′ , eq) = L3-step p1 f1 qτ
      in f0 , p1′ , f1′ , cong (λ z → f0tree f0 ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧ z) eq
L2-step f0 p1 f1 (sVis feq br) with αpar-vis-step-inv feq br
... | vSync _ _ pst qst =
      let (f0′ , eqp) = fork0-tag (fork0-step (fork0-of f0) pst)
          (p1′ , f1′ , eqq) = L3-step p1 f1 qst
      in f0′ , p1′ , f1′ , cong₂ (λ y z → y ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧ z) eqp eqq
... | vSoloL _ _ pst =
      let (f0′ , eq) = fork0-tag (fork0-step (fork0-of f0) pst)
      in f0′ , p1 , f1 , cong (λ z → z ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧ L3-tree p1 f1) eq
... | vSoloR _ _ qst =
      let (p1′ , f1′ , eq) = L3-step p1 f1 qst
      in f0 , p1′ , f1′ , cong (λ z → f0tree f0 ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧ z) eq

------------------------------------------------------------------------------------
-- Level 1 (the whole system): sysState = phil0 ⟦∥⟧ L2.  Invert one step into a
-- successor config (structural closure; consistency handled separately).
sys-step : ∀ cfg {l t′} → sysState cfg ─[ l ]─► t′ → Σ[ cfg′ ∈ SCfg ] (t′ ≡ sysState cfg′)
sys-step (p0 , f0 , p1 , f1) (sRet feq) with αpar-√-step-inv feq
... | v√ peq _ = ⊥-elim (p0tree-not-ret p0 peq)
sys-step (p0 , f0 , p1 , f1) (sSil feq) with αpar-τ-step-inv (sSil feq)
... | inj₁ (P′ , pτ , refl) =
      let (p0′ , eq) = phil0-tag (phil0-step (phil0-of p0) pτ)
      in (p0′ , f0 , p1 , f1) , cong (λ z → z ⟦ Comp.alpha cP0 ∥ unionα (cF0 ∷ cP1 ∷ cF1 ∷ []) ⟧ L2-tree f0 p1 f1) eq
... | inj₂ (Q′ , qτ , refl) =
      let (f0′ , p1′ , f1′ , eq) = L2-step f0 p1 f1 qτ
      in (p0 , f0′ , p1′ , f1′) , cong (λ z → p0tree p0 ⟦ Comp.alpha cP0 ∥ unionα (cF0 ∷ cP1 ∷ cF1 ∷ []) ⟧ z) eq
sys-step (p0 , f0 , p1 , f1) (sTau feq br) with αpar-τ-step-inv (sTau feq br)
... | inj₁ (P′ , pτ , refl) =
      let (p0′ , eq) = phil0-tag (phil0-step (phil0-of p0) pτ)
      in (p0′ , f0 , p1 , f1) , cong (λ z → z ⟦ Comp.alpha cP0 ∥ unionα (cF0 ∷ cP1 ∷ cF1 ∷ []) ⟧ L2-tree f0 p1 f1) eq
... | inj₂ (Q′ , qτ , refl) =
      let (f0′ , p1′ , f1′ , eq) = L2-step f0 p1 f1 qτ
      in (p0 , f0′ , p1′ , f1′) , cong (λ z → p0tree p0 ⟦ Comp.alpha cP0 ∥ unionα (cF0 ∷ cP1 ∷ cF1 ∷ []) ⟧ z) eq
sys-step (p0 , f0 , p1 , f1) (sVis feq br) with αpar-vis-step-inv feq br
... | vSync _ _ pst qst =
      let (p0′ , eqp) = phil0-tag (phil0-step (phil0-of p0) pst)
          (f0′ , p1′ , f1′ , eqq) = L2-step f0 p1 f1 qst
      in (p0′ , f0′ , p1′ , f1′) , cong₂ (λ y z → y ⟦ Comp.alpha cP0 ∥ unionα (cF0 ∷ cP1 ∷ cF1 ∷ []) ⟧ z) eqp eqq
... | vSoloL _ _ pst =
      let (p0′ , eq) = phil0-tag (phil0-step (phil0-of p0) pst)
      in (p0′ , f0 , p1 , f1) , cong (λ z → z ⟦ Comp.alpha cP0 ∥ unionα (cF0 ∷ cP1 ∷ cF1 ∷ []) ⟧ L2-tree f0 p1 f1) eq
... | vSoloR _ _ qst =
      let (f0′ , p1′ , f1′ , eq) = L2-step f0 p1 f1 qst
      in (p0 , f0′ , p1′ , f1′) , cong (λ z → p0tree p0 ⟦ Comp.alpha cP0 ∥ unionα (cF0 ∷ cP1 ∷ cF1 ∷ []) ⟧ z) eq

-- Closure of reachable system states under the big-step.
sys-reach : ∀ {s t′} → sysState cfg0 ⟹⟨ s ⟩ t′ → Σ[ cfg′ ∈ SCfg ] (t′ ≡ sysState cfg′)
sys-reach = go cfg0 refl
  where
    go : ∀ cfg {t s t′} → t ≡ sysState cfg → t ⟹⟨ s ⟩ t′ → Σ[ cfg′ ∈ SCfg ] (t′ ≡ sysState cfg′)
    go cfg refl ⟹-refl          = cfg , refl
    go cfg refl (⟹-τ  st rest)  = let (cfg′ , eq) = sys-step cfg st in go cfg′ eq rest
    go cfg refl (⟹-ev st rest)  = let (cfg′ , eq) = sys-step cfg st in go cfg′ eq rest

------------------------------------------------------------------------------------
-- Stage 4: the consistency invariant.  A philosopher "holds" forks per its position;
-- the fork's recorded holder must match.  Encoded with Bool so per-transition
-- preservation reduces by refl.
hold1 : PPos → Bool   -- holds fork 1 (its FIRST fork at n=2)
hold1 pT = false ; hold1 pO = true ; hold1 pE = true ; hold1 pD = true ; hold1 pR = false
hold0 : PPos → Bool   -- holds fork 0 (its SECOND fork; only while eating)
hold0 pT = false ; hold0 pO = false ; hold0 pE = true ; hold0 pD = false ; hold0 pR = false
isHO0 isHN0 isHO1 isHN1 : FPos → Bool
isHO0 fHO = true ; isHO0 fF = false ; isHO0 fHN = false ; isHO0 fR = false
isHN0 fHN = true ; isHN0 fF = false ; isHN0 fHO = false ; isHN0 fR = false
isHO1 fHO = true ; isHO1 fF = false ; isHO1 fHN = false ; isHO1 fR = false
isHN1 fHN = true ; isHN1 fF = false ; isHN1 fHO = false ; isHN1 fR = false

-- fork0 owner is phil0 (p=0); fork0 nbr is phil1 (0⊖1=1).
-- fork1 owner is phil1 (p=1); fork1 nbr is phil0 (1⊖1=0).
Cons : SCfg → Set
Cons (p0 , f0 , p1 , f1) =
    (hold1 p0 ≡ isHN1 f1)   -- phil0 holds fork1  ⟺  fork1 held by its nbr (phil0)
  × (hold1 p1 ≡ isHO1 f1)   -- phil1 holds fork1  ⟺  fork1 held by its owner (phil1)
  × (hold0 p0 ≡ isHO0 f0)   -- phil0 holds fork0  ⟺  fork0 held by its owner (phil0)
  × (hold0 p1 ≡ isHN0 f0)   -- phil1 holds fork0  ⟺  fork0 held by its nbr (phil1)

cons0 : Cons cfg0
cons0 = refl , refl , refl , refl

------------------------------------------------------------------------------------
-- Enriched per-component step lemmas: return the local transition (old→new) INDEXED by
-- the triggering label, so the system inversion can correlate the two synced operands
-- (they share the label) and assemble a config transition.  Cons-preservation then
-- reduces by computation.
-- Index transitions by the R-INDEPENDENT event (visible event or τ), since αpar levels
-- change the carrier R while a vSync shares the same underlying Event (X,e,a).
DPEvent : Set₁
DPEvent = Event {E = DP} {I = ExtI DP}
evt : DP (⊤ {lzero}) → Maybe DPEvent
evt e = just (evLabel (⊤ {lzero}) e tt)
evOf : ∀ {ℓr} {R : Set ℓr} → Label {E = DP} {I = ExtI DP} R → Maybe DPEvent
evOf (ev (evl e)) = just e
evOf (ev (√ _))   = nothing
evOf τ            = nothing

data P0Tr : PPos → PPos → Maybe DPEvent → Set where
  tp01 : P0Tr pT pO (evt (picks fzero (fsuc fzero)))
  tp00 : P0Tr pO pE (evt (picks fzero fzero))
  tpd0 : P0Tr pE pD (evt (putsdown fzero fzero))
  tpd1 : P0Tr pD pR (evt (putsdown fzero (fsuc fzero)))
  tlp  : P0Tr pR pT nothing
data P1Tr : PPos → PPos → Maybe DPEvent → Set where
  tp11 : P1Tr pT pO (evt (picks (fsuc fzero) (fsuc fzero)))
  tp10 : P1Tr pO pE (evt (picks (fsuc fzero) fzero))
  tpd0 : P1Tr pE pD (evt (putsdown (fsuc fzero) fzero))
  tpd1 : P1Tr pD pR (evt (putsdown (fsuc fzero) (fsuc fzero)))
  tlp  : P1Tr pR pT nothing

phil0-step′ : ∀ p {l t′} → p0tree p ─[ l ]─► t′ → Σ[ p′ ∈ PPos ] (t′ ≡ p0tree p′ × P0Tr p p′ (evOf l))
phil0-step′ pT (sRet eq) = case eq of λ ()
phil0-step′ pT (sSil eq) = case eq of λ ()
phil0-step′ pT (sTau refl br) = case br of λ ()
phil0-step′ pT (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
phil0-step′ pT (sVis {at = _ , picks fzero (fsuc fzero)}         {a = tt} refl br) = pO , sym (just-injective br) , tp01
phil0-step′ pT (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
phil0-step′ pT (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil0-step′ pT (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
phil0-step′ pT (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
phil0-step′ pT (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
phil0-step′ pT (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil0-step′ pO (sRet eq) = case eq of λ ()
phil0-step′ pO (sSil eq) = case eq of λ ()
phil0-step′ pO (sTau refl br) = case br of λ ()
phil0-step′ pO (sVis {at = _ , picks fzero fzero}                {a = tt} refl br) = pE , sym (just-injective br) , tp00
phil0-step′ pO (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
phil0-step′ pO (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
phil0-step′ pO (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil0-step′ pO (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
phil0-step′ pO (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
phil0-step′ pO (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
phil0-step′ pO (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil0-step′ pE (sRet eq) = case eq of λ ()
phil0-step′ pE (sSil eq) = case eq of λ ()
phil0-step′ pE (sTau refl br) = case br of λ ()
phil0-step′ pE (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
phil0-step′ pE (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
phil0-step′ pE (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
phil0-step′ pE (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil0-step′ pE (sVis {at = _ , putsdown fzero fzero}                {a = tt} refl br) = pD , sym (just-injective br) , tpd0
phil0-step′ pE (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
phil0-step′ pE (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
phil0-step′ pE (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil0-step′ pD (sRet eq) = case eq of λ ()
phil0-step′ pD (sSil eq) = case eq of λ ()
phil0-step′ pD (sTau refl br) = case br of λ ()
phil0-step′ pD (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
phil0-step′ pD (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
phil0-step′ pD (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
phil0-step′ pD (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil0-step′ pD (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
phil0-step′ pD (sVis {at = _ , putsdown fzero (fsuc fzero)}         {a = tt} refl br) = pR , sym (just-injective br) , tpd1
phil0-step′ pD (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
phil0-step′ pD (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil0-step′ pR (sSil refl) = pT , refl , tlp
phil0-step′ pR (sRet eq) = case eq of λ ()
phil0-step′ pR (sTau eq br) = case eq of λ ()
phil0-step′ pR (sVis eq br) = case eq of λ ()

phil1-step′ : ∀ p {l t′} → p1tree p ─[ l ]─► t′ → Σ[ p′ ∈ PPos ] (t′ ≡ p1tree p′ × P1Tr p p′ (evOf l))
phil1-step′ pT (sRet eq) = case eq of λ ()
phil1-step′ pT (sSil eq) = case eq of λ ()
phil1-step′ pT (sTau refl br) = case br of λ ()
phil1-step′ pT (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
phil1-step′ pT (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
phil1-step′ pT (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
phil1-step′ pT (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  {a = tt} refl br) = pO , sym (just-injective br) , tp11
phil1-step′ pT (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
phil1-step′ pT (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
phil1-step′ pT (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
phil1-step′ pT (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil1-step′ pO (sRet eq) = case eq of λ ()
phil1-step′ pO (sSil eq) = case eq of λ ()
phil1-step′ pO (sTau refl br) = case br of λ ()
phil1-step′ pO (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
phil1-step′ pO (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
phil1-step′ pO (sVis {at = _ , picks (fsuc fzero) fzero}         {a = tt} refl br) = pE , sym (just-injective br) , tp10
phil1-step′ pO (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil1-step′ pO (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
phil1-step′ pO (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
phil1-step′ pO (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
phil1-step′ pO (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil1-step′ pE (sRet eq) = case eq of λ ()
phil1-step′ pE (sSil eq) = case eq of λ ()
phil1-step′ pE (sTau refl br) = case br of λ ()
phil1-step′ pE (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
phil1-step′ pE (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
phil1-step′ pE (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
phil1-step′ pE (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil1-step′ pE (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
phil1-step′ pE (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
phil1-step′ pE (sVis {at = _ , putsdown (fsuc fzero) fzero}         {a = tt} refl br) = pD , sym (just-injective br) , tpd0
phil1-step′ pE (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil1-step′ pD (sRet eq) = case eq of λ ()
phil1-step′ pD (sSil eq) = case eq of λ ()
phil1-step′ pD (sTau refl br) = case br of λ ()
phil1-step′ pD (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
phil1-step′ pD (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
phil1-step′ pD (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
phil1-step′ pD (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
phil1-step′ pD (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
phil1-step′ pD (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
phil1-step′ pD (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
phil1-step′ pD (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  {a = tt} refl br) = pR , sym (just-injective br) , tpd1
phil1-step′ pR (sSil refl) = pT , refl , tlp
phil1-step′ pR (sRet eq) = case eq of λ ()
phil1-step′ pR (sTau eq br) = case eq of λ ()
phil1-step′ pR (sVis eq br) = case eq of λ ()

data F0Tr : FPos → FPos → Maybe DPEvent → Set where
  tf-own : F0Tr fF fHO (evt (picks fzero fzero))
  tf-nbr : F0Tr fF fHN (evt (picks (fsuc fzero) fzero))
  tf-pdO : F0Tr fHO fR (evt (putsdown fzero fzero))
  tf-pdN : F0Tr fHN fR (evt (putsdown (fsuc fzero) fzero))
  tf-lp  : F0Tr fR fF nothing
data F1Tr : FPos → FPos → Maybe DPEvent → Set where
  tf-own : F1Tr fF fHO (evt (picks (fsuc fzero) (fsuc fzero)))
  tf-nbr : F1Tr fF fHN (evt (picks fzero (fsuc fzero)))
  tf-pdO : F1Tr fHO fR (evt (putsdown (fsuc fzero) (fsuc fzero)))
  tf-pdN : F1Tr fHN fR (evt (putsdown fzero (fsuc fzero)))
  tf-lp  : F1Tr fR fF nothing

fork0-step′ : ∀ f {l t′} → f0tree f ─[ l ]─► t′ → Σ[ f′ ∈ FPos ] (t′ ≡ f0tree f′ × F0Tr f f′ (evOf l))
fork0-step′ fF (sRet eq) = case eq of λ ()
fork0-step′ fF (sSil eq) = case eq of λ ()
fork0-step′ fF (sTau {i = i} {a = a} refl br) = case trans (sym (st-f0-free i a)) br of λ ()
fork0-step′ fF (sVis {at = _ , picks fzero fzero}                {a = tt} refl br) = fHO , sym (just-injective br) , tf-own
fork0-step′ fF (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
fork0-step′ fF (sVis {at = _ , picks (fsuc fzero) fzero}         {a = tt} refl br) = fHN , sym (just-injective br) , tf-nbr
fork0-step′ fF (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork0-step′ fF (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
fork0-step′ fF (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
fork0-step′ fF (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
fork0-step′ fF (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork0-step′ fHO (sRet eq) = case eq of λ ()
fork0-step′ fHO (sSil eq) = case eq of λ ()
fork0-step′ fHO (sTau refl br) = case br of λ ()
fork0-step′ fHO (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
fork0-step′ fHO (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
fork0-step′ fHO (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
fork0-step′ fHO (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork0-step′ fHO (sVis {at = _ , putsdown fzero fzero}                {a = tt} refl br) = fR , sym (just-injective br) , tf-pdO
fork0-step′ fHO (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
fork0-step′ fHO (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
fork0-step′ fHO (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork0-step′ fHN (sRet eq) = case eq of λ ()
fork0-step′ fHN (sSil eq) = case eq of λ ()
fork0-step′ fHN (sTau refl br) = case br of λ ()
fork0-step′ fHN (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
fork0-step′ fHN (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
fork0-step′ fHN (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
fork0-step′ fHN (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork0-step′ fHN (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
fork0-step′ fHN (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
fork0-step′ fHN (sVis {at = _ , putsdown (fsuc fzero) fzero}         {a = tt} refl br) = fR , sym (just-injective br) , tf-pdN
fork0-step′ fHN (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork0-step′ fR (sSil refl) = fF , refl , tf-lp
fork0-step′ fR (sRet eq) = case eq of λ ()
fork0-step′ fR (sTau eq br) = case eq of λ ()
fork0-step′ fR (sVis eq br) = case eq of λ ()

fork1-step′ : ∀ f {l t′} → f1tree f ─[ l ]─► t′ → Σ[ f′ ∈ FPos ] (t′ ≡ f1tree f′ × F1Tr f f′ (evOf l))
fork1-step′ fF (sRet eq) = case eq of λ ()
fork1-step′ fF (sSil eq) = case eq of λ ()
fork1-step′ fF (sTau {i = i} {a = a} refl br) = case trans (sym (st-f1-free i a)) br of λ ()
fork1-step′ fF (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
fork1-step′ fF (sVis {at = _ , picks fzero (fsuc fzero)}         {a = tt} refl br) = fHN , sym (just-injective br) , tf-nbr
fork1-step′ fF (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
fork1-step′ fF (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  {a = tt} refl br) = fHO , sym (just-injective br) , tf-own
fork1-step′ fF (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
fork1-step′ fF (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
fork1-step′ fF (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
fork1-step′ fF (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork1-step′ fHO (sRet eq) = case eq of λ ()
fork1-step′ fHO (sSil eq) = case eq of λ ()
fork1-step′ fHO (sTau refl br) = case br of λ ()
fork1-step′ fHO (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
fork1-step′ fHO (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
fork1-step′ fHO (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
fork1-step′ fHO (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork1-step′ fHO (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
fork1-step′ fHO (sVis {at = _ , putsdown fzero (fsuc fzero)}         refl br) = case br of λ ()
fork1-step′ fHO (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
fork1-step′ fHO (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  {a = tt} refl br) = fR , sym (just-injective br) , tf-pdO
fork1-step′ fHN (sRet eq) = case eq of λ ()
fork1-step′ fHN (sSil eq) = case eq of λ ()
fork1-step′ fHN (sTau refl br) = case br of λ ()
fork1-step′ fHN (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
fork1-step′ fHN (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
fork1-step′ fHN (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
fork1-step′ fHN (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork1-step′ fHN (sVis {at = _ , putsdown fzero fzero}                refl br) = case br of λ ()
fork1-step′ fHN (sVis {at = _ , putsdown fzero (fsuc fzero)}         {a = tt} refl br) = fR , sym (just-injective br) , tf-pdN
fork1-step′ fHN (sVis {at = _ , putsdown (fsuc fzero) fzero}         refl br) = case br of λ ()
fork1-step′ fHN (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
fork1-step′ fR (sSil refl) = fF , refl , tf-lp
fork1-step′ fR (sRet eq) = case eq of λ ()
fork1-step′ fR (sTau eq br) = case eq of λ ()
fork1-step′ fR (sVis eq br) = case eq of λ ()

------------------------------------------------------------------------------------
-- The system config-transition relation (label-indexed), assembled by the inversion.
data STrans : SCfg → SCfg → Maybe DPEvent → Set where
  s-pick01 : ∀ {f0 p1} → STrans (pT , f0 , p1 , fF) (pO , f0 , p1 , fHN) (evt (picks fzero (fsuc fzero)))
  s-pick11 : ∀ {p0 f0} → STrans (p0 , f0 , pT , fF) (p0 , f0 , pO , fHO) (evt (picks (fsuc fzero) (fsuc fzero)))
  s-pick00 : ∀ {p1 f1} → STrans (pO , fF , p1 , f1) (pE , fHO , p1 , f1) (evt (picks fzero fzero))
  s-pick10 : ∀ {p0 f1} → STrans (p0 , fF , pO , f1) (p0 , fHN , pE , f1) (evt (picks (fsuc fzero) fzero))
  s-pd00   : ∀ {p1 f1} → STrans (pE , fHO , p1 , f1) (pD , fR , p1 , f1) (evt (putsdown fzero fzero))
  s-pd10   : ∀ {p0 f1} → STrans (p0 , fHN , pE , f1) (p0 , fR , pD , f1) (evt (putsdown (fsuc fzero) fzero))
  s-pd01   : ∀ {f0 p1} → STrans (pD , f0 , p1 , fHN) (pR , f0 , p1 , fR) (evt (putsdown fzero (fsuc fzero)))
  s-pd11   : ∀ {p0 f0} → STrans (p0 , f0 , pD , fHO) (p0 , f0 , pR , fR) (evt (putsdown (fsuc fzero) (fsuc fzero)))
  s-τp0    : ∀ {f0 p1 f1} → STrans (pR , f0 , p1 , f1) (pT , f0 , p1 , f1) nothing
  s-τp1    : ∀ {p0 f0 f1} → STrans (p0 , f0 , pR , f1) (p0 , f0 , pT , f1) nothing
  s-τf0    : ∀ {p0 p1 f1} → STrans (p0 , fR , p1 , f1) (p0 , fF , p1 , f1) nothing
  s-τf1    : ∀ {p0 f0 p1} → STrans (p0 , f0 , p1 , fR) (p0 , f0 , p1 , fF) nothing

------------------------------------------------------------------------------------
-- Routing predicates on events: is the event in the given operand's alphabet?  The
-- solo transitions carry the αpar NON-membership witness (¬pA/¬pB from the inversion),
-- so routing-impossible inhabitants (e.g. a neighbour-pick done "solo") are refutable.
inU3 : Maybe DPEvent → Set     -- L3's right operand (fork1) alphabet
inU3 nothing   = ⊥
inU3 (just evn) = (unionα (cF1 ∷ [])) .mem (Event.A evn , Event.e evn) (Event.a evn)
inP1 : Maybe DPEvent → Set     -- L3's left operand (phil1) alphabet
inP1 nothing   = ⊥
inP1 (just evn) = (Comp.alpha cP1) .mem (Event.A evn , Event.e evn) (Event.a evn)
inU2 : Maybe DPEvent → Set     -- L2's right operand (L3 = phil1/fork1) alphabet
inU2 nothing   = ⊥
inU2 (just evn) = (unionα (cP1 ∷ cF1 ∷ [])) .mem (Event.A evn , Event.e evn) (Event.a evn)
inF0 : Maybe DPEvent → Set     -- L2's left operand (fork0) alphabet
inF0 nothing   = ⊥
inF0 (just evn) = (Comp.alpha cF0) .mem (Event.A evn , Event.e evn) (Event.a evn)

------------------------------------------------------------------------------------
-- Level 3 inversion → transition (phil1 solo / fork1 solo / sync); solo carries the
-- ¬-membership witness (τ uses λ() since inU3/inP1 nothing = ⊥).
data L3Tr : PPos → FPos → PPos → FPos → Maybe DPEvent → Set₁ where
  l3-pL : ∀ {p1 p1′ f1 e} → P1Tr p1 p1′ e → ¬ inU3 e → L3Tr p1 f1 p1′ f1 e
  l3-fR : ∀ {p1 f1 f1′ e} → F1Tr f1 f1′ e → ¬ inP1 e → L3Tr p1 f1 p1 f1′ e
  l3-sy : ∀ {p1 p1′ f1 f1′ e} → P1Tr p1 p1′ (just e) → F1Tr f1 f1′ (just e) → L3Tr p1 f1 p1′ f1′ (just e)

L3-inv : ∀ p1 f1 {l t′} → L3-tree p1 f1 ─[ l ]─► t′
       → Σ[ p1′ ∈ PPos ] Σ[ f1′ ∈ FPos ] (t′ ≡ L3-tree p1′ f1′ × L3Tr p1 f1 p1′ f1′ (evOf l))
L3-inv p1 f1 (sRet feq) with αpar-√-step-inv feq
... | v√ peq _ = ⊥-elim (p1tree-not-ret p1 peq)
L3-inv p1 f1 (sSil feq) with αpar-τ-step-inv (sSil feq)
... | inj₁ (P′ , pτ , refl) = let (p1′ , eq , tr) = phil1-step′ p1 pτ
                              in p1′ , f1 , cong (λ z → z ⟦ Comp.alpha cP1 ∥ unionα (cF1 ∷ []) ⟧ f1tree f1) eq , l3-pL tr (λ ())
... | inj₂ (Q′ , qτ , refl) = let (f1′ , eq , tr) = fork1-step′ f1 qτ
                              in p1 , f1′ , cong (λ z → p1tree p1 ⟦ Comp.alpha cP1 ∥ unionα (cF1 ∷ []) ⟧ z) eq , l3-fR tr (λ ())
L3-inv p1 f1 (sTau feq br) with αpar-τ-step-inv (sTau feq br)
... | inj₁ (P′ , pτ , refl) = let (p1′ , eq , tr) = phil1-step′ p1 pτ
                              in p1′ , f1 , cong (λ z → z ⟦ Comp.alpha cP1 ∥ unionα (cF1 ∷ []) ⟧ f1tree f1) eq , l3-pL tr (λ ())
... | inj₂ (Q′ , qτ , refl) = let (f1′ , eq , tr) = fork1-step′ f1 qτ
                              in p1 , f1′ , cong (λ z → p1tree p1 ⟦ Comp.alpha cP1 ∥ unionα (cF1 ∷ []) ⟧ z) eq , l3-fR tr (λ ())
L3-inv p1 f1 (sVis feq br) with αpar-vis-step-inv feq br
... | vSync _ _ pst qst = let (p1′ , eqp , trp) = phil1-step′ p1 pst
                              (f1′ , eqq , trq) = fork1-step′ f1 qst
                          in p1′ , f1′ , cong₂ (λ y z → y ⟦ Comp.alpha cP1 ∥ unionα (cF1 ∷ []) ⟧ z) eqp eqq , l3-sy trp trq
... | vSoloL _ ¬pB pst = let (p1′ , eq , tr) = phil1-step′ p1 pst
                         in p1′ , f1 , cong (λ z → z ⟦ Comp.alpha cP1 ∥ unionα (cF1 ∷ []) ⟧ f1tree f1) eq , l3-pL tr ¬pB
... | vSoloR ¬pA _ qst = let (f1′ , eq , tr) = fork1-step′ f1 qst
                         in p1 , f1′ , cong (λ z → p1tree p1 ⟦ Comp.alpha cP1 ∥ unionα (cF1 ∷ []) ⟧ z) eq , l3-fR tr ¬pA

------------------------------------------------------------------------------------
-- Level 2 inversion: L2 = fork0 ⟦∥⟧ L3.  (fork0 solo / L3 advances / sync fork0+L3.)
data L2Tr : FPos → PPos → FPos → FPos → PPos → FPos → Maybe DPEvent → Set₁ where
  l2-fL : ∀ {f0 f0′ p1 f1 e}        → F0Tr f0 f0′ e → ¬ inU2 e → L2Tr f0 p1 f1 f0′ p1 f1 e
  l2-L3 : ∀ {f0 p1 f1 p1′ f1′ e}    → L3Tr p1 f1 p1′ f1′ e → ¬ inF0 e → L2Tr f0 p1 f1 f0 p1′ f1′ e
  l2-sy : ∀ {f0 f0′ p1 f1 p1′ f1′ e} → F0Tr f0 f0′ (just e) → L3Tr p1 f1 p1′ f1′ (just e) → L2Tr f0 p1 f1 f0′ p1′ f1′ (just e)

L2-inv : ∀ f0 p1 f1 {l t′} → L2-tree f0 p1 f1 ─[ l ]─► t′
       → Σ[ f0′ ∈ FPos ] Σ[ p1′ ∈ PPos ] Σ[ f1′ ∈ FPos ]
           (t′ ≡ L2-tree f0′ p1′ f1′ × L2Tr f0 p1 f1 f0′ p1′ f1′ (evOf l))
L2-inv f0 p1 f1 (sRet feq) with αpar-√-step-inv feq
... | v√ peq _ = ⊥-elim (f0tree-not-ret f0 peq)
L2-inv f0 p1 f1 (sSil feq) with αpar-τ-step-inv (sSil feq)
... | inj₁ (P′ , pτ , refl) = let (f0′ , eq , tr) = fork0-step′ f0 pτ
                              in f0′ , p1 , f1 , cong (λ z → z ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧ L3-tree p1 f1) eq , l2-fL tr (λ ())
... | inj₂ (Q′ , qτ , refl) = let (p1′ , f1′ , eq , tr) = L3-inv p1 f1 qτ
                              in f0 , p1′ , f1′ , cong (λ z → f0tree f0 ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧ z) eq , l2-L3 tr (λ ())
L2-inv f0 p1 f1 (sTau feq br) with αpar-τ-step-inv (sTau feq br)
... | inj₁ (P′ , pτ , refl) = let (f0′ , eq , tr) = fork0-step′ f0 pτ
                              in f0′ , p1 , f1 , cong (λ z → z ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧ L3-tree p1 f1) eq , l2-fL tr (λ ())
... | inj₂ (Q′ , qτ , refl) = let (p1′ , f1′ , eq , tr) = L3-inv p1 f1 qτ
                              in f0 , p1′ , f1′ , cong (λ z → f0tree f0 ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧ z) eq , l2-L3 tr (λ ())
L2-inv f0 p1 f1 (sVis feq br) with αpar-vis-step-inv feq br
... | vSync _ _ pst qst = let (f0′ , eqp , trp) = fork0-step′ f0 pst
                              (p1′ , f1′ , eqq , trq) = L3-inv p1 f1 qst
                          in f0′ , p1′ , f1′ , cong₂ (λ y z → y ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧ z) eqp eqq , l2-sy trp trq
... | vSoloL _ ¬pB pst = let (f0′ , eq , tr) = fork0-step′ f0 pst
                         in f0′ , p1 , f1 , cong (λ z → z ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧ L3-tree p1 f1) eq , l2-fL tr ¬pB
... | vSoloR ¬pA _ qst = let (p1′ , f1′ , eq , tr) = L3-inv p1 f1 qst
                         in f0 , p1′ , f1′ , cong (λ z → f0tree f0 ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧ z) eq , l2-L3 tr ¬pA

------------------------------------------------------------------------------------
-- Level 1 (whole system): sysState = phil0 ⟦∥⟧ L2.  Invert one step → STrans, the
-- synced operands correlated by the shared event (a vSync fixes the event for both).
private
  topα : PTree DP (ExtI DP) ⊥ → PTree DP (ExtI DP) (RetOf⁺ cF0 (cP1 ∷ cF1 ∷ []))
       → PTree DP (ExtI DP) (RetOf⁺ cP0 (cF0 ∷ cP1 ∷ cF1 ∷ []))
  topα x y = x ⟦ Comp.alpha cP0 ∥ unionα (cF0 ∷ cP1 ∷ cF1 ∷ []) ⟧ y

sys-inv : ∀ cfg {l t′} → sysState cfg ─[ l ]─► t′
        → Σ[ cfg′ ∈ SCfg ] (t′ ≡ sysState cfg′ × STrans cfg cfg′ (evOf l))
sys-inv (p0 , f0 , p1 , f1) (sRet feq) with αpar-√-step-inv feq
... | v√ peq _ = ⊥-elim (p0tree-not-ret p0 peq)
-- τ: phil0 reloop, or a τ inside L2.
sys-inv (p0 , f0 , p1 , f1) (sSil feq) with αpar-τ-step-inv (sSil feq)
... | inj₁ (P′ , pτ , refl) with phil0-step′ p0 pτ
...   | (_ , eqp , tlp) = (pT , f0 , p1 , f1) , cong (λ z → topα z (L2-tree f0 p1 f1)) eqp , s-τp0
sys-inv (p0 , f0 , p1 , f1) (sSil feq) | inj₂ (Q′ , qτ , refl) with L2-inv f0 p1 f1 qτ
...   | (_ , _ , _ , eqq , l2-fL tf-lp _)            = (p0 , fF , p1 , f1) , cong (λ z → topα (p0tree p0) z) eqq , s-τf0
...   | (_ , _ , _ , eqq , l2-L3 (l3-pL tlp _) _)    = (p0 , f0 , pT , f1) , cong (λ z → topα (p0tree p0) z) eqq , s-τp1
...   | (_ , _ , _ , eqq , l2-L3 (l3-fR tf-lp _) _)  = (p0 , f0 , p1 , fF) , cong (λ z → topα (p0tree p0) z) eqq , s-τf1
sys-inv (p0 , f0 , p1 , f1) (sTau feq br) with αpar-τ-step-inv (sTau feq br)
... | inj₁ (P′ , pτ , refl) with phil0-step′ p0 pτ
...   | (_ , eqp , tlp) = (pT , f0 , p1 , f1) , cong (λ z → topα z (L2-tree f0 p1 f1)) eqp , s-τp0
sys-inv (p0 , f0 , p1 , f1) (sTau feq br) | inj₂ (Q′ , qτ , refl) with L2-inv f0 p1 f1 qτ
...   | (_ , _ , _ , eqq , l2-fL tf-lp _)            = (p0 , fF , p1 , f1) , cong (λ z → topα (p0tree p0) z) eqq , s-τf0
...   | (_ , _ , _ , eqq , l2-L3 (l3-pL tlp _) _)    = (p0 , f0 , pT , f1) , cong (λ z → topα (p0tree p0) z) eqq , s-τp1
...   | (_ , _ , _ , eqq , l2-L3 (l3-fR tf-lp _) _)  = (p0 , f0 , p1 , fF) , cong (λ z → topα (p0tree p0) z) eqq , s-τf1
-- visible: phil0 syncs with L2 (vSync), or L2 advances solo (vSoloR); vSoloL impossible.
sys-inv (p0 , f0 , p1 , f1) (sVis feq br) with αpar-vis-step-inv feq br
... | vSync _ _ pst qst with phil0-step′ p0 pst
...   | (_ , eqp , tp01) with L2-inv f0 p1 f1 qst
...     | (_ , _ , _ , eqq , l2-L3 (l3-fR tf-nbr _) _) = (pO , f0 , p1 , fHN) , cong₂ topα eqp eqq , s-pick01
sys-inv (p0 , f0 , p1 , f1) (sVis feq br) | vSync _ _ pst qst | (_ , eqp , tp00) with L2-inv f0 p1 f1 qst
...     | (_ , _ , _ , eqq , l2-fL tf-own _) = (pE , fHO , p1 , f1) , cong₂ topα eqp eqq , s-pick00
...     | (_ , _ , _ , _ , l2-L3 _ w)  = ⊥-elim (w (refl , inj₁ refl))
...     | (_ , _ , _ , _ , l2-sy _ (l3-pL () _))
...     | (_ , _ , _ , _ , l2-sy _ (l3-fR () _))
...     | (_ , _ , _ , _ , l2-sy _ (l3-sy () _))
sys-inv (p0 , f0 , p1 , f1) (sVis feq br) | vSync _ _ pst qst | (_ , eqp , tpd0) with L2-inv f0 p1 f1 qst
...     | (_ , _ , _ , eqq , l2-fL tf-pdO _) = (pD , fR , p1 , f1) , cong₂ topα eqp eqq , s-pd00
...     | (_ , _ , _ , _ , l2-L3 _ w)  = ⊥-elim (w (refl , inj₁ refl))
...     | (_ , _ , _ , _ , l2-sy _ (l3-pL () _))
...     | (_ , _ , _ , _ , l2-sy _ (l3-fR () _))
...     | (_ , _ , _ , _ , l2-sy _ (l3-sy () _))
sys-inv (p0 , f0 , p1 , f1) (sVis feq br) | vSync _ _ pst qst | (_ , eqp , tpd1) with L2-inv f0 p1 f1 qst
...     | (_ , _ , _ , eqq , l2-L3 (l3-fR tf-pdN _) _) = (pR , f0 , p1 , fR) , cong₂ topα eqp eqq , s-pd01
sys-inv (p0 , f0 , p1 , f1) (sVis feq br) | vSoloR ¬pA _ qst with L2-inv f0 p1 f1 qst
...   | (_ , _ , _ , eqq , l2-L3 (l3-sy tp11 tf-own) _) = (p0 , f0 , pO , fHO) , cong (λ z → topα (p0tree p0) z) eqq , s-pick11
...   | (_ , _ , _ , eqq , l2-sy tf-nbr (l3-pL tp10 _)) = (p0 , fHN , pE , f1) , cong (λ z → topα (p0tree p0) z) eqq , s-pick10
...   | (_ , _ , _ , eqq , l2-sy tf-pdN (l3-pL tpd0 _)) = (p0 , fR , pD , f1) , cong (λ z → topα (p0tree p0) z) eqq , s-pd10
...   | (_ , _ , _ , eqq , l2-L3 (l3-sy tpd1 tf-pdO) _) = (p0 , f0 , pR , fR) , cong (λ z → topα (p0tree p0) z) eqq , s-pd11
-- spurious vSoloR cases (refuted by ¬pA = event ∉ phil0's alphabet, or by the routing witness)
...   | (_ , _ , _ , _ , l2-fL tf-own _)  = ⊥-elim (¬pA (refl , inj₁ refl))
...   | (_ , _ , _ , _ , l2-fL tf-nbr w)  = ⊥-elim (w (inj₁ (refl , inj₂ refl)))
...   | (_ , _ , _ , _ , l2-fL tf-pdO _)  = ⊥-elim (¬pA (refl , inj₁ refl))
...   | (_ , _ , _ , _ , l2-fL tf-pdN w)  = ⊥-elim (w (inj₁ (refl , inj₂ refl)))
...   | (_ , _ , _ , _ , l2-L3 (l3-pL tp11 w′) _) = ⊥-elim (w′ (inj₁ (refl , inj₁ refl)))
...   | (_ , _ , _ , _ , l2-L3 (l3-pL tp10 _) w)  = ⊥-elim (w (refl , inj₂ refl))
...   | (_ , _ , _ , _ , l2-L3 (l3-pL tpd0 _) w)  = ⊥-elim (w (refl , inj₂ refl))
...   | (_ , _ , _ , _ , l2-L3 (l3-pL tpd1 w′) _) = ⊥-elim (w′ (inj₁ (refl , inj₁ refl)))
...   | (_ , _ , _ , _ , l2-L3 (l3-fR tf-own w′) _) = ⊥-elim (w′ (refl , inj₁ refl))
...   | (_ , _ , _ , _ , l2-L3 (l3-fR tf-nbr _) _)  = ⊥-elim (¬pA (refl , inj₂ refl))
...   | (_ , _ , _ , _ , l2-L3 (l3-fR tf-pdO w′) _) = ⊥-elim (w′ (refl , inj₁ refl))
...   | (_ , _ , _ , _ , l2-L3 (l3-fR tf-pdN _) _)  = ⊥-elim (¬pA (refl , inj₂ refl))
...   | (_ , _ , _ , _ , l2-sy tf-own _) = ⊥-elim (¬pA (refl , inj₁ refl))
...   | (_ , _ , _ , _ , l2-sy tf-pdO _) = ⊥-elim (¬pA (refl , inj₁ refl))
sys-inv (p0 , f0 , p1 , f1) (sVis feq br) | vSoloL _ ¬pB pst with phil0-step′ p0 pst
...   | (_ , _ , tp01) = ⊥-elim (¬pB (inj₂ (inj₂ (inj₁ (refl , inj₂ refl)))))
...   | (_ , _ , tp00) = ⊥-elim (¬pB (inj₁ (refl , inj₁ refl)))
...   | (_ , _ , tpd0) = ⊥-elim (¬pB (inj₁ (refl , inj₁ refl)))
...   | (_ , _ , tpd1) = ⊥-elim (¬pB (inj₂ (inj₂ (inj₁ (refl , inj₂ refl)))))

------------------------------------------------------------------------------------
-- Consistency is preserved by every system transition (each reduces by refl: the
-- changed fork/phil recomputes, the unchanged Cons components are reused).
cons-pres : ∀ {cfg cfg′ e} → Cons cfg → STrans cfg cfg′ e → Cons cfg′
cons-pres (e1 , e2 , e3 , e4) s-pick01 = refl , e2 , e3 , e4
cons-pres (e1 , e2 , e3 , e4) s-pick11 = e1 , refl , e3 , e4
cons-pres (e1 , e2 , e3 , e4) s-pick00 = e1 , e2 , refl , e4
cons-pres (e1 , e2 , e3 , e4) s-pick10 = e1 , e2 , e3 , refl
cons-pres (e1 , e2 , e3 , e4) s-pd00   = e1 , e2 , refl , e4
cons-pres (e1 , e2 , e3 , e4) s-pd10   = e1 , e2 , e3 , refl
cons-pres (e1 , e2 , e3 , e4) s-pd01   = refl , e2 , e3 , e4
cons-pres (e1 , e2 , e3 , e4) s-pd11   = e1 , refl , e3 , e4
cons-pres c s-τp0 = c
cons-pres c s-τp1 = c
cons-pres c s-τf0 = c
cons-pres c s-τf1 = c

------------------------------------------------------------------------------------
-- progress (the deadlock-free essence): every consistent state can move.  Reloop ⇒ a
-- τ (sSil); the 7 consistent all-vis configs fire a sync (sVis); Cons rules out the
-- rest.  Enumerated over the finite (5×4×5×4) position space.
progress : (cfg : SCfg) → Cons cfg → ¬ IsStuck (sysState cfg)
progress (pT , fF , pT , fF) _ stuck = stuck (sVis {at = _ , picks fzero (fsuc fzero)} {a = tt} refl refl)
progress (pT , fF , pT , fHO) (_ , () , _ , _)
progress (pT , fF , pT , fHN) (() , _ , _ , _)
progress (pT , fF , pT , fR) _ stuck = stuck (sSil refl)
progress (pT , fF , pO , fF) (_ , () , _ , _)
progress (pT , fF , pO , fHO) _ stuck = stuck (sVis {at = _ , picks (fsuc fzero) fzero} {a = tt} refl refl)
progress (pT , fF , pO , fHN) (() , _ , _ , _)
progress (pT , fF , pO , fR) _ stuck = stuck (sSil refl)
progress (pT , fF , pE , fF) (_ , () , _ , _)
progress (pT , fF , pE , fHO) (_ , _ , _ , ())
progress (pT , fF , pE , fHN) (() , _ , _ , _)
progress (pT , fF , pE , fR) _ stuck = stuck (sSil refl)
progress (pT , fF , pD , fF) (_ , () , _ , _)
progress (pT , fF , pD , fHO) _ stuck = stuck (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)} {a = tt} refl refl)
progress (pT , fF , pD , fHN) (() , _ , _ , _)
progress (pT , fF , pD , fR) _ stuck = stuck (sSil refl)
progress (pT , fF , pR , fF) _ stuck = stuck (sSil refl)
progress (pT , fF , pR , fHO) _ stuck = stuck (sSil refl)
progress (pT , fF , pR , fHN) _ stuck = stuck (sSil refl)
progress (pT , fF , pR , fR) _ stuck = stuck (sSil refl)
progress (pT , fHO , pT , fF) (_ , _ , () , _)
progress (pT , fHO , pT , fHO) (_ , () , _ , _)
progress (pT , fHO , pT , fHN) (() , _ , _ , _)
progress (pT , fHO , pT , fR) _ stuck = stuck (sSil refl)
progress (pT , fHO , pO , fF) (_ , () , _ , _)
progress (pT , fHO , pO , fHO) (_ , _ , () , _)
progress (pT , fHO , pO , fHN) (() , _ , _ , _)
progress (pT , fHO , pO , fR) _ stuck = stuck (sSil refl)
progress (pT , fHO , pE , fF) (_ , () , _ , _)
progress (pT , fHO , pE , fHO) (_ , _ , () , _)
progress (pT , fHO , pE , fHN) (() , _ , _ , _)
progress (pT , fHO , pE , fR) _ stuck = stuck (sSil refl)
progress (pT , fHO , pD , fF) (_ , () , _ , _)
progress (pT , fHO , pD , fHO) (_ , _ , () , _)
progress (pT , fHO , pD , fHN) (() , _ , _ , _)
progress (pT , fHO , pD , fR) _ stuck = stuck (sSil refl)
progress (pT , fHO , pR , fF) _ stuck = stuck (sSil refl)
progress (pT , fHO , pR , fHO) _ stuck = stuck (sSil refl)
progress (pT , fHO , pR , fHN) _ stuck = stuck (sSil refl)
progress (pT , fHO , pR , fR) _ stuck = stuck (sSil refl)
progress (pT , fHN , pT , fF) (_ , _ , _ , ())
progress (pT , fHN , pT , fHO) (_ , () , _ , _)
progress (pT , fHN , pT , fHN) (() , _ , _ , _)
progress (pT , fHN , pT , fR) _ stuck = stuck (sSil refl)
progress (pT , fHN , pO , fF) (_ , () , _ , _)
progress (pT , fHN , pO , fHO) (_ , _ , _ , ())
progress (pT , fHN , pO , fHN) (() , _ , _ , _)
progress (pT , fHN , pO , fR) _ stuck = stuck (sSil refl)
progress (pT , fHN , pE , fF) (_ , () , _ , _)
progress (pT , fHN , pE , fHO) _ stuck = stuck (sVis {at = _ , putsdown (fsuc fzero) fzero} {a = tt} refl refl)
progress (pT , fHN , pE , fHN) (() , _ , _ , _)
progress (pT , fHN , pE , fR) _ stuck = stuck (sSil refl)
progress (pT , fHN , pD , fF) (_ , () , _ , _)
progress (pT , fHN , pD , fHO) (_ , _ , _ , ())
progress (pT , fHN , pD , fHN) (() , _ , _ , _)
progress (pT , fHN , pD , fR) _ stuck = stuck (sSil refl)
progress (pT , fHN , pR , fF) _ stuck = stuck (sSil refl)
progress (pT , fHN , pR , fHO) _ stuck = stuck (sSil refl)
progress (pT , fHN , pR , fHN) _ stuck = stuck (sSil refl)
progress (pT , fHN , pR , fR) _ stuck = stuck (sSil refl)
progress (pT , fR , pT , fF) _ stuck = stuck (sSil refl)
progress (pT , fR , pT , fHO) _ stuck = stuck (sSil refl)
progress (pT , fR , pT , fHN) _ stuck = stuck (sSil refl)
progress (pT , fR , pT , fR) _ stuck = stuck (sSil refl)
progress (pT , fR , pO , fF) _ stuck = stuck (sSil refl)
progress (pT , fR , pO , fHO) _ stuck = stuck (sSil refl)
progress (pT , fR , pO , fHN) _ stuck = stuck (sSil refl)
progress (pT , fR , pO , fR) _ stuck = stuck (sSil refl)
progress (pT , fR , pE , fF) _ stuck = stuck (sSil refl)
progress (pT , fR , pE , fHO) _ stuck = stuck (sSil refl)
progress (pT , fR , pE , fHN) _ stuck = stuck (sSil refl)
progress (pT , fR , pE , fR) _ stuck = stuck (sSil refl)
progress (pT , fR , pD , fF) _ stuck = stuck (sSil refl)
progress (pT , fR , pD , fHO) _ stuck = stuck (sSil refl)
progress (pT , fR , pD , fHN) _ stuck = stuck (sSil refl)
progress (pT , fR , pD , fR) _ stuck = stuck (sSil refl)
progress (pT , fR , pR , fF) _ stuck = stuck (sSil refl)
progress (pT , fR , pR , fHO) _ stuck = stuck (sSil refl)
progress (pT , fR , pR , fHN) _ stuck = stuck (sSil refl)
progress (pT , fR , pR , fR) _ stuck = stuck (sSil refl)
progress (pO , fF , pT , fF) (() , _ , _ , _)
progress (pO , fF , pT , fHO) (() , _ , _ , _)
progress (pO , fF , pT , fHN) _ stuck = stuck (sVis {at = _ , picks fzero fzero} {a = tt} refl refl)
progress (pO , fF , pT , fR) _ stuck = stuck (sSil refl)
progress (pO , fF , pO , fF) (() , _ , _ , _)
progress (pO , fF , pO , fHO) (() , _ , _ , _)
progress (pO , fF , pO , fHN) (_ , () , _ , _)
progress (pO , fF , pO , fR) _ stuck = stuck (sSil refl)
progress (pO , fF , pE , fF) (() , _ , _ , _)
progress (pO , fF , pE , fHO) (() , _ , _ , _)
progress (pO , fF , pE , fHN) (_ , () , _ , _)
progress (pO , fF , pE , fR) _ stuck = stuck (sSil refl)
progress (pO , fF , pD , fF) (() , _ , _ , _)
progress (pO , fF , pD , fHO) (() , _ , _ , _)
progress (pO , fF , pD , fHN) (_ , () , _ , _)
progress (pO , fF , pD , fR) _ stuck = stuck (sSil refl)
progress (pO , fF , pR , fF) _ stuck = stuck (sSil refl)
progress (pO , fF , pR , fHO) _ stuck = stuck (sSil refl)
progress (pO , fF , pR , fHN) _ stuck = stuck (sSil refl)
progress (pO , fF , pR , fR) _ stuck = stuck (sSil refl)
progress (pO , fHO , pT , fF) (() , _ , _ , _)
progress (pO , fHO , pT , fHO) (() , _ , _ , _)
progress (pO , fHO , pT , fHN) (_ , _ , () , _)
progress (pO , fHO , pT , fR) _ stuck = stuck (sSil refl)
progress (pO , fHO , pO , fF) (() , _ , _ , _)
progress (pO , fHO , pO , fHO) (() , _ , _ , _)
progress (pO , fHO , pO , fHN) (_ , () , _ , _)
progress (pO , fHO , pO , fR) _ stuck = stuck (sSil refl)
progress (pO , fHO , pE , fF) (() , _ , _ , _)
progress (pO , fHO , pE , fHO) (() , _ , _ , _)
progress (pO , fHO , pE , fHN) (_ , () , _ , _)
progress (pO , fHO , pE , fR) _ stuck = stuck (sSil refl)
progress (pO , fHO , pD , fF) (() , _ , _ , _)
progress (pO , fHO , pD , fHO) (() , _ , _ , _)
progress (pO , fHO , pD , fHN) (_ , () , _ , _)
progress (pO , fHO , pD , fR) _ stuck = stuck (sSil refl)
progress (pO , fHO , pR , fF) _ stuck = stuck (sSil refl)
progress (pO , fHO , pR , fHO) _ stuck = stuck (sSil refl)
progress (pO , fHO , pR , fHN) _ stuck = stuck (sSil refl)
progress (pO , fHO , pR , fR) _ stuck = stuck (sSil refl)
progress (pO , fHN , pT , fF) (() , _ , _ , _)
progress (pO , fHN , pT , fHO) (() , _ , _ , _)
progress (pO , fHN , pT , fHN) (_ , _ , _ , ())
progress (pO , fHN , pT , fR) _ stuck = stuck (sSil refl)
progress (pO , fHN , pO , fF) (() , _ , _ , _)
progress (pO , fHN , pO , fHO) (() , _ , _ , _)
progress (pO , fHN , pO , fHN) (_ , () , _ , _)
progress (pO , fHN , pO , fR) _ stuck = stuck (sSil refl)
progress (pO , fHN , pE , fF) (() , _ , _ , _)
progress (pO , fHN , pE , fHO) (() , _ , _ , _)
progress (pO , fHN , pE , fHN) (_ , () , _ , _)
progress (pO , fHN , pE , fR) _ stuck = stuck (sSil refl)
progress (pO , fHN , pD , fF) (() , _ , _ , _)
progress (pO , fHN , pD , fHO) (() , _ , _ , _)
progress (pO , fHN , pD , fHN) (_ , () , _ , _)
progress (pO , fHN , pD , fR) _ stuck = stuck (sSil refl)
progress (pO , fHN , pR , fF) _ stuck = stuck (sSil refl)
progress (pO , fHN , pR , fHO) _ stuck = stuck (sSil refl)
progress (pO , fHN , pR , fHN) _ stuck = stuck (sSil refl)
progress (pO , fHN , pR , fR) _ stuck = stuck (sSil refl)
progress (pO , fR , pT , fF) _ stuck = stuck (sSil refl)
progress (pO , fR , pT , fHO) _ stuck = stuck (sSil refl)
progress (pO , fR , pT , fHN) _ stuck = stuck (sSil refl)
progress (pO , fR , pT , fR) _ stuck = stuck (sSil refl)
progress (pO , fR , pO , fF) _ stuck = stuck (sSil refl)
progress (pO , fR , pO , fHO) _ stuck = stuck (sSil refl)
progress (pO , fR , pO , fHN) _ stuck = stuck (sSil refl)
progress (pO , fR , pO , fR) _ stuck = stuck (sSil refl)
progress (pO , fR , pE , fF) _ stuck = stuck (sSil refl)
progress (pO , fR , pE , fHO) _ stuck = stuck (sSil refl)
progress (pO , fR , pE , fHN) _ stuck = stuck (sSil refl)
progress (pO , fR , pE , fR) _ stuck = stuck (sSil refl)
progress (pO , fR , pD , fF) _ stuck = stuck (sSil refl)
progress (pO , fR , pD , fHO) _ stuck = stuck (sSil refl)
progress (pO , fR , pD , fHN) _ stuck = stuck (sSil refl)
progress (pO , fR , pD , fR) _ stuck = stuck (sSil refl)
progress (pO , fR , pR , fF) _ stuck = stuck (sSil refl)
progress (pO , fR , pR , fHO) _ stuck = stuck (sSil refl)
progress (pO , fR , pR , fHN) _ stuck = stuck (sSil refl)
progress (pO , fR , pR , fR) _ stuck = stuck (sSil refl)
progress (pE , fF , pT , fF) (() , _ , _ , _)
progress (pE , fF , pT , fHO) (() , _ , _ , _)
progress (pE , fF , pT , fHN) (_ , _ , () , _)
progress (pE , fF , pT , fR) _ stuck = stuck (sSil refl)
progress (pE , fF , pO , fF) (() , _ , _ , _)
progress (pE , fF , pO , fHO) (() , _ , _ , _)
progress (pE , fF , pO , fHN) (_ , () , _ , _)
progress (pE , fF , pO , fR) _ stuck = stuck (sSil refl)
progress (pE , fF , pE , fF) (() , _ , _ , _)
progress (pE , fF , pE , fHO) (() , _ , _ , _)
progress (pE , fF , pE , fHN) (_ , () , _ , _)
progress (pE , fF , pE , fR) _ stuck = stuck (sSil refl)
progress (pE , fF , pD , fF) (() , _ , _ , _)
progress (pE , fF , pD , fHO) (() , _ , _ , _)
progress (pE , fF , pD , fHN) (_ , () , _ , _)
progress (pE , fF , pD , fR) _ stuck = stuck (sSil refl)
progress (pE , fF , pR , fF) _ stuck = stuck (sSil refl)
progress (pE , fF , pR , fHO) _ stuck = stuck (sSil refl)
progress (pE , fF , pR , fHN) _ stuck = stuck (sSil refl)
progress (pE , fF , pR , fR) _ stuck = stuck (sSil refl)
progress (pE , fHO , pT , fF) (() , _ , _ , _)
progress (pE , fHO , pT , fHO) (() , _ , _ , _)
progress (pE , fHO , pT , fHN) _ stuck = stuck (sVis {at = _ , putsdown fzero fzero} {a = tt} refl refl)
progress (pE , fHO , pT , fR) _ stuck = stuck (sSil refl)
progress (pE , fHO , pO , fF) (() , _ , _ , _)
progress (pE , fHO , pO , fHO) (() , _ , _ , _)
progress (pE , fHO , pO , fHN) (_ , () , _ , _)
progress (pE , fHO , pO , fR) _ stuck = stuck (sSil refl)
progress (pE , fHO , pE , fF) (() , _ , _ , _)
progress (pE , fHO , pE , fHO) (() , _ , _ , _)
progress (pE , fHO , pE , fHN) (_ , () , _ , _)
progress (pE , fHO , pE , fR) _ stuck = stuck (sSil refl)
progress (pE , fHO , pD , fF) (() , _ , _ , _)
progress (pE , fHO , pD , fHO) (() , _ , _ , _)
progress (pE , fHO , pD , fHN) (_ , () , _ , _)
progress (pE , fHO , pD , fR) _ stuck = stuck (sSil refl)
progress (pE , fHO , pR , fF) _ stuck = stuck (sSil refl)
progress (pE , fHO , pR , fHO) _ stuck = stuck (sSil refl)
progress (pE , fHO , pR , fHN) _ stuck = stuck (sSil refl)
progress (pE , fHO , pR , fR) _ stuck = stuck (sSil refl)
progress (pE , fHN , pT , fF) (() , _ , _ , _)
progress (pE , fHN , pT , fHO) (() , _ , _ , _)
progress (pE , fHN , pT , fHN) (_ , _ , () , _)
progress (pE , fHN , pT , fR) _ stuck = stuck (sSil refl)
progress (pE , fHN , pO , fF) (() , _ , _ , _)
progress (pE , fHN , pO , fHO) (() , _ , _ , _)
progress (pE , fHN , pO , fHN) (_ , () , _ , _)
progress (pE , fHN , pO , fR) _ stuck = stuck (sSil refl)
progress (pE , fHN , pE , fF) (() , _ , _ , _)
progress (pE , fHN , pE , fHO) (() , _ , _ , _)
progress (pE , fHN , pE , fHN) (_ , () , _ , _)
progress (pE , fHN , pE , fR) _ stuck = stuck (sSil refl)
progress (pE , fHN , pD , fF) (() , _ , _ , _)
progress (pE , fHN , pD , fHO) (() , _ , _ , _)
progress (pE , fHN , pD , fHN) (_ , () , _ , _)
progress (pE , fHN , pD , fR) _ stuck = stuck (sSil refl)
progress (pE , fHN , pR , fF) _ stuck = stuck (sSil refl)
progress (pE , fHN , pR , fHO) _ stuck = stuck (sSil refl)
progress (pE , fHN , pR , fHN) _ stuck = stuck (sSil refl)
progress (pE , fHN , pR , fR) _ stuck = stuck (sSil refl)
progress (pE , fR , pT , fF) _ stuck = stuck (sSil refl)
progress (pE , fR , pT , fHO) _ stuck = stuck (sSil refl)
progress (pE , fR , pT , fHN) _ stuck = stuck (sSil refl)
progress (pE , fR , pT , fR) _ stuck = stuck (sSil refl)
progress (pE , fR , pO , fF) _ stuck = stuck (sSil refl)
progress (pE , fR , pO , fHO) _ stuck = stuck (sSil refl)
progress (pE , fR , pO , fHN) _ stuck = stuck (sSil refl)
progress (pE , fR , pO , fR) _ stuck = stuck (sSil refl)
progress (pE , fR , pE , fF) _ stuck = stuck (sSil refl)
progress (pE , fR , pE , fHO) _ stuck = stuck (sSil refl)
progress (pE , fR , pE , fHN) _ stuck = stuck (sSil refl)
progress (pE , fR , pE , fR) _ stuck = stuck (sSil refl)
progress (pE , fR , pD , fF) _ stuck = stuck (sSil refl)
progress (pE , fR , pD , fHO) _ stuck = stuck (sSil refl)
progress (pE , fR , pD , fHN) _ stuck = stuck (sSil refl)
progress (pE , fR , pD , fR) _ stuck = stuck (sSil refl)
progress (pE , fR , pR , fF) _ stuck = stuck (sSil refl)
progress (pE , fR , pR , fHO) _ stuck = stuck (sSil refl)
progress (pE , fR , pR , fHN) _ stuck = stuck (sSil refl)
progress (pE , fR , pR , fR) _ stuck = stuck (sSil refl)
progress (pD , fF , pT , fF) (() , _ , _ , _)
progress (pD , fF , pT , fHO) (() , _ , _ , _)
progress (pD , fF , pT , fHN) _ stuck = stuck (sVis {at = _ , putsdown fzero (fsuc fzero)} {a = tt} refl refl)
progress (pD , fF , pT , fR) _ stuck = stuck (sSil refl)
progress (pD , fF , pO , fF) (() , _ , _ , _)
progress (pD , fF , pO , fHO) (() , _ , _ , _)
progress (pD , fF , pO , fHN) (_ , () , _ , _)
progress (pD , fF , pO , fR) _ stuck = stuck (sSil refl)
progress (pD , fF , pE , fF) (() , _ , _ , _)
progress (pD , fF , pE , fHO) (() , _ , _ , _)
progress (pD , fF , pE , fHN) (_ , () , _ , _)
progress (pD , fF , pE , fR) _ stuck = stuck (sSil refl)
progress (pD , fF , pD , fF) (() , _ , _ , _)
progress (pD , fF , pD , fHO) (() , _ , _ , _)
progress (pD , fF , pD , fHN) (_ , () , _ , _)
progress (pD , fF , pD , fR) _ stuck = stuck (sSil refl)
progress (pD , fF , pR , fF) _ stuck = stuck (sSil refl)
progress (pD , fF , pR , fHO) _ stuck = stuck (sSil refl)
progress (pD , fF , pR , fHN) _ stuck = stuck (sSil refl)
progress (pD , fF , pR , fR) _ stuck = stuck (sSil refl)
progress (pD , fHO , pT , fF) (() , _ , _ , _)
progress (pD , fHO , pT , fHO) (() , _ , _ , _)
progress (pD , fHO , pT , fHN) (_ , _ , () , _)
progress (pD , fHO , pT , fR) _ stuck = stuck (sSil refl)
progress (pD , fHO , pO , fF) (() , _ , _ , _)
progress (pD , fHO , pO , fHO) (() , _ , _ , _)
progress (pD , fHO , pO , fHN) (_ , () , _ , _)
progress (pD , fHO , pO , fR) _ stuck = stuck (sSil refl)
progress (pD , fHO , pE , fF) (() , _ , _ , _)
progress (pD , fHO , pE , fHO) (() , _ , _ , _)
progress (pD , fHO , pE , fHN) (_ , () , _ , _)
progress (pD , fHO , pE , fR) _ stuck = stuck (sSil refl)
progress (pD , fHO , pD , fF) (() , _ , _ , _)
progress (pD , fHO , pD , fHO) (() , _ , _ , _)
progress (pD , fHO , pD , fHN) (_ , () , _ , _)
progress (pD , fHO , pD , fR) _ stuck = stuck (sSil refl)
progress (pD , fHO , pR , fF) _ stuck = stuck (sSil refl)
progress (pD , fHO , pR , fHO) _ stuck = stuck (sSil refl)
progress (pD , fHO , pR , fHN) _ stuck = stuck (sSil refl)
progress (pD , fHO , pR , fR) _ stuck = stuck (sSil refl)
progress (pD , fHN , pT , fF) (() , _ , _ , _)
progress (pD , fHN , pT , fHO) (() , _ , _ , _)
progress (pD , fHN , pT , fHN) (_ , _ , _ , ())
progress (pD , fHN , pT , fR) _ stuck = stuck (sSil refl)
progress (pD , fHN , pO , fF) (() , _ , _ , _)
progress (pD , fHN , pO , fHO) (() , _ , _ , _)
progress (pD , fHN , pO , fHN) (_ , () , _ , _)
progress (pD , fHN , pO , fR) _ stuck = stuck (sSil refl)
progress (pD , fHN , pE , fF) (() , _ , _ , _)
progress (pD , fHN , pE , fHO) (() , _ , _ , _)
progress (pD , fHN , pE , fHN) (_ , () , _ , _)
progress (pD , fHN , pE , fR) _ stuck = stuck (sSil refl)
progress (pD , fHN , pD , fF) (() , _ , _ , _)
progress (pD , fHN , pD , fHO) (() , _ , _ , _)
progress (pD , fHN , pD , fHN) (_ , () , _ , _)
progress (pD , fHN , pD , fR) _ stuck = stuck (sSil refl)
progress (pD , fHN , pR , fF) _ stuck = stuck (sSil refl)
progress (pD , fHN , pR , fHO) _ stuck = stuck (sSil refl)
progress (pD , fHN , pR , fHN) _ stuck = stuck (sSil refl)
progress (pD , fHN , pR , fR) _ stuck = stuck (sSil refl)
progress (pD , fR , pT , fF) _ stuck = stuck (sSil refl)
progress (pD , fR , pT , fHO) _ stuck = stuck (sSil refl)
progress (pD , fR , pT , fHN) _ stuck = stuck (sSil refl)
progress (pD , fR , pT , fR) _ stuck = stuck (sSil refl)
progress (pD , fR , pO , fF) _ stuck = stuck (sSil refl)
progress (pD , fR , pO , fHO) _ stuck = stuck (sSil refl)
progress (pD , fR , pO , fHN) _ stuck = stuck (sSil refl)
progress (pD , fR , pO , fR) _ stuck = stuck (sSil refl)
progress (pD , fR , pE , fF) _ stuck = stuck (sSil refl)
progress (pD , fR , pE , fHO) _ stuck = stuck (sSil refl)
progress (pD , fR , pE , fHN) _ stuck = stuck (sSil refl)
progress (pD , fR , pE , fR) _ stuck = stuck (sSil refl)
progress (pD , fR , pD , fF) _ stuck = stuck (sSil refl)
progress (pD , fR , pD , fHO) _ stuck = stuck (sSil refl)
progress (pD , fR , pD , fHN) _ stuck = stuck (sSil refl)
progress (pD , fR , pD , fR) _ stuck = stuck (sSil refl)
progress (pD , fR , pR , fF) _ stuck = stuck (sSil refl)
progress (pD , fR , pR , fHO) _ stuck = stuck (sSil refl)
progress (pD , fR , pR , fHN) _ stuck = stuck (sSil refl)
progress (pD , fR , pR , fR) _ stuck = stuck (sSil refl)
progress (pR , fF , pT , fF) _ stuck = stuck (sSil refl)
progress (pR , fF , pT , fHO) _ stuck = stuck (sSil refl)
progress (pR , fF , pT , fHN) _ stuck = stuck (sSil refl)
progress (pR , fF , pT , fR) _ stuck = stuck (sSil refl)
progress (pR , fF , pO , fF) _ stuck = stuck (sSil refl)
progress (pR , fF , pO , fHO) _ stuck = stuck (sSil refl)
progress (pR , fF , pO , fHN) _ stuck = stuck (sSil refl)
progress (pR , fF , pO , fR) _ stuck = stuck (sSil refl)
progress (pR , fF , pE , fF) _ stuck = stuck (sSil refl)
progress (pR , fF , pE , fHO) _ stuck = stuck (sSil refl)
progress (pR , fF , pE , fHN) _ stuck = stuck (sSil refl)
progress (pR , fF , pE , fR) _ stuck = stuck (sSil refl)
progress (pR , fF , pD , fF) _ stuck = stuck (sSil refl)
progress (pR , fF , pD , fHO) _ stuck = stuck (sSil refl)
progress (pR , fF , pD , fHN) _ stuck = stuck (sSil refl)
progress (pR , fF , pD , fR) _ stuck = stuck (sSil refl)
progress (pR , fF , pR , fF) _ stuck = stuck (sSil refl)
progress (pR , fF , pR , fHO) _ stuck = stuck (sSil refl)
progress (pR , fF , pR , fHN) _ stuck = stuck (sSil refl)
progress (pR , fF , pR , fR) _ stuck = stuck (sSil refl)
progress (pR , fHO , pT , fF) _ stuck = stuck (sSil refl)
progress (pR , fHO , pT , fHO) _ stuck = stuck (sSil refl)
progress (pR , fHO , pT , fHN) _ stuck = stuck (sSil refl)
progress (pR , fHO , pT , fR) _ stuck = stuck (sSil refl)
progress (pR , fHO , pO , fF) _ stuck = stuck (sSil refl)
progress (pR , fHO , pO , fHO) _ stuck = stuck (sSil refl)
progress (pR , fHO , pO , fHN) _ stuck = stuck (sSil refl)
progress (pR , fHO , pO , fR) _ stuck = stuck (sSil refl)
progress (pR , fHO , pE , fF) _ stuck = stuck (sSil refl)
progress (pR , fHO , pE , fHO) _ stuck = stuck (sSil refl)
progress (pR , fHO , pE , fHN) _ stuck = stuck (sSil refl)
progress (pR , fHO , pE , fR) _ stuck = stuck (sSil refl)
progress (pR , fHO , pD , fF) _ stuck = stuck (sSil refl)
progress (pR , fHO , pD , fHO) _ stuck = stuck (sSil refl)
progress (pR , fHO , pD , fHN) _ stuck = stuck (sSil refl)
progress (pR , fHO , pD , fR) _ stuck = stuck (sSil refl)
progress (pR , fHO , pR , fF) _ stuck = stuck (sSil refl)
progress (pR , fHO , pR , fHO) _ stuck = stuck (sSil refl)
progress (pR , fHO , pR , fHN) _ stuck = stuck (sSil refl)
progress (pR , fHO , pR , fR) _ stuck = stuck (sSil refl)
progress (pR , fHN , pT , fF) _ stuck = stuck (sSil refl)
progress (pR , fHN , pT , fHO) _ stuck = stuck (sSil refl)
progress (pR , fHN , pT , fHN) _ stuck = stuck (sSil refl)
progress (pR , fHN , pT , fR) _ stuck = stuck (sSil refl)
progress (pR , fHN , pO , fF) _ stuck = stuck (sSil refl)
progress (pR , fHN , pO , fHO) _ stuck = stuck (sSil refl)
progress (pR , fHN , pO , fHN) _ stuck = stuck (sSil refl)
progress (pR , fHN , pO , fR) _ stuck = stuck (sSil refl)
progress (pR , fHN , pE , fF) _ stuck = stuck (sSil refl)
progress (pR , fHN , pE , fHO) _ stuck = stuck (sSil refl)
progress (pR , fHN , pE , fHN) _ stuck = stuck (sSil refl)
progress (pR , fHN , pE , fR) _ stuck = stuck (sSil refl)
progress (pR , fHN , pD , fF) _ stuck = stuck (sSil refl)
progress (pR , fHN , pD , fHO) _ stuck = stuck (sSil refl)
progress (pR , fHN , pD , fHN) _ stuck = stuck (sSil refl)
progress (pR , fHN , pD , fR) _ stuck = stuck (sSil refl)
progress (pR , fHN , pR , fF) _ stuck = stuck (sSil refl)
progress (pR , fHN , pR , fHO) _ stuck = stuck (sSil refl)
progress (pR , fHN , pR , fHN) _ stuck = stuck (sSil refl)
progress (pR , fHN , pR , fR) _ stuck = stuck (sSil refl)
progress (pR , fR , pT , fF) _ stuck = stuck (sSil refl)
progress (pR , fR , pT , fHO) _ stuck = stuck (sSil refl)
progress (pR , fR , pT , fHN) _ stuck = stuck (sSil refl)
progress (pR , fR , pT , fR) _ stuck = stuck (sSil refl)
progress (pR , fR , pO , fF) _ stuck = stuck (sSil refl)
progress (pR , fR , pO , fHO) _ stuck = stuck (sSil refl)
progress (pR , fR , pO , fHN) _ stuck = stuck (sSil refl)
progress (pR , fR , pO , fR) _ stuck = stuck (sSil refl)
progress (pR , fR , pE , fF) _ stuck = stuck (sSil refl)
progress (pR , fR , pE , fHO) _ stuck = stuck (sSil refl)
progress (pR , fR , pE , fHN) _ stuck = stuck (sSil refl)
progress (pR , fR , pE , fR) _ stuck = stuck (sSil refl)
progress (pR , fR , pD , fF) _ stuck = stuck (sSil refl)
progress (pR , fR , pD , fHO) _ stuck = stuck (sSil refl)
progress (pR , fR , pD , fHN) _ stuck = stuck (sSil refl)
progress (pR , fR , pD , fR) _ stuck = stuck (sSil refl)
progress (pR , fR , pR , fF) _ stuck = stuck (sSil refl)
progress (pR , fR , pR , fHO) _ stuck = stuck (sSil refl)
progress (pR , fR , pR , fHN) _ stuck = stuck (sSil refl)
progress (pR , fR , pR , fR) _ stuck = stuck (sSil refl)

------------------------------------------------------------------------------------
-- Closure threading Cons: every state reachable from the initial config is sysState
-- cfg′ for a CONSISTENT cfg′ (induct on the big-step, sys-inv + cons-pres at each step).
reach-cons : ∀ {s t′} → sysState cfg0 ⟹⟨ s ⟩ t′ → Σ[ cfg′ ∈ SCfg ] (t′ ≡ sysState cfg′ × Cons cfg′)
reach-cons = go cfg0 cons0 refl
  where
    go : ∀ cfg {t s t′} → Cons cfg → t ≡ sysState cfg → t ⟹⟨ s ⟩ t′
       → Σ[ cfg′ ∈ SCfg ] (t′ ≡ sysState cfg′ × Cons cfg′)
    go cfg cons refl ⟹-refl         = cfg , refl , cons
    go cfg cons refl (⟹-τ  st rest) = let (cfg′ , eq , str) = sys-inv cfg st in go cfg′ (cons-pres cons str) eq rest
    go cfg cons refl (⟹-ev st rest) = let (cfg′ , eq , str) = sys-inv cfg st in go cfg′ (cons-pres cons str) eq rest

------------------------------------------------------------------------------------
-- THE THEOREM: the asymmetric dining-philosophers system (n = 2), built with the
-- compositional alphabetised parallel ∥ₐ⁺, is deadlock-free.
deadlock-free-asym : DeadlockFree SYSTEMasym
deadlock-free-asym bs stuck with reach-cons (embed∖√ bs)
... | (cfg′ , refl , cons′) = progress cfg′ cons′ stuck
