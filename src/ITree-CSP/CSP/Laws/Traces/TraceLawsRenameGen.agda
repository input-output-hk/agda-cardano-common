{-# OPTIONS --guardedness #-}

-- Trace laws for the GENERAL relational renaming `_⟦ R ¿ preimg ⟧` (same alphabet).
-- Unlike the injective `renameInv`, a target offered by ≥2 sources yields a fan-in
-- INTERNAL-CHOICE node (`rnFan` of ≥2 ⇒ `react ∅ τc`) reached by the visible event and
-- then resolved by a τ.  So a renamed visible step is in general WEAK (ev · τ*).
--
-- This file: the renaming relation on traces `RenTrG` and the trace INTRODUCTION
-- (renamed traces of P are traces of P⟦R⟧), handling fan-in via `rnFan-reach`.

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there; index)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.Traces.TraceLawsRenameGen {ℓ ℓe} {E : Set ℓ → Set ℓe} where
open PTree

open import Semantics.LTS       {E = E} {I = ExtI E}
open import Semantics.WeakBisim {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wev)
open import Semantics.Failures  {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; weaken-ev; _⊑T_)
open import CSP.Rename {E₁ = E} {E₂ = E} (λ e → e) (λ e → just e) (λ _ → refl)

private
  variable
    ℓr ℓR : Level
    Rr : Set ℓr
    R : ConcEvent₁ → ConcEvent₂ → Set ℓR
    preimg : (bt : AnyTypes E) (b : proj₁ bt)
           → List (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b))

-------------------------------------------------------------------------------------
-- Renaming relation on traces: each target event comes (via `R`/`preimg`) from a
-- source event enumerated in its preimage; √ passes through.
-------------------------------------------------------------------------------------

data RenTrG {Rr : Set ℓr}
            (R      : ConcEvent₁ → ConcEvent₂ → Set ℓR)
            (preimg : (bt : AnyTypes E) (b : proj₁ bt)
                    → List (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
          : List (Event√ Rr) → List (Event√ Rr) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr ⊔ ℓR) where
  []ᵍ : RenTrG R preimg [] []
  evᵍ : ∀ {at a bt b r s s′}
      → (at , a , r) ∈ preimg bt b
      → RenTrG R preimg s s′
      → RenTrG R preimg (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s)
                        (evl (evLabel (proj₁ bt) (proj₂ bt) b) ∷ s′)
  √ᵍ  : ∀ {rr s s′} → RenTrG R preimg s s′ → RenTrG R preimg (√ rr ∷ s) (√ rr ∷ s′)

-------------------------------------------------------------------------------------
-- force-equations for the general rename (re-do `with force P` so it reduces).
-------------------------------------------------------------------------------------

force-renG-ret : ∀ {P : PTree E (ExtI E) Rr} {r}
               → PTree.force P ≡ ret r → PTree.force (P ⟦ R ¿ preimg ⟧) ≡ ret r
force-renG-ret {P = P} eq with PTree.force P
... | ret _ = eq

force-renG-sil : ∀ {P P₁ : PTree E (ExtI E) Rr}
               → PTree.force P ≡ sil P₁ → PTree.force (P ⟦ R ¿ preimg ⟧) ≡ sil (P₁ ⟦ R ¿ preimg ⟧)
force-renG-sil {P = P} eq with PTree.force P
... | sil _ with refl ← eq = refl

force-renG-react : ∀ {P : PTree E (ExtI E) Rr}
                  {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) Rr))}
                  {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) Rr))}
                → PTree.force P ≡ react vP τcP
                → PTree.force (P ⟦ R ¿ preimg ⟧)
                  ≡ react (λ bt b → rnFan R preimg (rnCollect vP (preimg bt b)))
                         (extBranch R preimg τcP)
force-renG-react {P = P} eq with PTree.force P
... | react _ _ with refl ← eq = refl

-------------------------------------------------------------------------------------
-- Fan-in reach: any member of the collected source list is weakly reached by `rnFan`.
-------------------------------------------------------------------------------------

-- the k-th branch of the fan-in node hits the k-th source's renaming
rnNth-mem : ∀ {R : ConcEvent₁ → ConcEvent₂ → Set ℓR} {preimg}
              {ts : List (PTree E (ExtI E) Rr)} {t}
          → (mem : t ∈ ts) → rnNth R preimg ts (index mem) ≡ just (t ⟦ R ¿ preimg ⟧)
rnNth-mem (here refl) = refl
rnNth-mem (there mem) = rnNth-mem mem

rnFan-reach : ∀ {R : ConcEvent₁ → ConcEvent₂ → Set ℓR} {preimg}
                {ts : List (PTree E (ExtI E) Rr)} {t}
            → t ∈ ts
            → Σ[ W ∈ PTree E (ExtI E) Rr ] (rnFan R preimg ts ≡ just W × W ─[τ*]─► (t ⟦ R ¿ preimg ⟧))
rnFan-reach {ts = t′ ∷ []}     (here refl) = _ , refl , τ*-refl
rnFan-reach {R = R} {preimg = preimg} {ts = t′ ∷ u ∷ r} mem =
  _ , refl ,
  τ*-step (sTau {i = Lift ℓ (Fin (length (t′ ∷ u ∷ r))) , fin} {a = lift (index mem)}
                refl (rnNth-mem {R = R} {preimg = preimg} mem)) τ*-refl

-- an enabled source listed in the target's preimage is collected (generic in the
-- entry predicate `Pr`, since `rnCollect` is)
rnCollect-mem : ∀ {ℓP} {Pr : (at : AnyTypes E) → proj₁ at → Set ℓP}
                  {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) Rr))}
                  {entries : List (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] Pr at a)}
                  {at a} {pr : Pr at a} {P₁ : PTree E (ExtI E) Rr}
              → (at , a , pr) ∈ entries → vP at a ≡ just P₁ → P₁ ∈ rnCollect vP entries
rnCollect-mem {vP = vP} {at = at} {a = a} (here refl) eqv with vP at a | eqv
... | just P₁ | refl = here refl
rnCollect-mem {vP = vP} {entries = (at′ , a′ , _) ∷ _} (there mem) eqv with vP at′ a′
... | just _  = there (rnCollect-mem mem eqv)
... | nothing = rnCollect-mem mem eqv

-------------------------------------------------------------------------------------
-- Forward LTS step lemmas (the ev step is WEAK: ev then the fan-in resolution τ*).
-------------------------------------------------------------------------------------

extBranch-just : ∀ {R : ConcEvent₁ → ConcEvent₂ → Set ℓR} {preimg}
                   {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) Rr))}
                   {A} {eι₂ eι₁ : ExtI E A} {a : A} {P₁ : PTree E (ExtI E) Rr}
               → extBwd eι₂ ≡ just eι₁ → τcP (A , eι₁) a ≡ just P₁
               → extBranch R preimg τcP (A , eι₂) a ≡ just (P₁ ⟦ R ¿ preimg ⟧)
extBranch-just {eι₂ = eι₂} eqb eqt with extBwd eι₂ | eqb
... | just eι₁ | refl rewrite eqt = refl

ren-τ-fwd : ∀ {P P₁ : PTree E (ExtI E) Rr}
          → P ─[ τ ]─► P₁ → (P ⟦ R ¿ preimg ⟧) ─[ τ ]─► (P₁ ⟦ R ¿ preimg ⟧)
ren-τ-fwd {R = R} {preimg = preimg} {P = P} (sSil eq) =
  sSil (force-renG-sil {R = R} {preimg = preimg} {P = P} eq)
ren-τ-fwd {R = R} {preimg = preimg} {P = P} (sTau {τc = τcP} {i = A , eι₁} {a = a} eq br) =
  sTau {i = A , extFwd eι₁} {a = a}
       (force-renG-react {R = R} {preimg = preimg} {P = P} eq)
       (extBranch-just {R = R} {preimg = preimg} {τcP = τcP} {eι₂ = extFwd eι₁} {eι₁ = eι₁} {a = a}
                       (ext-linv eι₁) br)

ren-ev-fwd-weak : ∀ {P P₁ : PTree E (ExtI E) Rr} {at a bt b r}
                → P ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P₁
                → (at , a , r) ∈ preimg bt b
                → (P ⟦ R ¿ preimg ⟧) ═[ ev (evl (evLabel (proj₁ bt) (proj₂ bt) b)) ]═► (P₁ ⟦ R ¿ preimg ⟧)
ren-ev-fwd-weak {R = R} {preimg = preimg} {P = P} {bt = bt} {b = b}
                (sVis {v = vP} {at = at} {a = a} eq br) mem
  with rnFan-reach {R = R} {preimg = preimg}
                   (rnCollect-mem {vP = vP} {entries = preimg bt b} mem br)
... | W , eqFan , W→ =
  wev τ*-refl
      (sVis {at = bt} {a = b} (force-renG-react {R = R} {preimg = preimg} {P = P} eq) eqFan)
      W→

ren-√-fwd : ∀ {P : PTree E (ExtI E) Rr} {r}
          → PTree.force P ≡ ret r → (P ⟦ R ¿ preimg ⟧) ─[ ev (√ r) ]─► deadlock
ren-√-fwd {P = P} eq = sRet (force-renG-ret {P = P} eq)

deadlock-⟹-[] : {W : PTree E (ExtI E) Rr} {s : List (Event√ Rr)}
              → deadlock ⟹⟨ s ⟩ W → s ≡ [] × W ≡ deadlock
deadlock-⟹-[] ⟹-refl              = refl , refl
deadlock-⟹-[] (⟹-τ (sSil ()) _)
deadlock-⟹-[] (⟹-τ (sTau refl ()) _)
deadlock-⟹-[] (⟹-ev (sRet ()) _)
deadlock-⟹-[] (⟹-ev (sVis refl ()) _)

-------------------------------------------------------------------------------------
-- Trace INTRODUCTION: renamed traces of P are traces of P⟦R⟧ (fan-in via weak ev).
-------------------------------------------------------------------------------------

ren-trace-introG : ∀ {P P′ : PTree E (ExtI E) Rr} {s s′}
                 → P ⟹⟨ s ⟩ P′ → RenTrG R preimg s s′ → traces (P ⟦ R ¿ preimg ⟧) s′
ren-trace-introG ⟹-refl []ᵍ = _ , ⟹-refl
ren-trace-introG (⟹-τ pτ rest) ren with ren-trace-introG rest ren
... | W , reach = W , ⟹-τ (ren-τ-fwd pτ) reach
ren-trace-introG (⟹-ev pev rest) (evᵍ mem rest-ren) with ren-trace-introG rest rest-ren
... | W , reach = W , weaken-ev (ren-ev-fwd-weak pev mem) reach
ren-trace-introG (⟹-ev (sRet eq) rest) (√ᵍ rest-ren) with deadlock-⟹-[] rest
... | refl , refl with rest-ren
...   | []ᵍ = deadlock , ⟹-ev (ren-√-fwd eq) ⟹-refl

-------------------------------------------------------------------------------------
-- ELIM direction.  Harder than the injective case: a renamed visible step may land
-- in a fan-in INTERNAL-CHOICE node `fanNode ts` (when ≥2 sources map to the target),
-- which is NOT a renamed process.  We carry this intermediate state explicitly and
-- prove the elim by mutual recursion on aligned (`Q ⟦R⟧`) and fan-in nodes.
-------------------------------------------------------------------------------------

-- the fan-in internal-choice node: empty visible offer, τ-branches `rnBranch`.
fanNode : (R      : ConcEvent₁ → ConcEvent₂ → Set ℓR)
        → (preimg : (bt : AnyTypes E) (b : proj₁ bt)
                  → List (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
        → List (PTree E (ExtI E) Rr) → PTree E (ExtI E) Rr
fanNode R preimg ts = ptree (react (λ _ _ → nothing) (rnBranch R preimg ts))

-------------------------------------------------------------------------------------
-- force INVERSIONS for the general rename (recover the source node shape).
-------------------------------------------------------------------------------------

force-renG-ret-inv : ∀ {P : PTree E (ExtI E) Rr} {r}
                   → PTree.force (P ⟦ R ¿ preimg ⟧) ≡ ret r → PTree.force P ≡ ret r
force-renG-ret-inv {P = P} eq with PTree.force P
... | ret _    = eq
... | sil _    = case eq of λ ()
... | react _ _ = case eq of λ ()

force-renG-sil-inv : ∀ {P W : PTree E (ExtI E) Rr}
                   → PTree.force (P ⟦ R ¿ preimg ⟧) ≡ sil W
                   → Σ[ P₁ ∈ PTree E (ExtI E) Rr ] (PTree.force P ≡ sil P₁ × W ≡ P₁ ⟦ R ¿ preimg ⟧)
force-renG-sil-inv {P = P} eq with PTree.force P
... | ret _    = case eq of λ ()
... | sil P₁   = P₁ , refl , sym (sil-injective eq)
... | react _ _ = case eq of λ ()

force-renG-react-inv : ∀ {P : PTree E (ExtI E) Rr}
                        {v′ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) Rr))}
                        {τc′ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) Rr))}
                    → PTree.force (P ⟦ R ¿ preimg ⟧) ≡ react v′ τc′
                    → Σ[ vP ∈ _ ] Σ[ τcP ∈ _ ]
                        (PTree.force P ≡ react vP τcP
                         × v′ ≡ (λ bt b → rnFan R preimg (rnCollect vP (preimg bt b)))
                         × τc′ ≡ extBranch R preimg τcP)
force-renG-react-inv {P = P} eq with PTree.force P
... | ret _       = case eq of λ ()
... | sil _       = case eq of λ ()
... | react vP τcP = vP , τcP , refl , sym (proj₁ (react-injective eq)) , sym (proj₂ (react-injective eq))

-------------------------------------------------------------------------------------
-- Structural inversions for `rnCollect` / `rnFan` / `rnNth`.
-------------------------------------------------------------------------------------

-- every collected continuation comes from an enabled preimage entry
rnCollect-inv : ∀ {ℓP} {Pr : (at : AnyTypes E) → proj₁ at → Set ℓP}
                  {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) Rr))}
                  {entries : List (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] Pr at a)}
                  {t : PTree E (ExtI E) Rr}
              → t ∈ rnCollect vP entries
              → Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] Σ[ pr ∈ Pr at a ]
                  ((at , a , pr) ∈ entries × vP at a ≡ just t)
rnCollect-inv {entries = []} ()
rnCollect-inv {vP = vP} {entries = (at , a , pr) ∷ rest} mem with vP at a in eqv
... | nothing with at′ , a′ , pr′ , memE , eqv′ ← rnCollect-inv {vP = vP} {entries = rest} mem =
      at′ , a′ , pr′ , there memE , eqv′
... | just t′ with mem
...   | here refl  = at , a , pr , here refl , eqv
...   | there mem′ with at′ , a′ , pr′ , memE , eqv′ ← rnCollect-inv {vP = vP} {entries = rest} mem′ =
        at′ , a′ , pr′ , there memE , eqv′

-- `rnFan` is `nothing` only when empty; a singleton is τ-free, ≥2 is a fan-in node
rnFan-inv : ∀ {ts : List (PTree E (ExtI E) Rr)} {W}
          → rnFan R preimg ts ≡ just W
          → (Σ[ t ∈ PTree E (ExtI E) Rr ] (ts ≡ t ∷ [] × W ≡ t ⟦ R ¿ preimg ⟧))
          ⊎ (Σ[ t ∈ _ ] Σ[ u ∈ _ ] Σ[ r ∈ _ ]
               (ts ≡ t ∷ u ∷ r × W ≡ fanNode R preimg (t ∷ u ∷ r)))
rnFan-inv {ts = []}        ()
rnFan-inv {ts = t ∷ []}    refl = inj₁ (t , refl , refl)
rnFan-inv {ts = t ∷ u ∷ r} refl = inj₂ (t , u , r , refl , refl)

-- a τ-branch of the fan-in node resolves to the k-th source, renamed
rnNth-inv : ∀ {ts : List (PTree E (ExtI E) Rr)} {m} {k : Fin m} {W}
          → rnNth R preimg ts k ≡ just W
          → Σ[ t ∈ PTree E (ExtI E) Rr ] (t ∈ ts × W ≡ t ⟦ R ¿ preimg ⟧)
rnNth-inv {ts = []}      eq = case eq of λ ()
rnNth-inv {ts = t ∷ ts} {k = fzero}  refl = t , here refl , refl
rnNth-inv {ts = t ∷ ts} {k = fsuc k} eq with rnNth-inv {ts = ts} {k = k} eq
... | t′ , mem , eqW = t′ , there mem , eqW

-------------------------------------------------------------------------------------
-- LTS step inversions for renamed / fan-in states.
-------------------------------------------------------------------------------------

ren-τ-inv : ∀ {P W : PTree E (ExtI E) Rr}
          → (P ⟦ R ¿ preimg ⟧) ─[ τ ]─► W
          → Σ[ P₁ ∈ PTree E (ExtI E) Rr ] (P ─[ τ ]─► P₁ × W ≡ P₁ ⟦ R ¿ preimg ⟧)
ren-τ-inv {P = P} (sSil eq) with force-renG-sil-inv {P = P} eq
... | P₁ , eqP , eqW = P₁ , sSil eqP , eqW
ren-τ-inv {P = P} (sTau {i = A , eι₂} {a = a} eq br) with force-renG-react-inv {P = P} eq
... | vP , τcP , eqP , _ , refl with extBwd eι₂
...   | nothing = case br of λ ()
...   | just eι₁ with τcP (A , eι₁) a in eqt
...     | nothing = case br of λ ()
...     | just t′ = t′ , sTau eqP eqt , sym (just-injective br)

ren-ev-inv : ∀ {P W : PTree E (ExtI E) Rr} {e′}
           → (P ⟦ R ¿ preimg ⟧) ─[ ev e′ ]─► W
           → (Σ[ bt ∈ AnyTypes E ] Σ[ b ∈ proj₁ bt ] Σ[ vP ∈ _ ] Σ[ τcP ∈ _ ]
                (PTree.force P ≡ react vP τcP
                 × e′ ≡ evl (evLabel (proj₁ bt) (proj₂ bt) b)
                 × rnFan R preimg (rnCollect vP (preimg bt b)) ≡ just W))
           ⊎ (Σ[ r ∈ Rr ] (e′ ≡ √ r) × (PTree.force P ≡ ret r) × (W ≡ deadlock))
ren-ev-inv {P = P} (sRet eq) = inj₂ (_ , refl , force-renG-ret-inv {P = P} eq , refl)
ren-ev-inv {P = P} (sVis {at = bt} {a = b} eq br) with force-renG-react-inv {P = P} eq
... | vP , τcP , eqP , refl , _ = inj₁ (bt , b , vP , τcP , eqP , refl , br)

-- a fan-in node offers NO visible event (its vis-part is `λ _ _ → nothing`)
fanin-no-ev : ∀ {ts : List (PTree E (ExtI E) Rr)} {e′ W}
            → (fanNode R preimg ts) ─[ ev e′ ]─► W → ⊥
fanin-no-ev (sRet eq)    = case eq of λ ()
fanin-no-ev (sVis eq br) with react-injective eq
... | refl , _ = case br of λ ()

-- a τ-step from a fan-in node resolves the internal choice to one renamed source
ren-fanin-τ-inv : ∀ {ts : List (PTree E (ExtI E) Rr)} {W}
                → (fanNode R preimg ts) ─[ τ ]─► W
                → Σ[ t ∈ PTree E (ExtI E) Rr ] (t ∈ ts × W ≡ t ⟦ R ¿ preimg ⟧)
ren-fanin-τ-inv (sSil eq) = case eq of λ ()
ren-fanin-τ-inv {ts = ts} (sTau {i = A , eι₂} {a = a} eq br) with react-injective eq
... | refl , refl with eι₂ | a
...   | base _   | _      = case br of λ ()
...   | pair _ _ | _      = case br of λ ()
...   | fin      | lift k = rnNth-inv {ts = ts} {k = k} br

-------------------------------------------------------------------------------------
-- The mutual ELIM: a renamed trace comes from a source trace under `RenTrG`.
-- `elim-aligned` handles a renamed state `Q ⟦R⟧`; `elim-fanin` an internal-choice
-- fan-in node `fanNode (t∷u∷r)` (always ≥2 sources, hence non-empty).
-------------------------------------------------------------------------------------

elim-aligned : ∀ {Q Wf : PTree E (ExtI E) Rr} {s′}
             → (Q ⟦ R ¿ preimg ⟧) ⟹⟨ s′ ⟩ Wf
             → Σ[ s ∈ List (Event√ Rr) ] Σ[ P′ ∈ PTree E (ExtI E) Rr ]
                 (Q ⟹⟨ s ⟩ P′ × RenTrG R preimg s s′)

elim-fanin : ∀ {t u r} {Wf : PTree E (ExtI E) Rr} {s′}
           → (fanNode R preimg (t ∷ u ∷ r)) ⟹⟨ s′ ⟩ Wf
           → Σ[ t′ ∈ PTree E (ExtI E) Rr ] (t′ ∈ (t ∷ u ∷ r) ×
               Σ[ s ∈ List (Event√ Rr) ] Σ[ P′ ∈ PTree E (ExtI E) Rr ]
                 (t′ ⟹⟨ s ⟩ P′ × RenTrG R preimg s s′))

elim-aligned ⟹-refl = [] , _ , ⟹-refl , []ᵍ
elim-aligned (⟹-τ step rest) with ren-τ-inv step
... | Q₁ , Qτ , refl with elim-aligned rest
...   | s , P′ , Qreach , ren = s , P′ , ⟹-τ Qτ Qreach , ren
elim-aligned (⟹-ev step rest) with ren-ev-inv step
... | inj₂ (r , refl , eqQ , refl) with deadlock-⟹-[] rest
...   | refl , refl = √ r ∷ [] , deadlock , ⟹-ev (sRet eqQ) ⟹-refl , √ᵍ []ᵍ
elim-aligned (⟹-ev step rest) | inj₁ (bt , b , vP , τcP , eqQ , refl , eqFan)
  with rnFan-inv eqFan
... | inj₁ (t , eqts , refl)
      with rnCollect-inv {vP = vP} {entries = _} (subst (t ∈_) (sym eqts) (here refl))
...      | at , a , pr , memE , eqv with elim-aligned rest
...         | s , P′ , treach , ren =
              evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s , P′ ,
              ⟹-ev (sVis eqQ eqv) treach , evᵍ memE ren
elim-aligned (⟹-ev step rest) | inj₁ (bt , b , vP , τcP , eqQ , refl , eqFan)
  | inj₂ (t , u , r , eqts , refl)
      with elim-fanin rest
...      | t′ , memTs , s , P′ , treach , ren
         with rnCollect-inv {vP = vP} {entries = _} (subst (t′ ∈_) (sym eqts) memTs)
...         | at , a , pr , memE , eqv =
              evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s , P′ ,
              ⟹-ev (sVis eqQ eqv) treach , evᵍ memE ren

elim-fanin ⟹-refl = _ , here refl , [] , _ , ⟹-refl , []ᵍ
elim-fanin (⟹-τ step rest) with ren-fanin-τ-inv step
... | t′ , memTs , refl with elim-aligned rest
...   | s , P′ , treach , ren = t′ , memTs , s , P′ , treach , ren
elim-fanin (⟹-ev step rest) = ⊥-elim (fanin-no-ev step)

-- top-level ELIM
ren-trace-elimG : ∀ {P W : PTree E (ExtI E) Rr} {s′}
                → (P ⟦ R ¿ preimg ⟧) ⟹⟨ s′ ⟩ W
                → Σ[ s ∈ List (Event√ Rr) ] Σ[ P′ ∈ PTree E (ExtI E) Rr ]
                    (P ⟹⟨ s ⟩ P′ × RenTrG R preimg s s′)
ren-trace-elimG = elim-aligned

-------------------------------------------------------------------------------------
-- Trace monotonicity: elim the Q-side trace, transport via P ⊑T Q, re-intro.
-------------------------------------------------------------------------------------

renameG-mono-⊑ᵀ : ∀ {P Q : PTree E (ExtI E) Rr}
                → P ⊑T Q → (P ⟦ R ¿ preimg ⟧) ⊑T (Q ⟦ R ¿ preimg ⟧)
renameG-mono-⊑ᵀ p⊑q s′ (W , reachQ) with ren-trace-elimG reachQ
... | s , Q′ , Qreach , ren with p⊑q s (Q′ , Qreach)
...   | P′ , Preach = ren-trace-introG Preach ren
