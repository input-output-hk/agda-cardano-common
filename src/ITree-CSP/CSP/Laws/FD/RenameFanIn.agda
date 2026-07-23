{-# OPTIONS --guardedness #-}

-- Fan-in bridge (keystone for the relational rename-step law):
--
--   fanNode R preimg (t ∷ u ∷ rest)
--     ≈FD  ⨅⁺ (t ⟦ R ¿ preimg ⟧) (map (_⟦ R ¿ preimg ⟧) (u ∷ rest))
--
-- The fan-in node reaches EACH renamed source `tᵢ ⟦R⟧` in ONE τ-step (flat, n-ary),
-- while `⨅⁺` reaches them via a right-nested fold of binary ⊓ (so `tᵢ` for i≥1 takes i
-- τ's, and there are intermediate "partial-fold" states with no fan-in counterpart).
-- So this is NOT a (DR-)bisimulation.  But the SETS of reachable stable states /
-- divergences coincide, so it holds at ≈FD.  Proved FD-direct: failures⊥ and
-- divergences of BOTH sides decompose to the i-indexed UNION over `tᵢ ⟦R⟧`
-- (the resolving τ's never extend the trace), and those unions are equal.

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; map; length; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there; index)
import Data.List.Relation.Unary.Any as AnyM
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.FD.RenameFanIn {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟ using (_⊓_; ⨅⁺)
open import CSP.Rename {E₁ = E} {E₂ = E} (λ e → e) (λ e → just e) (λ _ → refl)
  using (_⟦_¿_⟧; rnBranch; rnNth; ConcEvent₁; ConcEvent₂)
open import CSP.Laws.Traces.TraceLawsRenameGen {E = E}
  using (fanNode; ren-fanin-τ-inv; fanin-no-ev; rnNth-mem)
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges)
open import Semantics.Refusals            {E = E} {I = ExtI E} using (Refuses)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (IsDivergence; divergences; div-extension-closed; failures⊥;
         _⊑F⊥_; _⊑D_; _⊑FD_; _≈FD_)
open import CSP.Laws.FD.FDLawsIChoiceAssoc  E-≟
  using (⊓-failures⊥→; ⊓-failures⊥←l; ⊓-failures⊥←r; ⊓-div→; ⊓-div←l; ⊓-div←r)
open import CSP.Laws.FD.ExtChoiceFD         E-≟
  using (fail-τ-prepend; div-τ-prepend; stable-no-τ; mk-div)

private
  variable
    ℓr ℓR : Level
    Rr : Set ℓr
    R : ConcEvent₁ → ConcEvent₂ → Set ℓR
    preimg : (bt : AnyTypes E) (b : proj₁ bt)
           → List (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b))

-- abbreviation: the renaming applied to a member
ren : ∀ {ℓr ℓR} {Rr : Set ℓr} (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
      (preimg : (bt : AnyTypes E) (b : proj₁ bt)
              → List (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
    → PTree E (ExtI E) Rr → PTree E (ExtI E) Rr
ren R preimg t = t ⟦ R ¿ preimg ⟧

-------------------------------------------------------------------------------------
-- The fan-in node is unstable for a non-empty source list: its head branch (the
-- `fzero` τ) is always enabled, reaching the (renamed) head.
-------------------------------------------------------------------------------------

fanNode-τ-head : (x : PTree E (ExtI E) Rr) (xs : List (PTree E (ExtI E) Rr))
               → (fanNode R preimg (x ∷ xs)) ─[ τ ]─► (x ⟦ R ¿ preimg ⟧)
fanNode-τ-head x xs =
  sTau {i = Lift ℓ (Fin (length (x ∷ xs))) , fin} {a = lift fzero} refl refl

-- a member can be lifted into an `Any` over the same list
∈→Any : ∀ {ℓp} {P : PTree E (ExtI E) Rr → Set ℓp} {t} {ts}
      → t ∈ ts → P t → Any P ts
∈→Any (here refl) p = here p
∈→Any (there m)   p = there (∈→Any m p)

-- the witness of an `Any` together with its membership proof
Any→mem : ∀ {ℓp} {P : PTree E (ExtI E) Rr → Set ℓp} {ts}
        → Any P ts → Σ[ t′ ∈ PTree E (ExtI E) Rr ] (t′ ∈ ts × P t′)
Any→mem (here {x = y} p) = y , here refl , p
Any→mem (there m) with Any→mem m
... | t′ , mm , p = t′ , there mm , p

-------------------------------------------------------------------------------------
-- FAN-IN SIDE failures decomposition (over a NON-EMPTY list x ∷ xs).
-------------------------------------------------------------------------------------

-- ELIM: recurse on the big-step. ⟹-refl impossible (fanNode unstable); the leading τ
-- resolves to one renamed source, leaving its failure at the same trace.
fanNode-fail-elim : (x : PTree E (ExtI E) Rr) (xs : List (PTree E (ExtI E) Rr))
                    {s : List (Event√ Rr)} {B : Event√ Rr → Set ℓr} {W : PTree E (ExtI E) Rr}
                  → (fanNode R preimg (x ∷ xs)) ⟹⟨ s ⟩ W → Refuses W B
                  → Any (λ t′ → failures (t′ ⟦ R ¿ preimg ⟧) s B) (x ∷ xs)
fanNode-fail-elim x xs ⟹-refl (st , _) =
  ⊥-elim (stable-no-τ st (fanNode-τ-head x xs))
fanNode-fail-elim x xs (⟹-τ step rest) ref with ren-fanin-τ-inv step
... | t′ , mem , refl = ∈→Any mem (_ , rest , ref)
fanNode-fail-elim x xs (⟹-ev step _) _ = ⊥-elim (fanin-no-ev step)

-------------------------------------------------------------------------------------
-- A member at list-position `k = index mem` is reached by a SINGLE τ-step of the
-- fan-in node (its `fin`-indexed τ-branch `rnBranch`/`rnNth`).  This generalises
-- `fanNode-τ-head` (the `fzero` / `here` case) to an arbitrary member.
-------------------------------------------------------------------------------------

fanNode-τ-mem : ∀ {x xs} {t : PTree E (ExtI E) Rr}
              → (mem : t ∈ (x ∷ xs))
              → (fanNode R preimg (x ∷ xs)) ─[ τ ]─► (t ⟦ R ¿ preimg ⟧)
fanNode-τ-mem {x = x} {xs = xs} mem =
  sTau {i = Lift ℓ (Fin (length (x ∷ xs))) , fin} {a = lift (index mem)}
       refl (rnNth-mem mem)

-- INTRO: a failure of one renamed source lifts to fanNode by prepending its τ.
fanNode-fail-intro : (x : PTree E (ExtI E) Rr) (xs : List (PTree E (ExtI E) Rr))
                     {s : List (Event√ Rr)} {B : Event√ Rr → Set ℓr}
                   → Any (λ t′ → failures (t′ ⟦ R ¿ preimg ⟧) s B) (x ∷ xs)
                   → failures (fanNode R preimg (x ∷ xs)) s B
fanNode-fail-intro {R = R} {preimg = preimg} x xs (here f)  =
  fail-τ-prepend (fanNode-τ-head x xs) f
fanNode-fail-intro {R = R} {preimg = preimg} x xs (there a) with Any→mem a
... | t′ , mem , f = fail-τ-prepend (fanNode-τ-mem (there mem)) f

-------------------------------------------------------------------------------------
-- FAN-IN SIDE divergence decomposition (over a NON-EMPTY list x ∷ xs).
-------------------------------------------------------------------------------------

-- ELIM: recurse on the divergence's reach big-step.  The leading τ's of the reach
-- resolve to renamed sources (never extending the trace); the divergence then lives
-- at one renamed source.  The `⟹-refl` base is NOT vacuous (the node is unstable):
-- the divergence is the node's own `Diverges`, whose first τ resolves to a source.
fanNode-div-elim : (x : PTree E (ExtI E) Rr) (xs : List (PTree E (ExtI E) Rr))
                   {s : List (Event√ Rr)}
                 → divergences (fanNode R preimg (x ∷ xs)) s
                 → Any (λ t′ → divergences (t′ ⟦ R ¿ preimg ⟧) s) (x ∷ xs)
fanNode-div-elim {R = R} {preimg = preimg} x xs {s = s} d =
  AnyM.map (λ {t′} dv → subst (divergences (t′ ⟦ R ¿ preimg ⟧)) (sym sp) dv)
           (go (d .IsDivergence.reach) (d .IsDivergence.divwit))
  where
    pre = d .IsDivergence.prefix
    suf = d .IsDivergence.suffix
    sp  : s ≡ pre ++ suf
    sp  = d .IsDivergence.split
    go : ∀ {pre′} {W} → (fanNode R preimg (x ∷ xs)) ⟹⟨ pre′ ⟩ W → Diverges W
       → Any (λ t′ → divergences (t′ ⟦ R ¿ preimg ⟧) (pre′ ++ suf)) (x ∷ xs)
    go ⟹-refl dw with ren-fanin-τ-inv (dw .Diverges.step)
    ... | t′ , mem , eqW =
            ∈→Any mem (record { prefix = [] ; suffix = suf ; split = refl
                              ; witness = _ ; reach = ⟹-refl
                              ; divwit = subst Diverges eqW (dw .Diverges.rest) })
    go (⟹-τ step rest) dw with ren-fanin-τ-inv step
    ... | t′ , mem , refl =
            ∈→Any mem (record { prefix = _ ; suffix = suf ; split = refl
                              ; witness = _ ; reach = rest ; divwit = dw })
    go (⟹-ev step _) dw = ⊥-elim (fanin-no-ev step)

-- INTRO: a divergence of one renamed source lifts to fanNode by prepending its τ.
fanNode-div-intro : (x : PTree E (ExtI E) Rr) (xs : List (PTree E (ExtI E) Rr))
                    {s : List (Event√ Rr)}
                  → Any (λ t′ → divergences (t′ ⟦ R ¿ preimg ⟧) s) (x ∷ xs)
                  → divergences (fanNode R preimg (x ∷ xs)) s
fanNode-div-intro {R = R} {preimg = preimg} x xs (here dv) =
  div-τ-prepend (fanNode-τ-head x xs) dv
fanNode-div-intro {R = R} {preimg = preimg} x xs (there a) with Any→mem a
... | t′ , mem , dv = div-τ-prepend (fanNode-τ-mem (there mem)) dv

-------------------------------------------------------------------------------------
-- failures⊥ = failures ⊎ divergences: combine the two halves into one Any.
-------------------------------------------------------------------------------------

fanNode-fail⊥-elim : (x : PTree E (ExtI E) Rr) (xs : List (PTree E (ExtI E) Rr))
                     {s : List (Event√ Rr)} {B : Event√ Rr → Set ℓr}
                   → failures⊥ (fanNode R preimg (x ∷ xs)) s B
                   → Any (λ t′ → failures⊥ (t′ ⟦ R ¿ preimg ⟧) s B) (x ∷ xs)
fanNode-fail⊥-elim x xs (inj₁ (W , reach , ref)) =
  AnyM.map inj₁ (fanNode-fail-elim x xs reach ref)
fanNode-fail⊥-elim x xs (inj₂ d) =
  AnyM.map inj₂ (fanNode-div-elim x xs d)

-- split an `Any` of `failures⊥` (= failures ⊎ divergences) into the two component
-- `Any`s (this needs a per-element case split, so it cannot just be `AnyM.map`).
Any-fail⊥-split : ∀ {ts : List (PTree E (ExtI E) Rr)}
                  {s : List (Event√ Rr)} {B : Event√ Rr → Set ℓr}
                → Any (λ t′ → failures⊥ (t′ ⟦ R ¿ preimg ⟧) s B) ts
                → Any (λ t′ → failures (t′ ⟦ R ¿ preimg ⟧) s B) ts
                ⊎ Any (λ t′ → divergences (t′ ⟦ R ¿ preimg ⟧) s) ts
Any-fail⊥-split (here (inj₁ f)) = inj₁ (here f)
Any-fail⊥-split (here (inj₂ d)) = inj₂ (here d)
Any-fail⊥-split (there a′) with Any-fail⊥-split a′
... | inj₁ af = inj₁ (there af)
... | inj₂ ad = inj₂ (there ad)

fanNode-fail⊥-intro : (x : PTree E (ExtI E) Rr) (xs : List (PTree E (ExtI E) Rr))
                      {s : List (Event√ Rr)} {B : Event√ Rr → Set ℓr}
                    → Any (λ t′ → failures⊥ (t′ ⟦ R ¿ preimg ⟧) s B) (x ∷ xs)
                    → failures⊥ (fanNode R preimg (x ∷ xs)) s B
fanNode-fail⊥-intro x xs a with Any-fail⊥-split a
... | inj₁ af = inj₁ (fanNode-fail-intro x xs af)
... | inj₂ ad = inj₂ (fanNode-div-intro x xs ad)

-------------------------------------------------------------------------------------
-- ⨅⁺ SIDE decomposition (induction over the tail list, via the binary ⊓ lemmas).
-- `⨅⁺ P [] = P`;  `⨅⁺ P (Q ∷ qs) = P ⊓ ⨅⁺ Q qs`.
-------------------------------------------------------------------------------------

⨅⁺-fail⊥-elim : (P : PTree E (ExtI E) Rr) (qs : List (PTree E (ExtI E) Rr))
                {s : List (Event√ Rr)} {B : Event√ Rr → Set ℓr}
              → failures⊥ (⨅⁺ P qs) s B
              → failures⊥ P s B ⊎ Any (λ Q → failures⊥ Q s B) qs
⨅⁺-fail⊥-elim P []       f = inj₁ f
⨅⁺-fail⊥-elim P (Q ∷ qs) f with ⊓-failures⊥→ P (⨅⁺ Q qs) f
... | inj₁ fP   = inj₁ fP
... | inj₂ fRest with ⨅⁺-fail⊥-elim Q qs fRest
...   | inj₁ fQ = inj₂ (here fQ)
...   | inj₂ a  = inj₂ (there a)

⨅⁺-fail⊥-intro-here : (P : PTree E (ExtI E) Rr) (qs : List (PTree E (ExtI E) Rr))
                      {s : List (Event√ Rr)} {B : Event√ Rr → Set ℓr}
                    → failures⊥ P s B → failures⊥ (⨅⁺ P qs) s B
⨅⁺-fail⊥-intro-here P []       f = f
⨅⁺-fail⊥-intro-here P (Q ∷ qs) f = ⊓-failures⊥←l P (⨅⁺ Q qs) f

⨅⁺-fail⊥-intro-there : (P : PTree E (ExtI E) Rr) (qs : List (PTree E (ExtI E) Rr))
                       {s : List (Event√ Rr)} {B : Event√ Rr → Set ℓr}
                     → Any (λ Q → failures⊥ Q s B) qs → failures⊥ (⨅⁺ P qs) s B
⨅⁺-fail⊥-intro-there P (Q ∷ qs) (here fQ) =
  ⊓-failures⊥←r P (⨅⁺ Q qs) (⨅⁺-fail⊥-intro-here Q qs fQ)
⨅⁺-fail⊥-intro-there P (Q ∷ qs) (there a) =
  ⊓-failures⊥←r P (⨅⁺ Q qs) (⨅⁺-fail⊥-intro-there Q qs a)

⨅⁺-div-elim : (P : PTree E (ExtI E) Rr) (qs : List (PTree E (ExtI E) Rr))
              {s : List (Event√ Rr)}
            → divergences (⨅⁺ P qs) s
            → divergences P s ⊎ Any (λ Q → divergences Q s) qs
⨅⁺-div-elim P []       d = inj₁ d
⨅⁺-div-elim P (Q ∷ qs) d with ⊓-div→ P (⨅⁺ Q qs) d
... | inj₁ dP   = inj₁ dP
... | inj₂ dRest with ⨅⁺-div-elim Q qs dRest
...   | inj₁ dQ = inj₂ (here dQ)
...   | inj₂ a  = inj₂ (there a)

⨅⁺-div-intro-here : (P : PTree E (ExtI E) Rr) (qs : List (PTree E (ExtI E) Rr))
                    {s : List (Event√ Rr)}
                  → divergences P s → divergences (⨅⁺ P qs) s
⨅⁺-div-intro-here P []       d = d
⨅⁺-div-intro-here P (Q ∷ qs) d = ⊓-div←l P (⨅⁺ Q qs) d

⨅⁺-div-intro-there : (P : PTree E (ExtI E) Rr) (qs : List (PTree E (ExtI E) Rr))
                     {s : List (Event√ Rr)}
                   → Any (λ Q → divergences Q s) qs → divergences (⨅⁺ P qs) s
⨅⁺-div-intro-there P (Q ∷ qs) (here dQ) =
  ⊓-div←r P (⨅⁺ Q qs) (⨅⁺-div-intro-here Q qs dQ)
⨅⁺-div-intro-there P (Q ∷ qs) (there a) =
  ⊓-div←r P (⨅⁺ Q qs) (⨅⁺-div-intro-there Q qs a)

-------------------------------------------------------------------------------------
-- Bridge `Any (λ t′ → φ (t′⟦R⟧)) (t ∷ u ∷ rest)`  ↔  head φ(t⟦R⟧)  +  tail Any over
-- `map (·⟦R⟧) (u ∷ rest)`, using `AnyP.map⁺`/`map⁻`.
-------------------------------------------------------------------------------------

-- collapse the head-vs-tail of an Any over the fan-in list onto the ⨅⁺ operands.
ren-Any→⨅ : ∀ {ℓp} {φ : PTree E (ExtI E) Rr → Set ℓp}
              {t u : PTree E (ExtI E) Rr} {rest : List (PTree E (ExtI E) Rr)}
          → Any (λ t′ → φ (t′ ⟦ R ¿ preimg ⟧)) (t ∷ u ∷ rest)
          → φ (t ⟦ R ¿ preimg ⟧)
          ⊎ Any φ (map (_⟦ R ¿ preimg ⟧) (u ∷ rest))
ren-Any→⨅ (here ph)  = inj₁ ph
ren-Any→⨅ (there a)  = inj₂ (AnyP.map⁺ a)

ren-⨅→Any : ∀ {ℓp} {φ : PTree E (ExtI E) Rr → Set ℓp}
              {t u : PTree E (ExtI E) Rr} {rest : List (PTree E (ExtI E) Rr)}
          → φ (t ⟦ R ¿ preimg ⟧)
          ⊎ Any φ (map (_⟦ R ¿ preimg ⟧) (u ∷ rest))
          → Any (λ t′ → φ (t′ ⟦ R ¿ preimg ⟧)) (t ∷ u ∷ rest)
ren-⨅→Any (inj₁ ph) = here ph
ren-⨅→Any (inj₂ a)  = there (AnyP.map⁻ a)

-------------------------------------------------------------------------------------
-- The keystone fan-in bridge: fanNode (t∷u∷rest) ≈FD ⨅⁺ (t⟦R⟧) (map (·⟦R⟧) (u∷rest)).
-------------------------------------------------------------------------------------

fanNode-⨅⁺-FD :
    (t u : PTree E (ExtI E) Rr) (rest : List (PTree E (ExtI E) Rr))
  → fanNode R preimg (t ∷ u ∷ rest)
    ≈FD ⨅⁺ (t ⟦ R ¿ preimg ⟧) (map (_⟦ R ¿ preimg ⟧) (u ∷ rest))
fanNode-⨅⁺-FD {R = R} {preimg = preimg} t u rest =
  (fan⊑F⊥⨅ , fan⊑D⨅) , (⨅⊑F⊥fan , ⨅⊑D⨅fan)
  where
    P  = t ⟦ R ¿ preimg ⟧
    qs = map (_⟦ R ¿ preimg ⟧) (u ∷ rest)

    -- fanNode ⊑F⊥ ⨅⁺ : a failure⊥ of ⨅⁺ is one of a member, hence of fanNode.
    fan⊑F⊥⨅ : fanNode R preimg (t ∷ u ∷ rest) ⊑F⊥ ⨅⁺ P qs
    fan⊑F⊥⨅ {s = s} {B = B} f with ⨅⁺-fail⊥-elim P qs f
    ... | inj₁ fP = fanNode-fail⊥-intro t (u ∷ rest)
                      (ren-⨅→Any {φ = λ W → failures⊥ W s B} (inj₁ fP))
    ... | inj₂ aQ = fanNode-fail⊥-intro t (u ∷ rest)
                      (ren-⨅→Any {φ = λ W → failures⊥ W s B} (inj₂ aQ))

    -- fanNode ⊑D ⨅⁺
    fan⊑D⨅ : fanNode R preimg (t ∷ u ∷ rest) ⊑D ⨅⁺ P qs
    fan⊑D⨅ {s = s} d with ⨅⁺-div-elim P qs d
    ... | inj₁ dP = fanNode-div-intro t (u ∷ rest)
                      (ren-⨅→Any {φ = λ W → divergences W s} (inj₁ dP))
    ... | inj₂ aQ = fanNode-div-intro t (u ∷ rest)
                      (ren-⨅→Any {φ = λ W → divergences W s} (inj₂ aQ))

    -- ⨅⁺ ⊑F⊥ fanNode
    ⨅⊑F⊥fan : ⨅⁺ P qs ⊑F⊥ fanNode R preimg (t ∷ u ∷ rest)
    ⨅⊑F⊥fan {s = s} {B = B} f
      with ren-Any→⨅ {φ = λ W → failures⊥ W s B} (fanNode-fail⊥-elim t (u ∷ rest) f)
    ... | inj₁ fP = ⨅⁺-fail⊥-intro-here  P qs fP
    ... | inj₂ aQ = ⨅⁺-fail⊥-intro-there P qs aQ

    -- ⨅⁺ ⊑D fanNode
    ⨅⊑D⨅fan : ⨅⁺ P qs ⊑D fanNode R preimg (t ∷ u ∷ rest)
    ⨅⊑D⨅fan {s = s} d
      with ren-Any→⨅ {φ = λ W → divergences W s} (fanNode-div-elim t (u ∷ rest) d)
    ... | inj₁ dP = ⨅⁺-div-intro-here  P qs dP
    ... | inj₂ aQ = ⨅⁺-div-intro-there P qs aQ
