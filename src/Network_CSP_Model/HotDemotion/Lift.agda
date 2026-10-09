{-# OPTIONS --guardedness #-}

-- Every step of `SysAt m s` is exactly one `sstep` move (no τ; √ only when final), so
-- traces of `Sys m` (as lists of `lbl` letters, no √) are exactly `Steps` runs.
module HotDemotion.Lift where

open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic using (tt)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees
open PTree
open import HotDemotion.Model
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import Semantics.Failures {E = Ev} {I = ExtI Ev} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import CSP.Operators Ev-≟

-- trace letters of a Steps label list: each (at , a) is the visible event `lbl at a`
lab : List (Σ (AnyTypes Ev) proj₁) → List (Event√ U)
lab []             = []
lab ((at , a) ∷ w) = lbl at a ∷ lab w

-- a non-final state's tree is a react node (offer map left abstract)
force-false : ∀ {m s} → final s ≡ false
            → Σ[ v ∈ ((at : AnyTypes Ev) → ContinueType at (Maybe Proc)) ] (force (SysAt m s) ≡ react v ∅t)
force-false {m} {s} fe with final s | fe
... | false | refl = _ , refl

-- the offer map of a react-shaped state returns the sstep successor
vis-intro : ∀ {m s v τc} → force (SysAt m s) ≡ react v τc → ∀ X (ch : Ev X) a {s′}
          → sstep (X , ch) a m s ≡ just s′ → v (X , ch) a ≡ just (SysAt m s′)
vis-intro {m} {s} eq X ch a se with final s | eq
... | true  | ()
... | false | refl with sstep (X , ch) a m s | se
...   | just _ | refl = refl

-- an sstep move only leaves a non-final state
sstep-nonfinal : ∀ {m s s′} (at : AnyTypes Ev) (a : proj₁ at) → sstep at a m s ≡ just s′ → final s ≡ false
sstep-nonfinal {s = mkSt hot _}      _ _ _ = refl
sstep-nonfinal {s = mkSt awaiting _} _ _ _ = refl
sstep-nonfinal {s = mkSt timedOut _} _ _ _ = refl
sstep-nonfinal {s = mkSt warmD _} (_ , gov) demote ()
sstep-nonfinal {s = mkSt warmD _} (_ , gov) warm   ()
sstep-nonfinal {s = mkSt warmD _} (_ , gov) tmo    ()
sstep-nonfinal {s = mkSt warmD _} (_ , gov) cold   ()
sstep-nonfinal {s = mkSt warmD _} (_ , rtn) _      ()
sstep-nonfinal {s = mkSt warmD _} (_ , env) _      ()
sstep-nonfinal {s = mkSt warmD _} (_ , int) _      ()
sstep-nonfinal {s = mkSt coldD _} (_ , gov) demote ()
sstep-nonfinal {s = mkSt coldD _} (_ , gov) warm   ()
sstep-nonfinal {s = mkSt coldD _} (_ , gov) tmo    ()
sstep-nonfinal {s = mkSt coldD _} (_ , gov) cold   ()
sstep-nonfinal {s = mkSt coldD _} (_ , rtn) _      ()
sstep-nonfinal {s = mkSt coldD _} (_ , env) _      ()
sstep-nonfinal {s = mkSt coldD _} (_ , int) _      ()

-- a visible step is an sstep move (the destination is SysAt of the successor state)
Sys-ev-inv : ∀ {m s X} {ch : Ev X} {a : X} {W}
           → SysAt m s ─[ ev (evl (evLabel X ch a)) ]─► W
           → Σ[ s′ ∈ St ] (sstep (X , ch) a m s ≡ just s′ × W ≡ SysAt m s′)
Sys-ev-inv {m} {s} {X} {ch} {a} (sVis eq br) with final s | eq | br
... | true  | () | _
... | false | refl | br′ with sstep (X , ch) a m s | br′
...   | just s′ | refl = s′ , refl , refl

-- an sstep move from a non-final state is a visible step
Sys-ev-intro : ∀ {m s s′} (at : AnyTypes Ev) (a : proj₁ at)
             → sstep at a m s ≡ just s′ → final s ≡ false
             → SysAt m s ─[ ev (lbl at a) ]─► SysAt m s′
Sys-ev-intro {m} {s} (X , ch) a eq fe with force-false {m} fe
... | v , feq = sVis feq (vis-intro feq X ch a eq)

-- the system has no τ
Sys-no-τ : ∀ {m s W} → ¬ (SysAt m s ─[ τ ]─► W)
Sys-no-τ {m} {s} (sSil eq) with final s | eq
... | true  | ()
... | false | ()
Sys-no-τ {m} {s} (sTau eq br) with final s | eq
... | true  | ()
... | false | refl with br
...   | ()

-- √ is only offered in a final state
Sys-√ : ∀ {m s W} {r : U} → SysAt m s ─[ ev (√ r) ]─► W → final s ≡ true
Sys-√ {m} {s} (sRet eq) with final s | eq
... | true  | _  = refl
... | false | ()

-- every run of the system on a lbl-trace is a Steps run between model states
traces⇒Steps : ∀ {m s W} (w : List (Σ (AnyTypes Ev) proj₁))
             → SysAt m s ⟹⟨ lab w ⟩ W → Σ[ s′ ∈ St ] (Steps m s w s′ × W ≡ SysAt m s′)
traces⇒Steps []                  ⟹-refl = _ , done , refl
traces⇒Steps []                  (⟹-τ st _) with Sys-no-τ st
... | ()
traces⇒Steps (_ ∷ _)             (⟹-τ st _) with Sys-no-τ st
... | ()
traces⇒Steps (((X , ch) , a) ∷ w)  (⟹-ev st rest) with Sys-ev-inv st
... | s₁ , eq , refl with traces⇒Steps w rest
...   | s′ , ss , eqW = s′ , more eq ss , eqW

-- every Steps run is a run of the system on its lbl-trace
Steps⇒traces : ∀ {m s s′ w} → Steps m s w s′ → SysAt m s ⟹⟨ lab w ⟩ SysAt m s′
Steps⇒traces done = ⟹-refl
Steps⇒traces (more {at = at} {a = a} eq ss) = ⟹-ev (Sys-ev-intro at a eq (sstep-nonfinal at a eq)) (Steps⇒traces ss)

-- traces of Sys m from the initial state
Sys-traces⇒Steps : ∀ {m W} (w : List (Σ (AnyTypes Ev) proj₁))
                 → Sys m ⟹⟨ lab w ⟩ W → Σ[ s ∈ St ] (Steps m st₀ w s × W ≡ SysAt m s)
Sys-traces⇒Steps = traces⇒Steps
