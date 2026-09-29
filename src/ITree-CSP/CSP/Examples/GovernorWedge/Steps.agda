{-# OPTIONS --guardedness #-}

-- Every step of the composite `SysAt m c g` is exactly one `sstep` move and vice
-- versa (no τ, no √), so reachability and traces reduce to the pure `Steps` relation.
module CSP.Examples.GovernorWedge.Steps where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (tt)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing; map; zip; _<∣>_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

open import Process_Trees
open PTree
open import CSP.Examples.GovernorWedge.Model
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import Semantics.Failures {E = Ev} {I = ExtI Ev} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import CSP.Operators Ev-≟
open import CSP.Laws.Traces.TraceLawsParallel Ev-≟ using (Par-sync; Par-soloL; Par-soloR)
open import CSP.Laws.Traces.TraceLawsParallelElim Ev-≟
  using (ParτR; τL; τR; Par-τ-elim; ParevR; evSync; evL; evR; evBoth; ev√; Par-ev-elim)

-- the composite's step: shared channels need both sides, conn only Conn, gov only Gov; cstep gets the mode's CM policy
sstep : (at : AnyTypes Ev) → proj₁ at → Mode → CState → GState → Maybe (CState × GState)
sstep (_ , conn)    a m c g = map (λ c′ → c′ , g) (cstep (_ , conn) a (cmP m) c)
sstep (_ , gov)     a m c g = map (λ g′ → c , g′) (gstep (_ , gov) a m g)
sstep (_ , hs)      a m c g = zip (cstep (_ , hs) a (cmP m) c) (gstep (_ , hs) a m g)
sstep (_ , trace)   a m c g = zip (cstep (_ , trace) a (cmP m) c) (gstep (_ , trace) a m g)
sstep (_ , stopped) a m c g = zip (cstep (_ , stopped) a (cmP m) c) (gstep (_ , stopped) a m g)
sstep (_ , rel)     a m c g = zip (cstep (_ , rel) a (cmP m) c) (gstep (_ , rel) a m g)

-- a composite step that drops the entry of an active incarnation (spec §4.4)
OrphanStep : Mode → CState → GState → (at : AnyTypes Ev) → proj₁ at → Set
OrphanStep m c g at a = Σ[ x ∈ ℕ ] Σ[ c′ ∈ CState ] Σ[ g′ ∈ GState ]
  (sstep at a m c g ≡ just (c′ , g′) × entry g ≡ just x × entry g′ ≢ just x × Active c x)

-- an orphaning step other than the IG's own release (v4 spec §4; carrier ℕ × Bool since v4.1a); Set₁ because at : AnyTypes Ev is
OrphanStepR : Mode → CState → GState → (at : AnyTypes Ev) → proj₁ at → Set₁
OrphanStepR m c g at a = OrphanStep m c g at a × at ≢ ((ℕ × Bool) , rel)

-- the offer-map equation behind a Conn step, from the cstep equation
Conn-br : ∀ {p X} {ch : Ev X} {a : X} {c c′}
        → cstep (X , ch) a p c ≡ just c′ → viewV (force (Conn p c)) (X , ch) a ≡ just (Conn p c′)
Conn-br {p} {X} {ch} {a} {c} eq with cstep (X , ch) a p c | eq
... | just _ | refl = refl

-- the offer-map equation behind a Gov step, from the gstep equation
Gov-br : ∀ {m X} {ch : Ev X} {a : X} {g g′}
       → gstep (X , ch) a m g ≡ just g′ → viewV (force (Gov m g)) (X , ch) a ≡ just (Gov m g′)
Gov-br {m} {X} {ch} {a} {g} eq with gstep (X , ch) a m g | eq
... | just _ | refl = refl

-- a visible Conn step is a cstep move
Conn-ev-inv : ∀ {p c X} {ch : Ev X} {a : X} {W}
            → Conn p c ─[ ev (evl (evLabel X ch a)) ]─► W
            → Σ[ c′ ∈ CState ] (cstep (X , ch) a p c ≡ just c′ × W ≡ Conn p c′)
Conn-ev-inv {p} {c} {X} {ch} {a} (sVis refl breq) with cstep (X , ch) a p c | breq
... | just c′ | refl = c′ , refl , refl

-- a cstep move is a visible Conn step
Conn-ev-intro : ∀ {p c c′ X} {ch : Ev X} {a : X}
              → cstep (X , ch) a p c ≡ just c′ → Conn p c ─[ ev (evl (evLabel X ch a)) ]─► Conn p c′
Conn-ev-intro {p} {c} {c′} {X} {ch} {a} eq = sVis refl (Conn-br {p} {X} {ch} {a} {c} eq)

-- Conn has no τ
Conn-no-τ : ∀ {p c W} → ¬ (Conn p c ─[ τ ]─► W)
Conn-no-τ (sSil ())
Conn-no-τ (sTau refl ())

-- Conn never terminates
Conn-no-√ : ∀ {p c W} {r : U} → ¬ (Conn p c ─[ ev (√ r) ]─► W)
Conn-no-√ (sRet ())

-- a visible Gov step is a gstep move
Gov-ev-inv : ∀ {m g X} {ch : Ev X} {a : X} {W}
           → Gov m g ─[ ev (evl (evLabel X ch a)) ]─► W
           → Σ[ g′ ∈ GState ] (gstep (X , ch) a m g ≡ just g′ × W ≡ Gov m g′)
Gov-ev-inv {m} {g} {X} {ch} {a} (sVis refl breq) with gstep (X , ch) a m g | breq
... | just g′ | refl = g′ , refl , refl

-- a gstep move is a visible Gov step
Gov-ev-intro : ∀ {m g g′ X} {ch : Ev X} {a : X}
             → gstep (X , ch) a m g ≡ just g′ → Gov m g ─[ ev (evl (evLabel X ch a)) ]─► Gov m g′
Gov-ev-intro {m} {g} {g′} {X} {ch} {a} eq = sVis refl (Gov-br {m} {X} {ch} {a} {g} eq)

-- Gov has no τ
Gov-no-τ : ∀ {m g W} → ¬ (Gov m g ─[ τ ]─► W)
Gov-no-τ (sSil ())
Gov-no-τ (sTau refl ())

-- Gov never terminates
Gov-no-√ : ∀ {m g W} {r : U} → ¬ (Gov m g ─[ ev (√ r) ]─► W)
Gov-no-√ (sRet ())

-- the composite has no τ
Sys-no-τ : ∀ {m c g W} → ¬ (SysAt m c g ─[ τ ]─► W)
Sys-no-τ {m} {c} {g} st with Par-τ-elim syncES (λ _ _ → tt) (Conn (cmP m) c) (Gov m g) st
... | τL _ st′ _ = Conn-no-τ st′
... | τR _ st′ _ = Gov-no-τ st′

-- the composite never terminates
Sys-no-√ : ∀ {m c g W} {r : U} → ¬ (SysAt m c g ─[ ev (√ r) ]─► W)
Sys-no-√ {m} {c} {g} st with Par-ev-elim syncES (λ _ _ → tt) (Conn (cmP m) c) (Gov m g) st
... | ev√ () _

-- a composite step on a shared channel: both sides move
sync-inv : ∀ {m c g X} {ch : Ev X} {a : X} {c′ g′}
         → cstep (X , ch) a (cmP m) c ≡ just c′ → gstep (X , ch) a m g ≡ just g′
         → zip (cstep (X , ch) a (cmP m) c) (gstep (X , ch) a m g) ≡ just (c′ , g′)
sync-inv eqc eqg rewrite eqc | eqg = refl

-- every visible composite step is an sstep move
Sys-step-inv : ∀ {m c g X} {ch : Ev X} {a : X} {W}
             → SysAt m c g ─[ ev (evl (evLabel X ch a)) ]─► W
             → Σ[ c′ ∈ CState ] Σ[ g′ ∈ GState ] (sstep (X , ch) a m c g ≡ just (c′ , g′) × W ≡ SysAt m c′ g′)
Sys-step-inv {m} {c} {g} {ch = hs} {a} st with Par-ev-elim syncES (λ _ _ → tt) (Conn (cmP m) c) (Gov m g) st
... | evSync _ Pst Qst with Conn-ev-inv Pst | Gov-ev-inv Qst
...   | c′ , eqc , refl | g′ , eqg , refl = c′ , g′ , sync-inv {m} {c} {g} {ch = hs} {a} eqc eqg , refl
Sys-step-inv {ch = hs} st | evL ¬s _      = ⊥-elim (¬s tt)
Sys-step-inv {ch = hs} st | evR ¬s _      = ⊥-elim (¬s tt)
Sys-step-inv {ch = hs} st | evBoth ¬s _ _ = ⊥-elim (¬s tt)
Sys-step-inv {m} {c} {g} {ch = trace} {a} st with Par-ev-elim syncES (λ _ _ → tt) (Conn (cmP m) c) (Gov m g) st
... | evSync _ Pst Qst with Conn-ev-inv Pst | Gov-ev-inv Qst
...   | c′ , eqc , refl | g′ , eqg , refl = c′ , g′ , sync-inv {m} {c} {g} {ch = trace} {a} eqc eqg , refl
Sys-step-inv {ch = trace} st | evL ¬s _      = ⊥-elim (¬s tt)
Sys-step-inv {ch = trace} st | evR ¬s _      = ⊥-elim (¬s tt)
Sys-step-inv {ch = trace} st | evBoth ¬s _ _ = ⊥-elim (¬s tt)
Sys-step-inv {m} {c} {g} {ch = stopped} {a} st with Par-ev-elim syncES (λ _ _ → tt) (Conn (cmP m) c) (Gov m g) st
... | evSync _ Pst Qst with Conn-ev-inv Pst | Gov-ev-inv Qst
...   | c′ , eqc , refl | g′ , eqg , refl = c′ , g′ , sync-inv {m} {c} {g} {ch = stopped} {a} eqc eqg , refl
Sys-step-inv {ch = stopped} st | evL ¬s _      = ⊥-elim (¬s tt)
Sys-step-inv {ch = stopped} st | evR ¬s _      = ⊥-elim (¬s tt)
Sys-step-inv {ch = stopped} st | evBoth ¬s _ _ = ⊥-elim (¬s tt)
Sys-step-inv {m} {c} {g} {ch = rel} {a} st with Par-ev-elim syncES (λ _ _ → tt) (Conn (cmP m) c) (Gov m g) st
... | evSync _ Pst Qst with Conn-ev-inv Pst | Gov-ev-inv Qst
...   | c′ , eqc , refl | g′ , eqg , refl = c′ , g′ , sync-inv {m} {c} {g} {ch = rel} {a} eqc eqg , refl
Sys-step-inv {ch = rel} st | evL ¬s _      = ⊥-elim (¬s tt)
Sys-step-inv {ch = rel} st | evR ¬s _      = ⊥-elim (¬s tt)
Sys-step-inv {ch = rel} st | evBoth ¬s _ _ = ⊥-elim (¬s tt)
Sys-step-inv {m} {c} {g} {ch = conn} st with Par-ev-elim syncES (λ _ _ → tt) (Conn (cmP m) c) (Gov m g) st
... | evSync () _ _
... | evL _ Pst with Conn-ev-inv Pst
...   | c′ , eqc , refl rewrite eqc = c′ , g , refl , refl
Sys-step-inv {ch = conn} st | evR _ Qst with Gov-ev-inv Qst
... | _ , () , _
Sys-step-inv {ch = conn} st | evBoth _ _ Qst with Gov-ev-inv Qst
... | _ , () , _
Sys-step-inv {m} {c} {g} {ch = gov} st with Par-ev-elim syncES (λ _ _ → tt) (Conn (cmP m) c) (Gov m g) st
... | evSync () _ _
... | evR _ Qst with Gov-ev-inv Qst
...   | g′ , eqg , refl rewrite eqg = c , g′ , refl , refl
Sys-step-inv {ch = gov} st | evL _ Pst with Conn-ev-inv Pst
... | _ , () , _
Sys-step-inv {ch = gov} st | evBoth _ Pst _ with Conn-ev-inv Pst
... | _ , () , _

-- a shared-channel sstep move splits into its two side moves
zip-split : ∀ {x : Maybe CState} {y : Maybe GState} {c′ g′}
          → zip x y ≡ just (c′ , g′) → x ≡ just c′ × y ≡ just g′
zip-split {just _} {just _} refl = refl , refl
zip-split {just _} {nothing} ()
zip-split {nothing} ()

-- a solo sstep move comes from its side's move
map-split : ∀ {A B : Set} {f : A → B} {x : Maybe A} {b}
          → map f x ≡ just b → Σ[ a ∈ A ] (x ≡ just a × f a ≡ b)
map-split {x = just a} refl = a , refl , refl

-- an alternative of two Maybe moves succeeds through one of them (fail from running or released)
alt-split : ∀ {A : Set} {x y : Maybe A} {a} → (x <∣> y) ≡ just a → x ≡ just a ⊎ y ≡ just a
alt-split {x = just _}  refl = inj₁ refl
alt-split {x = nothing} eq   = inj₂ eq

-- the CM half of a release is one of its three phase moves on some id, or leaves the live list unchanged (v4.1a spec §3)
rel-split : ∀ {b y is is′} → relLive b y is ≡ just is′
          → (Σ[ k ∈ ℕ ] movePh k hsd released is ≡ just is′) ⊎ (Σ[ k ∈ ℕ ] movePh k running released is ≡ just is′)
          ⊎ (Σ[ k ∈ ℕ ] movePh k failed failedT is ≡ just is′) ⊎ is′ ≡ is
rel-split {y = just (mkInc k hsd _)}     eq = inj₁ (k , eq)
rel-split {y = just (mkInc k running _)} eq = inj₂ (inj₁ (k , eq))
rel-split {y = just (mkInc k failed _)}  eq = inj₂ (inj₂ (inj₁ (k , eq)))
rel-split {true}  {just (mkInc _ closing _)}  refl = inj₂ (inj₂ (inj₂ refl))
rel-split {true}  {just (mkInc _ released _)} refl = inj₂ (inj₂ (inj₂ refl))
rel-split {true}  {just (mkInc _ failedT _)}  refl = inj₂ (inj₂ (inj₂ refl))
rel-split {true}  {nothing}                   refl = inj₂ (inj₂ (inj₂ refl))
rel-split {false} {just (mkInc _ closing _)}  ()
rel-split {false} {just (mkInc _ released _)} ()
rel-split {false} {just (mkInc _ failedT _)}  ()
rel-split {false} {nothing}                   ()

-- every sstep move is a visible composite step
Sys-step-intro : ∀ {m c g c′ g′} (at : AnyTypes Ev) (a : proj₁ at)
               → sstep at a m c g ≡ just (c′ , g′) → SysAt m c g ─[ ev (lbl at a) ]─► SysAt m c′ g′
Sys-step-intro {m} {c} {g} (_ , hs) a eq with zip-split eq
... | eqc , eqg = Par-sync syncES (λ _ _ → tt) (Conn (cmP m) c) (Gov m g) tt (Conn-ev-intro eqc) (Gov-ev-intro eqg)
Sys-step-intro {m} {c} {g} (_ , trace) a eq with zip-split eq
... | eqc , eqg = Par-sync syncES (λ _ _ → tt) (Conn (cmP m) c) (Gov m g) tt (Conn-ev-intro eqc) (Gov-ev-intro eqg)
Sys-step-intro {m} {c} {g} (_ , stopped) a eq with zip-split eq
... | eqc , eqg = Par-sync syncES (λ _ _ → tt) (Conn (cmP m) c) (Gov m g) tt (Conn-ev-intro eqc) (Gov-ev-intro eqg)
Sys-step-intro {m} {c} {g} (_ , rel) a eq with zip-split eq
... | eqc , eqg = Par-sync syncES (λ _ _ → tt) (Conn (cmP m) c) (Gov m g) tt (Conn-ev-intro eqc) (Gov-ev-intro eqg)
Sys-step-intro {m} {c} {g} (_ , conn) a eq with map-split {f = λ c′ → c′ , g} eq
... | _ , eqc , refl = Par-soloL syncES (λ _ _ → tt) (Conn (cmP m) c) (Gov m g) (λ ()) (Conn-ev-intro eqc) refl
Sys-step-intro {m} {c} {g} (_ , gov) a eq with map-split {f = λ g′ → c , g′} eq
... | _ , eqg , refl = Par-soloR syncES (λ _ _ → tt) (Conn (cmP m) c) (Gov m g) (λ ()) (Gov-ev-intro eqg) refl

-- the pure multi-step relation: a run of sstep moves labelled by the trace
data Steps (m : Mode) : CState → GState → List (Event√ U) → CState → GState → Set₁ where
  -- the empty run
  done : ∀ {c g} → Steps m c g [] c g
  -- one sstep move, then the rest
  step : ∀ {c g c₁ g₁ s c′ g′} (at : AnyTypes Ev) (a : proj₁ at)
       → sstep at a m c g ≡ just (c₁ , g₁) → Steps m c₁ g₁ s c′ g′
       → Steps m c g (lbl at a ∷ s) c′ g′

-- every composite run is a Steps run between model states
run-inv : ∀ {m c g s W} → SysAt m c g ⟹⟨ s ⟩ W
        → Σ[ c′ ∈ CState ] Σ[ g′ ∈ GState ] (W ≡ SysAt m c′ g′ × Steps m c g s c′ g′)
run-inv ⟹-refl = _ , _ , refl , done
run-inv (⟹-τ st _) = ⊥-elim (Sys-no-τ st)
run-inv (⟹-ev {e = √ _} st _) = ⊥-elim (Sys-no-√ st)
run-inv (⟹-ev {e = evl (evLabel X ch a)} st rest) with Sys-step-inv st
... | c₁ , g₁ , eq , refl with run-inv rest
...   | c′ , g′ , eqW , ss = c′ , g′ , eqW , step (X , ch) a eq ss

-- every Steps run is a composite run
run-intro : ∀ {m c g s c′ g′} → Steps m c g s c′ g′ → SysAt m c g ⟹⟨ s ⟩ SysAt m c′ g′
run-intro done = ⟹-refl
run-intro (step at a eq ss) = ⟹-ev (Sys-step-intro at a eq) (run-intro ss)

-- model states reachable from the initial state under mode m
Reach : Mode → CState → GState → Set₁
Reach m c g = Σ[ s ∈ List (Event√ U) ] Steps m c₀ g₀ s c g

-- test: the initial handshake is a composite step
t-hs₀ : SysAt AsBuilt c₀ g₀ ─[ ev (HS 0) ]─► SysAt AsBuilt (cst 1 (mkInc 0 hsd false ∷ []) []) (gst nothing (nc 0 ∷ []) idle)
t-hs₀ = Sys-step-intro (ℕ , hs) 0 refl

-- test: inversion shows the initial state refuses `take` (the IG queue is empty)
t-inv : ∀ {W} → SysAt AsBuilt c₀ g₀ ─[ ev (GV take) ]─► W → ⊥
t-inv st with Sys-step-inv st
... | _ , _ , () , _
