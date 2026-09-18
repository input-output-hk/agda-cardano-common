{-# OPTIONS --guardedness #-}

-- UCS chapter 7 §7.2: illustrating THROW.  The THROW HALF (everything BELOW the
-- `--&&&&&&&` separator line) of
--
--   fdr-examples/ucs/chapter07/section7-2.csp   (A.W. Roscoe, July 2010)
--
-- The half above that line (`resettable`, the INTERRUPT operator `/\`) is the
-- sibling module `CSP.Examples.UCS.Ch7.Resettable`.
--
-- Roscoe's point in this half: throw (`[|A|>`, here `_⟦_▷_`) is the only CSP
-- operator that lets a process OFFER an action which would lead to divergence
-- (or to a dead stop) while itself DODGING that fate, because the throw
-- intercepts the action and discards the process that offered it.  The two FDR
-- asserts of the half are exactly the two ways of exploiting that:
--
--   assert RT :[divergence free]                       -- TRUE (§B.1)
--   assert revivable({error},Divide) :[deadlock free]  -- TRUE (§B.2, §B.3)
--
-- Both truth values were re-derived from the definitions here before being
-- proved; both agree with the book.  BOTH ASSERTS ARE PROVED — each on a term
-- with the REAL `_⟦_▷_` at its head, whose fixed-point property w.r.t. the
-- source's recursive equation is certified by a STRONG bisimulation (`∼`).
--
-- §B.1  R = a -> R [] b -> DIV,  RT = R [|{b}|> RT.  `R`'s `b` is caught by the
--       throw, so `b` transfers control to the handler `RT` and DIV is NEVER
--       reached.  The throw node is STABLE (the left operand `R` is stable, and
--       `Θ-τ` over an everywhere-`nothing` τ-part is pointwise `nothing`), so the
--       only loop is the visible `a` — no reachable state has a τ at all.
--
-- §B.2  revivable(E,P) = P [|E|> (revive -> revivable(E,P)); `Divide` ends in
--       `error -> STOP`, which on its own deadlocks.  The throw catches `error`
--       before STOP is entered, `revive` restarts `Divide`, and STOP is therefore
--       UNREACHABLE.  Every reachable state offers a visible event, so `Progress`
--       holds and deadlock-freedom follows.
--
-- ═══════════════════════════════════════════════════════════════════════════════
-- ⚠  PRODUCTIVITY: NEITHER THROW FIXED POINT IS DIRECTLY CONSTRUCTIBLE.
-- ═══════════════════════════════════════════════════════════════════════════════
-- Both of the source's recursions go THROUGH the operator under test, and Agda's
-- `--guardedness` checker rejects every formulation of them.  Measured, not
-- guessed: each of the following was typechecked and each was refused with
-- `[TerminationIssue] Termination checking failed`, naming the corecursive
-- occurrence as the problematic call (all with the model of §A unchanged):
--
--   1.  RT = R ⟦ Bs ▷ RT
--   2.  force RT = force (R ⟦ Bs ▷ RT)
--   3.  RT = R ⟦ Bs ▷ ptree (force RT)
--   4.  force RT = force (R ⟦ Bs ▷ ptree (force RT))
--   5.  RT = R ⟦ Bs ▷ RTh   with   force RTh = force RT
--   6.  RT = R ⟦ Bs ▷ ptree (sil RT)                      (a τ-deviation anyway)
--   7.  RV = Divide ⟦ Es ▷ RVh
--         with force RVh = react (λ where (_ , revive) _ → just RV ; _ _ → nothing) ∅t
--   8.  force RV = force (Divide ⟦ Es ▷ RVh)              (same RVh)
--   9.  RV = Divide ⟦ Es ▷ ptree (react (λ where (_ , revive) _ → just RV
--                                                ; _ _ → nothing) ∅t)
--
-- The reason is structural: guardedness accepts a corecursive occurrence only when
-- it is a DIRECT argument of a CONSTRUCTOR (`react` / `just` / `ptree`) in a clause
-- whose left-hand side is a `force` copattern, and it does not see through an
-- ARGUMENT POSITION OF A DEFINED FUNCTION (the same wall documented in
-- `Ch7/Counter.agda` and `Ch4/ABP.agda`).  `_⟦_▷_` is a defined function, so the
-- handler slot is such a position; candidates 3 and 9 show that re-establishing a
-- constructor INSIDE that slot does not restore guardedness either, and candidates
-- 2/4/5/8 show that a `force` copattern on the recursive definition does not
-- either.  Roscoe's recursions are nevertheless CONSTRUCTIVE in CSP's sense (the
-- handler is reachable only after a visible event), and `revivable`'s `revive ->`
-- guard does not help here because the prefix is itself a defined operator.  Nor
-- can a generic fixed-point combinator rescue this: `force (fix f) = force (f (fix f))`
-- would accept `fix (λ X → X)`, so the obstruction is real, not an artefact of
-- these particular attempts — it is a property of the development, and the same
-- wall has been observed independently for the interrupt operator `_△_`.
--
-- HOW THE ASSERTS ARE STILL OBTAINED.  For each recursion, a WITNESS process is
-- built by inlined `react` copatterns and is then PROVED to solve the source's
-- equation, up to strong bisimulation, against the real operator; the assert is
-- stated on the real throw term.  Inlining is therefore never a substitute for the
-- operator under test — it only supplies the fixed point that `--guardedness`
-- refuses to build, and the equation it must satisfy is discharged, not assumed.
-- (What is NOT proved, in either half, is UNIQUENESS of the solution: that CSP
-- metatheorem — Roscoe's recursions here are constructive, so the fixed point is
-- unique up to ∼ — is quoted, not formalised.)
--
-- WHAT EACH SECTION PROVES — always with the REAL `_⟦_▷_` at the head of the term:
--
--   §B.1  `throw-divFree`  — the SCHEMATIC form: DivergenceFree X ⇒
--         DivergenceFree (R ⟦ {b} ▷ X), for every handler X.  This is the
--         mathematical content of the assert: `b` is intercepted, so DIV is
--         unreachable and the throw itself contributes no τ.
--         `rt-divergence-free` then discharges the assert on `R ⟦ {b} ▷ RTX`,
--         where `RTX` is a CONSTRUCTED SOLUTION of Roscoe's equation, certified by
--         the strong bisimulation `rtx-fixpoint : RTX ∼ (R ⟦ Bs ▷ RTX)`.  So §B.1
--         IS the assert, for a term that provably solves `X = R [|{b}|> X`.
--         `rtn-divergence-free` additionally covers every finite unfolding `RTn n`.
--
--   §B.2  `revivable-progress` / `revivable-deadlockFree` — the SCHEMATIC form:
--         Progress H ⇒ Progress (Divide ⟦ {error} ▷ H), for every handler H.  This
--         is the mathematical content of the second assert: the reachable-state
--         family `VState` has NO `Stop ⟦ Es ▷ H` member, because `error ∈ {error}`
--         is caught before STOP is entered (the `Θpass` case at `Derr` is refuted
--         by `Derr-ev-error`).  `rvn-deadlock-free` discharges it for every finite
--         approximation `RVn n` (n revivals deep, with the real `revive ->`
--         handler), independently of any fixed point.
--
--   §B.3  the ω-LIMIT, i.e. the assert itself.  `V` / `Vh` is the five-state
--         witness (the divider's four positions plus the handler);
--         `V-fixpoint : V dD ∼ (Divide ⟦ Es ▷ (revive ⟶₀ V dD))` and
--         `Vh-fixpoint : Vh ∼ (revive ⟶₀ V dD)` certify that it solves Roscoe's
--         `revivable(E,P) = P [|E|> (revive -> revivable(E,P))` at E = {error},
--         P = Divide — as a STRONG bisimulation, the same strength as
--         `rtx-fixpoint` in §B.1.  `revivable-deadlock-free` then states the
--         assert on `Divide ⟦ Es ▷ (revive ⟶₀ V dD)`: the real throw, the real
--         `revive ->` handler.  `divide-has-deadlock` certifies non-vacuity — the
--         UNPROTECTED divider does reach the stuck STOP along <num.0, den.0,
--         error>.
--
-- `CSP.Laws.DivFree.Closure` carries no `τ-Acc` closure for `_⟦_▷_`; the fact
-- needed here (a stable left operand makes the throw node stable) is proved
-- locally as `throw-stable` / `VState-stable` / `VR-stable` rather than in that
-- shared module.  The step inversions and introductions for the throw are REUSED
-- from `CSP.Laws.Traces.TraceLawsThrowInterrupt` (`Θ-ev-elim`, `Θ-throw-step`,
-- `Θ-pass-step`), not re-derived here.

module CSP.Examples.UCS.Ch7.Throw where

open import Level using (Lift; lift) renaming (zero to lzero)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using ()
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc; _/_)
open import Data.Nat.Properties using () renaming (_≟_ to _ℕ≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees
open PTree

------------------------------------------------------------------------------------
-- §A. The model.
------------------------------------------------------------------------------------

-- The data domain of the divider.  MODEL REDUCTION: the source declares
-- `channel num,den,res:{0..10}`; the INPUT domain is reduced to `Fin 3` = {0,1,2}
-- (the campaign's usual small-domain reduction), while `res` carries a plain `ℕ`.
-- Both parts of the reduction are behaviour-preserving for DEADLOCK-FREEDOM: the
-- proof below is PARAMETRIC in the two inputs (it never enumerates them), so the
-- size of the input domain is irrelevant, and dropping the upper bound on `res`
-- only removes the arithmetic side-obligation `x/y ≤ 10` — which carries no CSP
-- content — while KEEPING the two things the assert actually depends on: the
-- `y > 0` guard, and a GENUINE quotient `x / y` on the `res` channel.
Val : Set
Val = Fin 3

-- The channels of the throw half: `a`,`b` for R/RT; `num`,`den`,`res`,`error` for
-- Divide; `revive` for the reviving handler.  (`c` and `lightning` belong to the
-- interrupt half and are declared by the sibling module.)
data TEv : Set → Set where
  a b          : TEv ⊤          -- R's two events; `b` is the one the throw catches
  num den      : TEv Val        -- the divider's two inputs
  res          : TEv ℕ          -- the quotient output
  error        : TEv ⊤          -- the divide-by-zero run-time error
  revive       : TEv ⊤          -- the handler's restart event

-- Decidable equality on the event indices, as every CSP operator module needs.
TEv-≟ : (x y : AnyTypes TEv) → Dec (x ≡ y)
TEv-≟ (_ , a     ) (_ , a     ) = yes refl
TEv-≟ (_ , b     ) (_ , b     ) = yes refl
TEv-≟ (_ , num   ) (_ , num   ) = yes refl
TEv-≟ (_ , den   ) (_ , den   ) = yes refl
TEv-≟ (_ , res   ) (_ , res   ) = yes refl
TEv-≟ (_ , error ) (_ , error ) = yes refl
TEv-≟ (_ , revive) (_ , revive) = yes refl
TEv-≟ (_ , a     ) (_ , b     ) = no (λ ())
TEv-≟ (_ , a     ) (_ , num   ) = no (λ ())
TEv-≟ (_ , a     ) (_ , den   ) = no (λ ())
TEv-≟ (_ , a     ) (_ , res   ) = no (λ ())
TEv-≟ (_ , a     ) (_ , error ) = no (λ ())
TEv-≟ (_ , a     ) (_ , revive) = no (λ ())
TEv-≟ (_ , b     ) (_ , a     ) = no (λ ())
TEv-≟ (_ , b     ) (_ , num   ) = no (λ ())
TEv-≟ (_ , b     ) (_ , den   ) = no (λ ())
TEv-≟ (_ , b     ) (_ , res   ) = no (λ ())
TEv-≟ (_ , b     ) (_ , error ) = no (λ ())
TEv-≟ (_ , b     ) (_ , revive) = no (λ ())
TEv-≟ (_ , num   ) (_ , a     ) = no (λ ())
TEv-≟ (_ , num   ) (_ , b     ) = no (λ ())
TEv-≟ (_ , num   ) (_ , den   ) = no (λ ())
TEv-≟ (_ , num   ) (_ , res   ) = no (λ ())
TEv-≟ (_ , num   ) (_ , error ) = no (λ ())
TEv-≟ (_ , num   ) (_ , revive) = no (λ ())
TEv-≟ (_ , den   ) (_ , a     ) = no (λ ())
TEv-≟ (_ , den   ) (_ , b     ) = no (λ ())
TEv-≟ (_ , den   ) (_ , num   ) = no (λ ())
TEv-≟ (_ , den   ) (_ , res   ) = no (λ ())
TEv-≟ (_ , den   ) (_ , error ) = no (λ ())
TEv-≟ (_ , den   ) (_ , revive) = no (λ ())
TEv-≟ (_ , res   ) (_ , a     ) = no (λ ())
TEv-≟ (_ , res   ) (_ , b     ) = no (λ ())
TEv-≟ (_ , res   ) (_ , num   ) = no (λ ())
TEv-≟ (_ , res   ) (_ , den   ) = no (λ ())
TEv-≟ (_ , res   ) (_ , error ) = no (λ ())
TEv-≟ (_ , res   ) (_ , revive) = no (λ ())
TEv-≟ (_ , error ) (_ , a     ) = no (λ ())
TEv-≟ (_ , error ) (_ , b     ) = no (λ ())
TEv-≟ (_ , error ) (_ , num   ) = no (λ ())
TEv-≟ (_ , error ) (_ , den   ) = no (λ ())
TEv-≟ (_ , error ) (_ , res   ) = no (λ ())
TEv-≟ (_ , error ) (_ , revive) = no (λ ())
TEv-≟ (_ , revive) (_ , a     ) = no (λ ())
TEv-≟ (_ , revive) (_ , b     ) = no (λ ())
TEv-≟ (_ , revive) (_ , num   ) = no (λ ())
TEv-≟ (_ , revive) (_ , den   ) = no (λ ())
TEv-≟ (_ , revive) (_ , res   ) = no (λ ())
TEv-≟ (_ , revive) (_ , error ) = no (λ ())

open import CSP.Operators TEv-≟
open EventSet

-- The process type of this example: no data is returned, so R = ⊤.
TProc : Set₁
TProc = PTree TEv (ExtI TEv) (⊤poly {lzero})

------------------------------------------------------------------------------------
-- §A.1  Part 1 — R, DIV, and the throw's fixed-point witness / approximants.
------------------------------------------------------------------------------------

-- DIV = DIV |~| DIV: the τ-loop through INTERNAL CHOICE that the source declares.
-- This is neither the built-in `div` node (whose loop is a `sil` chain) nor the
-- hidden-event loop `AS ∖ {a}` used in `Ch6/FailDiv.agda`: it is a `react` node with
-- an empty visible part and TWO τ-branches (tags 0 and 1 of `br2`), both back to
-- DIV — i.e. POINTWISE equal to `force (DIV ⊓ DIV)` with `br2 DIV DIV` spelled out,
-- which is what lets the corecursive occurrence sit under `just` (the `_⊓_`
-- operator would wrap it in a function application and lose guardedness).
DIV : TProc
force DIV = react ∅v (λ where (_ , fin)      (lift fzero)        → just DIV
                              (_ , fin)      (lift (fsuc fzero)) → just DIV
                              (_ , fin)      _                   → nothing
                              (_ , base _)   _                   → nothing
                              (_ , pair _ _) _                   → nothing)

-- R = a -> R [] b -> DIV, as the single stable `react` node the external choice of
-- two prefixes on DISTINCT events denotes (again inlined so that both corecursive
-- targets sit directly under `just`).  R is NOT the operator under test.
R : TProc
force R = react (λ where (_ , a) _ → just R
                         (_ , b) _ → just DIV
                         _       _ → nothing) ∅t

-- The throw set {b}: membership predicate …
isB : AnyTypes TEv → Set
isB (_ , a     ) = ⊥
isB (_ , b     ) = ⊤
isB (_ , num   ) = ⊥
isB (_ , den   ) = ⊥
isB (_ , res   ) = ⊥
isB (_ , error ) = ⊥
isB (_ , revive) = ⊥

isB? : (at : AnyTypes TEv) → Dec (isB at)
isB? (_ , a     ) = no (λ z → z)
isB? (_ , b     ) = yes tt
isB? (_ , num   ) = no (λ z → z)
isB? (_ , den   ) = no (λ z → z)
isB? (_ , res   ) = no (λ z → z)
isB? (_ , error ) = no (λ z → z)
isB? (_ , revive) = no (λ z → z)

-- … and the event set itself (channel-level: the decision ignores the value).
Bs : EventSet
Bs = chanSet isB isB?

-- ⚠  RT = R [|{b}|> RT IS NOT CONSTRUCTIBLE (see the header): the corecursive
-- occurrence would sit in an ARGUMENT of the defined function `_⟦_▷_`, which
-- Agda's guardedness checker never accepts.  What is built instead:
--
--   * `RTX`  — a one-state SOLUTION of Roscoe's equation, certified by
--              `rtx-fixpoint : RTX ∼ (R ⟦ Bs ▷ RTX)` (§B.1); the assert is proved
--              for `R ⟦ Bs ▷ RTX`, i.e. WITH THE REAL THROW AT THE TOP;
--   * `RTn n` — the ω-approximants of RT (the throw nested n deep), all with the
--              real operator, proved divergence-free for EVERY n (§B.1).

-- The one-state solution of X = R [|{b}|> X: after `a` the state is unchanged, and
-- after the CAUGHT `b` control returns to the same state.  Written as a raw `react`
-- copattern — legitimate here because it is not offered as the port of the assert
-- but as a WITNESS whose fixed-point property is proved (`rtx-fixpoint`) against
-- the real operator.
RTX : TProc
force RTX = react (λ where (_ , a) _ → just RTX
                           (_ , b) _ → just RTX
                           _       _ → nothing) ∅t

-- STOP at this example's process type (the innermost handler of the approximants).
STOP : TProc
STOP = Stop

-- The ω-approximants of RT: `RTn (suc n) = R [|{b}|> RTn n`, `RTn 0 = STOP`.
-- Structurally recursive on `n`, hence productive, and the throw is the REAL one.
RTn : ℕ → TProc
RTn zero    = STOP
RTn (suc n) = R ⟦ Bs ▷ RTn n

------------------------------------------------------------------------------------
-- §A.2  Part 2 — the divider and the reviving throw.
------------------------------------------------------------------------------------

-- error -> STOP, the run-time-error branch of Divide (no recursion, so the real
-- prefix operator can be used).
Derr : TProc
Derr = error ⟶₀ Stop

-- Divide = num?x -> den?y -> if y>0 then res!(x/y) -> Divide else error -> STOP,
-- as three inlined `react` copatterns (forward-declared: `Dres`'s continuation is
-- the corecursive `Divide`).  `Dnum x` is the state after `num?x`, `Dres q` the
-- state offering the pinned output `res!q`.
Divide   : TProc
Dnum     : Val → TProc
Dres     : ℕ → TProc
resOffer : ℕ → (at : AnyTypes TEv) → ContinueType at (Maybe TProc)
fire     : {A : Set} → Dec A → Maybe TProc

force Divide = react (λ where (_ , num) x → just (Dnum x)
                              _         _ → nothing) ∅t

-- after num?x: read den?y; y = 0 fails the `y>0` guard and raises `error`,
-- y = suc y′ produces the genuine quotient x / y.
force (Dnum x) = react (λ where (_ , den) fzero     → just Derr
                                (_ , den) (fsuc y′) → just (Dres (toℕ x / suc (toℕ y′)))
                                _         _         → nothing) ∅t

force (Dres q) = react (resOffer q) ∅t

-- res!q: the offer FIRES ONLY at the computed quotient `q` (a pinned output — an
-- unpinned `res?w` would over-approximate the model and weaken the assert).  The
-- comparison is handed to `fire` rather than matched by a `with`, so that both
-- directions of the pinning (`res-diag`, `fire-inv`) are one-line pattern matches.
resOffer q (_ , res) w = fire (w ℕ≟ q)
resOffer q _         _ = nothing

-- the pinned continuation fires exactly when the offered value IS the quotient
fire (yes _) = just Divide
fire (no  _) = nothing

-- The throw set {error}: membership predicate …
isE : AnyTypes TEv → Set
isE (_ , a     ) = ⊥
isE (_ , b     ) = ⊥
isE (_ , num   ) = ⊥
isE (_ , den   ) = ⊥
isE (_ , res   ) = ⊥
isE (_ , error ) = ⊤
isE (_ , revive) = ⊥

isE? : (at : AnyTypes TEv) → Dec (isE at)
isE? (_ , a     ) = no (λ z → z)
isE? (_ , b     ) = no (λ z → z)
isE? (_ , num   ) = no (λ z → z)
isE? (_ , den   ) = no (λ z → z)
isE? (_ , res   ) = no (λ z → z)
isE? (_ , error ) = yes tt
isE? (_ , revive) = no (λ z → z)

-- … and the event set itself.
Es : EventSet
Es = chanSet isE isE?

-- ⚠  revivable({error},Divide) = Divide [|{error}|> (revive -> revivable(…)) IS
-- LIKEWISE NOT CONSTRUCTIBLE (see the header): the `revive ->` prefix guards the
-- recursion in CSP's sense, but the corecursive occurrence still ends up inside an
-- ARGUMENT of `_⟦_▷_`, and Agda's guardedness does not see through a defined
-- function.  Two things are built instead: here, the ω-APPROXIMANT family —
-- `RVn (suc n)` is the REAL throw with the REAL `revive ->` handler and allows n
-- further revivals, the innermost handler being the chaotic `Run` (which offers
-- everything, so it cannot itself deadlock and does not mask the property under
-- test) — and, in §B.3, the ω-LIMIT itself, as a five-state witness whose solution
-- of Roscoe's equation is certified by a strong bisimulation.
RVn : ℕ → TProc
RVn zero    = Run
RVn (suc n) = Divide ⟦ Es ▷ (revive ⟶₀ RVn n)

------------------------------------------------------------------------------------
-- §B. The proofs.
------------------------------------------------------------------------------------

open import Semantics.LTS            {E = TEv} {I = ExtI TEv} hiding (Diverges)
open import Semantics.Deadlock       {E = TEv} {I = ExtI TEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev; DeadlockFree)
open import Semantics.DivergenceFree {E = TEv} {I = ExtI TEv}
  using (DivergenceFree; Diverges; stable-no-τ; stable→¬div)
open import Semantics.DeadlockDR     {E = TEv} {I = ExtI TEv}
  using (Progress; progress⇒deadlockFree)
open import Semantics.Bisim          {E = TEv} {I = ExtI TEv}
  using (_∼_; Sbisim; SSimF; sbisim-refl)

------------------------------------------------------------------------------------
-- §B.0  Non-vacuity: the divergence the throw dodges is a REAL one.
------------------------------------------------------------------------------------

-- DIV diverges: τ-branch 0 of the internal choice leads straight back to DIV.
DIV-diverges : Diverges DIV
DIV-diverges .Diverges.next = DIV
DIV-diverges .Diverges.step = sTau {i = _ , fin {n = 2}} {a = lift fzero} refl refl
DIV-diverges .Diverges.rest = DIV-diverges

-- … and R really does offer `b` into it: R ─b─► DIV.
R-b-into-DIV : R ─[ ev (evl (evLabel ⊤ b tt)) ]─► DIV
R-b-into-DIV = sVis refl refl

------------------------------------------------------------------------------------
-- §B.1  assert RT :[divergence free]  —  TRUE.
------------------------------------------------------------------------------------

-- The throw node `R ⟦ {b} ▷ X` is STABLE for EVERY handler X: R's τ-part is `∅t`,
-- and `Θ-τ` over an everywhere-`nothing` τ-part is pointwise `nothing`.  (This is
-- the local `τ-Acc`-style closure fact for `_⟦_▷_` that `CSP.Laws.DivFree.Closure`
-- does not yet carry; it is proved here rather than in that shared module.)
throw-stable : ∀ {X : TProc} → isStable (R ⟦ Bs ▷ X)
throw-stable _ _ = refl

-- Every visible step of `R ⟦ {b} ▷ X` either stays put (the `a`-loop, since
-- a ∉ {b}) or is the CAUGHT `b`, which hands control to the handler X.  There is NO
-- transition into DIV: that is the whole point of the assert.
throw-ev : ∀ {X : TProc} {e t′} → (R ⟦ Bs ▷ X) ─[ ev (evl e) ]─► t′
         → (t′ ≡ (R ⟦ Bs ▷ X)) ⊎ (t′ ≡ X)
throw-ev (sVis {at = _ , a     } refl br) = inj₁ (sym (just-injective br))
throw-ev (sVis {at = _ , b     } refl br) = inj₂ (sym (just-injective br))
throw-ev (sVis {at = _ , num   } refl br) = case br of λ ()
throw-ev (sVis {at = _ , den   } refl br) = case br of λ ()
throw-ev (sVis {at = _ , res   } refl br) = case br of λ ()
throw-ev (sVis {at = _ , error } refl br) = case br of λ ()
throw-ev (sVis {at = _ , revive} refl br) = case br of λ ()

-- SCHEMATIC FORM OF THE ASSERT: divergence-freedom of the throw reduces ENTIRELY to
-- divergence-freedom of the HANDLER.  `b` is intercepted, so DIV is unreachable and
-- the throw contributes no divergence of its own (its node is stable).
throw-divFree : ∀ {X : TProc} → DivergenceFree X → DivergenceFree (R ⟦ Bs ▷ X)
throw-divFree {X} dfX = go
  where
    go : ∀ {s t′} → (R ⟦ Bs ▷ X) ⟹∖√⟨ s ⟩ t′ → ¬ Diverges t′
    go ∖√-refl          = stable→¬div (throw-stable {X})
    go (∖√-τ  st _)     = ⊥-elim (stable-no-τ (throw-stable {X}) st)
    go (∖√-ev st rest) with throw-ev st
    ... | inj₁ refl = go rest
    ... | inj₂ refl = dfX rest

-- STOP is stable …
STOP-stable : isStable STOP
STOP-stable _ _ = refl

-- … it offers nothing, so the only state it reaches is itself …
STOP-reach : ∀ {s t′} → STOP ⟹∖√⟨ s ⟩ t′ → t′ ≡ STOP
STOP-reach ∖√-refl                  = refl
STOP-reach (∖√-τ  st _)             = ⊥-elim (stable-no-τ STOP-stable st)
STOP-reach (∖√-ev (sVis refl br) _) = case br of λ ()

-- … and so it is (vacuously) divergence free: the innermost handler of the
-- approximants contributes no divergence.
STOP-divFree : DivergenceFree STOP
STOP-divFree reach rewrite STOP-reach reach = stable→¬div STOP-stable

-- RTX is stable (a pure visible menu {a,b}) …
RTX-stable : isStable RTX
RTX-stable _ _ = refl

-- … both of its events return to RTX …
RTX-ev : ∀ {e t′} → RTX ─[ ev (evl e) ]─► t′ → t′ ≡ RTX
RTX-ev (sVis {at = _ , a     } refl br) = sym (just-injective br)
RTX-ev (sVis {at = _ , b     } refl br) = sym (just-injective br)
RTX-ev (sVis {at = _ , num   } refl br) = case br of λ ()
RTX-ev (sVis {at = _ , den   } refl br) = case br of λ ()
RTX-ev (sVis {at = _ , res   } refl br) = case br of λ ()
RTX-ev (sVis {at = _ , error } refl br) = case br of λ ()
RTX-ev (sVis {at = _ , revive} refl br) = case br of λ ()

-- … so every √-free-reachable state of RTX is RTX …
RTX-reach : ∀ {s t′} → RTX ⟹∖√⟨ s ⟩ t′ → t′ ≡ RTX
RTX-reach ∖√-refl         = refl
RTX-reach (∖√-τ  st _)    = ⊥-elim (stable-no-τ RTX-stable st)
RTX-reach (∖√-ev st rest) with RTX-ev st
... | refl = RTX-reach rest

-- … and RTX is divergence free.
RTX-divFree : DivergenceFree RTX
RTX-divFree reach rewrite RTX-reach reach = stable→¬div RTX-stable

-- RTX SOLVES Roscoe's equation X = R [|{b}|> X, up to STRONG bisimulation: both
-- sides are stable react nodes offering exactly {a,b}; on `a` the throw stays put
-- while RTX loops (residual: the same pair again), and on the CAUGHT `b` both land
-- on RTX.  This is what makes the theorem below a statement about RT and not about
-- some unrelated process: `R ⟦ Bs ▷ RTX` is a fixed point of the source equation.
rtx-fwd      : SSimF (Sbisim (⊤poly {lzero})) RTX (R ⟦ Bs ▷ RTX)
rtx-bwd      : SSimF (Sbisim (⊤poly {lzero})) (R ⟦ Bs ▷ RTX) RTX
rtx-fixpoint : RTX ∼ (R ⟦ Bs ▷ RTX)
rtx-fixpoint⁻ : (R ⟦ Bs ▷ RTX) ∼ RTX

rtx-fixpoint  .Sbisim.fwd = rtx-fwd
rtx-fixpoint  .Sbisim.bwd = rtx-bwd
rtx-fixpoint⁻ .Sbisim.fwd = rtx-bwd
rtx-fixpoint⁻ .Sbisim.bwd = rtx-fwd

rtx-fwd .SSimF.on-ev (sRet eq)                          = case eq of λ ()
rtx-fwd .SSimF.on-ev (sVis {at = _ , a     } refl refl) = _ , sVis refl refl , rtx-fixpoint
rtx-fwd .SSimF.on-ev (sVis {at = _ , b     } refl refl) = _ , sVis refl refl , sbisim-refl _
rtx-fwd .SSimF.on-ev (sVis {at = _ , num   } refl br)   = case br of λ ()
rtx-fwd .SSimF.on-ev (sVis {at = _ , den   } refl br)   = case br of λ ()
rtx-fwd .SSimF.on-ev (sVis {at = _ , res   } refl br)   = case br of λ ()
rtx-fwd .SSimF.on-ev (sVis {at = _ , error } refl br)   = case br of λ ()
rtx-fwd .SSimF.on-ev (sVis {at = _ , revive} refl br)   = case br of λ ()
rtx-fwd .SSimF.on-tau (sSil eq)                         = case eq of λ ()
rtx-fwd .SSimF.on-tau (sTau refl br)                    = case br of λ ()

rtx-bwd .SSimF.on-ev (sRet eq)                          = case eq of λ ()
rtx-bwd .SSimF.on-ev (sVis {at = _ , a     } refl refl) = _ , sVis refl refl , rtx-fixpoint⁻
rtx-bwd .SSimF.on-ev (sVis {at = _ , b     } refl refl) = _ , sVis refl refl , sbisim-refl _
rtx-bwd .SSimF.on-ev (sVis {at = _ , num   } refl br)   = case br of λ ()
rtx-bwd .SSimF.on-ev (sVis {at = _ , den   } refl br)   = case br of λ ()
rtx-bwd .SSimF.on-ev (sVis {at = _ , res   } refl br)   = case br of λ ()
rtx-bwd .SSimF.on-ev (sVis {at = _ , error } refl br)   = case br of λ ()
rtx-bwd .SSimF.on-ev (sVis {at = _ , revive} refl br)   = case br of λ ()
rtx-bwd .SSimF.on-tau (sSil eq)                         = case eq of λ ()
rtx-bwd .SSimF.on-tau (sTau refl br)                    = case br of λ ()

-- ★ assert RT :[divergence free]  —  TRUE.  The REAL throw operator heads the term,
-- and its handler `RTX` is a certified solution of the source's equation
-- (`rtx-fixpoint`), so `R ⟦ Bs ▷ RTX` IS Roscoe's RT.  `b` never reaches DIV.
rt-divergence-free : DivergenceFree (R ⟦ Bs ▷ RTX)
rt-divergence-free = throw-divFree RTX-divFree

-- … and, independently of the fixed-point witness, EVERY finite unfolding of RT is
-- divergence free (the ω-approximants).
rtn-divergence-free : ∀ n → DivergenceFree (RTn n)
rtn-divergence-free zero    = STOP-divFree
rtn-divergence-free (suc n) = throw-divFree (rtn-divergence-free n)

------------------------------------------------------------------------------------
-- §B.2  assert revivable({error},Divide) :[deadlock free]  —  TRUE.
------------------------------------------------------------------------------------

open import Semantics.Deadlock {E = TEv} {I = ExtI TEv} using (IsStuck; HasDeadlock)
open import CSP.Laws.Traces.TraceLawsThrowInterrupt TEv-≟
  using (ΘevR; Θthrow; Θpass; Θdone; Θ-ev-elim; Θ-throw-step; Θ-pass-step)

-- STOP is stuck: it has no move at all …
STOP-stuck : IsStuck STOP
STOP-stuck (sRet eq)      = case eq of λ ()
STOP-stuck (sSil eq)      = case eq of λ ()
STOP-stuck (sVis refl br) = case br of λ ()
STOP-stuck (sTau refl br) = case br of λ ()

-- … and the UNPROTECTED divider really reaches it, along <num.0, den.0, error>:
-- `error -> STOP` is a genuine deadlock, which is exactly what the throw prevents
-- (so the assert below is not vacuous).
divide-has-deadlock : HasDeadlock Divide
divide-has-deadlock
  = _ , STOP
  , ∖√-ev (sVis {at = _ , num  } {a = fzero} refl refl)
     (∖√-ev (sVis {at = _ , den  } {a = fzero} refl refl)
       (∖√-ev (sVis {at = _ , error} {a = tt   } refl refl) ∖√-refl))
  , STOP-stuck

-- The pinned `res!q` offer fires at exactly the quotient q …
res-diag : ∀ (q : ℕ) → fire (q ℕ≟ q) ≡ just Divide
res-diag q with q ℕ≟ q
... | yes _  = refl
... | no  ¬p = ⊥-elim (¬p refl)

-- … and whatever value does fire it, the continuation is `Divide`.
fire-inv : ∀ {A : Set} {d : Dec A} {t′ : TProc} → fire d ≡ just t′ → t′ ≡ Divide
fire-inv {d = yes _} refl = refl
fire-inv {d = no  _} eq   = case eq of λ ()

-- Step inversions for the four divider states: each is a stable single-channel menu.
Divide-ev : ∀ {e t′} → Divide ─[ ev (evl e) ]─► t′ → Σ[ x ∈ Val ] (t′ ≡ Dnum x)
Divide-ev (sVis {at = _ , num   } {a = x} refl br) = x , sym (just-injective br)
Divide-ev (sVis {at = _ , a     } refl br) = case br of λ ()
Divide-ev (sVis {at = _ , b     } refl br) = case br of λ ()
Divide-ev (sVis {at = _ , den   } refl br) = case br of λ ()
Divide-ev (sVis {at = _ , res   } refl br) = case br of λ ()
Divide-ev (sVis {at = _ , error } refl br) = case br of λ ()
Divide-ev (sVis {at = _ , revive} refl br) = case br of λ ()

-- after num?x: `den.0` fails the guard (→ Derr), `den.(suc y′)` divides (→ Dres q)
Dnum-ev : ∀ {x e t′} → Dnum x ─[ ev (evl e) ]─► t′
        → (t′ ≡ Derr) ⊎ (Σ[ q ∈ ℕ ] (t′ ≡ Dres q))
Dnum-ev (sVis {at = _ , den} {a = fzero}   refl br) = inj₁ (sym (just-injective br))
Dnum-ev {x = x} (sVis {at = _ , den} {a = fsuc y′} refl br) =
  inj₂ (toℕ x / suc (toℕ y′) , sym (just-injective br))
Dnum-ev (sVis {at = _ , a     } refl br) = case br of λ ()
Dnum-ev (sVis {at = _ , b     } refl br) = case br of λ ()
Dnum-ev (sVis {at = _ , num   } refl br) = case br of λ ()
Dnum-ev (sVis {at = _ , res   } refl br) = case br of λ ()
Dnum-ev (sVis {at = _ , error } refl br) = case br of λ ()
Dnum-ev (sVis {at = _ , revive} refl br) = case br of λ ()

-- Derr offers ONLY `error`, and `error` IS in the throw set — this is the step the
-- throw intercepts, so STOP is never entered.
Derr-ev-error : ∀ {A} {e : TEv A} {x : A} {t′} → Derr ─[ ev (evl (evLabel A e x)) ]─► t′
              → isE (A , e)
Derr-ev-error {e = error } (sVis refl br) = tt
Derr-ev-error {e = a     } (sVis refl br) = case br of λ ()
Derr-ev-error {e = b     } (sVis refl br) = case br of λ ()
Derr-ev-error {e = num   } (sVis refl br) = case br of λ ()
Derr-ev-error {e = den   } (sVis refl br) = case br of λ ()
Derr-ev-error {e = res   } (sVis refl br) = case br of λ ()
Derr-ev-error {e = revive} (sVis refl br) = case br of λ ()

-- the pinned output returns control to Divide
Dres-ev : ∀ {q e t′} → Dres q ─[ ev (evl e) ]─► t′ → t′ ≡ Divide
Dres-ev (sVis {at = _ , res   } refl br) = fire-inv br
Dres-ev (sVis {at = _ , a     } refl br) = case br of λ ()
Dres-ev (sVis {at = _ , b     } refl br) = case br of λ ()
Dres-ev (sVis {at = _ , num   } refl br) = case br of λ ()
Dres-ev (sVis {at = _ , den   } refl br) = case br of λ ()
Dres-ev (sVis {at = _ , error } refl br) = case br of λ ()
Dres-ev (sVis {at = _ , revive} refl br) = case br of λ ()

-- The reachable states of the throw-protected divider, for an arbitrary handler H.
-- `Stop ⟦ Es ▷ H` is ABSENT — that is the content of the assert.
data VState (H : TProc) : TProc → Set₁ where
  atD : VState H (Divide ⟦ Es ▷ H)
  atN : (x : Val) → VState H (Dnum x ⟦ Es ▷ H)
  atE : VState H (Derr ⟦ Es ▷ H)
  atR : (q : ℕ) → VState H (Dres q ⟦ Es ▷ H)

-- Every such state is STABLE: each divider state is a stable pure-visible react
-- node, and `Θ-τ` over an everywhere-`nothing` τ-part is pointwise `nothing`.
VState-stable : ∀ {H t} → VState H t → isStable t
VState-stable atD     _ _ = refl
VState-stable (atN x) _ _ = refl
VState-stable atE     _ _ = refl
VState-stable (atR q) _ _ = refl

-- … hence none of them can do a τ.
VState-noτ : ∀ {H t t′} → VState H t → t ─[ τ ]─► t′ → ⊥
VState-noτ v st = stable-no-τ (VState-stable v) st

-- Every state has an enabled visible move: read a numerator / read a denominator /
-- raise the caught `error` / emit the pinned quotient.
VState-enabled : ∀ {H t} → VState H t
               → Σ[ l ∈ Label (⊤poly {lzero}) ] Σ[ t″ ∈ TProc ] (t ─[ l ]─► t″)
VState-enabled atD     = _ , _ , Θ-pass-step  (sVis {at = _ , num  } {a = fzero} refl refl) (λ z → z)
VState-enabled (atN x) = _ , _ , Θ-pass-step  (sVis {at = _ , den  } {a = fzero} refl refl) (λ z → z)
VState-enabled atE     = _ , _ , Θ-throw-step (sVis {at = _ , error} {a = tt   } refl refl) tt
VState-enabled (atR q) = _ , _ , Θ-pass-step  (sVis {at = _ , res  } {a = q} refl (res-diag q)) (λ z → z)

-- A visible step out of a reachable state either lands on another reachable state
-- or is the CAUGHT `error`, which hands control to the handler H.  The `Θpass` case
-- at `Derr` is refuted by `Derr-ev-error`: `error ∈ {error}`, so `Stop ⟦ Es ▷ H`
-- is unreachable.
VState-step : ∀ {H t t′ e} → VState H t → t ─[ ev (evl e) ]─► t′
            → VState H t′ ⊎ (t′ ≡ H)
VState-step {H} atD st with Θ-ev-elim Divide H st
... | Θthrow _ _        = inj₂ refl
... | Θpass  pstep _ with Divide-ev pstep
...   | x , refl        = inj₁ (atN x)
VState-step {H} (atN x) st with Θ-ev-elim (Dnum x) H st
... | Θthrow _ _        = inj₂ refl
... | Θpass  pstep _ with Dnum-ev pstep
...   | inj₁ refl       = inj₁ atE
...   | inj₂ (q , refl) = inj₁ (atR q)
VState-step {H} atE st with Θ-ev-elim Derr H st
... | Θthrow _ _        = inj₂ refl
... | Θpass  pstep ¬m   = ⊥-elim (¬m (Derr-ev-error pstep))
VState-step {H} (atR q) st with Θ-ev-elim (Dres q) H st
... | Θthrow _ _        = inj₂ refl
... | Θpass  pstep _ with Dres-ev pstep
...   | refl            = inj₁ atD

-- SCHEMATIC FORM OF THE ASSERT: the throw-protected divider makes progress
-- whenever its HANDLER does — `error` is intercepted before STOP is entered.
revivable-progress : ∀ {H : TProc} → Progress H → Progress (Divide ⟦ Es ▷ H)
revivable-progress {H} progH = go atD
  where
    go : ∀ {t s t′} → VState H t → t ⟹∖√⟨ s ⟩ t′
       → Σ[ l ∈ Label (⊤poly {lzero}) ] Σ[ t″ ∈ TProc ] (t′ ─[ l ]─► t″)
    go v ∖√-refl        = VState-enabled v
    go v (∖√-τ  st _)   = ⊥-elim (VState-noτ v st)
    go v (∖√-ev st rest) with VState-step v st
    ... | inj₁ v′   = go v′ rest
    ... | inj₂ refl = progH rest

-- … and therefore it is deadlock free whenever its handler makes progress.
revivable-deadlockFree : ∀ {H : TProc} → Progress H → DeadlockFree (Divide ⟦ Es ▷ H)
revivable-deadlockFree progH = progress⇒deadlockFree (revivable-progress progH)

-- The `revive ->` handler: it is stable, offers `revive`, and after it control is
-- inside H, so Progress lifts through the prefix.
revPre-stable : ∀ {H : TProc} → isStable (revive ⟶₀ H)
revPre-stable _ _ = refl

revPre-ev : ∀ {H : TProc} {e t′} → (revive ⟶₀ H) ─[ ev (evl e) ]─► t′ → t′ ≡ H
revPre-ev (sVis {at = _ , revive} refl br) = sym (just-injective br)
revPre-ev (sVis {at = _ , a     } refl br) = case br of λ ()
revPre-ev (sVis {at = _ , b     } refl br) = case br of λ ()
revPre-ev (sVis {at = _ , num   } refl br) = case br of λ ()
revPre-ev (sVis {at = _ , den   } refl br) = case br of λ ()
revPre-ev (sVis {at = _ , res   } refl br) = case br of λ ()
revPre-ev (sVis {at = _ , error } refl br) = case br of λ ()

prefix-progress : ∀ {H : TProc} → Progress H → Progress (revive ⟶₀ H)
prefix-progress {H} progH = go
  where
    go : ∀ {s t′} → (revive ⟶₀ H) ⟹∖√⟨ s ⟩ t′
       → Σ[ l ∈ Label (⊤poly {lzero}) ] Σ[ t″ ∈ TProc ] (t′ ─[ l ]─► t″)
    go ∖√-refl        = _ , _ , sVis {at = _ , revive} {a = tt} refl refl
    go (∖√-τ  st _)   = ⊥-elim (stable-no-τ (revPre-stable {H}) st)
    go (∖√-ev st rest) with revPre-ev st
    ... | refl = progH rest

-- `Run` (the approximants' innermost handler) offers every event, so it trivially
-- makes progress: its only reachable state is itself.
RUN : TProc
RUN = Run

RUN-ev : ∀ {e t′} → RUN ─[ ev (evl e) ]─► t′ → t′ ≡ RUN
RUN-ev (sVis refl br) = sym (just-injective br)

RUN-progress : Progress RUN
RUN-progress ∖√-refl        = _ , _ , sVis {at = _ , revive} {a = tt} refl refl
RUN-progress (∖√-τ  st _)   = ⊥-elim (stable-no-τ (λ _ _ → refl) st)
RUN-progress (∖√-ev st rest) with RUN-ev st
... | refl = RUN-progress rest

-- ★ assert revivable({error},Divide) :[deadlock free]  —  TRUE for every finite
-- approximation `RVn n` (the REAL throw with the REAL `revive ->` handler, n
-- revivals deep).  `error -> STOP` never deadlocks the system because the throw
-- catches `error` and `revive` restarts the divider.
rvn-progress : ∀ n → Progress (RVn n)
rvn-progress zero    = RUN-progress
rvn-progress (suc n) = revivable-progress (prefix-progress (rvn-progress n))

rvn-deadlock-free : ∀ n → DeadlockFree (RVn n)
rvn-deadlock-free n = progress⇒deadlockFree (rvn-progress n)

------------------------------------------------------------------------------------
-- §B.3  The ω-LIMIT: revivable({error},Divide) itself.
--
-- The literal fixed point is not constructible (see the header), so — exactly as
-- for RT in §B.1 — a WITNESS is built and its fixed-point property is proved
-- against the real operator.  Here the witness has five states instead of one,
-- because the divider does: the four divider positions plus the handler.  The
-- payoff is `V-fixpoint : V dD ∼ (Divide ⟦ Es ▷ (revive ⟶₀ V dD))` — Roscoe's
-- equation `revivable(E,P) = P [|E|> (revive -> revivable(E,P))` at E = {error},
-- P = Divide, up to STRONG bisimulation — and hence the assert itself on the real
-- throw term.  The §B.2 schematic results are kept unchanged alongside.
------------------------------------------------------------------------------------

-- The four positions of the divider, as a tag …
data DTag : Set where
  dD : DTag                -- Divide      (waiting for num?x)
  dN : Val → DTag          -- Dnum x      (waiting for den?y)
  dE : DTag                -- Derr        (about to raise the caught `error`)
  dR : ℕ → DTag            -- Dres q      (about to emit the pinned res!q)

-- … and the divider state each tag denotes.
Dst : DTag → TProc
Dst dD     = Divide
Dst (dN x) = Dnum x
Dst dE     = Derr
Dst (dR q) = Dres q

-- The WITNESS system: the throw-protected divider written out as inlined `react`
-- copatterns — one state per tag, plus the handler `Vh`.  `V dE`'s `error` goes to
-- `Vh` (the throw catches it, so STOP is simply ABSENT from the witness), and
-- `Vh`'s `revive` restarts at `V dD`.  Writing this out is legitimate because it
-- is NOT offered as the port of the assert: its fixed-point property against the
-- real `_⟦_▷_` is proved below (`V-fixpoint`), and the assert is then stated on the
-- real throw term.
V         : DTag → TProc
Vh        : TProc
vresOffer : ℕ → (at : AnyTypes TEv) → ContinueType at (Maybe TProc)
vfire     : {A : Set} → Dec A → Maybe TProc

force (V dD)     = react (λ where (_ , num) x → just (V (dN x))
                                  _         _ → nothing) ∅t
force (V (dN x)) = react (λ where (_ , den) fzero     → just (V dE)
                                  (_ , den) (fsuc y′) → just (V (dR (toℕ x / suc (toℕ y′))))
                                  _         _         → nothing) ∅t
force (V dE)     = react (λ where (_ , error) _ → just Vh
                                  _           _ → nothing) ∅t
force (V (dR q)) = react (vresOffer q) ∅t
force Vh         = react (λ where (_ , revive) _ → just (V dD)
                                  _           _ → nothing) ∅t

-- the witness's pinned output, mirroring `resOffer` / `fire` on the divider side
vresOffer q (_ , res) w = vfire (w ℕ≟ q)
vresOffer q _         _ = nothing
vfire (yes _) = just (V dD)
vfire (no  _) = nothing

-- The handler on the REAL side: `revive -> V dD`, the literal right-hand side of
-- Roscoe's equation once the recursive occurrence is the witness.
H₀ : TProc
H₀ = revive ⟶₀ V dD

-- The witness's pinned offer fires at exactly the quotient …
vres-diag : ∀ (q : ℕ) → vfire (q ℕ≟ q) ≡ just (V dD)
vres-diag q with q ℕ≟ q
... | yes _  = refl
... | no  ¬p = ⊥-elim (¬p refl)

-- … and the two systems SHARE that comparison, so whichever value fires one fires
-- the other, landing on the two systems' `Divide` states.  These two lemmas are the
-- only place where the pinning has to be reasoned about; they replace a `with` on a
-- stuck decision inside `Θ-vis`.
vfire-inv : ∀ {A : Set} {d : Dec A} {t′ : TProc}
          → vfire d ≡ just t′ → (t′ ≡ V dD) × (fire d ≡ just Divide)
vfire-inv {d = yes _} refl = refl , refl
vfire-inv {d = no  _} eq   = case eq of λ ()

fire-inv₂ : ∀ {A : Set} {d : Dec A} {t′ : TProc}
          → fire d ≡ just t′ → (t′ ≡ Divide) × (vfire d ≡ just (V dD))
fire-inv₂ {d = yes _} refl = refl , refl
fire-inv₂ {d = no  _} eq   = case eq of λ ()

-- The reachable states of the witness: the five states above and nothing else.
data VR : TProc → Set₁ where
  vSt : (t : DTag) → VR (V t)
  vHd : VR Vh

-- Step inversions for the witness: every state is a stable single-channel menu,
-- and every visible step lands on another reachable witness state (never on STOP).
V-ev : (t : DTag) {e : Event} {t′ : TProc} → V t ─[ ev (evl e) ]─► t′ → VR t′
V-ev dD (sVis {at = _ , num} {a = x} refl refl) = vSt (dN x)
V-ev dD (sVis {at = _ , a     } refl br) = case br of λ ()
V-ev dD (sVis {at = _ , b     } refl br) = case br of λ ()
V-ev dD (sVis {at = _ , den   } refl br) = case br of λ ()
V-ev dD (sVis {at = _ , res   } refl br) = case br of λ ()
V-ev dD (sVis {at = _ , error } refl br) = case br of λ ()
V-ev dD (sVis {at = _ , revive} refl br) = case br of λ ()
V-ev (dN x) (sVis {at = _ , den} {a = fzero  } refl refl) = vSt dE
V-ev (dN x) (sVis {at = _ , den} {a = fsuc y′} refl refl) = vSt (dR (toℕ x / suc (toℕ y′)))
V-ev (dN x) (sVis {at = _ , a     } refl br) = case br of λ ()
V-ev (dN x) (sVis {at = _ , b     } refl br) = case br of λ ()
V-ev (dN x) (sVis {at = _ , num   } refl br) = case br of λ ()
V-ev (dN x) (sVis {at = _ , res   } refl br) = case br of λ ()
V-ev (dN x) (sVis {at = _ , error } refl br) = case br of λ ()
V-ev (dN x) (sVis {at = _ , revive} refl br) = case br of λ ()
V-ev dE (sVis {at = _ , error} refl refl) = vHd
V-ev dE (sVis {at = _ , a     } refl br) = case br of λ ()
V-ev dE (sVis {at = _ , b     } refl br) = case br of λ ()
V-ev dE (sVis {at = _ , num   } refl br) = case br of λ ()
V-ev dE (sVis {at = _ , den   } refl br) = case br of λ ()
V-ev dE (sVis {at = _ , res   } refl br) = case br of λ ()
V-ev dE (sVis {at = _ , revive} refl br) = case br of λ ()
V-ev (dR q) (sVis {at = _ , res} refl br) with vfire-inv br
... | refl , _ = vSt dD
V-ev (dR q) (sVis {at = _ , a     } refl br) = case br of λ ()
V-ev (dR q) (sVis {at = _ , b     } refl br) = case br of λ ()
V-ev (dR q) (sVis {at = _ , num   } refl br) = case br of λ ()
V-ev (dR q) (sVis {at = _ , den   } refl br) = case br of λ ()
V-ev (dR q) (sVis {at = _ , error } refl br) = case br of λ ()
V-ev (dR q) (sVis {at = _ , revive} refl br) = case br of λ ()

Vh-ev : {e : Event} {t′ : TProc} → Vh ─[ ev (evl e) ]─► t′ → VR t′
Vh-ev (sVis {at = _ , revive} refl refl) = vSt dD
Vh-ev (sVis {at = _ , a     } refl br) = case br of λ ()
Vh-ev (sVis {at = _ , b     } refl br) = case br of λ ()
Vh-ev (sVis {at = _ , num   } refl br) = case br of λ ()
Vh-ev (sVis {at = _ , den   } refl br) = case br of λ ()
Vh-ev (sVis {at = _ , res   } refl br) = case br of λ ()
Vh-ev (sVis {at = _ , error } refl br) = case br of λ ()


-- The strong bisimulation between the witness and the real throw term, state by
-- state (`Vsim⁻` / `Vhsim⁻` are the mirrored pairs, so the backward residuals are
-- built without going through `sbisim-sym`, which would break productivity).
Vfwd   : (t : DTag) → SSimF (Sbisim (⊤poly {lzero})) (V t) (Dst t ⟦ Es ▷ H₀)
Vbwd   : (t : DTag) → SSimF (Sbisim (⊤poly {lzero})) (Dst t ⟦ Es ▷ H₀) (V t)
Vhfwd  : SSimF (Sbisim (⊤poly {lzero})) Vh H₀
Vhbwd  : SSimF (Sbisim (⊤poly {lzero})) H₀ Vh
Vsim   : (t : DTag) → V t ∼ (Dst t ⟦ Es ▷ H₀)
Vsim⁻  : (t : DTag) → (Dst t ⟦ Es ▷ H₀) ∼ V t
Vhsim  : Vh ∼ H₀
Vhsim⁻ : H₀ ∼ Vh

Vsim  t .Sbisim.fwd = Vfwd t
Vsim  t .Sbisim.bwd = Vbwd t
Vsim⁻ t .Sbisim.fwd = Vbwd t
Vsim⁻ t .Sbisim.bwd = Vfwd t
Vhsim   .Sbisim.fwd = Vhfwd
Vhsim   .Sbisim.bwd = Vhbwd
Vhsim⁻  .Sbisim.fwd = Vhbwd
Vhsim⁻  .Sbisim.bwd = Vhfwd

-- The witness SIMULATES the real throw term: each of its visible steps is matched
-- by the corresponding `Θ-pass-step` (num / den / res, none of which is in the
-- throw set) or, at `V dE`, by the `Θ-throw-step` that catches `error`.
Vfwd dD .SSimF.on-ev (sRet eq) = case eq of λ ()
Vfwd dD .SSimF.on-ev (sVis {at = _ , num} {a = x} refl refl) =
  _ , Θ-pass-step (sVis {at = _ , num} {a = x} refl refl) (λ z → z) , Vsim (dN x)
Vfwd dD .SSimF.on-ev (sVis {at = _ , a     } refl br) = case br of λ ()
Vfwd dD .SSimF.on-ev (sVis {at = _ , b     } refl br) = case br of λ ()
Vfwd dD .SSimF.on-ev (sVis {at = _ , den   } refl br) = case br of λ ()
Vfwd dD .SSimF.on-ev (sVis {at = _ , res   } refl br) = case br of λ ()
Vfwd dD .SSimF.on-ev (sVis {at = _ , error } refl br) = case br of λ ()
Vfwd dD .SSimF.on-ev (sVis {at = _ , revive} refl br) = case br of λ ()
Vfwd dD .SSimF.on-tau (sSil eq)      = case eq of λ ()
Vfwd dD .SSimF.on-tau (sTau refl br) = case br of λ ()

Vfwd (dN x) .SSimF.on-ev (sRet eq) = case eq of λ ()
Vfwd (dN x) .SSimF.on-ev (sVis {at = _ , den} {a = fzero} refl refl) =
  _ , Θ-pass-step (sVis {at = _ , den} {a = fzero} refl refl) (λ z → z) , Vsim dE
Vfwd (dN x) .SSimF.on-ev (sVis {at = _ , den} {a = fsuc y′} refl refl) =
  _ , Θ-pass-step (sVis {at = _ , den} {a = fsuc y′} refl refl) (λ z → z)
    , Vsim (dR (toℕ x / suc (toℕ y′)))
Vfwd (dN x) .SSimF.on-ev (sVis {at = _ , a     } refl br) = case br of λ ()
Vfwd (dN x) .SSimF.on-ev (sVis {at = _ , b     } refl br) = case br of λ ()
Vfwd (dN x) .SSimF.on-ev (sVis {at = _ , num   } refl br) = case br of λ ()
Vfwd (dN x) .SSimF.on-ev (sVis {at = _ , res   } refl br) = case br of λ ()
Vfwd (dN x) .SSimF.on-ev (sVis {at = _ , error } refl br) = case br of λ ()
Vfwd (dN x) .SSimF.on-ev (sVis {at = _ , revive} refl br) = case br of λ ()
Vfwd (dN x) .SSimF.on-tau (sSil eq)      = case eq of λ ()
Vfwd (dN x) .SSimF.on-tau (sTau refl br) = case br of λ ()

Vfwd dE .SSimF.on-ev (sRet eq) = case eq of λ ()
Vfwd dE .SSimF.on-ev (sVis {at = _ , error} {a = x} refl refl) =
  _ , Θ-throw-step (sVis {at = _ , error} {a = x} refl refl) tt , Vhsim
Vfwd dE .SSimF.on-ev (sVis {at = _ , a     } refl br) = case br of λ ()
Vfwd dE .SSimF.on-ev (sVis {at = _ , b     } refl br) = case br of λ ()
Vfwd dE .SSimF.on-ev (sVis {at = _ , num   } refl br) = case br of λ ()
Vfwd dE .SSimF.on-ev (sVis {at = _ , den   } refl br) = case br of λ ()
Vfwd dE .SSimF.on-ev (sVis {at = _ , res   } refl br) = case br of λ ()
Vfwd dE .SSimF.on-ev (sVis {at = _ , revive} refl br) = case br of λ ()
Vfwd dE .SSimF.on-tau (sSil eq)      = case eq of λ ()
Vfwd dE .SSimF.on-tau (sTau refl br) = case br of λ ()

Vfwd (dR q) .SSimF.on-ev (sRet eq) = case eq of λ ()
Vfwd (dR q) .SSimF.on-ev (sVis {at = _ , res} {a = w} refl br) with vfire-inv br
... | refl , feq =
  _ , Θ-pass-step (sVis {at = _ , res} {a = w} refl feq) (λ z → z) , Vsim dD
Vfwd (dR q) .SSimF.on-ev (sVis {at = _ , a     } refl br) = case br of λ ()
Vfwd (dR q) .SSimF.on-ev (sVis {at = _ , b     } refl br) = case br of λ ()
Vfwd (dR q) .SSimF.on-ev (sVis {at = _ , num   } refl br) = case br of λ ()
Vfwd (dR q) .SSimF.on-ev (sVis {at = _ , den   } refl br) = case br of λ ()
Vfwd (dR q) .SSimF.on-ev (sVis {at = _ , error } refl br) = case br of λ ()
Vfwd (dR q) .SSimF.on-ev (sVis {at = _ , revive} refl br) = case br of λ ()
Vfwd (dR q) .SSimF.on-tau (sSil eq)      = case eq of λ ()
Vfwd (dR q) .SSimF.on-tau (sTau refl br) = case br of λ ()

-- … and it is simulated BY the real throw term: the throw's offers reduce to the
-- witness's own (at `Dres q` the pinned comparison is shared, so the inversion
-- goes through `Θ-ev-elim`, whose `Θthrow` case is refuted by res ∉ {error}).
Vbwd dD .SSimF.on-ev (sRet eq) = case eq of λ ()
Vbwd dD .SSimF.on-ev (sVis {at = _ , num} {a = x} refl refl) =
  _ , sVis {at = _ , num} {a = x} refl refl , Vsim⁻ (dN x)
Vbwd dD .SSimF.on-ev (sVis {at = _ , a     } refl br) = case br of λ ()
Vbwd dD .SSimF.on-ev (sVis {at = _ , b     } refl br) = case br of λ ()
Vbwd dD .SSimF.on-ev (sVis {at = _ , den   } refl br) = case br of λ ()
Vbwd dD .SSimF.on-ev (sVis {at = _ , res   } refl br) = case br of λ ()
Vbwd dD .SSimF.on-ev (sVis {at = _ , error } refl br) = case br of λ ()
Vbwd dD .SSimF.on-ev (sVis {at = _ , revive} refl br) = case br of λ ()
Vbwd dD .SSimF.on-tau (sSil eq)      = case eq of λ ()
Vbwd dD .SSimF.on-tau (sTau refl br) = case br of λ ()

Vbwd (dN x) .SSimF.on-ev (sRet eq) = case eq of λ ()
Vbwd (dN x) .SSimF.on-ev (sVis {at = _ , den} {a = fzero} refl refl) =
  _ , sVis {at = _ , den} {a = fzero} refl refl , Vsim⁻ dE
Vbwd (dN x) .SSimF.on-ev (sVis {at = _ , den} {a = fsuc y′} refl refl) =
  _ , sVis {at = _ , den} {a = fsuc y′} refl refl , Vsim⁻ (dR (toℕ x / suc (toℕ y′)))
Vbwd (dN x) .SSimF.on-ev (sVis {at = _ , a     } refl br) = case br of λ ()
Vbwd (dN x) .SSimF.on-ev (sVis {at = _ , b     } refl br) = case br of λ ()
Vbwd (dN x) .SSimF.on-ev (sVis {at = _ , num   } refl br) = case br of λ ()
Vbwd (dN x) .SSimF.on-ev (sVis {at = _ , res   } refl br) = case br of λ ()
Vbwd (dN x) .SSimF.on-ev (sVis {at = _ , error } refl br) = case br of λ ()
Vbwd (dN x) .SSimF.on-ev (sVis {at = _ , revive} refl br) = case br of λ ()
Vbwd (dN x) .SSimF.on-tau (sSil eq)      = case eq of λ ()
Vbwd (dN x) .SSimF.on-tau (sTau refl br) = case br of λ ()

Vbwd dE .SSimF.on-ev (sRet eq) = case eq of λ ()
Vbwd dE .SSimF.on-ev (sVis {at = _ , error} {a = x} refl refl) =
  _ , sVis {at = _ , error} {a = x} refl refl , Vhsim⁻
Vbwd dE .SSimF.on-ev (sVis {at = _ , a     } refl br) = case br of λ ()
Vbwd dE .SSimF.on-ev (sVis {at = _ , b     } refl br) = case br of λ ()
Vbwd dE .SSimF.on-ev (sVis {at = _ , num   } refl br) = case br of λ ()
Vbwd dE .SSimF.on-ev (sVis {at = _ , den   } refl br) = case br of λ ()
Vbwd dE .SSimF.on-ev (sVis {at = _ , res   } refl br) = case br of λ ()
Vbwd dE .SSimF.on-ev (sVis {at = _ , revive} refl br) = case br of λ ()
Vbwd dE .SSimF.on-tau (sSil eq)      = case eq of λ ()
Vbwd dE .SSimF.on-tau (sTau refl br) = case br of λ ()

Vbwd (dR q) .SSimF.on-ev (sRet eq) = case eq of λ ()
Vbwd (dR q) .SSimF.on-ev (sVis {at = _ , res} {a = w} refl br)
  with Θ-ev-elim (Dres q) H₀ (sVis {at = _ , res} {a = w} refl br)
... | Θthrow _ m = ⊥-elim m
... | Θpass (sVis refl br′) _ with fire-inv₂ br′
...   | refl , veq = _ , sVis {at = _ , res} {a = w} refl veq , Vsim⁻ dD
Vbwd (dR q) .SSimF.on-ev (sVis {at = _ , a     } refl br) = case br of λ ()
Vbwd (dR q) .SSimF.on-ev (sVis {at = _ , b     } refl br) = case br of λ ()
Vbwd (dR q) .SSimF.on-ev (sVis {at = _ , num   } refl br) = case br of λ ()
Vbwd (dR q) .SSimF.on-ev (sVis {at = _ , den   } refl br) = case br of λ ()
Vbwd (dR q) .SSimF.on-ev (sVis {at = _ , error } refl br) = case br of λ ()
Vbwd (dR q) .SSimF.on-ev (sVis {at = _ , revive} refl br) = case br of λ ()
Vbwd (dR q) .SSimF.on-tau (sSil eq)      = case eq of λ ()
Vbwd (dR q) .SSimF.on-tau (sTau refl br) = case br of λ ()

-- The handler pair: `Vh` and the real `revive -> V dD` offer `revive` alone and
-- have the SAME continuation, so their residual is reflexivity.
Vhfwd .SSimF.on-ev (sRet eq) = case eq of λ ()
Vhfwd .SSimF.on-ev (sVis {at = _ , revive} {a = x} refl refl) =
  _ , sVis {at = _ , revive} {a = x} refl refl , sbisim-refl (V dD)
Vhfwd .SSimF.on-ev (sVis {at = _ , a     } refl br) = case br of λ ()
Vhfwd .SSimF.on-ev (sVis {at = _ , b     } refl br) = case br of λ ()
Vhfwd .SSimF.on-ev (sVis {at = _ , num   } refl br) = case br of λ ()
Vhfwd .SSimF.on-ev (sVis {at = _ , den   } refl br) = case br of λ ()
Vhfwd .SSimF.on-ev (sVis {at = _ , res   } refl br) = case br of λ ()
Vhfwd .SSimF.on-ev (sVis {at = _ , error } refl br) = case br of λ ()
Vhfwd .SSimF.on-tau (sSil eq)      = case eq of λ ()
Vhfwd .SSimF.on-tau (sTau refl br) = case br of λ ()

Vhbwd .SSimF.on-ev (sRet eq) = case eq of λ ()
Vhbwd .SSimF.on-ev (sVis {at = _ , revive} {a = x} refl refl) =
  _ , sVis {at = _ , revive} {a = x} refl refl , sbisim-refl (V dD)
Vhbwd .SSimF.on-ev (sVis {at = _ , a     } refl br) = case br of λ ()
Vhbwd .SSimF.on-ev (sVis {at = _ , b     } refl br) = case br of λ ()
Vhbwd .SSimF.on-ev (sVis {at = _ , num   } refl br) = case br of λ ()
Vhbwd .SSimF.on-ev (sVis {at = _ , den   } refl br) = case br of λ ()
Vhbwd .SSimF.on-ev (sVis {at = _ , res   } refl br) = case br of λ ()
Vhbwd .SSimF.on-ev (sVis {at = _ , error } refl br) = case br of λ ()
Vhbwd .SSimF.on-tau (sSil eq)      = case eq of λ ()
Vhbwd .SSimF.on-tau (sTau refl br) = case br of λ ()

-- Every witness state is stable …
VR-stable : ∀ {t} → VR t → isStable t
VR-stable (vSt dD)     _ _ = refl
VR-stable (vSt (dN x)) _ _ = refl
VR-stable (vSt dE)     _ _ = refl
VR-stable (vSt (dR q)) _ _ = refl
VR-stable vHd          _ _ = refl

-- … and every witness state has an enabled visible move.
VR-enabled : ∀ {t} → VR t
           → Σ[ l ∈ Label (⊤poly {lzero}) ] Σ[ t″ ∈ TProc ] (t ─[ l ]─► t″)
VR-enabled (vSt dD)     = _ , _ , sVis {at = _ , num   } {a = fzero} refl refl
VR-enabled (vSt (dN x)) = _ , _ , sVis {at = _ , den   } {a = fzero} refl refl
VR-enabled (vSt dE)     = _ , _ , sVis {at = _ , error } {a = tt   } refl refl
VR-enabled (vSt (dR q)) = _ , _ , sVis {at = _ , res   } {a = q    } refl (vres-diag q)
VR-enabled vHd          = _ , _ , sVis {at = _ , revive} {a = tt   } refl refl

-- reachability is closed under visible steps
VR-step : ∀ {t t′ e} → VR t → t ─[ ev (evl e) ]─► t′ → VR t′
VR-step (vSt t) st = V-ev t st
VR-step vHd     st = Vh-ev st

-- The witness makes progress: it has no τ at all, and every state it reaches has
-- an enabled event.  (This is the one induction over reach-paths that the ω-limit
-- needs; the handler slot of `revivable-progress` is fed from it.)
V-progress : Progress (V dD)
V-progress = go (vSt dD)
  where
    go : ∀ {t s t′} → VR t → t ⟹∖√⟨ s ⟩ t′
       → Σ[ l ∈ Label (⊤poly {lzero}) ] Σ[ t″ ∈ TProc ] (t′ ─[ l ]─► t″)
    go v ∖√-refl         = VR-enabled v
    go v (∖√-τ  st _)    = ⊥-elim (stable-no-τ (VR-stable v) st)
    go v (∖√-ev st rest) = go (VR-step v st) rest

-- ★ THE FIXED POINT.  `V dD` solves Roscoe's equation
--     revivable(E,P) = P [|E|> (revive -> revivable(E,P))
-- at E = {error}, P = Divide, up to STRONG bisimulation — the same strength as
-- `rtx-fixpoint` in §B.1, so `Divide ⟦ Es ▷ (revive ⟶₀ V dD)` IS
-- revivable({error},Divide).
V-fixpoint : V dD ∼ (Divide ⟦ Es ▷ (revive ⟶₀ V dD))
V-fixpoint = Vsim dD

-- … and the handler half of that equation, `Vh ∼ revive -> V dD`, which is what
-- makes the witness's own `error`-transfer the real `revive ->` handler.
Vh-fixpoint : Vh ∼ (revive ⟶₀ V dD)
Vh-fixpoint = Vhsim

-- ★ assert revivable({error},Divide) :[deadlock free]  —  TRUE.  Stated on the
-- real throw term with the real `revive ->` handler, whose fixed-point property is
-- `V-fixpoint`.  `error -> STOP` cannot deadlock the system: the throw catches
-- `error` before STOP is entered and `revive` restarts the divider.
revivable-deadlock-free : DeadlockFree (Divide ⟦ Es ▷ (revive ⟶₀ V dD))
revivable-deadlock-free = revivable-deadlockFree (prefix-progress V-progress)

-- the same conclusion for the witness itself (transported by nothing — it is proved
-- directly from `V-progress`), which the bisimulation shows is the same process
witness-deadlock-free : DeadlockFree (V dD)
witness-deadlock-free = progress⇒deadlockFree V-progress
