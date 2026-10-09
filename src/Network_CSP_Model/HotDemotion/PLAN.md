# Hot→warm Demotion Model Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A standalone CSP model of the outbound hot→warm demotion that proves Warm is impossible before ouroboros-consensus PR 2344 (with no Leios load) and guaranteed after it (given Praos blocks and TxSubmission2 requests), and that TxSubmission2 / missing blocks remain blockers.

**Architecture:** One monolithic step relation over a product state (governor phase × five hot-protocol phases), parameterised by a `Mode` (LeiosNotify variant, which environment events are offered, whether the timeout exists). The process `Sys m` is generated from the step function exactly like `GovernorWedge.Model.Conn`/`Gov` (no τ). Properties are proved on the pure step relation and lifted to `Sys` through a `Steps` correspondence module, following `GovernorWedge/Steps.agda`.

**Tech Stack:** Agda 2.8.0; libraries `standard-library`, `csp-ptree` (`Process_Trees`, `CSP.Operators`, `Semantics.LTS`, `Semantics.Failures`, `Semantics.Deadlock`, `Semantics.DivergenceFree`, `Semantics.LTL.Traces_Based`).

**Spec:** [`HotDemotion/DESIGN.md`](DESIGN.md) (facts and citations in [`HotDemotion/RESEARCH.md`](RESEARCH.md)).

## Global Constraints

- Run `agda` from `src/Network_CSP_Model` (the folder with `cardano-network-csp.agda-lib`), with `+RTS -M20G -RTS`. `systemd-run` does not work inside the command sandbox.
- Every module starts with `{-# OPTIONS --guardedness #-}`.
- A one-line comment above every new definition (data constructors excepted, as elsewhere in the repo).
- No `postulate`, no `TERMINATING`/`NON_TERMINATING`, no sized types, no `mutual` blocks (use forward declarations).
- Standalone: `HotDemotion/*` must not import `Cardano_network.*` (same rule as `GovernorWedge/`).
- No stray files in the project folder; scratch and logs go to `$TMPDIR`.
- Commits: author Kangfeng Ye, no `Co-Authored-By`/`Claude-Session` lines (CLAUDE.md). Commit only the task's files, using `git commit <paths>` so the user's staged `.gitignore` is not swept in. git is invisible inside the sandbox: run git with the sandbox disabled.
- Known Agda 2.8.0 bug: absurd clauses with a wildcard step pattern can hit `__IMPOSSIBLE__` (CompiledClause/Compile.hs:173) — list constructors explicitly.
- Known performance trap: consume long concrete runs through helper functions, not nested `with`.

## Review Focus

1. **Vacuity of D1/D3:** "warm unreachable" must not hold merely because `demote` is unreachable or the system deadlocks early. Pin it with a reachability witness: the pre-PR system *does* reach `gov awaiting` with every other protocol finished (Task 3, `pre-nearlyWarm`).
2. **The timeout must stay an escape:** in every reachable state where the governor is awaiting, `tmo` is enabled when `timer m ≡ true` (Task 3, `tmo-enabled`), otherwise D1's "every run ends Cold" is false.
3. **Environment gating must match the scenario:** an env event may only fire when its flag is set *and* its protocol is waiting for it; a `block` before `demote` must not pre-finish ChainSync. Pinned by `block-only-when-waiting` (Task 1).
4. **Post-PR LeiosNotify must not need any environment event:** `ln` must finish with `lnLoad ≡ false`. Pinned by `post-ln-noEnv` (Task 4).
5. **The bounded-progress number must be tight, not just valid:** a witness run attaining it (Task 4, `post-tight`), otherwise an off-by-one in the rank goes unnoticed.

---

## File Structure

| File | Responsibility |
|---|---|
| `HotDemotion/Model.agda` | Events, `Ev-≟`, phases, `Mode`, step functions `gstep`/`hstep`/`sstep`, the process `SysAt`/`Sys`, trace-letter helpers, the pure `Steps` relation |
| `HotDemotion/Lift.agda` | Correspondence between `Sys` process steps and `sstep` (no τ; √ only at the end), so traces of `Sys` ⇔ `Steps` |
| `HotDemotion/PrePR.agda` | D1 and its vacuity guards |
| `HotDemotion/PostPR.agda` | D2a, the bounded progress lemma, D2b (LTL) |
| `HotDemotion/Blockers.agda` | D3 (TxSubmission2 / no block), D4 contrast |
| `HotDemotion/README.md` | What is modelled, assumed, proved; theorem index; citation key pointer to `RESEARCH.md` |

---

### Task 1: The model

**Files:**
- Create: `HotDemotion/Model.agda`

**Interfaces:**
- Produces: `Proto`, `Variant`, `GAct`, `EnvAct`, `IntAct`, `Ev`, `Ev-≟`, `PSt`, `GPh`, `Mode` (fields `var`, `blocks`, `txReqs`, `lnLoad`, `timer`), `St` (fields `gph`, `ps : Proto → PSt`), `st₀`, `afterTerm : Variant → Proto → PSt`, `allFin : St → Bool`, `sstep : (at : AnyTypes Ev) → proj₁ at → Mode → St → Maybe St`, `final : St → Bool`, `SysAt : Mode → St → Proc`, `Sys : Mode → Proc`, letters `GV`, `RT`, `EV`, `IN`, relation `Steps : Mode → St → List (Σ (AnyTypes Ev) proj₁) → St → Set`.

- [ ] **Step 1: Write the module header, events and decidable equality**

```agda
{-# OPTIONS --guardedness #-}

-- Hot→warm demotion (DESIGN.md §3–§4): one demotion of one outbound peer; each hot
-- mini-protocol is reduced to its behaviour after the governor writes Terminate.
-- Citations: RESEARCH.md (ouroboros-network 4b3ab76, ouroboros-consensus 27fa649ff).
module HotDemotion.Model where

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

-- the five hot mini-protocols (RESEARCH.md §1)
data Proto : Set where
  cs bf tx lf ln : Proto

-- LeiosNotify before / after ouroboros-consensus PR 2344
data Variant : Set where
  pre post : Variant

-- governor actions: start demotion (write Terminate, PSA:997-999), all hot returned (PSA:1007-1014),
-- deactivate timeout (PSA:1025-1033), peer ends Cold (AP:988-1017)
data GAct : Set where
  demote warm tmo cold : GAct

-- environment: a Praos header arrives, the remote sends a blocking MsgRequestTxIds, a Leios reply arrives
data EnvAct : Set where
  block txReq lnReply : EnvAct

-- protocol-internal progress, kept visible (no τ in the model): BlockFetch finishes its in-flight batch;
-- post-PR LeiosNotify sends MsgQuit; the remote LeiosNotify server answers it (MsgCanceled…, MsgDone)
data IntAct : Set where
  bfDrain lnQuit lnQuitDone : IntAct

-- the four channels; ret p = hot protocol p returned (the governor's awaitAllResults, PSA:409-423)
data Ev : Set → Set where
  gov : Ev GAct
  ret : Ev Proto
  env : Ev EnvAct
  int : Ev IntAct

-- decidable equality on the existential event index
Ev-≟ : (x y : AnyTypes Ev) → Dec (x ≡ y)
Ev-≟ (_ , gov) (_ , gov) = yes refl
Ev-≟ (_ , ret) (_ , ret) = yes refl
Ev-≟ (_ , env) (_ , env) = yes refl
Ev-≟ (_ , int) (_ , int) = yes refl
Ev-≟ (_ , gov) (_ , ret) = no λ ()
Ev-≟ (_ , gov) (_ , env) = no λ ()
Ev-≟ (_ , gov) (_ , int) = no λ ()
Ev-≟ (_ , ret) (_ , gov) = no λ ()
Ev-≟ (_ , ret) (_ , env) = no λ ()
Ev-≟ (_ , ret) (_ , int) = no λ ()
Ev-≟ (_ , env) (_ , gov) = no λ ()
Ev-≟ (_ , env) (_ , ret) = no λ ()
Ev-≟ (_ , env) (_ , int) = no λ ()
Ev-≟ (_ , int) (_ , gov) = no λ ()
Ev-≟ (_ , int) (_ , ret) = no λ ()
Ev-≟ (_ , int) (_ , env) = no λ ()

open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import CSP.Operators Ev-≟

-- return type of every process
U : Set
U = ⊤ {0ℓ}

-- the process type
Proc : Set₁
Proc = PTree Ev (ExtI Ev) U
```

- [ ] **Step 2: Add phases, mode, state and the step functions**

```agda
-- a hot protocol's phase: running (before Terminate), waiting for an env event, needing an internal
-- step, post-PR LeiosNotify waiting for the server's answer to MsgQuit, ready to return, returned
data PSt : Set where
  running waitEnv needInt quitSent ready fin : PSt

-- governor phase: hot, awaiting all hot results under the timeout, Warm, timed out, Cold
data GPh : Set where
  hot awaiting warmD timedOut coldD : GPh

-- a model variant: LeiosNotify version, which env events the environment offers, whether the timeout exists
record Mode : Set where
  constructor mode
  field
    var    : Variant
    blocks : Bool
    txReqs : Bool
    lnLoad : Bool
    timer  : Bool
open Mode public

-- the model state
record St : Set where
  constructor mkSt
  field
    gph : GPh
    ps  : Proto → PSt
open St public

-- initial state: hot, every protocol running
st₀ : St
st₀ = mkSt hot (λ _ → running)

-- each protocol's phase right after Terminate (DESIGN.md §4 table)
afterTerm : Variant → Proto → PSt
afterTerm _    cs = waitEnv     -- ChainSync in StMustReply waits for a header
afterTerm _    bf = needInt     -- BlockFetch drains in-flight batches
afterTerm _    tx = waitEnv     -- TxSubmission2 outbound waits in StIdle for a blocking request
afterTerm _    lf = ready       -- LeiosFetch with nothing in flight stops at once
afterTerm pre  ln = waitEnv     -- pre-PR: owes replies; only a Leios reply lets it proceed
afterTerm post ln = needInt     -- post-PR: sends MsgQuit

-- set one protocol's phase
setP : Proto → PSt → (Proto → PSt) → (Proto → PSt)
setP p x f q = case (p , q) of λ where
  (cs , cs) → x ; (bf , bf) → x ; (tx , tx) → x ; (lf , lf) → x ; (ln , ln) → x
  _         → f q
```

(The executor may replace `setP` by a five-way pattern match if `case` on pairs does not reduce; keep the name and type.)

```agda
-- every hot protocol has returned
allFin : St → Bool
allFin s = isFin (ps s cs) ∧ isFin (ps s bf) ∧ isFin (ps s tx) ∧ isFin (ps s lf) ∧ isFin (ps s ln)
  where
  -- one phase is fin
  isFin : PSt → Bool
  isFin fin = true
  isFin _   = false

-- which protocol an env event serves, and whether the mode offers it
envFor : EnvAct → Proto
envFor block   = cs
envFor txReq   = tx
envFor lnReply = ln

-- the mode's flag for an env event
envOn : Mode → EnvAct → Bool
envOn m block   = blocks m
envOn m txReq   = txReqs m
envOn m lnReply = lnLoad m

-- the protocol an internal action belongs to, the phase it needs and the phase it yields
intMove : Variant → IntAct → Maybe (Proto × PSt × PSt)
intMove _    bfDrain    = just (bf , needInt , ready)
intMove post lnQuit     = just (ln , needInt , quitSent)
intMove post lnQuitDone = just (ln , quitSent , ready)
intMove pre  _          = nothing

-- one move of the whole system (governor and hot protocols synchronise on ret; DESIGN.md §4's ∥ is this product)
sstep : (at : AnyTypes Ev) → proj₁ at → Mode → St → Maybe St
sstep (_ , gov) demote m (mkSt hot f)      = just (mkSt awaiting (afterTerm (var m)))
sstep (_ , gov) warm   m s@(mkSt awaiting f) = if allFin s then just (mkSt warmD f) else nothing
sstep (_ , gov) tmo    m (mkSt awaiting f) = if timer m then just (mkSt timedOut f) else nothing
sstep (_ , gov) cold   m (mkSt timedOut f) = just (mkSt coldD f)
sstep (_ , gov) _      _ _                 = nothing
sstep (_ , ret) p      m (mkSt awaiting f) = stepIf (f p) ready (mkSt awaiting (setP p fin f))
sstep (_ , ret) _      _ _                 = nothing
sstep (_ , env) e      m (mkSt awaiting f) =
  if envOn m e then stepIf (f (envFor e)) waitEnv (mkSt awaiting (setP (envFor e) ready f)) else nothing
sstep (_ , env) _      _ _                 = nothing
sstep (_ , int) a      m (mkSt awaiting f) = case intMove (var m) a of λ where
  (just (p , need , yield)) → stepIf (f p) need (mkSt awaiting (setP p yield f))
  nothing                   → nothing
sstep (_ , int) _      _ _                 = nothing
```

with the helper (declare it before `sstep`):

```agda
-- succeed with s′ when the current phase is the expected one
stepIf : PSt → PSt → St → Maybe St
stepIf x y s′ = if eqP x y then just s′ else nothing
  where
  -- phase equality as a Bool
  eqP : PSt → PSt → Bool
  eqP running running   = true
  eqP waitEnv waitEnv   = true
  eqP needInt needInt   = true
  eqP quitSent quitSent = true
  eqP ready ready       = true
  eqP fin fin           = true
  eqP _ _               = false
```

- [ ] **Step 3: Add the process, the final states, letters and the pure relation**

```agda
-- the run is over: Warm or Cold reached
final : St → Bool
final (mkSt warmD _) = true
final (mkSt coldD _) = true
final _              = false

-- the system at a state, generated from sstep; it terminates (√) once final
SysAt : Mode → St → Proc
force (SysAt m s) = if final s then ret tt else react
  (λ where (X , ch) a → case sstep (X , ch) a m s of λ where
                          (just s′) → just (SysAt m s′)
                          nothing   → nothing)
  ∅t

-- the system under a mode
Sys : Mode → Proc
Sys m = SysAt m st₀

-- trace letters
lbl : (at : AnyTypes Ev) → proj₁ at → Event√ U
lbl (X , ch) a = evl (evLabel X ch a)

-- governor letter
GV : GAct → Event√ U
GV = lbl (GAct , gov)

-- return letter
RT : Proto → Event√ U
RT = lbl (Proto , ret)

-- environment letter
EV : EnvAct → Event√ U
EV = lbl (EnvAct , env)

-- internal-progress letter
IN : IntAct → Event√ U
IN = lbl (IntAct , int)

-- the pure multi-step relation over sstep
data Steps (m : Mode) : St → List (Σ (AnyTypes Ev) proj₁) → St → Set where
  done : ∀ {s} → Steps m s [] s
  more : ∀ {s s′ s″ at a w} → sstep at a m s ≡ just s′ → Steps m s′ w s″ → Steps m s ((at , a) ∷ w) s″
```

(`react`, `∅t`, `ret`, `evl`, `evLabel`, `Event√` are the names `GovernorWedge/Model.agda` uses; check their exact import there and copy it.)

- [ ] **Step 4: Add the Review-Focus pins for the model (Review Focus 3)**

```agda
-- a block is refused before demote: ChainSync cannot be pre-finished (Review Focus 3)
block-only-when-waiting : ∀ m → sstep (EnvAct , env) block m st₀ ≡ nothing
block-only-when-waiting m = refl

-- with lnLoad off, a Leios reply is refused even while LeiosNotify waits
lnReply-off : ∀ v b t c → sstep (EnvAct , env) lnReply (mode v b t false c) (mkSt awaiting (afterTerm v)) ≡ nothing
lnReply-off v b t c = refl
```

- [ ] **Step 5: Typecheck**

Run (from `src/Network_CSP_Model`): `agda HotDemotion/Model.agda +RTS -M20G -RTS`
Expected: exit 0, no warnings. If `refl` fails in Step 4 because `if`/`case` does not reduce, rewrite the offending function by direct pattern matching (keep names/types) and re-run.

- [ ] **Step 6: Commit**

```bash
git -C <repo> commit -m "HotDemotion: model of one hot-to-warm demotion" -- src/Network_CSP_Model/HotDemotion/Model.agda
```
(after `git add` of the file; sandbox disabled for git)

---

### Task 2: Process ↔ step correspondence

**Files:**
- Create: `HotDemotion/Lift.agda`

**Interfaces:**
- Consumes: everything from Task 1.
- Produces:
  - `Sys-ev-inv : SysAt m s ─[ ev (lbl at a) ]─► W → Σ[ s′ ∈ St ] (sstep at a m s ≡ just s′ × W ≡ SysAt m s′)`
  - `Sys-ev-intro : sstep at a m s ≡ just s′ → final s ≡ false → SysAt m s ─[ ev (lbl at a) ]─► SysAt m s′`
  - `Sys-no-τ : ¬ (SysAt m s ─[ τ ]─► W)`
  - `Sys-√ : SysAt m s ─[ ev (√ r) ]─► W → final s ≡ true`
  - `traces⇒Steps : Sys m ⟹∖√⟨ w ⟩ W → Σ[ s ∈ St ] (Steps m st₀ (unlbl w) s × W ≡ SysAt m s)` and `Steps⇒traces` (converse, for non-final intermediate states)
  - `unlbl : List (Event U) → List (Σ (AnyTypes Ev) proj₁)` (or state the lemmas over `Steps` labelled directly with `Event√`, whichever matches `GovernorWedge/Steps.agda`).

- [ ] **Step 1:** Copy the shape of `GovernorWedge/Steps.agda` (`Conn-br`, `Conn-ev-inv`, `Conn-ev-intro`, `Conn-no-τ`, `Conn-no-√`) for the single process `SysAt`, adding the `final` case: when `final s ≡ true` the tree is `ret tt` (only √); otherwise it is the `react` node.
- [ ] **Step 2:** Prove `traces⇒Steps` and `Steps⇒traces` by induction on the trace / on `Steps`.
- [ ] **Step 3:** Typecheck `agda HotDemotion/Lift.agda +RTS -M20G -RTS` — expected exit 0, no warnings.
- [ ] **Step 4:** Commit `Lift.agda` ("HotDemotion: process steps are exactly sstep moves").

---

### Task 3: D1 — pre-PR, no Leios load, Warm is unreachable

**Files:**
- Create: `HotDemotion/PrePR.agda`

**Interfaces:**
- Consumes: Tasks 1–2.
- Produces: `Pre : Bool → Bool → Mode` with `Pre b t = mode pre b t false true` (env flags for blocks/txReqs; no Leios load; timer on); `pre-noWarm`, `tmo-enabled`, `pre-endsCold`, `pre-nearlyWarm`.

Theorem statements (exact):

```agda
-- the LeiosNotify phase never reaches ready/fin while lnLoad is false (invariant on Steps)
pre-ln-stuck : ∀ {b t s w} → Steps (Pre b t) st₀ w s → ps s ln ≢ ready × ps s ln ≢ fin

-- D1: no trace of the pre-PR system contains warm
pre-noWarm : ∀ {b t w W} → Sys (Pre b t) ⟹∖√⟨ w ⟩ W → ¬ Any (_≡ GV-event warm) w

-- the timeout is always an escape while awaiting (Review Focus 2)
tmo-enabled : ∀ {m s w} → timer m ≡ true → Steps m st₀ w s → gph s ≡ awaiting
            → Σ[ s′ ∈ St ] (sstep (GAct , gov) tmo m s ≡ just s′)

-- D1, run form: every reachable state is either still hot/awaiting (and can still tmo → cold), timed out
-- (cold enabled), or Cold — never Warm
pre-endsCold : ∀ {b t w s} → Steps (Pre b t) st₀ w s → gph s ≢ warmD

-- vacuity guard (Review Focus 1): with blocks and txReqs on, the pre-PR system reaches a state that is
-- awaiting with every protocol but ln returned
pre-nearlyWarm : Σ[ w ∈ _ ] Σ[ s ∈ St ] (Steps (Pre true true) st₀ w s × gph s ≡ awaiting
                 × ps s cs ≡ fin × ps s bf ≡ fin × ps s tx ≡ fin × ps s lf ≡ fin)
```

(`GV-event warm` = the `Event U` underlying `GV warm`; use whatever `Lift.agda` fixes as the trace alphabet.)

- [ ] **Step 1:** State `pre-ln-stuck` and prove it by induction on `Steps`: the only moves changing `ln` are `env lnReply` (refused: `lnLoad` false), `int lnQuit/lnQuitDone` (refused: `intMove pre _ = nothing`) and `ret ln` (needs `ready`).
- [ ] **Step 2:** Derive `pre-endsCold` (a `warm` move needs `allFin`, false because of `ln`) and `pre-noWarm` via `traces⇒Steps`.
- [ ] **Step 3:** Prove `tmo-enabled` (direct from `sstep`'s `tmo` clause) and `pre-nearlyWarm` (explicit `Steps` witness: `demote`, `int bfDrain`, `env block`, `env txReq`, `ret cs`, `ret bf`, `ret tx`, `ret lf`).
- [ ] **Step 4:** Typecheck `agda HotDemotion/PrePR.agda +RTS -M20G -RTS`; expected exit 0.
- [ ] **Step 5:** Commit `PrePR.agda` ("HotDemotion: before PR 2344 demotion cannot end Warm").

---

### Task 4: D2 — post-PR, Warm is reachable and guaranteed

**Files:**
- Create: `HotDemotion/PostPR.agda`

**Interfaces:**
- Consumes: Tasks 1–2 (and `tmo-enabled` from Task 3 if useful).
- Produces: `Post : Bool → Bool → Bool → Mode` with `Post b t c = mode post b t false c`; `post-ln-noEnv`, `post-warmReachable` (D2a), `post-bounded`, `post-tight`, `post-warmLTL` (D2b).

Theorem statements:

```agda
-- post-PR LeiosNotify finishes without any env event (Review Focus 4)
post-ln-noEnv : ∀ {b t c} → Steps (Post b t c) (mkSt awaiting (afterTerm post)) (int-lnQuit ∷ int-lnQuitDone ∷ ret-ln ∷ []) _

-- D2a: from every reachable awaiting state, Warm is reachable using block, txReq and internal moves
post-warmReachable : ∀ {c w s} → Steps (Post true true c) st₀ w s → gph s ≡ awaiting
                   → Σ[ w′ ∈ _ ] Σ[ s′ ∈ St ] (Steps (Post true true c) s w′ s′ × gph s′ ≡ warmD)

-- bounded progress with the timeout removed: every run reaches √ (via warm) and has at most 12 events
post-bounded : DeadlockFree (Sys (Post true true false)) × DivergenceFree (Sys (Post true true false))
             × (∀ {w W} → Sys (Post true true false) ⟹∖√⟨ w ⟩ W → length w ≤ 12)

-- the bound is attained (Review Focus 5)
post-tight : Σ[ w ∈ _ ] Σ[ W ∈ Proc ] (Sys (Post true true false) ⟹∖√⟨ w ⟩ W × length w ≡ 12 × PTree.force W ≡ ret tt)

-- D2b (LTL): every maximal run of the timeout-free post-PR system reaches warm
post-warmLTL : (tr : Trace Rr (Sys (Post true true false))) → ◇ᵗ (atom WarmFired) tr
```

Notes for the executor:
- 12 = `demote` + `bfDrain` + `block` + `txReq` + `lnQuit` + `lnQuitDone` + 5 × `ret` + `warm`. If the model's rules make the true maximum different, prove the true number and explain in the comment (do not weaken to a loose bound).
- `DeadlockFree`/`DivergenceFree` come from `Semantics.Deadlock` / `Semantics.DivergenceFree`; the system has no τ (`Sys-no-τ`), so divergence freedom is immediate. Deadlock freedom: every non-final reachable state has an enabled move (a rank on `St` that decreases on every move; the bound follows from the rank).
- D2b: use `Semantics.LTL.Traces_Based` (`Trace`, `◇ᵗ`, `atom`, `FramePred`) exactly as `Cardano_network/Parametric/Leios/LeiosNotifyQuitLive.agda` does (`Ended`, `quit-live-sys`). Define `WarmFired` as the frame predicate that holds at a `warm` step. The DESIGN's fairness assumptions for `block`/`txReq` are vacuous here because the environment is always willing when the flag is set (same finding as `quit-live-sys`); say so in the comment. The imported `Traces_Based` carries two library postulates; do not use them, and record that in the README.

- [ ] **Step 1:** Prove `post-ln-noEnv` by computation (`more refl …`).
- [ ] **Step 2:** Define a rank `rk : St → ℕ` (governor 0/1 for demote, warm pending; per protocol: phases to `fin`) and prove `rk-dec : sstep at a (Post true true false) s ≡ just s′ → rk s′ < rk s`, plus `prog : final s ≡ false → reachable s → Σ … sstep … ≡ just _`.
- [ ] **Step 3:** Derive `post-warmReachable` and `post-bounded` from the rank and `Lift`.
- [ ] **Step 4:** Prove `post-tight` with the explicit 12-event trace.
- [ ] **Step 5:** Prove `post-warmLTL`.
- [ ] **Step 6:** Typecheck `agda HotDemotion/PostPR.agda +RTS -M20G -RTS`; expected exit 0, no warnings.
- [ ] **Step 7:** Commit `PostPR.agda` ("HotDemotion: after PR 2344 demotion ends Warm").

---

### Task 5: D3/D4 — remaining blockers and the contrast; README

**Files:**
- Create: `HotDemotion/Blockers.agda`, `HotDemotion/README.md`

**Interfaces:**
- Consumes: Tasks 1–4.

Theorem statements:

```agda
-- D3: post-PR, a remote that never sends a blocking request makes Warm unreachable
post-noTxReq-noWarm : ∀ {b c w s} → Steps (Post b false c) st₀ w s → gph s ≢ warmD

-- D3: post-PR, no Praos block during the wait makes Warm unreachable
post-noBlock-noWarm : ∀ {t c w s} → Steps (Post false t c) st₀ w s → gph s ≢ warmD

-- vacuity guards: in each case every other protocol can still return
post-noTxReq-nearlyWarm : Σ … (Steps (Post true false true) st₀ w s × gph s ≡ awaiting × ps s cs ≡ fin × ps s ln ≡ fin × …)
post-noBlock-nearlyWarm : Σ … (Steps (Post false true true) st₀ w s × gph s ≡ awaiting × ps s tx ≡ fin × ps s ln ≡ fin × …)

-- D4: same environment (blocks and txReqs on, no Leios load), before vs after
contrast : (∀ {w s} → Steps (Pre true true) st₀ w s → gph s ≢ warmD)
         × ((tr : Trace Rr (Sys (Post true true false))) → ◇ᵗ (atom WarmFired) tr)
```

- [ ] **Step 1:** Prove the D3 invariants (as `pre-ln-stuck`, for `tx` resp. `cs`) and the two vacuity witnesses.
- [ ] **Step 2:** Prove `contrast` by pairing `pre-endsCold` and `post-warmLTL`.
- [ ] **Step 3:** Write `HotDemotion/README.md`: what is modelled (DESIGN §3–4), assumptions (untimed: `tmo` is a free choice; env flags; LeiosNotify abstractions justified by `LeiosNotifyQuit.blk-stall` and `LeiosNotifyPipelinedProps.pblk-afterQuit` in comments only), the theorem index with `file:line`, reproduction commands, axioms (none used; `Traces_Based` postulates imported but unused), and the finding list (LeiosNotify pre-PR always forces Cold; TxSubmission2 and long block gaps still can; ChainSync limit 601–911 s > 300 s and the stale `Pol:27-28` comment).
- [ ] **Step 4:** Typecheck `agda HotDemotion/Blockers.agda +RTS -M20G -RTS`; grep all `HotDemotion/*.agda` for `postulate|TERMINATING|mutual|Sized`; expected exit 0 and no hits.
- [ ] **Step 5:** Commit `Blockers.agda` and `README.md` ("HotDemotion: remaining blockers and before/after contrast").

---

## Self-review

- Spec coverage: §3 events → Task 1; §4 processes → Task 1 (monolithic product `sstep`, documented as the ∥ of §4); D1 → Task 3; D2a/D2b → Task 4; D3/D4 → Task 5; §6 layout → File Structure (adds `Lift.agda` for the process correspondence, as `GovernorWedge/Steps.agda`); §7 → each task's typecheck step; §8 open points stay open (README).
- Deviation from DESIGN §4 recorded: the composition is the synchronous product step function, not a `Par⊤` of separate processes; same traces by construction, far cheaper proofs (the `GovernorWedge` pattern). D2b's fairness becomes vacuous; recorded in the comment and README.
- Names used across tasks: `Mode`/`mode`, `St`/`mkSt`, `ps`, `gph`, `st₀`, `afterTerm`, `sstep`, `Steps`, `SysAt`, `Sys`, `GV`/`RT`/`EV`/`IN`, `Pre`, `Post`, `WarmFired` — consistent.
