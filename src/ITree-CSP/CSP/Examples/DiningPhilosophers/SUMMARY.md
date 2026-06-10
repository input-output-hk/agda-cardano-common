# Dining Philosophers in CSP (Interaction Trees, Agda)

This folder formalises the Dining Philosophers problem over the native CSP
operators built on coinductive interaction trees, and proves both that the
**symmetric** system can **deadlock** and that the **asymmetric** system is
**deadlock-free**. All proofs are closed: no `postulate`, no holes (`{! !}`),
no `trustMe`, no `TODO`.

## Files in this folder

| File | Module | Role |
|---|---|---|
| `DiningPhilosophers.lagda.md`                  | `…DiningPhilosophers`                          | Relational (LTS-level) version of the example |
| `DiningPhilosophersCSP.lagda.md`               | `…DiningPhilosophersCSP`                        | Event type `DP`, and the `PHIL` / `FORK` processes |
| `DiningPhilosophersCSP_SystemP.lagda.md`       | `…DiningPhilosophersCSP_SystemP`                | `SYSTEM′` composition; symmetric & asymmetric configs |
| `DiningPhilosophersCSP_SystemP_Deadlock.agda`  | `…_Deadlock`                                    | `HasDeadlock SYSTEM′sym` (the symmetric deadlock) |
| `DiningPhilosophersCSP_SystemP_Traces.agda`    | `…_Traces`                                      | Trace-level lemmas |
| `DiningPhilosophersCSP_SystemP_States.agda`    | `…_States`                                      | Per-component FSM states |
| `DiningPhilosophersCSP_SystemP_SysStates.agda` | `…_SysStates`                                   | `ValidCfg` invariant + reachability bridge `SYSTEM′-valid` |
| `DiningPhilosophersCSP_SystemP_Progress.agda`  | `…_Progress`                                    | Progress / resource-ordering argument |
| `DiningPhilosophersCSP_SystemP_DeadlockFree.agda` | `…_DeadlockFree`                             | `DeadlockFree SYSTEM′asym` (the asymmetric result) |

(All modules are under the prefix `CSP.Examples.DiningPhilosophers.`)

## 1. The model

**Events.** A ring of `n = 2 + m` philosophers and forks
(`Phil = Fork = Fin n`), with two channels:

```agda
data DP : Set → Set where
  picks    : Phil → Fork → DP ⊤
  putsdown : Phil → Fork → DP ⊤
```

**Components** (`DiningPhilosophersCSP.lagda.md`):

```agda
PHIL first second i =
  loop0 ( picks i (first i)  ⟶₀ picks i (second i)  ⟶₀
          putsdown i (second i) ⟶₀ putsdown i (first i) ⟶₀ Skip )

FORK j =
  loop0 ( (picks j j      ⟶₀ putsdown j j      ⟶₀ Skip)
        □ (picks (j ⊖1) j ⟶₀ putsdown (j ⊖1) j ⟶₀ Skip) )
```

- `PHIL` picks two forks in order (`first`, then `second`), eats, then puts
  them down in reverse — looping forever via `loop0`.
- `FORK j` offers an **external choice** (`□`) between its own philosopher `j`
  and neighbour `j ⊖1`. It is a one-at-a-time mutual-exclusion lock.

**System composition** (`DiningPhilosophersCSP_SystemP.lagda.md`):

```agda
SYSTEM′ first second = PHILS first second ∥⇘ syncAll ¿ syncAll-dec ⇙ FORKS
```

where `PHILS = ⦀list (map PHIL allPhils)` and `FORKS = ⦀list (map FORK allPhils)`
are pure **interleavings** (`⦀`), and the two blocks are joined by a
**full-synchronisation parallel** (`∥⇘ syncAll ⇙`): every `picks`/`putsdown`
event must be agreed by both a philosopher and the relevant fork.

**Two configurations decide the outcome:**

| Config | `first i` / `second i` | Result |
|---|---|---|
| **Symmetric** `SYSTEM′sym`  | `i` / `i ⊕1` (all grab left first) | **deadlocks** |
| **Asymmetric** `SYSTEM′asym` | philosopher 0 flips order           | **deadlock-free** |

```agda
asymFirst  i = if ⌊ i ≟ fzero ⌋ then i ⊕1 else i
asymSecond i = if ⌊ i ≟ fzero ⌋ then i    else i ⊕1
```

Philosopher 0 grabs its *right* fork first; everyone else grabs *left* first —
breaking the circular wait.

## 2. What deadlock means

From `ITree_Relations/Deadlock.agda`:

```agda
DeadlockFree t = ∀ {s t′} → t ═⟨ s ⟩═► t′ → IsStuck t′ → ⊥
HasDeadlock t  = ∃ reachable t′ with IsStuck t′
```

`═⟨ s ⟩═►` is the τ-absorbing big-step reachability; `IsStuck` means no LTS
label is enabled **and** the state has not successfully terminated (successful
termination is *not* deadlock). So deadlock-freedom = no reachable state is
stuck.

## 3. Proving deadlock (symmetric system)

`DiningPhilosophersCSP_SystemP_Deadlock.agda`:

```agda
philosophers-deadlock′ : HasDeadlock SYSTEM′sym
philosophers-deadlock′ = _ , _ , deadlock-reachable , deadlock-stuck

¬deadlock-free′ : ¬ DeadlockFree SYSTEM′sym
¬deadlock-free′ = hasDeadlock⇒¬deadlockFree philosophers-deadlock′
```

**Witness state:** after the trace `picksTrace allPhils` (each philosopher takes
its left fork exactly once):

```agda
deadlock-reachable :
  SYSTEM′sym ═⟨ map evl (picksTrace allPhils) ⟩═►
    (PHILS′ ∥⇘ syncAll ¿ syncAll-dec ⇙ FORKS′)
```

Two parts:

1. **Reachability** — `phils-chain` / `forks-chain` show each block fires all
   `n` left-picks **τ-free**, and `combine-sync` merges them through the
   full-sync parallel (both sides must agree on each event).
2. **Stuckness** — `∥⇘-full-stuck` reduces "stuck" to *disjoint offers*: at
   every event at least one side refuses it.

```agda
disjoint-offers (_ , picks i f)    a = inj₂ (FORKS′-refuses …)  -- forks now only offer putsdown
disjoint-offers (_ , putsdown i f) a = inj₁ (PHILS′-refuses …)  -- phils now only want their 2nd pick
```

Every philosopher holds its left fork and wants its right (a `picks`); every
fork is taken and only offers `putsdown`. The offer sets are disjoint ⇒ no
synchronisation ⇒ stuck. Sanity-checked by elaborating at `m = 0` (n = 2).

## 4. Proving deadlock-freedom (asymmetric system)

`DiningPhilosophersCSP_SystemP_DeadlockFree.agda`:

```agda
deadlock-free-asym : DeadlockFree SYSTEM′asym
deadlock-free-asym bs stuck with SYSTEM′-valid asym-fs≢ bs
... | (cfg , refl , V) = asym-no-deadlock V stuck
```

The proof is two layers (not a state-space enumeration):

**Bridge — `SYSTEM′-valid` (`…_SysStates`).** Every reachable state of `SYSTEM′`
is shown equal to some `sysState f s cfg` satisfying a `ValidCfg` invariant.
`cfg` records each philosopher's FSM position
(`think → held1 → held2 → down1 → reloop`) and each fork's
(`free → heldOwn/heldNbr → reloop`), with consistency: each held fork has
exactly one owner. This collapses the coinductive tree into a finite symbolic
configuration.

**Progress — `enabled⇒¬stuck` + resource ordering (`…_Progress`).**

```agda
enabled⇒¬stuck : ValidCfg cfg → EnabledCfg f s cfg → ¬ IsStuck (sysState f s cfg)
```

Then `no-deadlock-cfg` shows *every* valid asymmetric config is enabled, via a
**resource-ordering / Dijkstra argument** rather than brute force:

```agda
no-deadlock-cfg rank (ra : ∀ i → rank (f i) < rank (s i)) … V =
  enabled⇒¬stuck V (enabledCfg rank ra fown sown V)
```

The asymmetric `first` / `second` admit a `rank : Fork → ℕ` with
`rank (first i) < rank (second i)` for **all** `i`. Case analysis on a
reachable config:

- a philosopher at `held2` / `down1` can `putsdown` (a visible step);
- a component at `reloop` has a τ-step available;
- otherwise (everyone waiting) `scan` / `maxHeld` finds the holder of the
  highest-rank fork — its next fork is necessarily free or held by a strictly
  lower-rank holder, so it can always advance. The highest-rank holder never
  waits ⇒ no circular wait ⇒ the config is enabled, hence not stuck.

## 5. Proof hygiene

Verified: no `postulate`, no holes `{! !}`, no `trustMe`, no `TODO` across all
files in this folder. Uses of `⊥-elim` are legitimate refutations of
unreachable cases. Both the symmetric (`HasDeadlock`) and asymmetric
(`DeadlockFree`) results are genuine end-to-end Agda proofs over the native CSP
operators (`⦀`, `∥⇘…⇙`, `□`, `⟶₀`, `loop0`).
