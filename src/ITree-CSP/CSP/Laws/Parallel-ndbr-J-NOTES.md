# `∥-⊓` distributivity in `Parallel.agda` — status and the `ndbr-J` frontier

Working notes for picking up the remaining postulates in `src/CSP/Laws/Parallel.agda`.
Covers the two distributivity laws and, in detail, the `ndbr|ndbr` "J-merge"
cases that remain postulated. Self-contained; read this before re-attacking them.

## Where things stand

Both laws are real, structured DRWbisim (`≈`) proofs:

- `∥-⊓-distrib-R : P ∥ (Q⊓R') ≈ (P∥Q) ⊓ (P∥R')` — case-splits the LHS step on `force P`.
- `∥-⊓-distrib-L : (P⊓Q) ∥ R' ≈ (P∥R') ⊓ (Q∥R')` — mirror, case-splits on `force R'`.

Fully proven (no pragma): the `sil`, `ret`, `vis` simulation cases (`*-stable-ret`,
`*-stable-vis`, the `fwd-on-tau` dispatchers), the assembly, and all the
"impossible-branch" discharges in `*-fwd-on-{ret,vis}` (incl. `sMixVis`).

`{-# NON_TERMINATING #-}` but real proofs: `distrib-{R,L}-bwd-on-tau`
(genuine τ-chain self-recursion on the forced child) and `∥-sil-R-absorb`
(`force R' ≡ sil R'' → (X ∥ R') ≈ (X ∥ R'')`).

### Remaining trusted surface — 12 postulates (6 per direction)

```
distrib-{R,L}-fwd-on-tau-ndbr-J            -- force of non-choice operand = ndbr
distrib-{R,L}-fwd-on-tau-stable-mix        -- force of non-choice operand = mix
distrib-{R,L}-bwd-on-tau-ndbr-J-zero       -- RHS picked the P∥… / left branch
distrib-{R,L}-bwd-on-tau-ndbr-J-suc        -- RHS picked the …∥… / right branch
distrib-{R,L}-bwd-on-tau-stable-mix-fzero
distrib-{R,L}-bwd-on-tau-stable-mix-fsucfzero
```

These are exactly the cases where the *non-choice* operand's `force` is itself
`ndbr` or `mix`, so the parallel operator takes its `ndbr|ndbr` merge clause
(`mergeNdbr'`) or a `mix` clause. They are identical in shape for R and L.

## Important correction: there is **no reduction wall**

An earlier hypothesis — that the operator's `force` cannot reduce the `ndbr|ndbr`
clause — was a **misdiagnosis**. The operator *does* reduce it:
`force (P ∥ (Q⊓R')) ≡ ndbr g wi wa pr` is provable by `refl` when you match the
matched operand as `ndbr _ (_ , _) _ _` (destructure the witness pair so the
clause's `(AP , iP)` pattern fires). The real blocker in the failed attempts was
an **implicit `{P}`** in the head-unfolding lemmas, which blocks the
`with ITree.force P` abstraction ("blocked on `_P…`" / unsolved metas).

**Recipe that works** (already used to close the `absurd : ⊥` cases):
- Make the operand **explicit** in any `force`-unfolding lemma. See the proven
  `force-∥R-ndbr-eq`, `force-∥R-mix-eq`, `force-∥R-notmix` and the L mirrors.
- Use the aux-style `aux (ITree.force …) refl` case-split (it substitutes), **not**
  `inspect` (which keeps the scrutinee abstract, so `force LHS` stays stuck).
- Gotcha: matching `force (Q⊓R')` in a `with` raises a `CoverageIssue` (Agda
  wants all five `NodeKind` cases). Don't match it — rely on its definitional `ndbr`.

So the `ndbr-J` cases are *approachable* (you can compute `force LHS`). The
difficulty is mathematical, not reduction.

## Detailed scoping — forward `distrib-R-fwd-on-tau-ndbr-J`

Setup: `force P ≡ ndbr fP wiP waP wpP`. `LHS = P ∥ (Q⊓R')`, `RHS = (P∥Q) ⊓ (P∥R')`.
A τ-step out of LHS picks a **pair** index `(aP, aQ)`; `mergeNdbr'` (see
`CSP/Definitions/Parallel.agda:147`) gives `t'` by cases on
`(fP (…) aP , br2 Q R' (…) aQ)` — recall `br2 Q R'` returns `just Q` at
`lift fzero`, `just R'` at `lift (fsuc fzero)`, else `nothing`:

| case | `(fP aP , br2 aQ)`        | `t'`           | difficulty |
|------|--------------------------|----------------|------------|
| A    | `(just P' , Q)`          | `P' ∥ Q`       | **hard**   |
| B    | `(just P' , R')`         | `P' ∥ R'`      | **hard**   |
| C    | `(just P' , nothing)`    | `P' ∥ (Q⊓R')`  | medium     |
| D    | `(nothing , Q)`          | `P  ∥ Q`       | trivial    |
| E    | `(nothing , R')`         | `P  ∥ R'`      | trivial    |
| F    | `(nothing , nothing)`    | — (`nothing`)  | absurd     |

- **D / E (trivial):** `RHS` does one τ via `br2` to `P∥Q` (resp. `P∥R'`), and
  `t' ≈ u'` by `drwbisim-refl`. No analysis of `Q`/`R'` needed.
- **F:** `mergeNdbr' = nothing` contradicts `… ≡ just t'`; `case … of λ ()`.
- **C (medium):** `t' = P'∥(Q⊓R')`. Close by corecursion: `∥-⊓-distrib-R P'`
  gives `P'∥(Q⊓R') ≈ (P'∥Q)⊓(P'∥R')`, then bridge to `RHS = (P∥Q)⊓(P∥R')`.
  The bridge needs `P'∥Q ≈ P∥Q` etc., i.e. "P stepped via its `ndbr`" — same
  obstruction as A/B below.
- **A / B (hard):** `t' = P'∥Q`. To match, `RHS` picks `P∥Q`, then we need
  `(P∥Q) ═[τ]═► (≈ P'∥Q)` — i.e. **P performs its own `ndbr`-step *inside* the
  parallel**, for arbitrary `Q`. Call this `par-ndbrL`. It holds for:
  - `force Q = ret` / `vis`: `force (P∥Q)` is `ndbr` distributing P's branches
    (`ndbr|ret`/`ndbr|vis` clauses) ⇒ one τ-step to `P'∥Q`. ✓
  - `force Q = sil Q_`: `force (P∥Q) = sil (P∥Q_)`; recurse on `Q_`
    (`NON_TERMINATING`), bridge `P'∥Q ≈ P'∥Q_` via `∥-sil-R-absorb`. ✓
  - **`force Q = ndbr` / `mix` with no `nothing` branch: FAILS.** The merge
    couples every P-move to a Q-move, so `P'∥Q` is not directly reachable; the
    only successors are `P'∥Q''`. Relating `P'∥Q` to those needs full
    bisimulation reasoning, not a finite step. **This is the crux.**

Backward (`-ndbr-J-zero/-suc`) is the dual: `RHS` picks a branch (`P∥Q` / `P∥R'`)
and we must show `LHS = P ∥ (Q⊓R')` weakly reaches `≈` that branch — same
`par-ndbr` obstruction. The `mix` cases are analogous with the slide clauses.

## Verdict

`ndbr-J` is the **genuine hard mathematical core** of these laws (which is why the
original author postulated it). Cases D/E/F are trivial, C is corecursion, but
A/B require a parallel-step lemma that **fails when the non-choice operand is
`ndbr`/`mix`** without a `nothing` branch.

Closing A/B/C properly needs infrastructure that **does not exist in the repo**:

- a **`∥`-congruence for DRWbisim**, `Y ≈ Y' → (X ∥ Y) ≈ (X ∥ Y')` (and the
  symmetric left version), plus
- **divergence-aware** lemmas (e.g. relating `P∥Q` and `P'∥Q` when `Q` diverges,
  via the DR-weak-bisim divergence clauses).

That is itself a fresh major proof, comparable to a new development — not a small
patch. Building `∥`-congruence first is the right framing if/when this is picked up.

### Cheaper-but-low-value alternative

One could convert each `*-ndbr-J*` postulate into a real function that closes
D/E/F and postulates only A/B/C (narrowing the trusted statement). Not
recommended: it still needs the full ~100-line merge case-split scaffold per
postulate (with arity-unification fiddliness), and leaves the hard A/B/C content
trusted anyway — modest trust reduction for substantial effort.

## Starting points for whoever picks this up

1. Read `CSP/Definitions/Parallel.agda` lines ~44–166 (the operator clauses,
   esp. `ndbr|ndbr` at 147 and the surrounding `ndbr|ret`/`ndbr|vis`).
2. Reuse the proven, explicit-operand head lemmas as templates:
   `force-∥{R,L}-ndbr-eq`, `force-∥{R,L}-mix-eq`, `force-∥{R,L}-notmix`,
   `force-∥-sil-{L,R}`, `force-∥{R,L}-ret`, `force-∥{R,L}-vis`.
3. The trace lemmas `Interleave-trace-aux` / `Parallel-trace-aux` already do a
   full `ndbr|ndbr` *pair-index* case-split (search for `pair` and `mergeNdbr'`);
   mirror that machinery for the merge decomposition.
4. First build `∥`-congruence (`par-ndbrL`/`par-ndbrR` step lemmas, then full
   congruence). Without it, A/B cannot close.
5. `∥-sil-R-absorb` (already proven) is the template for the `NON_TERMINATING`
   sil-chain recursion you'll need on the non-choice operand.
