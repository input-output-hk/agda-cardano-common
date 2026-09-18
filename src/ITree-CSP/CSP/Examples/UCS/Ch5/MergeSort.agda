{-# OPTIONS --guardedness #-}

-- UCS chapter 5: mergesort — the recursive, dynamically-growing merge-sort network
-- (mergesort.csp, A.W. Roscoe; source fdr-examples/ucs/chapter05/mergesort.csp).
--
--     M     = in.end -> out.end -> M  []  in?x:T -> M1(x)
--     M1(x) = in.end -> out!x -> out.end -> M
--             []  in?y:T -> (((upto!x -> downto!y -> Mu)
--                             [upto <-> in, upfrom <-> out] M)
--                             [downto <-> in, downfrom <-> out] M)
--     Mu = in.end -> upto.end -> downto.end -> O1  []  in?x:T -> upto.x -> Md
--     Md = in.end -> upto.end -> downto.end -> O1  []  in?x:T -> downto.x -> Mu
--     O1 = upfrom?x -> downfrom?y -> O2(x,y)
--     O2(x,y) = the guarded four-way merge (both-end / one-end / compare `x < y`)
--
-- MODEL-ONLY, and the source itself says why: its first line reads "This is an
-- infinite state process that will not run on FDR, but it will on ProBE", and the
-- file contains NO FDR `assert` at all.  So — exactly as in the sibling
-- `CSP.Examples.UCS.Ch7.Counter` — we only certify that the processes are
-- well-defined (productive) process trees and exhibit transition sanity checks,
-- with NO FD/refinement theorem.  There is nothing to refine against: Roscoe gives
-- no specification for this network at this point in the book.
--
-- DATA DOMAIN, REDUCED (and why the reduction is structure-preserving).  The source
-- takes `T = {0..10}` and encodes the end-of-list marker as `end = -1`, remarking
-- "could have used constructed datatypes instead".  We take that up:
--   * `Val` = {v0, v1} — a TWO-element sorted type.  What the network turns on is
--     (a) the marker's distinctness from data, (b) the `x < y` comparison in `O2`,
--     (c) `O2`'s four guards.  Two values already make `_<V_` non-trivial in both
--     directions (`v0 <V v1` holds, `v1 <V v0` does not) — see `o2-lt` / `o2-ge`
--     (§B.5), and both outcomes are reached by whole-network runs (§B.3, §B.4) — so
--     nothing the model turns on is lost; eleven values would only multiply the case
--     enumeration.  (`Ch5.NCopy` / `Ch5.NCopyL` reduce the same `T` to `Bool`.)
--   * `Val′ = dat Val | end` — the marker is a REAL constructor, not a sentinel
--     integer, so `end`'s distinctness from every datum is a type-level fact rather
--     than an arithmetic side condition.  This is the source's own suggestion.
-- All six channels and all thirteen controller states are present, unreduced.
--
-- LINK PARALLEL, TWO PAIRS (the construction under test).  Link parallel is not an
-- operator of this development; it is derived, as in `Ch5.NCopyL`: relabel the linked
-- channels onto shared ones, parallel-compose synchronising on them, hide them.
-- `mergesort.csp` needs the TWO-PAIR form `[a <-> b, c <-> d]`, twice over, so the
-- two link channel-pairs must stay distinct — but, contrary to the textbook
-- derivation, only ONE operand needs relabelling per link.  The controller already
-- owns four pairwise-distinct link channels (`upto`/`upfrom` for the upper sub-net,
-- `downto`/`downfrom` for the lower), so we let the links BE those channels and
-- relabel only the sub-net: `in ↦ upto`, `out ↦ upfrom` (resp. `downto`/`downfrom`).
-- The composite's external interface is then LITERALLY Roscoe's — `{in, out}`, since
-- all four link channels are hidden — so, unlike `Ch5.NCopyL`'s alphabet shift, not
-- even an injective-relabelling caveat is needed.  `_[up↔]_` / `_[dn↔]_` (§A.5) are
-- each a genuine rename-parallel-hide term and `Net` (§A.7) composes the two exactly
-- as the source's two nested link parallels do; `M1c`'s second branch is `Net` applied
-- to the sub-processes, i.e. the link parallel is NOT inlined away.
--
-- PRODUCTIVITY, AND THE ONE DEVIATION FROM ROSCOE (a DEPTH BUDGET).  `M1`'s
-- continuation mentions `M` twice, UNDER the link parallels, i.e. the recursion runs
-- through CSP operators.  `--guardedness` rejects that, and three formulations were
-- measured here (all three: `TerminationIssue` from Agda 2.8.0), extending the
-- nine attempts recorded in `Ch7.Throw`'s header and the two in `Ch7.Resettable`'s:
--   (i)   `force P = react (λ … → just (P ∖ H)) ∅t` — a corecursive occurrence that is
--         an ARGUMENT of any function application (`∖`, `∥⇘⇙`, `renameInv`, or a
--         clique-internal stand-in) is not guarded, however many constructors sit
--         outside that application.  (A corecursive occurrence inside a LAMBDA passed
--         to a function — e.g. under `case_of_` — is fine; that is the difference.)
--   (ii)  network shape as an inductive `Net`, interpreted by one `⟦_⟧` whose leaf
--         clauses are guarded and whose `node` clause recurses on the structurally
--         SMALLER sub-nets: rejected, because Agda accepts no clique that MIXES
--         guarded corecursion with structural recursion — it needs one measure, and
--         the guarded calls grow the net while the structural calls shrink it.
--   (iii) the same with `force` copatterns on the leaf clauses and a plain clause for
--         `node`: rejected, and strictly worse — mixing copattern and non-copattern
--         clauses in one definition loses guardedness for ALL of them.
-- So the network is built the way `Ch7.Counter` builds its counter — the solution is
-- CONSTRUCTED EXPLICITLY as a self-contained family — but here the fix is to make the
-- sprouted sub-process a PARAMETER rather than a corecursive occurrence: `Mc S` is
-- Roscoe's `M` with `S` supplied as the process each sprouted half-list is fed to
-- (§A.7), a clique whose every corecursive call sits directly under `just`, hence
-- productive.  `Msort n` (§A.8) then ties the knot to depth `n` by ordinary
-- STRUCTURAL recursion on `n`, outside the corecursive clique: `Msort (suc n) =
-- Mc (Msort n)`, i.e. literally Roscoe's equation with the child one budget lower,
-- and `Msort zero = Mc Stop`, a cell that cannot sprout.
--
-- This is the module's ONLY deviation from the source, and it is a TRUNCATION, not a
-- distortion: the budget is spent only by the `in?y` sprout, so `Msort n` agrees with
-- Roscoe's `M` on every behaviour of recursion depth ≤ n and can otherwise only
-- REFUSE (the deepest child is `Stop`) — never mis-sort.  `Msort` is the standard
-- finite-approximation presentation of the unique solution of Roscoe's equations, and
-- it is what a lazy explorer such as ProBE (the only tool the source claims to run on)
-- actually explores.  Because the checks in §B are stated for `Mc S` / `Mc (Mc S)`
-- with `S` UNIVERSALLY QUANTIFIED, each of them holds at EVERY budget `Msort (suc n)`
-- at once, and none of them relies on the truncation.  The unbounded `M` itself is not
-- definable here without sized types, `NON_TERMINATING`, a postulate, or inlining the
-- link parallel away — all four excluded.
--
-- No `postulate`, no `NON_TERMINATING`/`TERMINATING`, no sized types, no holes.

module CSP.Examples.UCS.Ch5.MergeSort where

open import Level renaming (zero to lzero)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

------------------------------------------------------------------------------------
-- §A. Model.
------------------------------------------------------------------------------------

-- §A.1 the sorted type `T` (reduced to two elements) and its `<` comparison.
data Val : Set where
  v0 v1 : Val

-- `T'` = T ∪ {end}: the end-of-list marker as a constructor, not the source's `-1`.
data Val′ : Set where
  dat : Val → Val′
  end : Val′

-- the order on `T` that `O2`'s fourth guard tests (`x < y`)
_<V_ : Val → Val → Bool
v0 <V v1 = true
v0 <V v0 = false
v1 <V _  = false

-- decidable equality on `T'` (used to PIN outputs: `out!x`, `upto!x`, `downto!y`)
_≟V′_ : (x y : Val′) → Dec (x ≡ y)
dat v0 ≟V′ dat v0 = yes refl
dat v1 ≟V′ dat v1 = yes refl
dat v0 ≟V′ dat v1 = no λ ()
dat v1 ≟V′ dat v0 = no λ ()
dat _  ≟V′ end    = no λ ()
end    ≟V′ dat _  = no λ ()
end    ≟V′ end    = yes refl

-- §A.2 the six channels of `channel in,out,upto,downto,upfrom,downfrom : T'`.
data Ch : Set where
  cin cout cupto cdownto cupfrom cdownfrom : Ch

-- one event constructor carrying (channel , value) — cf. `Ch5.NCopy`'s `NEv`
data MEv : Set → Set where
  c : MEv (Ch × Val′)

-- the type carried by `c`, named so event/label expressions stay short
Cv : Set
Cv = Ch × Val′

-- decidable equality on the (single-inhabitant) event sort
MEv-≟ : (x y : AnyTypes MEv) → Dec (x ≡ y)
MEv-≟ (_ , c) (_ , c) = yes refl

open import CSP.Operators MEv-≟
open EventSet

-- the CSP process type of this example
MProc : Set₁
MProc = PTree MEv (ExtI MEv) (⊤poly {lzero})

-- §A.3 the two link channel-sets, one per link pair (each is synchronised on, then
-- hidden).  L1 = {upto, upfrom} links the controller to the UPPER sub-net;
-- L2 = {downto, downfrom} links it to the LOWER one.
L1 L2 : EventSet
L1 .mem (_ , c) (cin       , _) = ⊥
L1 .mem (_ , c) (cout      , _) = ⊥
L1 .mem (_ , c) (cupto     , _) = ⊤poly {lzero}
L1 .mem (_ , c) (cdownto   , _) = ⊥
L1 .mem (_ , c) (cupfrom   , _) = ⊤poly {lzero}
L1 .mem (_ , c) (cdownfrom , _) = ⊥
L1 .dec (_ , c) (cin       , _) = no (λ z → z)
L1 .dec (_ , c) (cout      , _) = no (λ z → z)
L1 .dec (_ , c) (cupto     , _) = yes tt
L1 .dec (_ , c) (cdownto   , _) = no (λ z → z)
L1 .dec (_ , c) (cupfrom   , _) = yes tt
L1 .dec (_ , c) (cdownfrom , _) = no (λ z → z)
L2 .mem (_ , c) (cin       , _) = ⊥
L2 .mem (_ , c) (cout      , _) = ⊥
L2 .mem (_ , c) (cupto     , _) = ⊥
L2 .mem (_ , c) (cdownto   , _) = ⊤poly {lzero}
L2 .mem (_ , c) (cupfrom   , _) = ⊥
L2 .mem (_ , c) (cdownfrom , _) = ⊤poly {lzero}
L2 .dec (_ , c) (cin       , _) = no (λ z → z)
L2 .dec (_ , c) (cout      , _) = no (λ z → z)
L2 .dec (_ , c) (cupto     , _) = no (λ z → z)
L2 .dec (_ , c) (cdownto   , _) = yes tt
L2 .dec (_ , c) (cupfrom   , _) = no (λ z → z)
L2 .dec (_ , c) (cdownfrom , _) = yes tt

-- the same-alphabet injective renaming instance (identity event injection); the
-- relabelling is value-level (the channel lives in `c`'s carried value), so it is
-- supplied as a target→source preimage map, exactly as in `Ch5.NCopyL`
open import CSP.Rename {E₁ = MEv} {E₂ = MEv} (λ e → e) (λ e → just e) (λ _ → refl)
  using (ConcEvent₁; invPreimg)
open import CSP.Laws.Traces.TraceLawsRename {E = MEv} using (_⟦_⟧ⁱ; ren-ev-fwd)

-- §A.4 the two link relabellings, each applied to ONE operand (the sub-net).
-- `upInv`: the upper sub-net's `in` is driven from `upto` and its `out` read as
-- `upfrom`; every other target channel has no source, i.e. is blocked.
upInv : (bt : AnyTypes MEv) → proj₁ bt → Maybe ConcEvent₁
upInv (_ , c) (cupto     , w) = just ((_ , c) , (cin  , w))
upInv (_ , c) (cupfrom   , w) = just ((_ , c) , (cout , w))
upInv (_ , c) (cin       , _) = nothing
upInv (_ , c) (cout      , _) = nothing
upInv (_ , c) (cdownto   , _) = nothing
upInv (_ , c) (cdownfrom , _) = nothing

-- `dnInv`: likewise for the lower sub-net, via `downto`/`downfrom`.
dnInv : (bt : AnyTypes MEv) → proj₁ bt → Maybe ConcEvent₁
dnInv (_ , c) (cdownto   , w) = just ((_ , c) , (cin  , w))
dnInv (_ , c) (cdownfrom , w) = just ((_ , c) , (cout , w))
dnInv (_ , c) (cin       , _) = nothing
dnInv (_ , c) (cout      , _) = nothing
dnInv (_ , c) (cupto     , _) = nothing
dnInv (_ , c) (cupfrom   , _) = nothing

-- §A.5 LINK PARALLEL (derived, local — no shared module is touched).
-- `P [up↔] Q` is Roscoe's `P [upto <-> in, upfrom <-> out] Q`: relabel Q's `in`/`out`
-- onto the link channels `upto`/`upfrom`, parallel-compose synchronising exactly on
-- the link set L1, and hide L1.  BOTH link pairs of this operator are carried by the
-- one rename, which is what makes the two-pair form no dearer than `Ch5.NCopyL`'s
-- one-pair form.
_[up↔]_ : MProc → MProc → MProc
P [up↔] Q = (P ∥⇘ L1 ⇙ (Q ⟦ upInv ⟧ⁱ)) ∖ L1

-- `P [dn↔] Q` = `P [downto <-> in, downfrom <-> out] Q`, the second link parallel.
_[dn↔]_ : MProc → MProc → MProc
P [dn↔] Q = (P ∥⇘ L2 ⇙ (Q ⟦ dnInv ⟧ⁱ)) ∖ L2

-- §A.6 the controller states: the `upto!x -> downto!y -> Mu` head of `M1`'s second
-- branch, the distributor `Mu`/`Md`, and the merger `O1`/`O2`.  (Prefix and external
-- choice are spelled as raw `react` nodes: the controller is not the construction
-- under test, and a corecursion through `⟶`/`□` would hit the guardedness wall.)
data CSt : Set where
  sndU : Val → Val → CSt      -- upto!x -> downto!y -> Mu
  sndD : Val → CSt            -- downto!y -> Mu
  mu   : CSt                  -- Mu
  md   : CSt                  -- Md
  upU  : Val → CSt            -- upto.x -> Md      (Mu after in?x)
  dnD  : Val → CSt            -- downto.x -> Mu    (Md after in?x)
  uE   : CSt                  -- upto.end -> downto.end -> O1
  dE   : CSt                  -- downto.end -> O1
  o1   : CSt                  -- O1
  o1b  : Val′ → CSt           -- downfrom?y -> O2(x,y)
  o2   : Val′ → Val′ → CSt    -- O2(x,y)
  wU   : Val′ → CSt           -- upfrom?x' -> O2(x',y)
  wD   : Val′ → CSt           -- downfrom?y' -> O2(x,y')

-- the controller process
ctrl : CSt → MProc

-- upto!x -> downto!y -> Mu  (pinned output on the upper link)
force (ctrl (sndU x y)) = react
  (λ where (_ , c) (cupto , w) → case w ≟V′ dat x of λ where
              (yes _) → just (ctrl (sndD y))
              (no  _) → nothing
           (_ , c) _ → nothing)
  ∅t
-- downto!y -> Mu
force (ctrl (sndD y)) = react
  (λ where (_ , c) (cdownto , w) → case w ≟V′ dat y of λ where
              (yes _) → just (ctrl mu)
              (no  _) → nothing
           (_ , c) _ → nothing)
  ∅t
-- Mu = in.end -> upto.end -> downto.end -> O1  []  in?x:T -> upto.x -> Md
force (ctrl mu) = react
  (λ where (_ , c) (cin , end)   → just (ctrl uE)
           (_ , c) (cin , dat x) → just (ctrl (upU x))
           (_ , c) _ → nothing)
  ∅t
-- Md = in.end -> upto.end -> downto.end -> O1  []  in?x:T -> downto.x -> Mu
force (ctrl md) = react
  (λ where (_ , c) (cin , end)   → just (ctrl uE)
           (_ , c) (cin , dat x) → just (ctrl (dnD x))
           (_ , c) _ → nothing)
  ∅t
-- upto.x -> Md  (the distributor's turn flips to `down`)
force (ctrl (upU x)) = react
  (λ where (_ , c) (cupto , w) → case w ≟V′ dat x of λ where
              (yes _) → just (ctrl md)
              (no  _) → nothing
           (_ , c) _ → nothing)
  ∅t
-- downto.x -> Mu  (… and back to `up`)
force (ctrl (dnD x)) = react
  (λ where (_ , c) (cdownto , w) → case w ≟V′ dat x of λ where
              (yes _) → just (ctrl mu)
              (no  _) → nothing
           (_ , c) _ → nothing)
  ∅t
-- upto.end -> downto.end -> O1  (close both sub-lists)
force (ctrl uE) = react
  (λ where (_ , c) (cupto , end) → just (ctrl dE)
           (_ , c) _ → nothing)
  ∅t
-- downto.end -> O1
force (ctrl dE) = react
  (λ where (_ , c) (cdownto , end) → just (ctrl o1)
           (_ , c) _ → nothing)
  ∅t
-- O1 = upfrom?x -> downfrom?y -> O2(x,y)
force (ctrl o1) = react
  (λ where (_ , c) (cupfrom , w) → just (ctrl (o1b w))
           (_ , c) _ → nothing)
  ∅t
-- downfrom?y -> O2(x,y)
force (ctrl (o1b x)) = react
  (λ where (_ , c) (cdownfrom , w) → just (ctrl (o2 x w))
           (_ , c) _ → nothing)
  ∅t
-- O2, guard 1 (x==end and y==end): out.end -> Mu
force (ctrl (o2 end end)) = react
  (λ where (_ , c) (cout , end) → just (ctrl mu)
           (_ , c) _ → nothing)
  ∅t
-- O2, guard 2 (x==end and y!=end): out.y -> downfrom?y' -> O2(x,y')
force (ctrl (o2 end (dat b))) = react
  (λ where (_ , c) (cout , w) → case w ≟V′ dat b of λ where
              (yes _) → just (ctrl (wD end))
              (no  _) → nothing
           (_ , c) _ → nothing)
  ∅t
-- O2, guard 3 (x!=end and y==end): out.x -> upfrom?x' -> O2(x',y)
force (ctrl (o2 (dat a) end)) = react
  (λ where (_ , c) (cout , w) → case w ≟V′ dat a of λ where
              (yes _) → just (ctrl (wU end))
              (no  _) → nothing
           (_ , c) _ → nothing)
  ∅t
-- O2, guard 4 (both live): if x < y then out.x -> upfrom?x' -> O2(x',y)
--                                  else out.y -> downfrom?y' -> O2(x,y')
force (ctrl (o2 (dat a) (dat b))) = react
  (λ where (_ , c) (cout , w) → case a <V b of λ where
              true  → case w ≟V′ dat a of λ where
                        (yes _) → just (ctrl (wU (dat b)))
                        (no  _) → nothing
              false → case w ≟V′ dat b of λ where
                        (yes _) → just (ctrl (wD (dat a)))
                        (no  _) → nothing
           (_ , c) _ → nothing)
  ∅t
-- upfrom?x' -> O2(x',y)
force (ctrl (wU y)) = react
  (λ where (_ , c) (cupfrom , w) → just (ctrl (o2 w y))
           (_ , c) _ → nothing)
  ∅t
-- downfrom?y' -> O2(x,y')
force (ctrl (wD x)) = react
  (λ where (_ , c) (cdownfrom , w) → just (ctrl (o2 x w))
           (_ , c) _ → nothing)
  ∅t

-- §A.7 the sprouted network: the two nested link parallels of `M1`'s second branch,
-- verbatim — a controller linked to the upper sub-process and then to the lower one.
Net : CSt → MProc → MProc → MProc
Net cs P Q = (ctrl cs [up↔] P) [dn↔] Q

-- Roscoe's `M`, with the process handed to each sprouted half-list as a PARAMETER
-- (see the header: that is what keeps every corecursive call directly under `just`).
Mc  : MProc → MProc          -- M
M1c : MProc → Val → MProc    -- M1(x)
Moc : MProc → Val → MProc    -- out!x -> out.end -> M
Mec : MProc → MProc          -- out.end -> M

-- M = in.end -> out.end -> M  []  in?x:T -> M1(x)
force (Mc S) = react
  (λ where (_ , c) (cin , end)   → just (Mec S)
           (_ , c) (cin , dat x) → just (M1c S x)
           (_ , c) _ → nothing)
  ∅t
-- M1(x) = in.end -> out!x -> out.end -> M  []  in?y:T -> (the two link parallels)
force (M1c S x) = react
  (λ where (_ , c) (cin , end)   → just (Moc S x)
           (_ , c) (cin , dat y) → just (Net (sndU x y) S S)
           (_ , c) _ → nothing)
  ∅t
-- out!x -> out.end -> M  (the output value is PINNED)
force (Moc S x) = react
  (λ where (_ , c) (cout , w) → case w ≟V′ dat x of λ where
              (yes _) → just (Mec S)
              (no  _) → nothing
           (_ , c) _ → nothing)
  ∅t
-- out.end -> M
force (Mec S) = react
  (λ where (_ , c) (cout , end) → just (Mc S)
           (_ , c) _ → nothing)
  ∅t

-- §A.8 the merge sorter at recursion-depth budget `n`: `Msort (suc n)` is literally
-- Roscoe's `M` with its two sprouted children one budget lower, and `Msort zero` is
-- an `M` whose children cannot sprout at all (see the header on the truncation).
Msort : ℕ → MProc
Msort zero    = Mc Stop
Msort (suc n) = Mc (Msort n)

------------------------------------------------------------------------------------
-- §B. Transition-sanity checks (model-only — no FD/refinement claim).
--
-- Every check is stated for `Mc S` / `Mc (Mc S)` with `S : MProc` UNIVERSALLY
-- QUANTIFIED, hence holds at `Msort (suc n)` for every budget `n` at once.
------------------------------------------------------------------------------------

open import Semantics.LTS      {E = MEv} {I = ExtI MEv}
open import Semantics.Failures {E = MEv} {I = ExtI MEv}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import CSP.Laws.Traces.TraceLawsParallel MEv-≟
  using (Par-sync; Par-soloL; Par-τ-L)
open import CSP.Laws.Traces.TraceLawsHide MEv-≟
  using (Hide-keep; Hide-hidden; Hide-τ)

-- a concrete visible event `ch.w` of this alphabet
evt : Ch → Val′ → Event√ (⊤poly {lzero})
evt ch w = evl (evLabel Cv c (ch , w))

------------------------------------------------------------------------------------
-- §B.1 lifting a component step to the whole sprouted network.  Six lemmas: an
-- external (in/out) event of the controller survives both hides; a link event of
-- either pair becomes a τ of the network.  Nothing here forces the sub-processes, so
-- all six hold for ARBITRARY sub-processes (any depth of nesting below).
------------------------------------------------------------------------------------

-- a renamed sub-net refuses every target event with no source: the preimage list is
-- empty, so the renamed offer is `nothing` whatever the sub-net's own node is
noOff : ∀ (P : MProc) {inv : (bt : AnyTypes MEv) → proj₁ bt → Maybe ConcEvent₁}
          (ch : Ch) (w : Val′)
      → invPreimg inv (Cv , c) (ch , w) ≡ []
      → viewV (PTree.force (P ⟦ inv ⟧ⁱ)) (Cv , c) (ch , w) ≡ nothing
noOff P ch w eq with PTree.force P
... | ret _     = refl
... | sil _     = refl
... | react _ _ rewrite eq = refl

-- the controller's `in.w` is external: not in L1, not in L2, and neither sub-net
-- offers it (both have had their own `in` relabelled away)
nodeIn : ∀ (cs cs′ : CSt) (P Q : MProc) (w : Val′)
       → ctrl cs ─[ ev (evt cin w) ]─► ctrl cs′
       → Net cs P Q ─[ ev (evt cin w) ]─► Net cs′ P Q
nodeIn cs cs′ P Q w st =
  Hide-keep L2 _ (λ z → z)
    (Par-soloL L2 (λ _ _ → tt) _ (Q ⟦ dnInv ⟧ⁱ) (λ z → z)
      (Hide-keep L1 _ (λ z → z)
        (Par-soloL L1 (λ _ _ → tt) (ctrl cs) (P ⟦ upInv ⟧ⁱ) (λ z → z) st
          (noOff P cin w refl)))
      (noOff Q cin w refl))

-- … and so is the controller's `out.w` (the merged output of the whole network)
nodeOut : ∀ (cs cs′ : CSt) (P Q : MProc) (w : Val′)
        → ctrl cs ─[ ev (evt cout w) ]─► ctrl cs′
        → Net cs P Q ─[ ev (evt cout w) ]─► Net cs′ P Q
nodeOut cs cs′ P Q w st =
  Hide-keep L2 _ (λ z → z)
    (Par-soloL L2 (λ _ _ → tt) _ (Q ⟦ dnInv ⟧ⁱ) (λ z → z)
      (Hide-keep L1 _ (λ z → z)
        (Par-soloL L1 (λ _ _ → tt) (ctrl cs) (P ⟦ upInv ⟧ⁱ) (λ z → z) st
          (noOff P cout w refl)))
      (noOff Q cout w refl))

-- LINK 1, downward: the controller's `upto.w` synchronises with the upper sub-net's
-- `in.w` (its relabelled `upto`) and the handshake is hidden ⇒ a τ of the network
nodeτUp : ∀ (cs cs′ : CSt) (P P′ Q : MProc) (w : Val′)
        → ctrl cs ─[ ev (evt cupto w) ]─► ctrl cs′
        → P ─[ ev (evt cin w) ]─► P′
        → Net cs P Q ─[ τ ]─► Net cs′ P′ Q
nodeτUp cs cs′ P P′ Q w sc sp =
  Hide-τ L2 _
    (Par-τ-L L2 (λ _ _ → tt) _ (Q ⟦ dnInv ⟧ⁱ)
      (Hide-hidden L1 _ tt
        (Par-sync L1 (λ _ _ → tt) (ctrl cs) (P ⟦ upInv ⟧ⁱ) tt sc
          (ren-ev-fwd {inv = upInv} {at = Cv , c} {a = cin , w}
                      {bt = Cv , c} {b = cupto , w} sp refl))))

-- LINK 1, upward: the upper sub-net's `out.w` is read by the controller as `upfrom.w`
nodeτUpF : ∀ (cs cs′ : CSt) (P P′ Q : MProc) (w : Val′)
         → ctrl cs ─[ ev (evt cupfrom w) ]─► ctrl cs′
         → P ─[ ev (evt cout w) ]─► P′
         → Net cs P Q ─[ τ ]─► Net cs′ P′ Q
nodeτUpF cs cs′ P P′ Q w sc sp =
  Hide-τ L2 _
    (Par-τ-L L2 (λ _ _ → tt) _ (Q ⟦ dnInv ⟧ⁱ)
      (Hide-hidden L1 _ tt
        (Par-sync L1 (λ _ _ → tt) (ctrl cs) (P ⟦ upInv ⟧ⁱ) tt sc
          (ren-ev-fwd {inv = upInv} {at = Cv , c} {a = cout , w}
                      {bt = Cv , c} {b = cupfrom , w} sp refl))))

-- LINK 2, downward: `downto.w` is OUTSIDE L1, so it passes the inner parallel and
-- hide untouched, then synchronises with the lower sub-net and is hidden by L2
nodeτDn : ∀ (cs cs′ : CSt) (P Q Q′ : MProc) (w : Val′)
        → ctrl cs ─[ ev (evt cdownto w) ]─► ctrl cs′
        → Q ─[ ev (evt cin w) ]─► Q′
        → Net cs P Q ─[ τ ]─► Net cs′ P Q′
nodeτDn cs cs′ P Q Q′ w sc sq =
  Hide-hidden L2 _ tt
    (Par-sync L2 (λ _ _ → tt) _ (Q ⟦ dnInv ⟧ⁱ) tt
      (Hide-keep L1 _ (λ z → z)
        (Par-soloL L1 (λ _ _ → tt) (ctrl cs) (P ⟦ upInv ⟧ⁱ) (λ z → z) sc
          (noOff P cdownto w refl)))
      (ren-ev-fwd {inv = dnInv} {at = Cv , c} {a = cin , w}
                  {bt = Cv , c} {b = cdownto , w} sq refl))

-- LINK 2, upward: the lower sub-net's `out.w` is read as `downfrom.w`
nodeτDnF : ∀ (cs cs′ : CSt) (P Q Q′ : MProc) (w : Val′)
         → ctrl cs ─[ ev (evt cdownfrom w) ]─► ctrl cs′
         → Q ─[ ev (evt cout w) ]─► Q′
         → Net cs P Q ─[ τ ]─► Net cs′ P Q′
nodeτDnF cs cs′ P Q Q′ w sc sq =
  Hide-hidden L2 _ tt
    (Par-sync L2 (λ _ _ → tt) _ (Q ⟦ dnInv ⟧ⁱ) tt
      (Hide-keep L1 _ (λ z → z)
        (Par-soloL L1 (λ _ _ → tt) (ctrl cs) (P ⟦ upInv ⟧ⁱ) (λ z → z) sc
          (noOff P cdownfrom w refl)))
      (ren-ev-fwd {inv = dnInv} {at = Cv , c} {a = cout , w}
                  {bt = Cv , c} {b = cdownfrom , w} sq refl))

------------------------------------------------------------------------------------
-- §B.2 the leaf paths: `M` accepts data on `in`, the empty list, the singleton.
------------------------------------------------------------------------------------

-- M accepts a value on `in`, becoming M1(x)
cell-in : ∀ (S : MProc) (x : Val) → Mc S ─[ ev (evt cin (dat x)) ]─► M1c S x
cell-in S x = sVis refl refl

-- the EMPTY list:  in.end -> out.end -> M
empty-list : ∀ (S : MProc)
           → Mc S ⟹⟨ evt cin end ∷ evt cout end ∷ [] ⟩ Mc S
empty-list S = ⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) ⟹-refl)

-- the SINGLETON list:  in.v0 -> in.end -> out!v0 -> out.end -> M
singleton-v0 : ∀ (S : MProc)
             → Mc S ⟹⟨ evt cin (dat v0) ∷ evt cin end
                     ∷ evt cout (dat v0) ∷ evt cout end ∷ [] ⟩ Mc S
singleton-v0 S =
  ⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
  (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) ⟹-refl)))

-- … and the same for the other value
singleton-v1 : ∀ (S : MProc)
             → Mc S ⟹⟨ evt cin (dat v1) ∷ evt cin end
                     ∷ evt cout (dat v1) ∷ evt cout end ∷ [] ⟩ Mc S
singleton-v1 S =
  ⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
  (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) ⟹-refl)))

------------------------------------------------------------------------------------
-- §B.3 THE POINT OF THE EXAMPLE: a two-element sort, fed OUT of order.
--
-- Input <v1, v0> ⇒ output <v0, v1>: ASCENDING.  Fourteen steps — six visible and
-- eight hidden handshakes on the four link channels — run in full below, one named
-- lemma each, so the intermediate network states are on the record.  This run takes
-- `O2`'s guard 4 ELSE branch (`v1 < v0` is false, so the LOWER stream's head is
-- emitted first) and then guard 3 and guard 1.
------------------------------------------------------------------------------------

-- 1. in.v1 : the root cell takes the first datum
sA1 : ∀ (S : MProc) → Mc (Mc S) ─[ ev (evt cin (dat v1)) ]─► M1c (Mc S) v1
sA1 S = sVis refl refl

-- 2. in.v0 : the second datum SPROUTS the network (both link parallels appear here)
sA2 : ∀ (S : MProc)
    → M1c (Mc S) v1 ─[ ev (evt cin (dat v0)) ]─► Net (sndU v1 v0) (Mc S) (Mc S)
sA2 S = sVis refl refl

-- 3. τ : upto!v1 hands the first datum to the UPPER sub-net
sA3 : ∀ (S : MProc)
    → Net (sndU v1 v0) (Mc S) (Mc S) ─[ τ ]─► Net (sndD v0) (M1c S v1) (Mc S)
sA3 S = nodeτUp (sndU v1 v0) (sndD v0) (Mc S) (M1c S v1) (Mc S) (dat v1)
                (sVis refl refl) (sVis refl refl)

-- 4. τ : downto!v0 hands the second datum to the LOWER sub-net
sA4 : ∀ (S : MProc)
    → Net (sndD v0) (M1c S v1) (Mc S) ─[ τ ]─► Net mu (M1c S v1) (M1c S v0)
sA4 S = nodeτDn (sndD v0) mu (M1c S v1) (Mc S) (M1c S v0) (dat v0)
                (sVis refl refl) (sVis refl refl)

-- 5. in.end : the input list ends (the distributor Mu takes it)
sA5 : ∀ (S : MProc)
    → Net mu (M1c S v1) (M1c S v0) ─[ ev (evt cin end) ]─► Net uE (M1c S v1) (M1c S v0)
sA5 S = nodeIn mu uE (M1c S v1) (M1c S v0) end (sVis refl refl)

-- 6. τ : upto.end closes the upper sub-list
sA6 : ∀ (S : MProc)
    → Net uE (M1c S v1) (M1c S v0) ─[ τ ]─► Net dE (Moc S v1) (M1c S v0)
sA6 S = nodeτUp uE dE (M1c S v1) (Moc S v1) (M1c S v0) end
                (sVis refl refl) (sVis refl refl)

-- 7. τ : downto.end closes the lower sub-list; the merger O1 starts
sA7 : ∀ (S : MProc)
    → Net dE (Moc S v1) (M1c S v0) ─[ τ ]─► Net o1 (Moc S v1) (Moc S v0)
sA7 S = nodeτDn dE o1 (Moc S v1) (M1c S v0) (Moc S v0) end
                (sVis refl refl) (sVis refl refl)

-- 8. τ : upfrom?x reads v1 back from the upper sub-net
sA8 : ∀ (S : MProc)
    → Net o1 (Moc S v1) (Moc S v0) ─[ τ ]─► Net (o1b (dat v1)) (Mec S) (Moc S v0)
sA8 S = nodeτUpF o1 (o1b (dat v1)) (Moc S v1) (Mec S) (Moc S v0) (dat v1)
                 (sVis refl refl) (sVis refl refl)

-- 9. τ : downfrom?y reads v0 back from the lower sub-net ⇒ O2(v1,v0)
sA9 : ∀ (S : MProc)
    → Net (o1b (dat v1)) (Mec S) (Moc S v0) ─[ τ ]─►
      Net (o2 (dat v1) (dat v0)) (Mec S) (Mec S)
sA9 S = nodeτDnF (o1b (dat v1)) (o2 (dat v1) (dat v0)) (Mec S) (Moc S v0) (Mec S)
                 (dat v0) (sVis refl refl) (sVis refl refl)

-- 10. out.v0 : guard 4, ELSE branch (`v1 < v0` fails) ⇒ the SMALLER value leaves first
sA10 : ∀ (S : MProc)
     → Net (o2 (dat v1) (dat v0)) (Mec S) (Mec S) ─[ ev (evt cout (dat v0)) ]─►
       Net (wD (dat v1)) (Mec S) (Mec S)
sA10 S = nodeOut (o2 (dat v1) (dat v0)) (wD (dat v1)) (Mec S) (Mec S) (dat v0)
                 (sVis refl refl)

-- 11. τ : downfrom?y' finds the lower stream exhausted ⇒ O2(v1,end)
sA11 : ∀ (S : MProc)
     → Net (wD (dat v1)) (Mec S) (Mec S) ─[ τ ]─►
       Net (o2 (dat v1) end) (Mec S) (Mc S)
sA11 S = nodeτDnF (wD (dat v1)) (o2 (dat v1) end) (Mec S) (Mec S) (Mc S) end
                  (sVis refl refl) (sVis refl refl)

-- 12. out.v1 : guard 3 (lower exhausted) ⇒ drain the upper stream
sA12 : ∀ (S : MProc)
     → Net (o2 (dat v1) end) (Mec S) (Mc S) ─[ ev (evt cout (dat v1)) ]─►
       Net (wU end) (Mec S) (Mc S)
sA12 S = nodeOut (o2 (dat v1) end) (wU end) (Mec S) (Mc S) (dat v1) (sVis refl refl)

-- 13. τ : upfrom?x' finds the upper stream exhausted too ⇒ O2(end,end)
sA13 : ∀ (S : MProc)
     → Net (wU end) (Mec S) (Mc S) ─[ τ ]─► Net (o2 end end) (Mc S) (Mc S)
sA13 S = nodeτUpF (wU end) (o2 end end) (Mec S) (Mc S) (Mc S) end
                  (sVis refl refl) (sVis refl refl)

-- 14. out.end : guard 1 ⇒ the sorted list is closed and the distributor restarts
sA14 : ∀ (S : MProc)
     → Net (o2 end end) (Mc S) (Mc S) ─[ ev (evt cout end) ]─► Net mu (Mc S) (Mc S)
sA14 S = nodeOut (o2 end end) mu (Mc S) (Mc S) end (sVis refl refl)

-- THE SORT: feed <v1, v0>, observe <v0, v1> — the output comes out ASCENDING, with
-- the eight link handshakes invisible (they are τ's, as link parallel demands).
sortA : ∀ (S : MProc)
      → Mc (Mc S) ⟹⟨ evt cin (dat v1) ∷ evt cin (dat v0) ∷ evt cin end
                    ∷ evt cout (dat v0) ∷ evt cout (dat v1) ∷ evt cout end ∷ [] ⟩
        Net mu (Mc S) (Mc S)
sortA S =
  ⟹-ev (sA1 S) (⟹-ev (sA2 S) (⟹-τ (sA3 S) (⟹-τ (sA4 S) (⟹-ev (sA5 S)
 (⟹-τ (sA6 S) (⟹-τ (sA7 S) (⟹-τ (sA8 S) (⟹-τ (sA9 S) (⟹-ev (sA10 S)
 (⟹-τ (sA11 S) (⟹-ev (sA12 S) (⟹-τ (sA13 S) (⟹-ev (sA14 S) ⟹-refl)))))))))))))

------------------------------------------------------------------------------------
-- §B.4 the mirrored run: input <v0, v1> ⇒ output <v0, v1>, again ascending.  This
-- one takes `O2`'s guard 4 THEN branch (`v0 < v1` holds, so the UPPER stream's head
-- is emitted first) and then guard 2 and guard 1 — so between §B.3 and §B.4 all four
-- guards of `O2` and BOTH outcomes of the `x < y` test are reached by whole-network
-- runs, not merely by controller-local steps.
------------------------------------------------------------------------------------

sB1 : ∀ (S : MProc) → Mc (Mc S) ─[ ev (evt cin (dat v0)) ]─► M1c (Mc S) v0
sB1 S = sVis refl refl

sB2 : ∀ (S : MProc)
    → M1c (Mc S) v0 ─[ ev (evt cin (dat v1)) ]─► Net (sndU v0 v1) (Mc S) (Mc S)
sB2 S = sVis refl refl

sB3 : ∀ (S : MProc)
    → Net (sndU v0 v1) (Mc S) (Mc S) ─[ τ ]─► Net (sndD v1) (M1c S v0) (Mc S)
sB3 S = nodeτUp (sndU v0 v1) (sndD v1) (Mc S) (M1c S v0) (Mc S) (dat v0)
                (sVis refl refl) (sVis refl refl)

sB4 : ∀ (S : MProc)
    → Net (sndD v1) (M1c S v0) (Mc S) ─[ τ ]─► Net mu (M1c S v0) (M1c S v1)
sB4 S = nodeτDn (sndD v1) mu (M1c S v0) (Mc S) (M1c S v1) (dat v1)
                (sVis refl refl) (sVis refl refl)

sB5 : ∀ (S : MProc)
    → Net mu (M1c S v0) (M1c S v1) ─[ ev (evt cin end) ]─► Net uE (M1c S v0) (M1c S v1)
sB5 S = nodeIn mu uE (M1c S v0) (M1c S v1) end (sVis refl refl)

sB6 : ∀ (S : MProc)
    → Net uE (M1c S v0) (M1c S v1) ─[ τ ]─► Net dE (Moc S v0) (M1c S v1)
sB6 S = nodeτUp uE dE (M1c S v0) (Moc S v0) (M1c S v1) end
                (sVis refl refl) (sVis refl refl)

sB7 : ∀ (S : MProc)
    → Net dE (Moc S v0) (M1c S v1) ─[ τ ]─► Net o1 (Moc S v0) (Moc S v1)
sB7 S = nodeτDn dE o1 (Moc S v0) (M1c S v1) (Moc S v1) end
                (sVis refl refl) (sVis refl refl)

sB8 : ∀ (S : MProc)
    → Net o1 (Moc S v0) (Moc S v1) ─[ τ ]─► Net (o1b (dat v0)) (Mec S) (Moc S v1)
sB8 S = nodeτUpF o1 (o1b (dat v0)) (Moc S v0) (Mec S) (Moc S v1) (dat v0)
                 (sVis refl refl) (sVis refl refl)

sB9 : ∀ (S : MProc)
    → Net (o1b (dat v0)) (Mec S) (Moc S v1) ─[ τ ]─►
      Net (o2 (dat v0) (dat v1)) (Mec S) (Mec S)
sB9 S = nodeτDnF (o1b (dat v0)) (o2 (dat v0) (dat v1)) (Mec S) (Moc S v1) (Mec S)
                 (dat v1) (sVis refl refl) (sVis refl refl)

-- guard 4, THEN branch (`v0 < v1` holds) ⇒ the upper stream's head leaves first
sB10 : ∀ (S : MProc)
     → Net (o2 (dat v0) (dat v1)) (Mec S) (Mec S) ─[ ev (evt cout (dat v0)) ]─►
       Net (wU (dat v1)) (Mec S) (Mec S)
sB10 S = nodeOut (o2 (dat v0) (dat v1)) (wU (dat v1)) (Mec S) (Mec S) (dat v0)
                 (sVis refl refl)

sB11 : ∀ (S : MProc)
     → Net (wU (dat v1)) (Mec S) (Mec S) ─[ τ ]─►
       Net (o2 end (dat v1)) (Mc S) (Mec S)
sB11 S = nodeτUpF (wU (dat v1)) (o2 end (dat v1)) (Mec S) (Mc S) (Mec S) end
                  (sVis refl refl) (sVis refl refl)

-- guard 2 (upper exhausted) ⇒ drain the lower stream
sB12 : ∀ (S : MProc)
     → Net (o2 end (dat v1)) (Mc S) (Mec S) ─[ ev (evt cout (dat v1)) ]─►
       Net (wD end) (Mc S) (Mec S)
sB12 S = nodeOut (o2 end (dat v1)) (wD end) (Mc S) (Mec S) (dat v1) (sVis refl refl)

sB13 : ∀ (S : MProc)
     → Net (wD end) (Mc S) (Mec S) ─[ τ ]─► Net (o2 end end) (Mc S) (Mc S)
sB13 S = nodeτDnF (wD end) (o2 end end) (Mc S) (Mec S) (Mc S) end
                  (sVis refl refl) (sVis refl refl)

sB14 : ∀ (S : MProc)
     → Net (o2 end end) (Mc S) (Mc S) ─[ ev (evt cout end) ]─► Net mu (Mc S) (Mc S)
sB14 S = nodeOut (o2 end end) mu (Mc S) (Mc S) end (sVis refl refl)

-- feed <v0, v1>, observe <v0, v1>: ascending again (the already-sorted input)
sortB : ∀ (S : MProc)
      → Mc (Mc S) ⟹⟨ evt cin (dat v0) ∷ evt cin (dat v1) ∷ evt cin end
                    ∷ evt cout (dat v0) ∷ evt cout (dat v1) ∷ evt cout end ∷ [] ⟩
        Net mu (Mc S) (Mc S)
sortB S =
  ⟹-ev (sB1 S) (⟹-ev (sB2 S) (⟹-τ (sB3 S) (⟹-τ (sB4 S) (⟹-ev (sB5 S)
 (⟹-τ (sB6 S) (⟹-τ (sB7 S) (⟹-τ (sB8 S) (⟹-τ (sB9 S) (⟹-ev (sB10 S)
 (⟹-τ (sB11 S) (⟹-ev (sB12 S) (⟹-τ (sB13 S) (⟹-ev (sB14 S) ⟹-refl)))))))))))))

-- Both runs instantiate at a CONCRETE budget: `Msort 1 = Mc (Msort 0) = Mc (Mc Stop)`,
-- so the sort above is literally a run of the (closed) merge sorter at budget 1 —
-- which is all a two-element list can spend.  Nothing in §B.3/§B.4 touched the
-- deepest child, so the same terms serve `Msort (suc n)` for every larger `n`.
sort-budget-1 : Msort 1 ⟹⟨ evt cin (dat v1) ∷ evt cin (dat v0) ∷ evt cin end
                         ∷ evt cout (dat v0) ∷ evt cout (dat v1) ∷ evt cout end ∷ [] ⟩
                Net mu (Mc Stop) (Mc Stop)
sort-budget-1 = sortA Stop

------------------------------------------------------------------------------------
-- §B.5 non-vacuity.
------------------------------------------------------------------------------------

-- The distributor really ALTERNATES: at `Mu` a datum goes UP, at `Md` the next goes
-- DOWN, and the turn returns to `Mu`.  Stated on the whole network, so the two
-- sub-nets are seen to receive one datum each: the upper one takes v0, the lower v1.
distrib-alt : ∀ (S : MProc)
            → Net mu (Mc S) (Mc S)
              ⟹⟨ evt cin (dat v0) ∷ evt cin (dat v1) ∷ [] ⟩
              Net mu (M1c S v0) (M1c S v1)
distrib-alt S =
  ⟹-ev (nodeIn mu (upU v0) (Mc S) (Mc S) (dat v0) (sVis refl refl))
 (⟹-τ  (nodeτUp (upU v0) md (Mc S) (M1c S v0) (Mc S) (dat v0)
                 (sVis refl refl) (sVis refl refl))
 (⟹-ev (nodeIn md (dnD v1) (M1c S v0) (Mc S) (dat v1) (sVis refl refl))
 (⟹-τ  (nodeτDn (dnD v1) mu (M1c S v0) (Mc S) (M1c S v1) (dat v1)
                 (sVis refl refl) (sVis refl refl))
        ⟹-refl)))

-- `O2`'s comparison is really consulted, and BOTH outcomes occur: with `v0 < v1` the
-- head of the UPPER stream is emitted (and the upper stream is re-read) …
o2-lt : ctrl (o2 (dat v0) (dat v1)) ─[ ev (evt cout (dat v0)) ]─► ctrl (wU (dat v1))
o2-lt = sVis refl refl

-- … and with `v1 < v0` false, the head of the LOWER stream is (and the lower re-read)
o2-ge : ctrl (o2 (dat v1) (dat v0)) ─[ ev (evt cout (dat v0)) ]─► ctrl (wD (dat v1))
o2-ge = sVis refl refl

-- the two one-sided guards drain the surviving stream …
o2-up-only : ctrl (o2 (dat v1) end) ─[ ev (evt cout (dat v1)) ]─► ctrl (wU end)
o2-up-only = sVis refl refl

o2-dn-only : ctrl (o2 end (dat v1)) ─[ ev (evt cout (dat v1)) ]─► ctrl (wD end)
o2-dn-only = sVis refl refl

-- … and the both-exhausted guard closes the output list and restarts the distributor
o2-both-end : ctrl (o2 end end) ─[ ev (evt cout end) ]─► ctrl mu
o2-both-end = sVis refl refl
