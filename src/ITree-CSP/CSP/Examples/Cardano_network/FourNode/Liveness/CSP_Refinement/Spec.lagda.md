# Four-node diamond block-liveness — CSP refinement specification

This module *states* (does not prove) the block-liveness property of the broken
four-node diamond `systemBroken` (`FourNodeDiamondBroken.lagda.md`) as a **CSP
failures–divergences refinement**, as a counterpart to the trace-LTL
`BlockLiveness⁺` of the sibling route `../LTL/Spec.lagda.md`. The reading is: *if at
least one complete path A→B→D or A→C→D stays whole, a block `b` produced by
NodeA is received by NodeD; if both paths are broken, NodeD need not receive
it.* Unlike the LTL version's **global** confinement hypothesis
(`G ¬brkG1 ∨ G ¬brkG2`), the Spec here observes the `break` events and tracks
path-wholeness **per state**, so the CSP statement needs no implication
primitive. Design doc:
`docs/superpowers/specs/2026-08-04-fournode-liveness-csp-refinement-design.md`.

```agda
{-# OPTIONS --guardedness #-}
```

```agda
import Data.Unit as U
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤ₚ)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁)
open import Level using (0ℓ; Lift; lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary using (¬_)
open import Data.Bool.Properties using () renaming (_≟_ to _≟B_)
open import Class.DecEq using (DecEq; _≟_)
open import Function using (case_of_)

open import Process_Trees using (PTree; ExtI; AnyTypes; ContinueType; react; ptree; base; pair; fin)
open PTree

module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.Spec where
```

The healthy diamond supplies the shared `Params` `p`, the four link ids, and
the block domain `Block₃` with its decidable equality; the broken diamond
supplies the system under specification:

```agda
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; linkAB; linkAC; linkBD; linkCD; Block₃; b1; b2; DecEq-Block₃
        ; nodeA; nodeB; nodeC; nodeD )
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondBroken
  using ( systemBroken )
open import CSP.Examples.Cardano_network.Base using ( lo; hi; DecEq-Dir )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Link; apiBF; apiKA; break
        ; sendBFBlock; recvBFBlock; sendBFStartBatch; sendKAMsg )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p
  using ( CopySpecBreakableA; ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( EventSet; Stop; pchoice; Prefix-cont; Output-cont; ∅v; ∅t; _∖_; _∥⇘_⇙_; _⦀_ )

open import Semantics.FailuresDivergences
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _⊑FD_; ⊑FD-trans; divergences )

-- the STABLE-FAILURES order `⊑F` and its transitivity (for the `⊑F` target and the
-- reduction theorem of the last section)
open import Semantics.Failures
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _⊑F_; ⊑F-trans )

-- the two UNCONDITIONAL `⊑F` monotonicity laws the `⊑F` reduction is built from, plus the
-- CONDITIONAL `⊑FD` hiding law `Hide-mono-⊑FD-df` the `⊑FD` reduction needs instead (the
-- unconditional `⊑FD` hiding law is FALSE — see that module's header)
open import CSP.Laws.FD.HideMonoFD     (Net_Api-≟ {Payload})
  using ( Hide-mono-⊑F; Hide-mono-⊑FD-df )
open import CSP.Laws.FD.ParallelMonoFD (Net_Api-≟ {Payload})
  using ( ∥-mono-⊑F; ⦀-mono-⊑F; ∥-mono-⊑FD; ⦀-mono-⊑FD )
```

Two abbreviations: the process type at this alphabet, and the shape of a
visible-offer map (a *menu*) over it.

```agda
-- a specification process over the whole-system alphabet
SpecProc : Set₁
SpecProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ₚ {0ℓ})

-- a visible-offer map (menu) over that alphabet
SpecMenu : Set₁
SpecMenu = (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe SpecProc)

-- compatibility alias: on this branch `nodeA` is already block-generic
-- (`nodeA : Block₃ → …`), which is exactly what this file's `nodeAOf` meant
nodeAOf : Block₃ → SpecProc
nodeAOf = nodeA
```

## The kept alphabet and the hide set

Exactly three event classes stay visible: A's produce of the distinguished
block `b` (`apiBF l hi sendBFBlock ! b`, `l ∈ {AB, AC}`), D's receive of `b`
(`apiBF l hi recvBFBlock ! b`, `l ∈ {BD, CD}`), and every `break`. The
decision is `Bool`-valued so that both `EventSet` fields follow mechanically
and every sanity test reduces by computation.

```agda
-- is this (event, carried value) pair KEPT visible?  A's produce of b on AB/AC at hi,
-- D's receive of b on BD/CD at hi, and every break; everything else is hidden.
keptB : Block₃ → (at : AnyTypes (Net_Api Payload)) → proj₁ at → Bool
keptB b (_ , break _)                    _ = true
keptB b (_ , apiBF l d sendBFBlock)      a =
  (⌊ l ≟ linkAB ⌋ ∨ ⌊ l ≟ linkAC ⌋) ∧ ⌊ d ≟ hi ⌋ ∧ ⌊ a ≟ b ⌋
keptB b (_ , apiBF l d recvBFBlock)      a =
  (⌊ l ≟ linkBD ⌋ ∨ ⌊ l ≟ linkCD ⌋) ∧ ⌊ d ≟ hi ⌋ ∧ ⌊ a ≟ b ⌋
keptB _ _                                _ = false

-- the HIDDEN event set: the complement of the kept alphabet, decided by `keptB`
hidden : Block₃ → EventSet
hidden b = record
  { mem = λ at a → keptB b at a ≡ false
  ; dec = λ at a → keptB b at a ≟B false
  }
```

## Menu union, the discharged state, and the delivery obligation

Menus compose by first-match union. `Done` is CHAOS over the kept alphabet:
an internal choice between `Stop` (so it may refuse anything) and a menu
accepting any kept event — the most-permissive **divergence-free** process,
which is what "the obligation is discharged, but no post-delivery livelock"
means. `Done` is *not* `Stop` (that would forbid post-receipt breaks the
system can perform) and *not* `Run′` (that could never refuse, so it would
forbid the system to quiesce).

```agda
-- left-associative so chains of ⊕v (used below) parse without parentheses
infixl 5 _⊕v_

-- first-match union of two visible-offer menus (the left menu wins where both offer)
_⊕v_ : SpecMenu → SpecMenu → SpecMenu
(v₁ ⊕v v₂) at a with v₁ at a
... | just t  = just t
... | nothing = v₂ at a

-- forward declarations (project convention: no old-style `mutual` blocks); this
-- follows the SAME shape as `tableSpec`/`tGo`/`tMenu` in NodeSpecs.agda (the
-- "τ-free table-FSM interpreter"): a small dispatcher `doneGo` whose OWN two
-- clauses pattern-match DIRECTLY on a given `Bool` argument, with the
-- corecursive call as the immediate argument of `just` in one clause
Done      : Block₃ → SpecProc
doneGo    : Block₃ → Bool → Maybe SpecProc
doneMenu  : Block₃ → SpecMenu
-- `delivMenu b p1 g1 p2 g2`: p1/p2 = "A produced on AB / on AC", g1/g2 = "path ABD / ACD whole"
delivMenu : Block₃ → Bool → Bool → Bool → Bool → SpecMenu

-- CHAOS over the kept alphabet: τ either to Stop (refuse everything) or to the
-- accepting menu; divergence-free, so a post-delivery livelock is still forbidden.
-- `br2`/`pchoice` are INLINED here (not called as the library combinators) —
-- isolated minimal reproduction showed that routing the self-recursive `Done b`
-- through the library `br2`/`pchoice` calls makes Agda's termination checker
-- reject the self-call as unguarded, even though the exact same shape typechecks
-- when `br2`'s case-split and `pchoice`'s `ptree (react … )` wrapping are written
-- out directly in this clause instead of called as external functions
force (Done b) = react ∅v (λ where
  (_ , fin) x → case x of λ where
    (lift fzero)        → just Stop
    (lift (fsuc fzero)) → just (ptree (react (doneMenu b) (λ _ _ → nothing)))
    _                   → nothing
  (_ , base _)   _ → nothing
  (_ , pair _ _) _ → nothing)

-- the guarded corecursive step: `just (Done b)` sits as a DIRECT clause RHS,
-- pattern-matching on doneGo's own (already-given) Bool argument
doneGo b false = nothing
doneGo b true  = just (Done b)

-- accept any of the 8 kept events and stay discharged: exactly the KEPT events
-- (`keptB`, Task 1) lead back to `Done b`, everything else is refused
doneMenu b at a = doneGo b (keptB b at a)

-- the currently-obligated delivery: a path's receive of b is offered iff A actually PRODUCED
-- on that path's entry link (p1 / p2) AND the path is still whole (g1 / g2).  The produce
-- conjunct is essential (FIX 1): A runs two independent per-link drivers, so `⟨send@AB⟩` alone
-- must not obligate D's receive on CD — C never got the block.
delivMenu b p1 g1 p2 g2 =
       (if p1 ∧ g1 then Output-cont (apiBF linkBD hi recvBFBlock) b (Done b) else ∅v)
  ⊕v (if p2 ∧ g2 then Output-cont (apiBF linkCD hi recvBFBlock) b (Done b) else ∅v)
```

## The produced state and the idle state

`Prod b p1 g1 p2 g2` is a pure internal choice (`react ∅v …`) over eight
branches. Branch 0 is the bare delivery; branches 1–4 add one `break` each;
branches 5–6 add one repeat-produce each; branch 7 (the may-deliver branch)
offers both receives unconditionally. Because `delivMenu` appears in branches
0–6, the delivery cannot be refused while a path has been produced on and is
still whole — the liveness obligation (adding branch 7's offer on top cannot
remove it). Because each break/produce appears in one branch only, the Spec
still permits the system to refuse them. Branch 7 alone lets D receive even
when the Spec's own flags do not obligate it — the block may already have
crossed a since-broken link before the break (a fact `hidden` from the Spec),
so this keeps that trace legal without making the receive a must-offer.

The four state flags are **monotone**: `p1`/`p2` only go `false → true`
(A produced on AB / on AC — set by `LSpec`'s two produce branches and by
`Prod`'s two repeat-produce branches), `g1`/`g2` only go `true → false`
(a `break` on AB or BD downs path ABD; on AC or CD downs path ACD).

`LSpec` (idle, `b` not yet produced) carries **no** obligation, so its branch 0
is `Stop`: it may refuse everything. Its remaining branches accept a break or
A's produce, the latter entering `Prod` with the corresponding produce bit set
(and the other still `false` — in the idle state nothing has been produced,
which is why `LSpec` needs only the two `g` flags).

```agda
-- forward declarations.  Task 3's refined guardedness lesson (beyond Task 2's pchoice/br2
-- finding): Agda's guardedness checker recognises a (mutually) recursive call as guarded only
-- when the recursive HEAD is written LITERALLY as the direct argument of
-- `just`/`ptree`/`react`/`sil` in the clause where it appears — exactly
-- `doneGo b true = just (Done b)` above, where `Done b` is spelled out, not received as a
-- parameter.  A helper GENERIC in the successor STATE (`k` of type `SpecProc`, e.g.
-- `brkGo k true = just k`) is NOT traced through, even when that helper is `with`-free and
-- forward-declared in the very same group — confirmed empirically.
--
-- BUT (the clause that keeps the dispatcher count down, FIX 2): only the *head* must be
-- literal.  The state's DATA arguments may be arbitrary expressions — both in the dispatcher's
-- own clause (where they are plain variables, `just (Prod b p1 g1 p2 g2)`) and at every CALL
-- site, which may pass any expression it likes (`prodGo b p1 false p2 g2 …` to clear `g1`,
-- `prodGo b true g1 p2 g2 …` to set `p1`).  So there is no need for a separate dispatcher per
-- flag substitution: TWO dispatchers suffice — one naming `Prod`, one naming `LSpec`.
Prod  : Block₃ → Bool → Bool → Bool → Bool → SpecProc
prodτ : Block₃ → Bool → Bool → Bool → Bool
      → (i : AnyTypes (ExtI (Net_Api Payload))) → ContinueType i (Maybe SpecProc)
LSpec : Block₃ → Bool → Bool → SpecProc
idleτ : Block₃ → Bool → Bool
      → (i : AnyTypes (ExtI (Net_Api Payload))) → ContinueType i (Maybe SpecProc)

-- is this (event, value) exactly `break l`?  A pure predicate — no Prod/LSpec reference.
isBrk : Link → (at : AnyTypes (Net_Api Payload)) → proj₁ at → Bool
isBrk l (_ , break l') _ = ⌊ l ≟ l' ⌋
isBrk _ _              _ = false

-- is this (event, value) exactly A's send of b on link l at direction hi?
isProd1 : Link → Block₃ → (at : AnyTypes (Net_Api Payload)) → proj₁ at → Bool
isProd1 l b (_ , apiBF l' d sendBFBlock) a = ⌊ l ≟ l' ⌋ ∧ ⌊ d ≟ hi ⌋ ∧ ⌊ a ≟ b ⌋
isProd1 _ _ _ _ = false

-- the ONE guarded step into `Prod`: `just (Prod …)` with the head literal and every flag a
-- plain variable, so each call site substitutes the flags it needs (mirrors `doneGo`).  Used by
-- all six of `Prod`'s may-event branches AND by `LSpec`'s two produce branches.
prodGo : Block₃ → Bool → Bool → Bool → Bool → Bool → Maybe SpecProc
prodGo b p1 g1 p2 g2 false = nothing
prodGo b p1 g1 p2 g2 true  = just (Prod b p1 g1 p2 g2)

-- the ONE guarded step within `LSpec` (idle): a break moves to another idle state
idleGo : Block₃ → Bool → Bool → Bool → Maybe SpecProc
idleGo b g1 g2 false = nothing
idleGo b g1 g2 true  = just (LSpec b g1 g2)

-- produced: the delivery is the single must-offer (present in every τ-branch)
force (Prod b p1 g1 p2 g2) = react ∅v (prodτ b p1 g1 p2 g2)

-- branch 0 = delivery only; 1-4 = delivery + one break; 5-6 = delivery + one repeat-produce.
-- `pchoice v` is INLINED here as `ptree (react v ∅t)` (its own definition,
-- `CSP/Operators.agda:188-191`).  Each menu is written as an inline extended lambda (NOT
-- `_⊕v_`/`Prefix-cont`/`Output-cont` — all external, and all break guardedness for the reason
-- noted above): try `delivMenu` first, else dispatch the one break/produce this branch owns
-- via the literal `prodGo` above, with the flags this branch updates substituted at the call.
prodτ b p1 g1 p2 g2 (_ , fin) (lift fzero) =
  just (ptree (react (delivMenu b p1 g1 p2 g2) ∅t))
prodτ b p1 g1 p2 g2 (_ , fin) (lift (fsuc fzero)) =
  just (ptree (react (λ where at a → case delivMenu b p1 g1 p2 g2 at a of λ where
    (just t) → just t
    nothing  → prodGo b p1 false p2 g2 (isBrk linkAB at a)) ∅t))
prodτ b p1 g1 p2 g2 (_ , fin) (lift (fsuc (fsuc fzero))) =
  just (ptree (react (λ where at a → case delivMenu b p1 g1 p2 g2 at a of λ where
    (just t) → just t
    nothing  → prodGo b p1 false p2 g2 (isBrk linkBD at a)) ∅t))
prodτ b p1 g1 p2 g2 (_ , fin) (lift (fsuc (fsuc (fsuc fzero)))) =
  just (ptree (react (λ where at a → case delivMenu b p1 g1 p2 g2 at a of λ where
    (just t) → just t
    nothing  → prodGo b p1 g1 p2 false (isBrk linkAC at a)) ∅t))
prodτ b p1 g1 p2 g2 (_ , fin) (lift (fsuc (fsuc (fsuc (fsuc fzero))))) =
  just (ptree (react (λ where at a → case delivMenu b p1 g1 p2 g2 at a of λ where
    (just t) → just t
    nothing  → prodGo b p1 g1 p2 false (isBrk linkCD at a)) ∅t))
-- branches 5-6: a repeat-produce SETS that path's produce bit (A may produce on AB and only
-- later on AC), which is what makes the AC-path obligation appear exactly when it should
prodτ b p1 g1 p2 g2 (_ , fin) (lift (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) =
  just (ptree (react (λ where at a → case delivMenu b p1 g1 p2 g2 at a of λ where
    (just t) → just t
    nothing  → prodGo b true g1 p2 g2 (isProd1 linkAB b at a)) ∅t))
prodτ b p1 g1 p2 g2 (_ , fin) (lift (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) =
  just (ptree (react (λ where at a → case delivMenu b p1 g1 p2 g2 at a of λ where
    (just t) → just t
    nothing  → prodGo b p1 g1 true g2 (isProd1 linkAC b at a)) ∅t))
-- branch 7: the may-deliver branch — offers BOTH receives UNCONDITIONALLY
-- (`delivMenu b true true true true`, ignoring the branch's real flags), each leading to
-- `Done b`.  This keeps a late delivery (the block already crossed a since-broken link before
-- it broke, a fact `hidden` from the Spec) trace-LEGAL without gating it: added to branches
-- 0-6's must-offer (which is untouched — adding an offer cannot remove one), so when a path is
-- produced-on and whole the receive stays a must-offer; otherwise this branch alone still lets
-- D receive as a refusable may-event, matching what the real system can do.
prodτ b p1 g1 p2 g2 (_ , fin) (lift (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) =
  just (ptree (react (delivMenu b true true true true) ∅t))
prodτ _ _  _  _  _  (_ , fin)      _ = nothing
prodτ _ _  _  _  _  (_ , base _)   _ = nothing
prodτ _ _  _  _  _  (_ , pair _ _) _ = nothing

-- idle: b not yet produced, so no must-offer — branch 0 may refuse everything
force (LSpec b g1 g2) = react ∅v (idleτ b g1 g2)

-- branch 0 = Stop; 1-4 = one break each; 5-6 = A's produce on AB / AC, entering Prod with
-- exactly that path's produce bit set (the other stays `false` — nothing else was produced).
-- No `delivMenu` here (idle carries no obligation), so each branch's menu is JUST the one
-- break/produce dispatch — an inline extended lambda over the literal `idleGo`/`prodGo` above.
idleτ b g1 g2 (_ , fin) (lift fzero) = just Stop
idleτ b g1 g2 (_ , fin) (lift (fsuc fzero)) =
  just (ptree (react (λ where at a → idleGo b false g2 (isBrk linkAB at a)) ∅t))
idleτ b g1 g2 (_ , fin) (lift (fsuc (fsuc fzero))) =
  just (ptree (react (λ where at a → idleGo b false g2 (isBrk linkBD at a)) ∅t))
idleτ b g1 g2 (_ , fin) (lift (fsuc (fsuc (fsuc fzero)))) =
  just (ptree (react (λ where at a → idleGo b g1 false (isBrk linkAC at a)) ∅t))
idleτ b g1 g2 (_ , fin) (lift (fsuc (fsuc (fsuc (fsuc fzero))))) =
  just (ptree (react (λ where at a → idleGo b g1 false (isBrk linkCD at a)) ∅t))
idleτ b g1 g2 (_ , fin) (lift (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) =
  just (ptree (react (λ where at a → prodGo b true g1 false g2 (isProd1 linkAB b at a)) ∅t))
idleτ b g1 g2 (_ , fin) (lift (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) =
  just (ptree (react (λ where at a → prodGo b false g1 true g2 (isProd1 linkAC b at a)) ∅t))
idleτ _ _  _  (_ , fin)      _ = nothing
idleτ _ _  _  (_ , base _)   _ = nothing
idleτ _ _  _  (_ , pair _ _) _ = nothing
```

## Sanity tests — the hide set

`hidden b` keeps the produce, the receive, and the breaks; it hides
other-value BF events, other api channels, the wrong direction, and
interior-link BF events.

```agda
-- keeps A's produce of b1 on AB
_ : keptB b1 (Block₃ , apiBF linkAB hi sendBFBlock) b1 ≡ true
_ = refl

-- keeps D's receive of b1 on CD
_ : keptB b1 (Block₃ , apiBF linkCD hi recvBFBlock) b1 ≡ true
_ = refl

-- keeps every break
_ : keptB b1 (U.⊤ , break linkBD) U.tt ≡ true
_ = refl

-- hides the wrong block value (b2 ≢ b1)
_ : keptB b1 (Block₃ , apiBF linkAB hi sendBFBlock) b2 ≡ false
_ = refl

-- hides the wrong DIRECTION: A's produce is kept only at `hi` (pins the `⌊ d ≟ hi ⌋` conjunct)
_ : keptB b1 (Block₃ , apiBF linkAB lo sendBFBlock) b1 ≡ false
_ = refl

-- hides an INTERIOR link on the send side: only A's outgoing links AB/AC are kept, so B's
-- forwarding send on BD is hidden (pins the `linkAB ∨ linkAC` restriction on `sendBFBlock`)
_ : keptB b1 (Block₃ , apiBF linkBD hi sendBFBlock) b1 ≡ false
_ = refl

-- hides the wrong tag/link pairing: a `recvBFBlock` on AB is not one of D's incoming links
-- (pins the `linkBD ∨ linkCD` restriction on `recvBFBlock`)
_ : keptB b1 (Block₃ , apiBF linkAB hi recvBFBlock) b1 ≡ false
_ = refl

-- hides another BF tag entirely (`sendBFStartBatch` is interior batch bookkeeping)
_ : keptB b1 (U.⊤ , apiBF linkAB hi sendBFStartBatch) U.tt ≡ false
_ = refl

-- hides another api CHANNEL entirely (KeepAlive traffic is never part of the kept alphabet)
_ : keptB b1 (U.⊤ , apiKA linkAB hi sendKAMsg) U.tt ≡ false
_ = refl

-- `hidden b1`'s DECISION procedure says `no` on a KEPT event (A's produce of b1 is NOT a
-- member of the hidden set) — the only test that exercises the `EventSet.dec` field …
_ : ⌊ EventSet.dec (hidden b1) (Block₃ , apiBF linkAB hi sendBFBlock) b1 ⌋ ≡ false
_ = refl

-- … and `yes` on a hidden one (the same event at the wrong direction IS in the hidden set)
_ : ⌊ EventSet.dec (hidden b1) (Block₃ , apiBF linkAB lo sendBFBlock) b1 ⌋ ≡ true
_ = refl
```

## Sanity tests — the delivery menu

With a path produced-on and whole the delivery is offered; if the path is
broken, *or* A never produced on its entry link, it is refusable; the bare
delivery menu never offers a break or a produce (that is what makes those
may-events refusable).

```agda
-- produced on AB and path ABD whole ⇒ BD's receive of b1 is offered, leading to Done
_ : delivMenu b1 true true false false (Block₃ , apiBF linkBD hi recvBFBlock) b1 ≡ just (Done b1)
_ = refl

-- produced on AC and path ACD whole ⇒ CD's receive of b1 is offered
_ : delivMenu b1 false false true true (Block₃ , apiBF linkCD hi recvBFBlock) b1 ≡ just (Done b1)
_ = refl

-- path ABD broken (though produced on AB) ⇒ BD's receive is NOT offered
_ : delivMenu b1 true false true true (Block₃ , apiBF linkBD hi recvBFBlock) b1 ≡ nothing
_ = refl

-- both paths broken ⇒ neither receive is offered (delivery fully refusable)
_ : delivMenu b1 true false true false (Block₃ , apiBF linkCD hi recvBFBlock) b1 ≡ nothing
_ = refl

-- FIX 1, the falsifier that motivated the produce bits: A produced on AB only, so even though
-- path ACD is WHOLE, D's receive on CD is NOT obligated — C never got the block
_ : delivMenu b1 true true false true (Block₃ , apiBF linkCD hi recvBFBlock) b1 ≡ nothing
_ = refl

-- the mirror image: A produced on AC only ⇒ BD's receive is not obligated either
_ : delivMenu b1 false true true true (Block₃ , apiBF linkBD hi recvBFBlock) b1 ≡ nothing
_ = refl

-- the delivery menu alone never offers a break (⇒ breaks stay refusable)
_ : delivMenu b1 true true true true (U.⊤ , break linkAB) U.tt ≡ nothing
_ = refl

-- nor a produce
_ : delivMenu b1 true true true true (Block₃ , apiBF linkAB hi sendBFBlock) b1 ≡ nothing
_ = refl

-- Done accepts a break and stays in Done
_ : doneMenu b1 (U.⊤ , break linkCD) U.tt ≡ just (Done b1)
_ = refl
```

## Sanity tests — must-offer vs may-event

The delivery is offered in **every** branch of `Prod` (must-offer); each break
and produce is offered in **its own** branch only, and is absent from the bare
delivery branch (may-event, refusable). Breaks are idempotent: re-breaking a
downed path returns to the same state, so no break can re-enable delivery.

```agda
-- branch 0 (bare delivery) offers the delivery ...
_ : prodτ b1 true true true true (Lift 0ℓ (Fin 8) , fin) (lift Data.Fin.zero)
      ≡ just (pchoice (delivMenu b1 true true true true))
_ = refl

-- ... and the break-AB branch ALSO offers the delivery (must-offer in every branch)
_ : (delivMenu b1 true true true true
       ⊕v Prefix-cont (break linkAB) (λ _ → Prod b1 true false true true))
      (Block₃ , apiBF linkBD hi recvBFBlock) b1
    ≡ just (Done b1)
_ = refl

-- the break-AB branch also offers break AB, downing path ABD
_ : (delivMenu b1 true true true true
       ⊕v Prefix-cont (break linkAB) (λ _ → Prod b1 true false true true))
      (U.⊤ , break linkAB) U.tt
    ≡ just (Prod b1 true false true true)
_ = refl

-- re-breaking an already-down path is idempotent (g1 stays false; delivery not re-enabled)
_ : (delivMenu b1 true false true true
       ⊕v Prefix-cont (break linkBD) (λ _ → Prod b1 true false true true))
      (U.⊤ , break linkBD) U.tt
    ≡ just (Prod b1 true false true true)
_ = refl

-- Idle branch 0 is Stop: before the produce there is no must-offer at all
_ : idleτ b1 true true (Lift 0ℓ (Fin 8) , fin) (lift Data.Fin.zero) ≡ just Stop
_ = refl

-- Idle's produce branch offers A's send of b1 on AB and enters Prod with p1 set (p2 still false)
_ : Output-cont (apiBF linkAB hi sendBFBlock) b1 (Prod b1 true true false true)
      (Block₃ , apiBF linkAB hi sendBFBlock) b1
    ≡ just (Prod b1 true true false true)
_ = refl
```

## Coverage against the real τ-maps

Four of the six tests above (the `delivMenu ⊕v Prefix-cont …`/`Output-cont …` ones) are built
from standalone shadow-menu expressions — facts about a menu the implementation no longer
constructs directly (`prodτ`/`idleτ` dispatch via inline lambdas + `isBrk`/`isProd1` instead).
They still hold and are still falsifiable, but they don't constrain `prodτ`/`idleτ` themselves.
(The other two — branch 0 of `prodτ` and of `idleτ` — do probe the real τ-maps.) `offersOf`
extracts the actual visible-offer menu of a τ-branch's (stable) successor, so the tests below
probe the real τ-maps directly across *all* the flag-updating branches: a `g1`/`g2` or `p1`/`p2`
swap, or a dropped `delivMenu` in any one branch, would fail these.

```agda
-- the visible-offer map of a τ-branch's (stable) successor, ∅v if absent
offersOf : Maybe SpecProc → SpecMenu
offersOf nothing  = ∅v
offersOf (just t) with force t
... | react v _ = v
... | _         = ∅v

-- branch 1 (break-AB) still offers the must-offer delivery on recv@BD, on the REAL τ-map
_ : offersOf (prodτ b1 true true true true (Lift 0ℓ (Fin 8) , fin) (lift (fsuc fzero)))
      (Block₃ , apiBF linkBD hi recvBFBlock) b1 ≡ just (Done b1)
_ = refl

-- branch 2 (break-BD) still offers the must-offer delivery on recv@BD
_ : offersOf (prodτ b1 true true true true (Lift 0ℓ (Fin 8) , fin) (lift (fsuc (fsuc fzero))))
      (Block₃ , apiBF linkBD hi recvBFBlock) b1 ≡ just (Done b1)
_ = refl

-- branch 3 (break-AC) still offers the must-offer delivery on recv@CD
_ : offersOf (prodτ b1 true true true true (Lift 0ℓ (Fin 8) , fin)
               (lift (fsuc (fsuc (fsuc fzero)))))
      (Block₃ , apiBF linkCD hi recvBFBlock) b1 ≡ just (Done b1)
_ = refl

-- branch 4 (break-CD) still offers the must-offer delivery on recv@CD
_ : offersOf (prodτ b1 true true true true (Lift 0ℓ (Fin 8) , fin)
               (lift (fsuc (fsuc (fsuc (fsuc fzero))))))
      (Block₃ , apiBF linkCD hi recvBFBlock) b1 ≡ just (Done b1)
_ = refl

-- branch 5 (repeat-produce on AB) still offers the must-offer delivery on recv@BD
_ : offersOf (prodτ b1 true true true true (Lift 0ℓ (Fin 8) , fin)
               (lift (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
      (Block₃ , apiBF linkBD hi recvBFBlock) b1 ≡ just (Done b1)
_ = refl

-- branch 6 (repeat-produce on AC) still offers the must-offer delivery on recv@CD
_ : offersOf (prodτ b1 true true true true (Lift 0ℓ (Fin 8) , fin)
               (lift (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))
      (Block₃ , apiBF linkCD hi recvBFBlock) b1 ≡ just (Done b1)
_ = refl

-- branch 1's break-AB clears g1 (path ABD), NOT g2, and leaves both produce bits alone
_ : offersOf (prodτ b1 true true true true (Lift 0ℓ (Fin 8) , fin) (lift (fsuc fzero)))
      (U.⊤ , break linkAB) U.tt ≡ just (Prod b1 true false true true)
_ = refl

-- branch 2's break-BD clears g1 too (BD is path ABD's exit link), NOT g2 — a swap-catcher
_ : offersOf (prodτ b1 true true true true (Lift 0ℓ (Fin 8) , fin) (lift (fsuc (fsuc fzero))))
      (U.⊤ , break linkBD) U.tt ≡ just (Prod b1 true false true true)
_ = refl

-- branch 3's break-AC clears g2 (path ACD), NOT g1 — the swap-catcher
_ : offersOf (prodτ b1 true true true true (Lift 0ℓ (Fin 8) , fin)
               (lift (fsuc (fsuc (fsuc fzero)))))
      (U.⊤ , break linkAC) U.tt ≡ just (Prod b1 true true true false)
_ = refl

-- branch 4's break-CD clears g2 too (CD is path ACD's exit link), NOT g1 — a swap-catcher
_ : offersOf (prodτ b1 true true true true (Lift 0ℓ (Fin 8) , fin)
               (lift (fsuc (fsuc (fsuc (fsuc fzero))))))
      (U.⊤ , break linkCD) U.tt ≡ just (Prod b1 true true true false)
_ = refl

-- branch 5's repeat-produce on AB SETS p1 (not p2) and touches no g flag — pins FIX 1
_ : offersOf (prodτ b1 false true false true (Lift 0ℓ (Fin 8) , fin)
               (lift (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
      (Block₃ , apiBF linkAB hi sendBFBlock) b1 ≡ just (Prod b1 true true false true)
_ = refl

-- branch 6's repeat-produce on AC SETS p2 (not p1) — so A producing on AB and only LATER on AC
-- does raise the ACD obligation, which is exactly what the produce bits are for
_ : offersOf (prodτ b1 true true false true (Lift 0ℓ (Fin 8) , fin)
               (lift (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))
      (Block₃ , apiBF linkAC hi sendBFBlock) b1 ≡ just (Prod b1 true true true true)
_ = refl

-- branch 7 (the may-deliver branch) offers recv@BD even when p1 = g1 = false — so a late
-- delivery stays trace-legal although it is never obligated
_ : offersOf (prodτ b1 false false false false (Lift 0ℓ (Fin 8) , fin)
               (lift (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))
      (Block₃ , apiBF linkBD hi recvBFBlock) b1 ≡ just (Done b1)
_ = refl

-- the bare delivery menu (branches 0-6's must-offer) still REFUSES recv@BD once g1 = false —
-- confirms the must-offer really is gated; only branch 7 offers it unconditionally
_ : delivMenu b1 true false true false (Block₃ , apiBF linkBD hi recvBFBlock) b1 ≡ nothing
_ = refl

-- idle branch 2's break-BD clears g1 (path ABD), NOT g2, on the REAL idle τ-map
_ : offersOf (idleτ b1 true true (Lift 0ℓ (Fin 8) , fin) (lift (fsuc (fsuc fzero))))
      (U.⊤ , break linkBD) U.tt ≡ just (LSpec b1 false true)
_ = refl

-- idle branch 4's break-CD clears g2 (path ACD), NOT g1
_ : offersOf (idleτ b1 true true (Lift 0ℓ (Fin 8) , fin)
               (lift (fsuc (fsuc (fsuc (fsuc fzero))))))
      (U.⊤ , break linkCD) U.tt ≡ just (LSpec b1 true false)
_ = refl

-- idle branch 5: A's produce on AB enters Prod with p1 set and p2 STILL FALSE — the heart of
-- FIX 1, since it is what stops ⟨send@AB⟩ from obligating D's receive on CD
_ : offersOf (idleτ b1 true true (Lift 0ℓ (Fin 8) , fin)
               (lift (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
      (Block₃ , apiBF linkAB hi sendBFBlock) b1 ≡ just (Prod b1 true true false true)
_ = refl

-- idle branch 6: A's produce on AC enters Prod with p2 set and p1 still false (the mirror)
_ : offersOf (idleτ b1 true true (Lift 0ℓ (Fin 8) , fin)
               (lift (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))
      (Block₃ , apiBF linkAC hi sendBFBlock) b1 ≡ just (Prod b1 false true true true)
_ = refl
```

## The specification

`systemBrokenOf b` is the broken four-node diamond with A producing block `b`.
It is already `(… ∖ ioES)`, and `ioES` (input/output only) is disjoint from the
api/break channels, so `∖ hidden b` hides the remaining internal api traffic and
leaves exactly the kept alphabet visible. The initial state has both paths whole;
the Spec tracks breaks from the first event onward.

Why `⊑FD` carries the liveness content: suppose a trace reaches `Prod` in a
state where A has produced on some path's entry link and that path is still
whole (`pᵢ ∧ gᵢ`), and the system is then stable, refusing that path's
delivery. Then `(t , {recvBFBlock·b}) ∈ failures(systemBrokenOf b ∖ hidden b)`,
but `delivMenu` is present in every τ-branch of `Prod`, so `LSpec` cannot
refuse that event — the failure is absent on the left and the refinement fails.
Hence the refinement *holding* says the system never stably refuses delivery on
a path it was given the block on and that is still whole, and (by the `⊑D`
component) never livelocks before it. Where `pᵢ ∧ gᵢ` fails — both paths
broken, or A never produced on that path — `LSpec` refuses delivery too, so
the system may as well.

```agda
-- the broken four-node diamond with NodeA producing the block `b`
systemBrokenOf : Block₃ → SpecProc
systemBrokenOf b =
  (CopySpecBreakableA ∥⇘ ioES ⇙ (nodeAOf b ⦀ (nodeB ⦀ (nodeC ⦀ nodeD)))) ∖ ioES

-- sanity: instantiating at b1 recovers the shipped system (nodeAOf = nodeA)
_ : systemBrokenOf b1 ≡ systemBroken b1
_ = refl

-- THE SPECIFICATION (a Set: stated, deliberately unproved, NOT postulated)
LivenessSpec : Set _
LivenessSpec = ∀ (b : Block₃) → LSpec b true true ⊑FD (systemBrokenOf b ∖ hidden b)
```

## Truth analysis (documentation for the future proof — no code)

1. **The `⊑D` component is satisfiable: the hidden system is divergence-free.**
   Hiding creates τ's, so this needed checking — but `systemBroken` cannot
   diverge under *any* hiding set, because every maximal run is **finite**
   (order 10² events). Three facts bound it: the node drivers are finite,
   non-looping sequential processes (`produce` = nine prefixes then `Skip`,
   `FourNodeDiamond.lagda.md:200-211`; `consume` = six then `Ret`, `:223-239`
   — ≤ 60 api/`done` rendezvous system-wide, `:253-270`); every wire message
   is paid for by an api rendezvous with one of those drivers, since `apiES`
   gates all six api channels plus `done` (`:154-185`) and `∥⇘ A ⇙` requires
   both operands to offer a synced event (`CSP/Operators.agda:552-560`), which
   hiding relabels but does not lift; and nothing cycles unilaterally, as
   every `loop0` body is a `pchoice` — a stable node with no τ
   (`CSP/Operators.agda:188-191`) — so each iteration must first consume an
   `input` (`Network.agda:253-273`). There is no `div`, `⊓`, or `Run` in the
   Cardano model. So the `⊑D` inclusion is *vacuously* satisfiable, which is
   the same shape every prior Cardano FD refinement relies on.

   **Proving it formally is a separate campaign.** The tool is
   `Hide-noDiv-from-MAcc : MAcc A P → ¬ Diverges (P ∖ A)`
   (`CSP/Laws/FD/HideDivergence.agda:77-79`), instantiated at `A := hidden b`
   and `P :=` the un-hidden body, with `MAcc` built by well-founded recursion
   on a measure over a hand-written state decode (template:
   `NetworkVerification/NetworkRefinementGen.agda:2241-2247`; closest
   precedent: `BlockFetchNetRefinementBisim.agda:8550-8562` with
   `BlockFetchNetRefinementNet.agda:929`). There is **no `MAcc` closure
   calculus** — `CSP/Laws/DivFree/Closure.agda:28-33` explicitly declines the
   hide case, since hiding is "genuinely conditional" — so the decode and
   measure are bespoke work. Feasibility caution, stated precisely: in the one
   prior composite-mux refinement, non-divergence (`nd-net`) was left as a
   postulate specifically "for want of a per-state `MAcc`/measure argument" —
   the same missing ingredient named here — while what actually *defeated the
   typechecker* was the neighbouring, logically-complete `sim-fwd-ev`
   step-inversion proof, discarded because deep normalisation of the composite
   term did not finish in feasible time/memory
   (`Terminable/NetworkTRefinement.agda:592-601`, header `:28-40`). So the two
   risks are distinct and both apply: the measure is unbuilt work, and step
   inversion over a composite of this size is the documented cost wall (≈2.5 min
   / ≈20 GB per step for this four-node system).

   **Every block is an operative instance**, because the statement quantifies
   over the block-generic `systemBrokenOf b`. The shipped `systemBroken` fixes
   A's block to `b1` (`produce` offers it with `!`, a single value), which would
   have made `∀ b` vacuous for `b2`/`b3` — the kept BF events would simply be
   unreachable. `nodeAOf` removes that limitation with no change of meaning for
   any existing consumer (`nodeA = nodeAOf b1`, and `systemBrokenOf b1 ≡
   systemBroken`). The finiteness bound above is independent of the block, so
   divergence-freedom holds for every instance.

   **The Spec side is divergence-free by construction, not merely by luck.**
   `Done`, `Prod`, and `LSpec` each have a τ-map whose every branch's successor
   is itself `react`-headed with an **empty** τ-map (`∅t` for `Done`'s two
   branches and for every `prodτ`/`idleτ` branch) — so no τ-chain on the Spec
   side ever exceeds length 1, and `LSpec b true true` cannot diverge for any
   `b`, full stop, with no measure or well-founded argument needed. This is
   what makes the statement's `⊑D` half a real check on the *implementation*
   rather than something that could fail on the Spec's own account — it
   complements the finding above that the hidden implementation is
   divergence-free too, so `⊑D` is non-vacuously satisfiable on **both** sides.

2. **The delivery obligation is gated on the *produce* as well as on
   path-wholeness — the per-path produce bits.** *This is the amendment that
   makes the statement plausible at all; the earlier formulation was refuted.*
   The obligation the Spec imposes is precisely:

   > if A produced `b` on path X's **entry** link **and** path X is whole, then
   > D's receive of `b` on path X's **exit** link is not refused.

   Gating on path-wholeness alone (`delivMenu b g1 g2`) made the statement
   **false**, and at trace length 1. NodeA runs two *independent* per-link BF
   drivers (`nodeAOf b = … ∥⇘ apiES ⇙ (produce linkAB hi b ⦀ produce linkAC hi b)`,
   `FourNodeDiamond.lagda.md:255-256`), and the block reaches C only via
   `apiBF linkAC hi sendBFBlock`. So take `t = ⟨apiBF linkAB hi sendBFBlock · b⟩`
   and `X = {apiBF linkCD hi recvBFBlock · b}`. On the **implementation** side,
   the AC driver τ-advances (its `apiCS` prelude is hidden) to a state offering
   its send on AC, while the AB chain delivers as far as D's kept — hence
   *visible*, not τ — receive on BD; that state is **stable** and refuses the
   receive on CD, because C never received the block. So `(t , X) ∈ failures(…)`.
   On the **Spec** side, all eight branches of the old `Prod b true true` offered
   the receive on CD, so `(t , X) ∉ failures(LSpec b true true)` and `⊑F⊥` failed
   — for a reason with nothing to do with liveness. (Same class of defect as item
   3 below, one axis over: that one is the AB-then-BD axis, this is AB-then-CD.
   The may-deliver branch cannot help, since *adding* offers never creates a
   refusal.)

   The root cause is that path-wholeness is only half the antecedent: an
   obligation to deliver on a path presupposes that something was *put onto*
   that path. The fix carries two more state bits — `p1` = "A produced on AB",
   `p2` = "A produced on AC" — and gates each receive on the **conjunction**
   (`p1 ∧ g1`, `p2 ∧ g2`). `LSpec`'s two produce branches enter `Prod` with
   exactly the corresponding bit set (the other still `false`), and `Prod`'s two
   repeat-produce branches **set** the corresponding bit, so A producing on AB
   and only later on AC does raise the ACD obligation at that point. The `p`
   bits are monotone `false → true`, the `g` bits monotone `true → false`, so no
   event can retract an obligation once it is properly incurred. With this,
   `⟨send@AB⟩` obligates only the receive on BD — which the implementation does
   offer at every stable state, the whole A→B→D chain after A's produce being
   hidden — so the liveness bite survives intact and becomes plausible rather
   than refuted.

3. **Delivery is *permitted* more widely than it is *obligated* — the
   may-deliver branch (branch 7 of `Prod`).** Gating the delivery offer on
   path-wholeness alone (`g1`/`g2`) made the Spec forbid the trace
   `break linkAB · recvBFBlock@BD`, which the implementation **can** perform:
   if `b` crossed AB *before* AB broke, B already holds it, and B→D on BD
   still delivers. The AB crossing is itself a **hidden** event, so the Spec
   has no way to distinguish "AB broke before the block crossed" from "AB
   broke after" — both look identical once the crossing is hidden. Because
   `⊑FD` implies trace inclusion, the refinement would have failed on a
   *trace*, for a reason that has nothing to do with liveness.

   The root cause was one mechanism doing two jobs. In the failures model, an
   offer present in **every** τ-branch of a state is *obligated* — a
   must-offer, which is exactly what a stable-refusal failure can catch. An
   offer present in only **one** branch is *permitted but refusable* — the
   system may take that branch, or may take a different one that refuses it.
   The fix keeps the flag-gated `delivMenu` in every one of `Prod`'s original
   branches (so the must-offer is exactly unchanged) and adds an eighth
   τ-branch that offers **both** receives unconditionally
   (`delivMenu b true true true true`, ignoring the branch's real flags).
   Adding offers can never remove one, so when a path is produced-on and whole
   the must-offer survives verbatim through the extra branch; an unobligated
   receive, by contrast, is offered in that one extra branch only, so it stays
   refusable — "both paths broken ⇒ NodeD need not receive" is unaffected,
   while the once-forbidden late-delivery trace is now legal.

   *Rejected alternative:* gating the must-offer on the path's **terminal**
   link alone (e.g. `g1` tracking only `break linkBD`) fails the other way —
   it would *demand* delivery even when AB broke early and B never received
   the block in the first place, so the Spec would be unsatisfiable on a
   *failure*. Full rationale: Decision 11 of the design doc.

4. **Quiescence — and why `Done` must be CHAOS.** `systemBroken` **never
   terminates: it deadlocks.** Once the finite drivers `Skip`, the api gate
   blocks every api event forever (`CSP/Operators.agda:580-604`), while the
   never-terminating KeepAlive/TxSubmission/Leios peers stop the nodes from
   `√`-ing. This is the 2026-07-07 done-quiescence finding for the
   `System_CopySpec` family, and it is exactly what the failures component
   tests. Two consequences: the statement's content is that no such quiescence
   happens *between* A's produce of `b` and D's receipt of it while a path is
   whole; and the Spec's post-delivery state **must** be able to refuse
   everything, or `⊑FD` would fail on a *failure* rather than on liveness —
   which is precisely why `Done` is CHAOS (with its `Stop` τ-branch) and not a
   break-accepting `Run`-style process.

5. **Why the property is plausible.** A and D each interleave (`⦀`) their two
   per-link drivers, so a stalled broken-path driver cannot block the intact
   path's driver; B and C are pass-throughs on distinct paths; and where
   `pᵢ ∧ gᵢ` holds, A did put the block onto path *i* and that whole path A→X→D
   is unbroken, so the block's onward journey on it is composed entirely of
   **hidden** internal steps — nothing visible has to happen for D's receive to
   become available, which is exactly why the receive should never be stably
   refused. Note the gate is per-path and conjunctive: `g1 ∨ g2` alone is *not*
   what the Spec now demands (that was the refuted formulation of item 2); it
   demands the receive only on those paths A actually produced on.

6. **`LSpec` offering no receive is causally justified.** The idle state
   permits no `recvBFBlock·b` at all, which is sound only if D genuinely cannot
   receive `b` before A has sent it. It cannot: the BF server puts a block onto
   the wire **solely** as the continuation of the kept api rendezvous
   `apiBF l d sendBFBlock` (`BlockFetch.lagda.md:288-291` — `stStreaming`'s only
   block-carrying offer is `apiBFev l d sendBFBlock` continuing to `sendBF …
   (MsgBlock b)`), so no `b` exists anywhere downstream until A's kept produce
   has occurred. Hence the first kept event on any run that reaches D's receive
   is A's produce, and the idle state is never asked to offer a receive.

7. **Boundary cases the proof must confront.** (a) `break` may fire *after*
   the block is in flight on that link — the breakable medium discards the
   cell's state (`△ break → Skip`), so delivery must be argued via the other
   path's copy; note the Spec's `g` flags go false on the break, which is what
   makes this sound rather than a counterexample. (b) A's driver on a broken
   path may never emit its `sendBFBlock`; the Spec permits that, since produce
   is a may-event — and, by item 2, that path's receive then carries no
   obligation either, since its `p` bit stays `false`. (c) `Done` being CHAOS
   means nothing is claimed after the first delivery except divergence-freedom.

8. **Proof route (future).** Direct reasoning on the composite is intractable
   (≈2.5 min / ≈20 GB per step). The route is: a spec-equivalence for the
   breakable medium (`CopySpecBreakableA ≈DR` an abstract broken-copy spec,
   currently deferred); an abstract-system failures/divergences argument; then
   transfer via the FD congruences (`≈FD` compositionality of `∖`/`∥`/`⦀`) and
   `⊑FD`-monotonicity. Sizing that campaign is future work.

## The stable-failures target, and a compositional reduction of it

`LivenessSpec` above is stated at the failures–divergences order. Item 8 of the
truth analysis notes that direct reasoning on the composite is intractable, and
item 1 that the `⊑D` half needs a bespoke `MAcc` measure over a ~150-leaf
composite that nobody has built. Both obstacles are attached specifically to the
**divergence** component. So we also state the **stable-failures** analogue and,
for it, prove an honest compositional reduction.

`⊑F` retains the *entire* liveness content of the statement. The property is a
**must-offer** — "D's receive of `b` is not stably refused when A produced on a
whole path" — and a must-offer is precisely a statement about *stable refusals*,
which is exactly what `failures` records and what `⊑F` transports. Read off the
truth analysis: the refutations of the two earlier formulations (items 2 and 3)
were both located in the failures component, and the argument in "Why `⊑FD`
carries the liveness content" above uses only `failures`. What `⊑F` drops,
relative to `⊑FD`, is one strictly weaker extra clause that `⊑FD` adds on top:
*no livelock before delivery* (`⊑D`), plus the divergence-chaos closure of
`⊑F⊥`. Nothing about delivery itself is weakened.

Why the distinction is decisive rather than cosmetic. The unconditional law
`P ⊑FD Q → (P ∖ A) ⊑FD (Q ∖ A)` is **FALSE** — refuted in the header of
`CSP/Laws/FD/HideMonoFD.agda` by an infinitely-branching `P` whose hide has no
infinite τ-path — so the only available `⊑FD` hiding law is the conditional
`Hide-mono-⊑FD-df`, which demands divergence-freedom of `Q ∖ A`: here, of the
*whole hidden four-node composite*, i.e. exactly the unbuilt `MAcc` campaign of
item 1, and demanded **twice** (once per hide). `Hide-mono-⊑F`
(`CSP/Laws/FD/HideMonoFD.agda:255`) has no side condition at all: `⊑F` has no
divergence disjunct to begin with, so the branch of the `⊑FD` proof that fails
simply does not arise. Consequently the *double* hide in the target needs no
hide-algebra whatsoever — no `hide-combine`, no `∼`-bridge — just
`Hide-mono-⊑F` applied twice, once for `ioES` and once for `hidden b`.

```agda
-- THE STABLE-FAILURES SPECIFICATION (a Set: stated, deliberately unproved, NOT
-- postulated — the `⊑F` analogue of `LivenessSpec`, keeping the whole must-offer
-- content and dropping only `⊑FD`'s "no livelock before delivery" clause)
LivenessSpecF : Set _
LivenessSpecF = ∀ (b : Block₃) → LSpec b true true ⊑F (systemBrokenOf b ∖ hidden b)
```

### The reduction theorem

The theorem below is generic in the five component specifications, so it commits
to no particular abstraction of the medium or of the nodes: each is an arbitrary
`SpecProc` accompanied by its own `⊑F` obligation. Given the five obligations,
`⊑F`-monotonicity rebuilds them through the exact term structure of
`systemBrokenOf b ∖ hidden b` — `⦀-mono-⊑F` three times, matching the
**right-nested** bracketing `ASpec ⦀ (BSpec ⦀ (CSpec ⦀ DSpec))`, then
`∥-mono-⊑F` at the `ioES` interface, then `Hide-mono-⊑F` for `∖ ioES` and again
for `∖ hidden b` — leaving one residual goal about the assembled *abstract*
system, which `⊑F-trans` composes with.

```agda
-- reduces the `⊑F` liveness goal for one block to five per-component obligations
-- plus one residual goal about the assembled abstract system: `⦀-mono-⊑F` ×3
-- (right-nested), `∥-mono-⊑F`, then `Hide-mono-⊑F` ×2 (for `ioES`, then `hidden b`).
liveness-F-from-components :
    ∀ (b : Block₃) (MSpec ASpec BSpec CSpec DSpec : SpecProc)
  → MSpec ⊑F CopySpecBreakableA
  → ASpec ⊑F nodeAOf b
  → BSpec ⊑F nodeB
  → CSpec ⊑F nodeC
  → DSpec ⊑F nodeD
  → LSpec b true true
      ⊑F (((MSpec ∥⇘ ioES ⇙ (ASpec ⦀ (BSpec ⦀ (CSpec ⦀ DSpec)))) ∖ ioES) ∖ hidden b)
  → LSpec b true true ⊑F (systemBrokenOf b ∖ hidden b)
liveness-F-from-components b MSpec ASpec BSpec CSpec DSpec hM hA hB hC hD res =
  ⊑F-trans res
    (Hide-mono-⊑F (hidden b)
      (Hide-mono-⊑F ioES
        (∥-mono-⊑F ioES hM (⦀-mono-⊑F hA (⦀-mono-⊑F hB (⦀-mono-⊑F hC hD))))))
```

### The payoff, and its limit

The corollary makes the reduction's shape explicit: `LivenessSpecF` follows from
*block-indexed families* of component specs together with, for each block, the
five obligations and the residual goal.

```agda
-- `LivenessSpecF` holds as soon as, for every block, there are five component specs
-- refined by the corresponding real components and the assembled abstract system
-- satisfies the residual goal.  Pure `∀`-instantiation of the theorem above.
liveness-F-corollary :
    (MSpec ASpec BSpec CSpec DSpec : Block₃ → SpecProc)
  → (∀ b → MSpec b ⊑F CopySpecBreakableA)
  → (∀ b → ASpec b ⊑F nodeAOf b)
  → (∀ b → BSpec b ⊑F nodeB)
  → (∀ b → CSpec b ⊑F nodeC)
  → (∀ b → DSpec b ⊑F nodeD)
  → (∀ b → LSpec b true true
             ⊑F (((MSpec b ∥⇘ ioES ⇙ (ASpec b ⦀ (BSpec b ⦀ (CSpec b ⦀ DSpec b))))
                   ∖ ioES) ∖ hidden b))
  → LivenessSpecF
liveness-F-corollary MSpec ASpec BSpec CSpec DSpec hM hA hB hC hD res b =
  liveness-F-from-components b (MSpec b) (ASpec b) (BSpec b) (CSpec b) (DSpec b)
    (hM b) (hA b) (hB b) (hC b) (hD b) (res b)
```

**Structural limitation — read this before continuing the campaign.**
Monotonicity is one-directional: `SPEC ⊑F IMPL` unfolds (`Semantics/Failures.agda:42-43`)
to `failures IMPL ⊆ failures SPEC`, so a legal component spec may only be *more*
nondeterministic than the component it abstracts — abstraction **adds**
refusals. But the property being reduced is a must-offer, i.e. an assertion that
certain refusals are *absent*. Every refusal a component spec adds is a refusal
the assembled abstract system may inherit, and any such refusal that survives to
a kept `recvBFBlock·b` at a produced-on, whole path breaks the residual goal
outright. So the component specs cannot be abstracted far: each must still
witness that its share of the delivery chain cannot quiesce. Concretely, an
`MSpec` that may refuse to forward, or a `BSpec`/`CSpec` that may stall as a
pass-through, is admissible for the five obligations yet makes the residual goal
false. The reduction therefore **relocates** the difficulty into the residual
goal and buys modularity of the *plumbing* only; it does not dissolve the
liveness argument, and it gives no licence to abstract the components down to
their traces. Where it does pay is that the residual goal is stated over
hand-written finite specs instead of over the real ~150-leaf composite, which is
what makes step inversion feasible at all (item 8's ≈2.5 min / ≈20 GB per step
applies to the real composite, not to the abstract one).

## The failures-divergences reduction — the `⊑FD` analogue

`⊑F` retains the must-offer content of the property, but it is nonetheless the
**wrong** order to state the property at, and not merely a weaker one: a divergent
implementation has no stable states, hence no failures at all, so `⊑F` is satisfied
of it *vacuously*, with no delivery ever having to occur. This is not a hypothetical
worry — it is machine-checked in `CSP.Examples.InvariantMini`, whose `SysV`
(`InvariantMini.agda:633-634`) diverges after its one kept event (`V₁-diverges`,
`:703-706`) and, precisely because it therefore has no failures past that point
(`SysV-no-failure-after-a`/`V₁-no-failures`, `:718-725`), satisfies its own liveness
`Spec` vacuously: `Spec⊑F-SysV : Spec ⊑F SysV` (`:772-773`). So an `⊑F` refinement can
hold for a system that never delivers anything — `⊑FD` is what rules that out, via its
`⊑D` half, and is therefore the order that actually expresses "no livelock before
delivery," which is the whole point of a liveness statement.

The price is real, not a bookkeeping artefact: unlike `Hide-mono-⊑F`,
`Hide-mono-⊑FD-df` carries a divergence-freedom side condition on the **implementation**
side of each hide, and the double hide in `systemBrokenOf b ∖ hidden b` means the side
condition is needed **twice**. The two obligations are not the same fact stated twice —
hiding *creates* τ's, so divergence-freedom of `systemBrokenOf b` (after the `ioES` hide)
does not hand you divergence-freedom of `systemBrokenOf b ∖ hidden b` (after the second,
`hidden b`, hide) for free — but they are the *same underlying fact* recurring at two
hiding levels: both ultimately rest on the finite-run bound of item 1 of the truth
analysis (the ≤ 60-rendezvous system-wide bound), applied once per hide. That bound is
still unbuilt as a formal `MAcc` measure, so both divergence obligations below are the
campaign's remaining hard dependency, exactly as item 1 already flagged for `⊑D` in
general — the reduction below does not remove that dependency, it just isolates it into
two named, reusable hypotheses instead of one monolithic goal about the whole composite.

```agda
-- reduces the `⊑FD` liveness goal for one block to five per-component `⊑FD`
-- obligations, TWO divergence-freedom hypotheses (one per hide level — hiding creates
-- τ's, so divergence-freedom is not preserved by hiding and the second does not follow
-- from the first), and one residual goal about the assembled abstract system:
-- `⦀-mono-⊑FD` ×3 (right-nested), `∥-mono-⊑FD`, then `Hide-mono-⊑FD-df` ×2 (for `ioES`,
-- then `hidden b`), each discharged by its own divergence-freedom hypothesis on the
-- IMPLEMENTATION side at that hiding level.  The inner hypothesis is stated as
-- `¬ divergences (systemBrokenOf b) s` rather than spelling out `Body ∖ ioES`, since
-- `systemBrokenOf b` unfolds definitionally to exactly that hide and typechecks directly
-- as the argument `Hide-mono-⊑FD-df ioES` demands.
liveness-FD-from-components :
    ∀ (b : Block₃) (MSpec ASpec BSpec CSpec DSpec : SpecProc)
  → MSpec ⊑FD CopySpecBreakableA
  → ASpec ⊑FD nodeAOf b
  → BSpec ⊑FD nodeB
  → CSpec ⊑FD nodeC
  → DSpec ⊑FD nodeD
  → (∀ {s} → ¬ divergences (systemBrokenOf b) s)
  → (∀ {s} → ¬ divergences (systemBrokenOf b ∖ hidden b) s)
  → LSpec b true true
      ⊑FD (((MSpec ∥⇘ ioES ⇙ (ASpec ⦀ (BSpec ⦀ (CSpec ⦀ DSpec)))) ∖ ioES) ∖ hidden b)
  → LSpec b true true ⊑FD (systemBrokenOf b ∖ hidden b)
liveness-FD-from-components b MSpec ASpec BSpec CSpec DSpec hM hA hB hC hD hDiv1 hDiv2 res =
  ⊑FD-trans res
    (Hide-mono-⊑FD-df (hidden b)
      (Hide-mono-⊑FD-df ioES
        (∥-mono-⊑FD ioES hM (⦀-mono-⊑FD hA (⦀-mono-⊑FD hB (⦀-mono-⊑FD hC hD))))
        hDiv1)
      hDiv2)
```

The corollary mirrors `liveness-F-corollary`: block-indexed families of component specs,
both divergence-freedom hypotheses quantified over every block, and the residual goal,
together give `LivenessSpec` — the divergence-strict statement, not its vacuously
satisfiable `⊑F` cousin.

```agda
-- `LivenessSpec` holds as soon as, for every block, there are five component specs
-- refined (at `⊑FD`) by the corresponding real components, both divergence-freedom
-- obligations hold, and the assembled abstract system satisfies the residual goal.
-- Pure `∀`-instantiation of the theorem above.
liveness-FD-corollary :
    (MSpec ASpec BSpec CSpec DSpec : Block₃ → SpecProc)
  → (∀ b → MSpec b ⊑FD CopySpecBreakableA)
  → (∀ b → ASpec b ⊑FD nodeAOf b)
  → (∀ b → BSpec b ⊑FD nodeB)
  → (∀ b → CSpec b ⊑FD nodeC)
  → (∀ b → DSpec b ⊑FD nodeD)
  → (∀ b {s} → ¬ divergences (systemBrokenOf b) s)
  → (∀ b {s} → ¬ divergences (systemBrokenOf b ∖ hidden b) s)
  → (∀ b → LSpec b true true
             ⊑FD (((MSpec b ∥⇘ ioES ⇙ (ASpec b ⦀ (BSpec b ⦀ (CSpec b ⦀ DSpec b))))
                   ∖ ioES) ∖ hidden b))
  → LivenessSpec
liveness-FD-corollary MSpec ASpec BSpec CSpec DSpec hM hA hB hC hD hDiv1 hDiv2 res b =
  liveness-FD-from-components b (MSpec b) (ASpec b) (BSpec b) (CSpec b) (DSpec b)
    (hM b) (hA b) (hB b) (hC b) (hD b) (hDiv1 b) (hDiv2 b) (res b)
```

## Relation to `BlockLiveness⁺`

Both state the same informal property. `BlockLiveness⁺` uses **global**
confinement (one path group never breaks) and lives in the trace-LTL layer;
`LivenessSpec` uses **per-state** break tracking and lives in the FD
refinement layer, so it needs no implication primitive and its hypothesis is
strictly weaker. Neither is proved.
