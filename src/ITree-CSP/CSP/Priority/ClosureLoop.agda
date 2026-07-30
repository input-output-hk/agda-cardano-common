{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Layer 2 (loop closure) — a `FinBr` certificate for the self-looping
-- medium leaf `loop0 (pchoice menu)` (see the praos-over-leios plan).
--
-- The channel-level priority operator `Priᶜ` requires a `FinBr`
-- (finite-branching stability certificate) for whatever process it wraps.
-- Every `NetworkLink` medium leaf is a `loop0 (pchoice menu)` cell, and this
-- module builds its `FinBr`.
--
-- Shape analysis (all DEFINITIONAL, confirmed against `CSP.Operators`):
--   * `pchoice menu` forces to `react menu ∅t`  (stable: empty τ-part).
--   * `loop0 body   = iter-bind (loopStep body tt) (loopStep body)` where
--     `loopStep body a = body >>= loop-k`, `loop-k a′ = Ret (inj₁ a′)`
--     (from `CSP.Laws.FD.IterateFD`).
--
-- Hence `loop0 (pchoice menu) = Wtree menu (pchoice menu)`, where
--   `Wtree menu t = iter-bind (t >>= loop-k) (loopStep (pchoice menu))`
-- is "run the menu continuation `t`, then loop back".  A visible step of the
-- head cell fires a menu offer whose continuation `tcont` is an ARBITRARY
-- `PTree ⊤`; the step lands in `Wtree menu tcont`, which runs `tcont` and,
-- once it returns, τ-loops back to `loop0 (pchoice menu)`.
--
-- So `finBr-loop0menu` needs, besides the finite offer support, a `FinBr`
-- for each menu continuation (`menufin`).  The certificate for the running
-- continuation is `finBr-loopseq`, corecursive with `finBr-loop0menu` at the
-- loop-back point; the corecursive calls sit directly under the `FinBr.next`
-- copattern (guarded, exactly as `finBr-∥`/`finBr-div` in `Closure.agda`), so
-- NO `NON_TERMINATING` / sized types.
--
-- Safe discipline (as `Closure.agda`; the literal `--safe` flag is co-infective
-- and blocked by a pre-existing postulate in the imported `IterateFD` chain
-- (`CSP.Laws.FD.IterateFD`), so the pragma is just `--guardedness`): no
-- `postulate`, no `NON_TERMINATING`, no `--sized-types`,
-- nothing from `Classical`/`dne`.  A single-step inversion `loopbody-elim`
-- (indexed by the target tree, mirroring `Par-ev-elim`) refines each successor so
-- the guarded corecursive calls need no `subst`.
------------------------------------------------------------------------

open import Level using (lower; _⊔_) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
import Data.Maybe.Relation.Unary.Any as MAny
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂; Σ-syntax)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees

module CSP.Priority.ClosureLoop {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open PTree
open import Semantics.LTS {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import CSP.Priority.Base {ℓ} {ℓe} {E} using (FinBr)
open import CSP.Operators E-≟
  using (loop0; pchoice; iter-bind; _>>=_; Ret; iterV; iterT; bindV; bindT; viewV; viewT; ⦀⋆)
open import CSP.Priority.Closure {ℓ} {ℓe} E-≟
  using (finBr-⦀; finBr-Skip)
open import CSP.Laws.FD.IterateFD E-≟
  using (loop-k; loopStep;
         iterV-inv; iterT-inv; sil-inj; react-inj-v; react-inj-τ)
open import CSP.Laws.Traces.TraceLawsBind E-≟
  using (bindV-elim; bindT-elim)

------------------------------------------------------------------------
-- The visible-offer menu shape carried by every leaf: an offer map into
-- `PTree ⊤` continuations (as in `CSP.Examples.Cardano_network.Network.Menu`).
------------------------------------------------------------------------

Menu : Set (lsuc ℓ ⊔ ℓe)
Menu = (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) (⊤ {ℓ})))

------------------------------------------------------------------------
-- Small maybe/continuation helpers (local copies of `Closure.agda`'s private
-- lemmas; kept here so this module stays independent of `Closure`).
------------------------------------------------------------------------

private
  -- extract a `just`-witness from `Is-just`, and its converse.
  is-just→just : ∀ {ℓ'} {X : Set ℓ'} {m : Maybe X} → Is-just m → Σ[ x ∈ X ] m ≡ just x
  is-just→just {m = just x} _ = x , refl

  ≡just→Is-just : ∀ {ℓ'} {X : Set ℓ'} {m : Maybe X} {x} → m ≡ just x → Is-just m
  ≡just→Is-just refl = MAny.just _

  -- read `isStable` off a react-forced node (both directions), given its force eq.
  st→τc∅ : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R}
             {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
             {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
         → PTree.force t ≡ react v τc → isStable t → ∀ i a → τc i a ≡ nothing
  st→τc∅ {t = t} eqf st with PTree.force t | eqf
  ... | react v τc | refl = st

  τc∅→st : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R}
             {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
             {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
         → PTree.force t ≡ react v τc → (∀ i a → τc i a ≡ nothing) → isStable t
  τc∅→st {t = t} eqf h with PTree.force t | eqf
  ... | react v τc | refl = h

  -- a visible step of `P` at channel `(A₀,e₀)` ⇒ that channel is in P's support.
  vstep→chan∈ : ∀ {ℓr} {R : Set ℓr} {P : PTree E (ExtI E) R}
                  {A₀ : Set ℓ} {e₀ : E A₀} {a₀ : A₀} {t′}
              → (fp : FinBr P)
              → P ─[ ev (evl (evLabel A₀ e₀ a₀)) ]─► t′
              → (A₀ , e₀) ∈ FinBr.chan-supp fp
  vstep→chan∈ {A₀ = A₀} {e₀ = e₀} {a₀ = a₀} fp step with ev-inv step
  ... | vP , τcP , eqP , br = FinBr.chan-compl fp eqP (A₀ , e₀) a₀ (≡just→Is-just br)

  -- `iterT`/`bindT` are `nothing` exactly where their underlying `viewT` is.
  iterT-nothing : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
      (k : A → PTree E (ExtI E) (A ⊎ R)) (nP : NodeKind E (ExtI E) (A ⊎ R))
      {i : AnyTypes (ExtI E)} {a : proj₁ i}
    → viewT nP i a ≡ nothing → iterT k nP i a ≡ nothing
  iterT-nothing k nP {i} {a} e with viewT nP i a | e
  ... | nothing | _ = refl

  iterT-nothing-inv : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
      (k : A → PTree E (ExtI E) (A ⊎ R)) (nP : NodeKind E (ExtI E) (A ⊎ R))
      {i : AnyTypes (ExtI E)} {a : proj₁ i}
    → iterT k nP i a ≡ nothing → viewT nP i a ≡ nothing
  iterT-nothing-inv k nP {i} {a} e with viewT nP i a
  ... | nothing = refl
  ... | just x  = case e of λ ()

  bindT-nothing : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      (k : R → PTree E (ExtI E) S) (nP : NodeKind E (ExtI E) R)
      {i : AnyTypes (ExtI E)} {a : proj₁ i}
    → viewT nP i a ≡ nothing → bindT k nP i a ≡ nothing
  bindT-nothing k nP {i} {a} e with viewT nP i a | e
  ... | nothing | _ = refl

  bindT-nothing-inv : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      (k : R → PTree E (ExtI E) S) (nP : NodeKind E (ExtI E) R)
      {i : AnyTypes (ExtI E)} {a : proj₁ i}
    → bindT k nP i a ≡ nothing → viewT nP i a ≡ nothing
  bindT-nothing-inv k nP {i} {a} e with viewT nP i a
  ... | nothing = refl
  ... | just x  = case e of λ ()

------------------------------------------------------------------------
-- `Wtree menu t` = "run continuation `t`, then loop back to loop0 (pchoice menu)".
-- Definitionally `Wtree menu (pchoice menu) ≡ loop0 (pchoice menu)`.
------------------------------------------------------------------------

Wtree : ∀ {ℓr} {R : Set ℓr} (menu : Menu)
      → PTree E (ExtI E) (⊤ {ℓ}) → PTree E (ExtI E) R
Wtree menu t = iter-bind (t >>= loop-k) (loopStep (pchoice menu))

------------------------------------------------------------------------
-- Single-step inversion for `Wtree menu tcont`, indexed by the target tree
-- (mirrors `Par-ev-elim`/`ParevR`), so `next` refines each successor with no
-- `subst` on the corecursive result — keeping guardedness syntactic.
--
-- Every clause follows `iter-bind-inv`'s idiom: `with PTree.force tcont in eqt
-- | eqf` so the step's own force-equation `eqf` reduces once the continuation's
-- forced node is exposed (the abstraction rewrites the stuck `force tcont`).
------------------------------------------------------------------------

data LoopBodyStep {ℓr} {R : Set ℓr} (menu : Menu) (tcont : PTree E (ExtI E) (⊤ {ℓ}))
   : PTree E (ExtI E) R → Label R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  -- the continuation fires a visible offer ⇒ run its successor, then loop.
  lbVis  : ∀ {X} {e : E X} {a : X} {Pv}
         → tcont ─[ ev (evl (evLabel X e a)) ]─► Pv
         → LoopBodyStep menu tcont (Wtree menu Pv) (ev (evl (evLabel X e a)))
  -- the continuation does its own τ ⇒ slide on.
  lbTau  : ∀ {c} → tcont ─[ τ ]─► c → LoopBodyStep menu tcont (Wtree menu c) τ
  -- the continuation returned ⇒ τ loop-back to the head cell.
  lbLoop : PTree.force tcont ≡ ret tt → LoopBodyStep menu tcont (loop0 (pchoice menu)) τ

-- invert a step of `Wtree menu tcont` into a `LoopBodyStep`.
loopbody-elim : ∀ {ℓr} {R : Set ℓr} (menu : Menu) (tcont : PTree E (ExtI E) (⊤ {ℓ}))
                  {t′ : PTree E (ExtI E) R} {l : Label R}
              → (Wtree menu tcont) ─[ l ]─► t′
              → LoopBodyStep menu tcont t′ l
-- √ tick: `Wtree` never forces to `ret` (loop-k only tags `inj₁`), so absurd.
loopbody-elim menu tcont (sRet eqf) with PTree.force tcont in eqt | eqf
... | ret tt       | ()   -- force = sil (loop-back) ≠ ret
... | sil c        | ()   -- force = sil (slide)     ≠ ret
... | react vP τcP | ()   -- force = react           ≠ ret
-- silent step: either the loop-back (continuation returned) or a slide.
loopbody-elim menu tcont (sSil eqf) with PTree.force tcont in eqt | eqf
... | ret tt       | eqf′ =
      subst (λ x → LoopBodyStep menu tcont x τ) (sil-inj eqf′) (lbLoop eqt)
... | sil c        | eqf′ =
      subst (λ x → LoopBodyStep menu tcont x τ) (sil-inj eqf′) (lbTau (sSil eqt))
... | react vP τcP | ()   -- force = react ≠ sil
-- τ-branch step: the continuation's own τ (lifted through bind/iter).
loopbody-elim menu tcont (sTau {i = i} {a = a} eqf brτ) with PTree.force tcont in eqt | eqf
... | ret tt       | ()   -- force = sil ≠ react
... | sil c        | ()   -- force = sil ≠ react
... | react vP τcP | eqf′
      with iterT-inv (loopStep (pchoice menu)) (bindV loop-k (react vP τcP)) (bindT loop-k (react vP τcP))
             (subst (λ f → f i a ≡ just _) (sym (react-inj-τ eqf′)) brτ)
...   | u , eqτ' , equ with bindT-elim loop-k (react vP τcP) eqτ'
...     | Pt , eqvτ , equ2 =
          subst (λ x → LoopBodyStep menu tcont x τ)
                (trans (cong (λ z → iter-bind z (loopStep (pchoice menu))) (sym equ2)) equ)
                (lbTau (sTau eqt eqvτ))
-- visible step: the continuation's own offer (lifted through bind/iter).
loopbody-elim menu tcont (sVis {at = at} {a = a} eqf brv) with PTree.force tcont in eqt | eqf
... | ret tt       | ()   -- force = sil ≠ react
... | sil c        | ()   -- force = sil ≠ react
... | react vP τcP | eqf′
      with iterV-inv (loopStep (pchoice menu)) (bindV loop-k (react vP τcP)) (bindT loop-k (react vP τcP))
             (subst (λ f → f at a ≡ just _) (sym (react-inj-v eqf′)) brv)
...   | u , eqv' , equ with bindV-elim loop-k (react vP τcP) eqv'
...     | Pv , eqvv , equ2 =
          subst (λ x → LoopBodyStep menu tcont x (ev (evl (evLabel (proj₁ at) (proj₂ at) a))))
                (trans (cong (λ z → iter-bind z (loopStep (pchoice menu))) (sym equ2)) equ)
                (lbVis (sVis eqt eqvv))

------------------------------------------------------------------------
-- `FinBr` for the head cell `pchoice menu` (a stable react node, exactly
-- `finBr-prefix` generalised to a multi-channel menu with supplied support).
------------------------------------------------------------------------

-- support + completeness + a `FinBr` for every menu continuation.
finBr-pchoice : ∀ (menu : Menu)
                  (supp : List (AnyTypes E))
                  (compl : ∀ at a → Is-just (menu at a) → at ∈ supp)
                  (menufin : ∀ at a t → menu at a ≡ just t → FinBr {R = ⊤ {ℓ}} t)
              → FinBr {R = ⊤ {ℓ}} (pchoice menu)
FinBr.stable?   (finBr-pchoice menu supp compl menufin) = yes (λ i a → refl)   -- τc = ∅t
FinBr.chan-supp (finBr-pchoice menu supp compl menufin) = supp
FinBr.chan-compl (finBr-pchoice menu supp compl menufin) refl at a isj = compl at a isj
FinBr.next (finBr-pchoice menu supp compl menufin) (sVis {at = at} {a = a} refl br) = menufin at a _ br
FinBr.next (finBr-pchoice menu supp compl menufin) (sRet ())        -- react ≢ ret
FinBr.next (finBr-pchoice menu supp compl menufin) (sSil ())        -- react ≢ sil
FinBr.next (finBr-pchoice menu supp compl menufin) (sTau refl ())   -- τc = ∅t ⇒ absurd

------------------------------------------------------------------------
-- `FinBr` for the running continuation `Wtree menu tcont`, corecursive with
-- itself (slide) and with `finBr-pchoice` (loop-back).  Every corecursive call
-- sits under the `FinBr.next` copattern (guarded).
------------------------------------------------------------------------

finBr-loopseq : ∀ {ℓr} {R : Set ℓr}
                  (menu : Menu)
                  (supp : List (AnyTypes E))
                  (compl : ∀ at a → Is-just (menu at a) → at ∈ supp)
                  (menufin : ∀ at a t → menu at a ≡ just t → FinBr {R = ⊤ {ℓ}} t)
                  (tcont : PTree E (ExtI E) (⊤ {ℓ}))
              → FinBr {R = ⊤ {ℓ}} tcont
              → FinBr {R = R} (Wtree menu tcont)
-- stability: `ret`/`sil` continuations leave `Wtree` a sil node (unstable);
-- a react continuation is stable iff it is (τ-maps agree pointwise).
FinBr.stable? (finBr-loopseq menu supp compl menufin tcont fb) with PTree.force tcont in eqt
... | ret tt        = no lower
... | sil c        = no lower
... | react vP τcP with FinBr.stable? fb
...   | yes st = yes (λ i a →
          iterT-nothing (loopStep (pchoice menu))
            (react (bindV loop-k (react vP τcP)) (bindT loop-k (react vP τcP)))
            (bindT-nothing loop-k (react vP τcP) (st→τc∅ {t = tcont} eqt st i a)))
...   | no ¬st = no (λ emt → ¬st (τc∅→st {t = tcont} eqt (λ i a →
          bindT-nothing-inv loop-k (react vP τcP)
            (iterT-nothing-inv (loopStep (pchoice menu))
               (react (bindV loop-k (react vP τcP)) (bindT loop-k (react vP τcP)))
               (emt i a)))))
-- offers exactly the continuation's channels.
FinBr.chan-supp (finBr-loopseq menu supp compl menufin tcont fb) = FinBr.chan-supp fb
FinBr.chan-compl (finBr-loopseq menu supp compl menufin tcont fb) eqr at a isj
  with is-just→just isj
... | t′ , br with loopbody-elim menu tcont (sVis eqr br)
...   | lbVis Pev = vstep→chan∈ fb Pev
-- step inversion: slide on (visible / τ), or loop back once the continuation returns.
FinBr.next (finBr-loopseq menu supp compl menufin tcont fb) step
  with loopbody-elim menu tcont step
... | lbVis Pev = finBr-loopseq menu supp compl menufin _ (FinBr.next fb Pev)
... | lbTau cτ  = finBr-loopseq menu supp compl menufin _ (FinBr.next fb cτ)
... | lbLoop _  = finBr-loopseq menu supp compl menufin (pchoice menu)
                    (finBr-pchoice menu supp compl menufin)

------------------------------------------------------------------------
-- `finBr-loop0menu` — the deliverable: `FinBr` for a single self-looping menu
-- cell `loop0 (pchoice menu)` (definitionally `Wtree menu (pchoice menu)`).
------------------------------------------------------------------------

finBr-loop0menu : ∀ {ℓr} {R : Set ℓr}
                    (menu : Menu)
                    (supp : List (AnyTypes E))
                    (compl : ∀ at a → Is-just (menu at a) → at ∈ supp)
                    (menufin : ∀ at a t → menu at a ≡ just t → FinBr {R = ⊤ {ℓ}} t)
                → FinBr {R = R} (loop0 (pchoice menu))
finBr-loop0menu menu supp compl menufin =
  finBr-loopseq menu supp compl menufin (pchoice menu) (finBr-pchoice menu supp compl menufin)

------------------------------------------------------------------------
-- `finBr-⦀⋆` — `FinBr` for a replicated interleaving `⦀⋆ ps` (CSP `|||`),
-- by structural recursion on `ps` folding the binary `finBr-⦀` (Closure.agda),
-- with `finBr-Skip` as the `⦀⋆ [] = Skip` base case.  Ordinary list recursion,
-- not corecursion (no guardedness subtlety).
------------------------------------------------------------------------

finBr-⦀⋆ : ∀ {ℓr} (ps : List (PTree E (ExtI E) (⊤ {ℓr})))
         → All FinBr ps
         → FinBr {R = ⊤ {ℓr}} (⦀⋆ ps)
finBr-⦀⋆ []       []          = finBr-Skip
finBr-⦀⋆ (p ∷ ps) (fp ∷ fbs)  = finBr-⦀ fp (finBr-⦀⋆ ps fbs)
