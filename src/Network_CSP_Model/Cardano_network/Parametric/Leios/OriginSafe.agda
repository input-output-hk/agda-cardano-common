{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE GENERIC ORIGIN/SOUNDNESS CARRIER.
--
-- Every safety theorem of the Linear-Leios campaign has the same shape:
-- some labels MINT keys, some labels are GATED by the keys minted so far,
-- and the claim is that the composite never fires a gated label whose gate
-- is shut.  `Parametric.AnnounceSafeCarrier` is that pattern written once
-- for announcements; this module is it written once for all of them.
--
-- TWO SIMPLIFICATIONS OVER `AnnounceSafeCarrier`.
--   * The gate reads the WHOLE minted set (`gate : Minted → at → a → Bool`),
--     not one key, so cert soundness (S3 — "these blobs certify this hash")
--     is an instance and not a separate carrier.
--   * The offer map is UNIFORM in the channel (`if gate ms at a then …`),
--     so the thirty-clause `menuStep` alphabet enumeration that
--     `AnnounceSafeCarrier` needs (its catch-all does not reduce until the
--     constructor is known) collapses to one clause, and `onForge`/`onOther`
--     collapse to one field `onEv`.
--
-- THE SHAPE OF `FreeAt` (the leaf predicate five tasks will use).  A leaf is
-- FREE when every visible event it can ever perform is ungated AT EVERY
-- MINTED SET, it never ticks, and every state it steps to is free again.  It
-- says NOTHING about minting — a free leaf may mint freely, because
-- `osafe-free : FreeAt M → OSafe ms M` holds at every `ms` and the minted set
-- therefore never matters.  That is one obligation fewer per leaf than the
-- plan's sketch (which also asked for `mints … ≡ []`); the obligation is
-- genuinely unnecessary, not dropped.  `fEv` bundles the gate fact with the
-- coinductive residual so a leaf inverts each step once, not twice.
--
-- `osafe-ParL` AND `osafe-ParR` ARE THE SAME LEMMA, and are shipped as two
-- ALIASES of one `osafe-Par`.  Which operand the `evSync` arm takes the gate
-- from is invisible in the type: both arms prove the same proposition
-- `gate ms (X , e) a ≡ true` from hypotheses the lemma demands anyway.
--
-- THE REAL ASYMMETRY IS THE HYPOTHESIS, AND `OSafe∖` IS THE ANSWER.  At a
-- rendezvous ONE side emits a gated label with a value it computed, and the
-- other side merely ACCEPTS it — and an accepting side offers the label for
-- EVERY value, so it has no `OSafe` at all (`Gated` is outright false for it).
-- The emitting side is where the gate obligation belongs; the accepting side
-- takes the waiver `OSafe∖ A`, which is `OSafe` with `gateOK` dropped exactly
-- on the synchronisation set `A` — sound because an `A`-event cannot fire
-- without its partner's agreement.  Which side accepts depends on the
-- theorem, so BOTH directions are shipped:
--   * `osafe-ParS`  waives the LEFT operand.  S3 (cert soundness): the vote
--     store EMITS `stCert ! h` (right), and `certSink` — a thread — merely
--     absorbs it (left, `NodeLogicL.certSink`).
--   * `osafe-ParS′` waives the RIGHT operand.  S2/S1/S2′: the voter/forge
--     THREAD emits `stPutVote v` / `stPutBody eb` (left, and it carries the
--     gate), and the store accepts any value (right, `NodeLogicL.voteStep`,
--     `NodeLogicL.bodyStep`).
-- `osafe∖-Par`/`osafe∖-⦀`/`osafe∖-⦀Fin⁺` carry the waiver through the fold
-- that contains the accepting leaf; `osafe∖-offers` builds the leaf itself.
--
-- WHAT IT BUYS.  `osafe→⊑T` turns ONE `OSafe []` fact about a composite
-- into the whole `⊑T` safety property.  Nothing here proves a leaf fact;
-- that is each instance's job (Tasks 8–12).
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.OriginSafe where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties using (any⁺; any⁻)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI

open import Process_Trees using (PTree; ptree; react; AnyTypes; ContinueType; ExtI)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Topology using (Topology)
import Cardano_network.Net as N
import Cardano_network.Data as D
import CSP.Operators as O

------------------------------------------------------------------------
-- Membership, once, for every instance
--
-- `NodeLogicL.memberOf` is DEFINITIONALLY this function, so the two lemmas
-- below apply to the stores' own membership tests verbatim.  They are public
-- because Tasks 8–12 are told to reuse `memberOf-mono` as it stands.
------------------------------------------------------------------------

-- is `x` in `xs`?
memberOf : ∀ {A : Set} → ⦃ DecEq A ⦄ → A → List A → Bool
memberOf x xs = any (λ y → ⌊ y ≟ x ⌋) xs

-- the Boolean test reflects propositional membership
memberOf→∈ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ (x : A) (xs : List A)
           → memberOf x xs ≡ true → x ∈ xs
memberOf→∈ x xs eq =
  Any.map (λ {y} t → sym (toWitness t))
          (any⁻ (λ y → ⌊ y ≟ x ⌋) xs (Equivalence.from T-≡ eq))

-- …and propositional membership implies the Boolean test
∈→memberOf : ∀ {A : Set} ⦃ _ : DecEq A ⦄ (x : A) (xs : List A)
           → x ∈ xs → memberOf x xs ≡ true
∈→memberOf x xs q =
  Equivalence.to T-≡
    (any⁺ (λ y → ⌊ y ≟ x ⌋) (Any.map (λ {y} e → fromWitness (sym e)) q))

-- MEMBERSHIP IS MONOTONE under list inclusion: this is what makes a membership
-- gate satisfy `gate-mono` in every instance
memberOf-mono : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {x : A} {xs ys : List A}
              → xs ⊆ ys → memberOf x xs ≡ true → memberOf x ys ≡ true
memberOf-mono {x = x} {xs = xs} {ys = ys} sub eq =
  ∈→memberOf x ys (sub (memberOf→∈ x xs eq))

------------------------------------------------------------------------
-- The generic layer
------------------------------------------------------------------------

-- the carrier, parametric in the network parameters, the topology and the api
-- alphabet — the same three parameters `Parametric.Node` takes, so `Proc` below
-- is literally that module's
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  open N p using (Net_Api; Net_Api-≟)
  open D p using (Payload)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload})
    using ( pchoice; Ret; _>>=_; iter; iter-bind; loop; loop0; Stop; _⊓_
          ; Skip; Prefix₀
          ; EventSet; ∅ES; Par; par-brBoth; _⦀_; _∥⇘_⇙_; _∖_; ⦀Fin⁺ )
  open import Cardano_network.Parametric.Node p t apiES using (Proc)
  open import Semantics.LTS
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (Label; Event√; ev; τ; evl; √; evLabel; _─[_]─►_; sRet; sVis; sSil)
  open import Semantics.WeakBisim
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (_═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl; τ*-step)
  open import Semantics.WeakSim
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (WSim; wsim→⊑T)
  open import Semantics.Failures
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⊑T_)
  open import Semantics.BisimFromRel
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (module WSimFromRel)
  open import CSP.Laws.Bisim.IterCong (Net_Api-≟ {Payload}) using (iter-bind-ev)
  open import CSP.Laws.Traces.TraceLawsBind (Net_Api-≟ {Payload}) using (bind-ev)
  open import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload})
    using (Par-τ-elim; τL; τR; Par-ev-elim; evSync; evL; evR; evBoth; ev√)
  open import CSP.Laws.Traces.TraceLawsParallelTrace (Net_Api-≟ {Payload})
    using (brBoth-τ-elim; brBoth-no-ev)
  open import CSP.Laws.Traces.TraceLawsHide (Net_Api-≟ {Payload})
    using (Hide-τ-elim; hτP; hτH; Hide-ev-elim; heV; he√)
  open import CSP.Laws.Traces.TraceLawsExtChoice (Net_Api-≟ {Payload}) using (NonRet)
  open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
    using ( OffersOnly; NoRet; OffersOnly-mono
          ; OffersOnly-Skip; OffersOnly-Prefix₀; OffersOnly-loop0; NoRet-loop0 )

  -- a process that never returns cannot TICK: a `√` step is exactly a `ret` node.
  -- (`AnnounceSafeLeaves.noRet→noTick`, re-derived here so nothing is imported from
  -- the announcement campaign.)
  noRet→noTick : ∀ {M M′ : Proc} {x : ⊤ {0ℓ}} → NoRet M → M ─[ ev (√ x) ]─► M′ → ⊥
  noRet→noTick nr (sRet eq) = subst NonRet eq (NoRet.nowNR nr)

  -- one origin discipline: a key type, what each label mints, what each label needs,
  -- and the fact that minting more can only OPEN gates, never shut them
  module Origin
    (Key : Set) (dk : DecEq Key)
    (mints : (at : AnyTypes (Net_Api Payload)) → proj₁ at → List Key)
    (gate  : List Key → (at : AnyTypes (Net_Api Payload)) → proj₁ at → Bool)
    (gate-mono : ∀ {ms ms′} → ms ⊆ ms′
               → ∀ at a → gate ms at a ≡ true → gate ms′ at a ≡ true) where

    instance
      -- the key equality, re-exported so instance search inside and below this
      -- module resolves `memberOf` at `Key`
      DecEq-Key : DecEq Key
      DecEq-Key = dk

    ------------------------------------------------------------------------
    -- The minted set
    ------------------------------------------------------------------------

    -- the keys minted so far.  Keys are never removed: a permission, once granted, is
    -- permanent — which is what makes `gate-mono` the only monotonicity law needed.
    Minted : Set
    Minted = List Key

    -- the minted set after a label
    mintedAfter : (at : AnyTypes (Net_Api Payload)) → proj₁ at → Minted → Minted
    mintedAfter at a ms = mints at a ++ ms

    -- the minted set only grows
    mintedAfter-⊇ : ∀ at a {ms} → ms ⊆ mintedAfter at a ms
    mintedAfter-⊇ at a = ∈-++⁺ʳ (mints at a)

    -- growing the minted set on both sides of a label keeps the inclusion
    mintedAfter-mono : ∀ at a {ms ms′} → ms ⊆ ms′
                     → mintedAfter at a ms ⊆ mintedAfter at a ms′
    mintedAfter-mono at a sub q with ∈-++⁻ (mints at a) q
    ... | inj₁ l = ∈-++⁺ˡ l
    ... | inj₂ r = ∈-++⁺ʳ (mints at a) (sub r)

    ------------------------------------------------------------------------
    -- The specification
    ------------------------------------------------------------------------

    -- THE SPECIFICATION'S OFFER MAP, uniform in the channel: a label is offered iff its
    -- gate is open, and firing it mints whatever it mints
    originOffer : Minted → (at : AnyTypes (Net_Api Payload))
                → ContinueType at
                    (Maybe (PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Minted))
    originOffer ms at a = if gate ms at a then just (Ret (mintedAfter at a ms)) else nothing

    -- THE SPECIFICATION at `⊑T`: every trace is permitted except one firing a gated
    -- label whose gate is shut.  No `⊓ Stop` — `⊑T` ignores refusals, so the
    -- Chaos-shaping the `⊑F` family needs is inert (`AnnounceSafe.AnnounceSpecT`).
    OriginSpecT : Proc
    OriginSpecT = loop (λ ms → pchoice (originOffer ms)) []

    -- THE SPECIFICATION at `⊑F`, for a consumer that needs a refusal-saturated spec:
    -- the `⊓ Stop` makes it Chaos-shaped rather than RUN-shaped, so it imposes no
    -- offer obligation.  The bridge below targets `OriginSpecT`; relating the two is
    -- `AnnounceSafe`'s collapse argument (`saturated→⊑T→⊑F`), not re-proved here.
    OriginSpec : Proc
    OriginSpec = loop (λ ms → pchoice (originOffer ms) ⊓ Stop) []

    ------------------------------------------------------------------------
    -- The carrier
    ------------------------------------------------------------------------

    -- the gate as a proposition about a process: every visible step it can take has an
    -- open gate
    Gated : Minted → Proc → Set₁
    Gated ms M = ∀ {X} {e : Net_Api Payload X} {a : X} {M′}
               → M ─[ ev (evl (evLabel X e a)) ]─► M′ → gate ms (X , e) a ≡ true

    -- SAFETY AS A COINDUCTIVE PREDICATE ON PROCESSES: `M` fires no shut-gated label,
    -- and every state it steps to is safe against the set that step leaves behind
    record OSafe (ms : Minted) (M : Proc) : Set₁ where
      coinductive
      field
        -- here and now: every visible step of `M` has an open gate
        gateOK : Gated ms M
        -- a τ — including the resolution of a `par-brBoth` collision — keeps `ms`
        onτ    : ∀ {M′} → M ─[ τ ]─► M′ → OSafe ms M′
        -- a visible step mints what it mints
        onEv   : ∀ {X} {e : Net_Api Payload X} {a : X} {M′}
               → M ─[ ev (evl (evLabel X e a)) ]─► M′
               → OSafe (mintedAfter (X , e) a ms) M′
        -- `M` never TICKS: the spec is a `loop`, so it has no `√` to match one with
        noTick : ∀ {x : ⊤ {0ℓ}} {M′} → M ─[ ev (√ x) ]─► M′ → ⊥
    open OSafe public

    -- a label that mints nothing leaves the minted set alone.  Not corecursive — it is
    -- a `subst`, and it is applied to the ARGUMENT of a corecursive call, never around
    -- one, so productivity is unaffected.
    osafe-nomint : ∀ {at a ms M} → mints at a ≡ []
                 → OSafe (mintedAfter at a ms) M → OSafe ms M
    osafe-nomint {ms = ms} {M = M} eq h = subst (λ ks → OSafe (ks ++ ms) M) eq h

    -- minting only ever OPENS gates, so a state safe against a smaller minted set is
    -- safe against a larger one.  Corecursive through every field, guarded by copatterns.
    osafe-mono : ∀ {ms ms′ M} → ms ⊆ ms′ → OSafe ms M → OSafe ms′ M
    osafe-mono sub s .gateOK st = gate-mono sub _ _ (gateOK s st)
    osafe-mono sub s .onτ    st = osafe-mono sub (onτ s st)
    osafe-mono sub s .onEv {e = e} {a = a} st =
      osafe-mono (mintedAfter-mono (_ , e) a sub) (onEv s st)
    osafe-mono sub s .noTick st = noTick s st

    ------------------------------------------------------------------------
    -- The vacuous leaf
    ------------------------------------------------------------------------

    -- A FREE PROCESS: every visible event it can perform is ungated at EVERY minted
    -- set, it never ticks, and every state it steps to is free again.  Minting is
    -- irrelevant — see the module header.  `fEv` bundles the gate fact with the
    -- residual so one step inversion discharges both.
    record FreeAt (M : Proc) : Set₁ where
      coinductive
      field
        -- a visible step: its gate is open whatever has been minted, and the successor
        -- is free
        fEv   : ∀ {X} {e : Net_Api Payload X} {a : X} {M′}
              → M ─[ ev (evl (evLabel X e a)) ]─► M′
              → (∀ ms → gate ms (X , e) a ≡ true) × FreeAt M′
        -- a τ keeps the process free
        fτ    : ∀ {M′} → M ─[ τ ]─► M′ → FreeAt M′
        -- a free process never ticks either
        fTick : ∀ {x : ⊤ {0ℓ}} {M′} → M ─[ ev (√ x) ]─► M′ → ⊥
    open FreeAt public

    -- A VACUOUS LEAF IS SAFE, at every minted set
    osafe-free : ∀ {ms M} → FreeAt M → OSafe ms M
    osafe-free f .gateOK st = proj₁ (fEv f st) _
    osafe-free f .onτ    st = osafe-free (fτ f st)
    osafe-free f .onEv   st = osafe-free (proj₂ (fEv f st))
    osafe-free f .noTick st = fTick f st

    ------------------------------------------------------------------------
    -- The congruences
    --
    -- `OSafe` is closed under the three operators the composite is built from:
    -- parallel (hence interleaving and its replicated form) and hiding.  Each is
    -- proved by ONE inversion of the operator's step relation, per field, with
    -- copattern-guarded corecursion — no state family, no reachability induction.
    ------------------------------------------------------------------------

    -- THE PARALLEL CONGRUENCE, and its collision companion, mutually corecursive.
    --
    -- `osafe-both` covers the `par-brBoth` COLLISION node `Par`'s `par-pVis` builds when
    -- both operands offer the same event outside the synchronisation set.  That node
    -- offers NO visible event at all, so three of its four fields are discharged
    -- outright by `brBoth-no-ev`; its only moves are the two internal-choice τ's
    -- committing to `Par P′ Q` or `Par P Q′`, and those go straight back into
    -- `osafe-Par`.
    osafe-Par  : ∀ {ms} (A : EventSet) {P Q}
               → OSafe ms P → OSafe ms Q → OSafe ms (P ∥⇘ A ⇙ Q)
    osafe-both : ∀ {ms} (A : EventSet) {P Q P′ Q′}
               → OSafe ms P → OSafe ms Q → OSafe ms P′ → OSafe ms Q′
               → OSafe ms (ptree (react (λ _ _ → nothing)
                                  (par-brBoth A (λ _ _ → tt) P Q P′ Q′)))

    -- a visible event of the composite is that event in one operand, which licenses it
    osafe-Par A {P = P} {Q = Q} sP sQ .gateOK st with Par-ev-elim A (λ _ _ → tt) P Q st
    ... | evSync _ stP _   = gateOK sP stP
    ... | evL    _ stP     = gateOK sP stP
    ... | evR    _ stQ     = gateOK sQ stQ
    ... | evBoth _ stP _   = gateOK sP stP
    -- a τ of the composite is a τ of one operand; the other is untouched
    osafe-Par A {P = P} {Q = Q} sP sQ .onτ st with Par-τ-elim A (λ _ _ → tt) P Q st
    ... | τL P′ stP refl   = osafe-Par A (onτ sP stP) sQ
    ... | τR Q′ stQ refl   = osafe-Par A sP (onτ sQ stQ)
    -- a visible event: whichever operand(s) performed it move to the grown minted set,
    -- and the operand that did not is carried across by `osafe-mono`
    osafe-Par A {P = P} {Q = Q} sP sQ .onEv {e = e} {a = a} st
      with Par-ev-elim A (λ _ _ → tt) P Q st
    ... | evSync _ stP stQ = osafe-Par A (onEv sP stP) (onEv sQ stQ)
    ... | evL    _ stP     = osafe-Par A (onEv sP stP)
                                         (osafe-mono (mintedAfter-⊇ (_ , e) a) sQ)
    ... | evR    _ stQ     = osafe-Par A (osafe-mono (mintedAfter-⊇ (_ , e) a) sP)
                                         (onEv sQ stQ)
    ... | evBoth _ stP stQ = osafe-both A (osafe-mono (mintedAfter-⊇ (_ , e) a) sP)
                                          (osafe-mono (mintedAfter-⊇ (_ , e) a) sQ)
                                          (onEv sP stP) (onEv sQ stQ)
    -- `Par`'s joint `√` requires both operands to tick, so ONE operand's `noTick` suffices
    osafe-Par A {P = P} {Q = Q} sP sQ .noTick st with Par-ev-elim A (λ _ _ → tt) P Q st
    ... | ev√ fpP _        = noTick sP (sRet fpP)

    osafe-both A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .gateOK st =
      ⊥-elim (brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st)
    osafe-both A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .onτ st
      with brBoth-τ-elim A (λ _ _ → tt) P Q P′ Q′ st
    ... | inj₁ refl = osafe-Par A sP′ sQ
    ... | inj₂ refl = osafe-Par A sP sQ′
    osafe-both A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .onEv st =
      ⊥-elim (brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st)
    osafe-both A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .noTick st =
      brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st

    -- AN ALIAS of `osafe-Par`, for a consumer that means "take the gate from the left
    -- operand at a rendezvous" …
    osafe-ParL : ∀ {ms} (A : EventSet) {P Q}
               → OSafe ms P → OSafe ms Q → OSafe ms (P ∥⇘ A ⇙ Q)
    osafe-ParL = osafe-Par

    -- … and THE SAME ALIAS again for "from the right": the choice of arm does not
    -- appear in the type — both arms prove `gate ms (X , e) a ≡ true` from hypotheses
    -- the congruence demands anyway.  When an operand cannot carry `gateOK` at all,
    -- the lemma wanted is `osafe-ParS` / `osafe-ParS′`, not one of these.
    osafe-ParR : ∀ {ms} (A : EventSet) {P Q}
               → OSafe ms P → OSafe ms Q → OSafe ms (P ∥⇘ A ⇙ Q)
    osafe-ParR = osafe-Par

    -- INTERLEAVING is parallel at the empty synchronisation set, definitionally
    osafe-⦀ : ∀ {ms P Q} → OSafe ms P → OSafe ms Q → OSafe ms (P ⦀ Q)
    osafe-⦀ = osafe-Par ∅ES

    -- REPLICATED INTERLEAVING: `⦀Fin⁺ (suc n) f = f fzero ⦀ ⦀Fin⁺ n (f ∘ fsuc)` is
    -- definitional, so this is plain `Fin` recursion on top of `osafe-⦀`
    osafe-⦀Fin⁺ : ∀ {ms} (n : ℕ) {f : Fin (suc n) → Proc}
                → (∀ i → OSafe ms (f i)) → OSafe ms (⦀Fin⁺ n f)
    osafe-⦀Fin⁺ zero            h = h fzero
    osafe-⦀Fin⁺ (suc n) {f = f} h =
      osafe-⦀ (h fzero) (osafe-⦀Fin⁺ n {f = λ i → f (fsuc i)} (λ i → h (fsuc i)))

    -- THE SIDE CONDITION OF HIDING: no hidden event MINTS.  A hidden mint would let
    -- the implementation grow its key set silently while the spec's state stood still,
    -- and `osafe-mono` runs the wrong way to repair that.  A hidden GATED event needs
    -- no condition: hiding it merely removes occasions to violate the gate.
    HideOK : EventSet → Set₁
    HideOK A = ∀ {X} {e : Net_Api Payload X} {x : X}
             → EventSet.mem A (X , e) x → mints (X , e) x ≡ []

    -- THE HIDING CONGRUENCE: a visible step of `P ∖ A` is the same visible step of `P`;
    -- a τ of `P ∖ A` is either a τ of `P` or a hidden visible event of `P`, and
    -- `HideOK` says the latter mints nothing, so the minted set is unchanged.
    osafe-Hide : ∀ {ms} (A : EventSet) → HideOK A → ∀ {P} → OSafe ms P → OSafe ms (P ∖ A)
    osafe-Hide A ok {P = P} s .gateOK st with Hide-ev-elim A P st
    ... | heV P′ _ stP      = gateOK s stP
    osafe-Hide A ok {P = P} s .onτ st with Hide-τ-elim A P st
    ... | hτP P′ stP refl   = osafe-Hide A ok (onτ s stP)
    ... | hτH {e = e} {a = x} P′ c stP refl =
            osafe-Hide A ok (osafe-nomint (ok {e = e} {x = x} c) (onEv s stP))
    osafe-Hide A ok {P = P} s .onEv st with Hide-ev-elim A P st
    ... | heV P′ _ stP      = osafe-Hide A ok (onEv s stP)
    osafe-Hide A ok {P = P} s .noTick st with Hide-ev-elim A P st
    ... | he√ eq            = noTick s (sRet eq)

    ------------------------------------------------------------------------
    -- THE SYNCHRONISATION-SET WAIVER
    --
    -- A thread that merely ABSORBS a gated rendezvous event has no `OSafe` at all:
    -- `NodeLogicL.certSink n = loop0 (certEv n ⟶ λ _ → Skip)` offers `stCert ! h`
    -- for EVERY `h`, so `Gated ms (certSink n)` is refutable.  It does not need one.
    -- Every event of a synchronisation set `A` requires its partner's agreement, so
    -- the partner is where the gate obligation belongs, and `OSafe∖ A` is `OSafe`
    -- with `gateOK` waived exactly on `A`.  Outside `A` nothing is waived, which is
    -- what keeps `osafe-ParS`'s solo arms sound.
    ------------------------------------------------------------------------

    -- SAFETY MODULO A SYNCHRONISATION SET: as `OSafe`, but the gate obligation holds
    -- only for events OUTSIDE `A`
    record OSafe∖ (A : EventSet) (ms : Minted) (M : Proc) : Set₁ where
      coinductive
      field
        -- here and now: every visible step of `M` on a channel outside `A` has an
        -- open gate.  Inside `A`, nothing is claimed.
        gateOK∖ : ∀ {X} {e : Net_Api Payload X} {a : X} {M′}
                → ¬ EventSet.mem A (X , e) a
                → M ─[ ev (evl (evLabel X e a)) ]─► M′ → gate ms (X , e) a ≡ true
        -- a τ keeps `ms`
        onτ∖    : ∀ {M′} → M ─[ τ ]─► M′ → OSafe∖ A ms M′
        -- a visible step mints what it mints
        onEv∖   : ∀ {X} {e : Net_Api Payload X} {a : X} {M′}
                → M ─[ ev (evl (evLabel X e a)) ]─► M′
                → OSafe∖ A (mintedAfter (X , e) a ms) M′
        -- `M` never TICKS
        noTick∖ : ∀ {x : ⊤ {0ℓ}} {M′} → M ─[ ev (√ x) ]─► M′ → ⊥
    open OSafe∖ public

    -- THE WEAKENING: a fully safe process is safe modulo any synchronisation set
    osafe→osafe∖ : ∀ {A ms M} → OSafe ms M → OSafe∖ A ms M
    osafe→osafe∖ s .gateOK∖ _ st = gateOK s st
    osafe→osafe∖ s .onτ∖      st = osafe→osafe∖ (onτ s st)
    osafe→osafe∖ s .onEv∖     st = osafe→osafe∖ (onEv s st)
    osafe→osafe∖ s .noTick∖   st = noTick s st

    -- a vacuous leaf is safe modulo any synchronisation set too
    free→osafe∖ : ∀ {A ms M} → FreeAt M → OSafe∖ A ms M
    free→osafe∖ f = osafe→osafe∖ (osafe-free f)

    -- monotonicity of the waived carrier, field for field as `osafe-mono`
    osafe∖-mono : ∀ {A ms ms′ M} → ms ⊆ ms′ → OSafe∖ A ms M → OSafe∖ A ms′ M
    osafe∖-mono sub s .gateOK∖ ¬a st = gate-mono sub _ _ (gateOK∖ s ¬a st)
    osafe∖-mono sub s .onτ∖       st = osafe∖-mono sub (onτ∖ s st)
    osafe∖-mono sub s .onEv∖ {e = e} {a = a} st =
      osafe∖-mono (mintedAfter-mono (_ , e) a sub) (onEv∖ s st)
    osafe∖-mono sub s .noTick∖    st = noTick∖ s st

    -- an event is UNGATED when its gate stands open whatever has been minted — the
    -- constantly-`true` channels of an instance's `gate`
    Ungated : (at : AnyTypes (Net_Api Payload)) → proj₁ at → Set
    Ungated at a = ∀ ms → gate ms at a ≡ true

    -- THE LEAF ALPHABET OF THE WAIVER, as an `Alpha`: every event a waived leaf
    -- offers is either INSIDE the synchronisation set (its partner licenses it) or
    -- UNGATED (nobody needs to).  A peer bundle needs exactly this mixture — it
    -- offers gated api events inside `apiES` and ungated `input`/`output` outside it.
    inAOrFree : EventSet → (at : AnyTypes (Net_Api Payload)) → proj₁ at → Set
    inAOrFree A at a = EventSet.mem A at a ⊎ Ungated at a

    -- THE WAIVED LEAF, generically: a process that never returns and offers only
    -- `inAOrFree A` events is `OSafe∖ A` at every minted set.  `OffersOnly`/`NoRet`
    -- are the repo's own step-closed invariants (`CSP.Laws.Bisim.DRCongruenceRep`)
    -- and `inAOrFree A` is literally an `Alpha`, so a waived leaf costs one
    -- `OffersOnly` witness and `NoRet-loop0`.  (`AnnounceSafeLeaves.env-oo`/
    -- `env-sync` are the two special cases this one lemma replaces.)
    osafe∖-offers : ∀ {A : EventSet} {ms M}
                  → OffersOnly (inAOrFree A) M → NoRet M → OSafe∖ A ms M
    osafe∖-offers oo nr .gateOK∖ ¬a st with OffersOnly.now oo st
    ... | inj₁ inA = ⊥-elim (¬a inA)
    ... | inj₂ ung = ung _
    osafe∖-offers oo nr .onτ∖    st =
      osafe∖-offers (OffersOnly.step oo st) (NoRet.stepNR nr st)
    osafe∖-offers oo nr .onEv∖   st =
      osafe∖-offers (OffersOnly.step oo st) (NoRet.stepNR nr st)
    osafe∖-offers oo nr .noTick∖ st = noRet→noTick nr st

    -- THE ABSORBING SINK, the special case where every event is inside `A`:
    -- `certSink`'s shape
    osafe∖-inA : ∀ {A : EventSet} {ms M}
               → OffersOnly (EventSet.mem A) M → NoRet M → OSafe∖ A ms M
    osafe∖-inA oo nr = osafe∖-offers (OffersOnly-mono (λ _ _ → inj₁) oo) nr

    -- THE WAIVED PARALLEL CONGRUENCE, and its collision companion: the waiver survives
    -- any parallel composition, at ANY synchronisation set `B`.  This is what carries
    -- the waiver through the thread fold that contains the sink.  No side condition:
    -- an event outside `A` is licensed by whichever operand moves, and both operands
    -- carry the same waiver.
    osafe∖-Par  : ∀ {A ms} (B : EventSet) {P Q}
                → OSafe∖ A ms P → OSafe∖ A ms Q → OSafe∖ A ms (P ∥⇘ B ⇙ Q)
    osafe∖-both : ∀ {A ms} (B : EventSet) {P Q P′ Q′}
                → OSafe∖ A ms P → OSafe∖ A ms Q → OSafe∖ A ms P′ → OSafe∖ A ms Q′
                → OSafe∖ A ms (ptree (react (λ _ _ → nothing)
                                     (par-brBoth B (λ _ _ → tt) P Q P′ Q′)))

    osafe∖-Par B {P = P} {Q = Q} sP sQ .gateOK∖ ¬a st
      with Par-ev-elim B (λ _ _ → tt) P Q st
    ... | evSync _ stP _   = gateOK∖ sP ¬a stP
    ... | evL    _ stP     = gateOK∖ sP ¬a stP
    ... | evR    _ stQ     = gateOK∖ sQ ¬a stQ
    ... | evBoth _ stP _   = gateOK∖ sP ¬a stP
    osafe∖-Par B {P = P} {Q = Q} sP sQ .onτ∖ st with Par-τ-elim B (λ _ _ → tt) P Q st
    ... | τL P′ stP refl   = osafe∖-Par B (onτ∖ sP stP) sQ
    ... | τR Q′ stQ refl   = osafe∖-Par B sP (onτ∖ sQ stQ)
    osafe∖-Par B {P = P} {Q = Q} sP sQ .onEv∖ {e = e} {a = a} st
      with Par-ev-elim B (λ _ _ → tt) P Q st
    ... | evSync _ stP stQ = osafe∖-Par B (onEv∖ sP stP) (onEv∖ sQ stQ)
    ... | evL    _ stP     = osafe∖-Par B (onEv∖ sP stP)
                                          (osafe∖-mono (mintedAfter-⊇ (_ , e) a) sQ)
    ... | evR    _ stQ     = osafe∖-Par B (osafe∖-mono (mintedAfter-⊇ (_ , e) a) sP)
                                          (onEv∖ sQ stQ)
    ... | evBoth _ stP stQ = osafe∖-both B (osafe∖-mono (mintedAfter-⊇ (_ , e) a) sP)
                                           (osafe∖-mono (mintedAfter-⊇ (_ , e) a) sQ)
                                           (onEv∖ sP stP) (onEv∖ sQ stQ)
    osafe∖-Par B {P = P} {Q = Q} sP sQ .noTick∖ st with Par-ev-elim B (λ _ _ → tt) P Q st
    ... | ev√ fpP _        = noTick∖ sP (sRet fpP)

    osafe∖-both B {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .gateOK∖ ¬a st =
      ⊥-elim (brBoth-no-ev B (λ _ _ → tt) P Q P′ Q′ st)
    osafe∖-both B {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .onτ∖ st
      with brBoth-τ-elim B (λ _ _ → tt) P Q P′ Q′ st
    ... | inj₁ refl = osafe∖-Par B sP′ sQ
    ... | inj₂ refl = osafe∖-Par B sP sQ′
    osafe∖-both B {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .onEv∖ st =
      ⊥-elim (brBoth-no-ev B (λ _ _ → tt) P Q P′ Q′ st)
    osafe∖-both B {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .noTick∖ st =
      brBoth-no-ev B (λ _ _ → tt) P Q P′ Q′ st

    -- the waiver survives interleaving …
    osafe∖-⦀ : ∀ {A ms P Q} → OSafe∖ A ms P → OSafe∖ A ms Q → OSafe∖ A ms (P ⦀ Q)
    osafe∖-⦀ = osafe∖-Par ∅ES

    -- … and the replicated interleaving the thread fold is built from
    osafe∖-⦀Fin⁺ : ∀ {A ms} (n : ℕ) {f : Fin (suc n) → Proc}
                 → (∀ i → OSafe∖ A ms (f i)) → OSafe∖ A ms (⦀Fin⁺ n f)
    osafe∖-⦀Fin⁺ zero            h = h fzero
    osafe∖-⦀Fin⁺ (suc n) {f = f} h =
      osafe∖-⦀ (h fzero) (osafe∖-⦀Fin⁺ n {f = λ i → f (fsuc i)} (λ i → h (fsuc i)))

    -- THE MIXED PARALLEL CONGRUENCE, and its collision companion.  The LEFT operand
    -- carries the waiver on `A`, the RIGHT is fully safe, and the composite is fully
    -- safe: an `A`-event is a rendezvous and `Q` licenses it; a solo or collision
    -- event is outside `A` and the operand that moved licenses it.  The only side
    -- condition is the one already inside `OSafe ms Q` — `Q` respects the gate
    -- everywhere, in particular on the `A`-events it synchronises on.  This is the
    -- orientation `nodeLogicL` needs: threads (with the sink) on the left of
    -- `∥⇘ storeES ⇙`, the stores on the right.
    osafe-ParS  : ∀ {ms} (A : EventSet) {P Q}
                → OSafe∖ A ms P → OSafe ms Q → OSafe ms (P ∥⇘ A ⇙ Q)
    osafe-bothS : ∀ {ms} (A : EventSet) {P Q P′ Q′}
                → OSafe∖ A ms P → OSafe ms Q → OSafe∖ A ms P′ → OSafe ms Q′
                → OSafe ms (ptree (react (λ _ _ → nothing)
                                   (par-brBoth A (λ _ _ → tt) P Q P′ Q′)))

    osafe-ParS A {P = P} {Q = Q} sP sQ .gateOK st with Par-ev-elim A (λ _ _ → tt) P Q st
    ... | evSync _ _   stQ = gateOK sQ stQ
    ... | evL    ¬p stP    = gateOK∖ sP ¬p stP
    ... | evR    _  stQ    = gateOK sQ stQ
    ... | evBoth ¬p stP _  = gateOK∖ sP ¬p stP
    osafe-ParS A {P = P} {Q = Q} sP sQ .onτ st with Par-τ-elim A (λ _ _ → tt) P Q st
    ... | τL P′ stP refl   = osafe-ParS A (onτ∖ sP stP) sQ
    ... | τR Q′ stQ refl   = osafe-ParS A sP (onτ sQ stQ)
    osafe-ParS A {P = P} {Q = Q} sP sQ .onEv {e = e} {a = a} st
      with Par-ev-elim A (λ _ _ → tt) P Q st
    ... | evSync _ stP stQ = osafe-ParS A (onEv∖ sP stP) (onEv sQ stQ)
    ... | evL    _ stP     = osafe-ParS A (onEv∖ sP stP)
                                          (osafe-mono (mintedAfter-⊇ (_ , e) a) sQ)
    ... | evR    _ stQ     = osafe-ParS A (osafe∖-mono (mintedAfter-⊇ (_ , e) a) sP)
                                          (onEv sQ stQ)
    ... | evBoth _ stP stQ = osafe-bothS A (osafe∖-mono (mintedAfter-⊇ (_ , e) a) sP)
                                           (osafe-mono (mintedAfter-⊇ (_ , e) a) sQ)
                                           (onEv∖ sP stP) (onEv sQ stQ)
    osafe-ParS A {P = P} {Q = Q} sP sQ .noTick st with Par-ev-elim A (λ _ _ → tt) P Q st
    ... | ev√ _ fpQ        = noTick sQ (sRet fpQ)

    osafe-bothS A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .gateOK st =
      ⊥-elim (brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st)
    osafe-bothS A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .onτ st
      with brBoth-τ-elim A (λ _ _ → tt) P Q P′ Q′ st
    ... | inj₁ refl = osafe-ParS A sP′ sQ
    ... | inj₂ refl = osafe-ParS A sP sQ′
    osafe-bothS A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .onEv st =
      ⊥-elim (brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st)
    osafe-bothS A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .noTick st =
      brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st

    -- THE MIRROR: the waiver on the RIGHT operand.  `osafe-ParS` with the arms
    -- swapped, proved directly — transporting `OSafe` along `Par-comm` would need an
    -- "`OSafe` respects `∼`" lemma that does not exist.  This is the orientation
    -- S2/S1/S2′ need: the EMITTING thread is on the left of `∥⇘ storeES ⇙` and
    -- carries the gate, the accepting store is on the right and takes the waiver.
    -- Same side conditions as `osafe-ParS`: none beyond `OSafe ms P` itself.
    osafe-ParS′  : ∀ {ms} (A : EventSet) {P Q}
                 → OSafe ms P → OSafe∖ A ms Q → OSafe ms (P ∥⇘ A ⇙ Q)
    osafe-bothS′ : ∀ {ms} (A : EventSet) {P Q P′ Q′}
                 → OSafe ms P → OSafe∖ A ms Q → OSafe ms P′ → OSafe∖ A ms Q′
                 → OSafe ms (ptree (react (λ _ _ → nothing)
                                    (par-brBoth A (λ _ _ → tt) P Q P′ Q′)))

    osafe-ParS′ A {P = P} {Q = Q} sP sQ .gateOK st with Par-ev-elim A (λ _ _ → tt) P Q st
    ... | evSync _  stP _   = gateOK sP stP
    ... | evL    _  stP     = gateOK sP stP
    ... | evR    ¬p stQ     = gateOK∖ sQ ¬p stQ
    ... | evBoth _  stP _   = gateOK sP stP
    osafe-ParS′ A {P = P} {Q = Q} sP sQ .onτ st with Par-τ-elim A (λ _ _ → tt) P Q st
    ... | τL P′ stP refl    = osafe-ParS′ A (onτ sP stP) sQ
    ... | τR Q′ stQ refl    = osafe-ParS′ A sP (onτ∖ sQ stQ)
    osafe-ParS′ A {P = P} {Q = Q} sP sQ .onEv {e = e} {a = a} st
      with Par-ev-elim A (λ _ _ → tt) P Q st
    ... | evSync _ stP stQ  = osafe-ParS′ A (onEv sP stP) (onEv∖ sQ stQ)
    ... | evL    _ stP      = osafe-ParS′ A (onEv sP stP)
                                            (osafe∖-mono (mintedAfter-⊇ (_ , e) a) sQ)
    ... | evR    _ stQ      = osafe-ParS′ A (osafe-mono (mintedAfter-⊇ (_ , e) a) sP)
                                            (onEv∖ sQ stQ)
    ... | evBoth _ stP stQ  = osafe-bothS′ A (osafe-mono (mintedAfter-⊇ (_ , e) a) sP)
                                             (osafe∖-mono (mintedAfter-⊇ (_ , e) a) sQ)
                                             (onEv sP stP) (onEv∖ sQ stQ)
    osafe-ParS′ A {P = P} {Q = Q} sP sQ .noTick st with Par-ev-elim A (λ _ _ → tt) P Q st
    ... | ev√ fpP _         = noTick sP (sRet fpP)

    osafe-bothS′ A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .gateOK st =
      ⊥-elim (brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st)
    osafe-bothS′ A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .onτ st
      with brBoth-τ-elim A (λ _ _ → tt) P Q P′ Q′ st
    ... | inj₁ refl = osafe-ParS′ A sP′ sQ
    ... | inj₂ refl = osafe-ParS′ A sP sQ′
    osafe-bothS′ A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .onEv st =
      ⊥-elim (brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st)
    osafe-bothS′ A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .noTick st =
      brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st

    ------------------------------------------------------------------------
    -- The specification's own states
    ------------------------------------------------------------------------

    private
      -- the tree type the spec's `loop` iterates over
      Tree : Set → Set₁
      Tree X = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) X

      -- `loop`'s state-threading continuation: hand the new state back to `iter`
      κ : Minted → Tree (Minted ⊎ ⊤ {0ℓ})
      κ ms = Ret (inj₁ ms)

      -- the `iter` step `loop` builds from `OriginSpecT`'s body
      StepT : Minted → Tree (Minted ⊎ ⊤ {0ℓ})
      StepT ms = pchoice (originOffer ms) >>= κ

      -- the `sil` back-edge `loop` emits after a visible event
      ST : Minted → Proc
      ST ms = iter-bind (Ret ms >>= κ) StepT

    -- THE SPEC AT A MINTED SET: `OriginSpecT`'s state after a run that minted `ms`.
    -- This is what `OSafe ms` is a simulation hypothesis for.
    OriginSpecAt : Minted → Proc
    OriginSpecAt ms = iter StepT ms

    -- …and at the empty minted set it IS the shipped spec, definitionally
    specAt-init : OriginSpecAt [] ≡ OriginSpecT
    specAt-init = refl

    -- the spec's menu offers the event and lands on the loop-back edge
    specEv : ∀ {ms ms′} {at : AnyTypes (Net_Api Payload)} {a : proj₁ at}
           → originOffer ms at a ≡ just (Ret ms′)
           → OriginSpecAt ms ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► ST ms′
    specEv {ms} eq =
      iter-bind-ev StepT (StepT ms)
        (bind-ev κ (pchoice (originOffer ms)) (sVis refl eq))

    -- and the loop-back edge τ's straight into the next menu
    specLoop : ∀ {ms} → ST ms ─[ τ ]─► OriginSpecAt ms
    specLoop = sSil refl

    -- the spec's menu takes the `just` branch exactly when the gate is open
    gateEq : ∀ {ms at a} → gate ms at a ≡ true
           → originOffer ms at a ≡ just (Ret (mintedAfter at a ms))
    gateEq eq rewrite eq = refl

    -- EVERY visible step the implementation can make is offered by the spec's menu, and
    -- its successor is safe against the state the menu moves to.  ONE clause, because
    -- `originOffer` is uniform in the channel — this is the whole saving over
    -- `AnnounceSafeCarrier.menuStep`'s thirty-clause alphabet enumeration.
    menuStep : ∀ {ms M M′} → OSafe ms M
             → (at : AnyTypes (Net_Api Payload)) (a : proj₁ at)
             → M ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► M′
             → originOffer ms at a ≡ just (Ret (mintedAfter at a ms))
               × OSafe (mintedAfter at a ms) M′
    menuStep s at a st = gateEq (gateOK s st) , onEv s st

    ------------------------------------------------------------------------
    -- The bridge
    ------------------------------------------------------------------------

    private
      -- the step-matching relation `WSimFromRel` runs on: an implementation state is
      -- related to the spec state at the minted set it is safe against
      OSafeR : Proc → Proc → Set₁
      OSafeR M Q = Σ[ ms ∈ Minted ] (OSafe ms M × (Q ≡ OriginSpecAt ms))

      -- a visible step is matched by the menu, then the loop-back τ
      osafeE : ∀ {P Q} {l : Event√ (⊤ {0ℓ})} {P′} → OSafeR P Q → P ─[ ev l ]─► P′
             → Σ[ Q′ ∈ Proc ] ((Q ═[ ev l ]═► Q′) × OSafeR P′ Q′)
      osafeE {l = evl (evLabel A e a)} (ms , s , refl) st with menuStep s (A , e) a st
      ... | eq , s′ =
        OriginSpecAt (mintedAfter (A , e) a ms)
        , wev τ*-refl (specEv eq) (τ*-step specLoop τ*-refl)
        , (mintedAfter (A , e) a ms , s′ , refl)
      -- a `√` is impossible: the spec is a `loop` and cannot match one
      osafeE {l = √ x} (ms , s , refl) st = ⊥-elim (noTick s st)

      -- a τ is matched by the EMPTY weak τ-run: the spec's state is unchanged
      osafeT : ∀ {P Q P′} → OSafeR P Q → P ─[ τ ]─► P′
             → Σ[ Q′ ∈ Proc ] ((Q ═[ τ ]═► Q′) × OSafeR P′ Q′)
      osafeT (ms , s , refl) st = OriginSpecAt ms , wτ τ*-refl , (ms , onτ s st , refl)

      open WSimFromRel OSafeR osafeE osafeT using (rel→wsim)

    -- A SAFE STATE IS SIMULATED BY THE SPEC AT ITS MINTED SET.  This is the whole
    -- content of the carrier: `OSafe` was chosen to be exactly the relation
    -- `WSimFromRel` needs, so the coinduction principle discharges it outright.
    osafe→wsim : ∀ {ms M} → OSafe ms M → WSim (⊤ {0ℓ}) M (OriginSpecAt ms)
    osafe→wsim {ms} s = rel→wsim (ms , s , refl)

    -- THE BRIDGE: one `OSafe []` fact about a composite IS its safety property at `⊑T`.
    -- Note the argument order — `wsim→⊑T` takes the IMPLEMENTATION first.
    osafe→⊑T : ∀ {M} → OSafe [] M → OriginSpecT ⊑T M
    osafe→⊑T s = wsim→⊑T (osafe→wsim s)

  ------------------------------------------------------------------------
  -- A typechecking witness
  ------------------------------------------------------------------------

  -- the TRIVIAL origin discipline — nothing mints, nothing is gated — really does
  -- instantiate `Origin`, so the parameter telescope is inhabited as written
  module TrivialOrigin =
    Origin ℕ DecEqI.DecEq-ℕ (λ _ _ → []) (λ _ _ _ → true) (λ _ _ _ eq → eq)

  -- …and `certSink`'s EXACT shape — a `loop0` prefix sink whose one channel lies
  -- inside the synchronisation set — really is `OSafe∖ A`, at every minted set and
  -- with no claim about the gate on that channel
  sinkWitness : ∀ (A : EventSet) {X : Set} {e : Net_Api Payload X}
              → (∀ a → EventSet.mem A (X , e) a)
              → ∀ ms → TrivialOrigin.OSafe∖ A ms (loop0 (Prefix₀ e Skip))
  sinkWitness A hmem ms =
    TrivialOrigin.osafe∖-inA
      (OffersOnly-loop0 (OffersOnly-Prefix₀ hmem OffersOnly-Skip)) NoRet-loop0
