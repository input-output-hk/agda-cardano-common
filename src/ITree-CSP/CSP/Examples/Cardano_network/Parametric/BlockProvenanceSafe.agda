{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — FROM `Wf` TO `Safe`: the bridge from the
-- assume-guarantee carrier of `Parametric.BlockProvenance` to the
-- announcement-safety carrier of `Parametric.AnnounceSafeCarrier`.
--
-- `Safe ms M` has five fields.  `gate` is `Wf`'s guarantee at the announce
-- channel (`BlockProvenance.wf→gate`).  The three step fields come from
-- `Wf`'s `stepW`, which DEMANDS `OK s′ a` for the label taken — the rely.
-- At the top of the composition no rely is left: the step's `OK` is `M`'s
-- OWN guarantee, `nowW`, provided the label is in `G`.  That is the ONE
-- side condition of the bridge, `Covers G`: the guarantee alphabet
-- contains every block-carrying label.  It is exactly what the assembly
-- delivers once each leaf's rely has been discharged by another leaf's
-- guarantee (`Parametric.AnnounceSafeCopy`), and it is what makes a `Wf`
-- fact on a partial alphabet — any single leaf's — NOT bridgeable: a leaf
-- cannot be `Safe`, and this bridge says why.
--
-- `noTick` comes from nowhere in `Wf`: `Wf` holds of `deadlock`, hence of
-- terminating processes.  It is taken from `DRCongruenceRep.NoRet`, the
-- step-closed "never returns" invariant, which the system inherits from
-- ANY ONE forever-loop in it (`Par` ticks only when BOTH operands do):
-- the closure lemmas below carry a `NoRet` on the RIGHT operand through
-- `∥⇘ A ⇙` (the repo has only the left-operand one), through `∖ A`, and
-- through the head of a `⦀Fin⁺`.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.BlockProvenanceSafe where

open import Level using (0ℓ; lift)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Process_Trees using (PTree; ptree; react; ret; sil; AnyTypes; ExtI; base; pair; fin)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O
import CSP.Examples.Cardano_network.Parametric.AnnounceSafe as AS
import CSP.Examples.Cardano_network.Parametric.AnnounceInvariant as AI
import CSP.Examples.Cardano_network.Parametric.AnnounceSafeCarrier as ASC
import CSP.Examples.Cardano_network.Parametric.AnnounceSafeLeaves as ASL
import CSP.Examples.Cardano_network.Parametric.BlockProvenance as BP

-- the same three parameters as every other `Parametric.Announce*`/`BlockProvenance*`
-- module, so `Safe`, `Wf`, `Carries` and `next` below are literally theirs
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  open N p
    using ( Net_Api; Net_Api-≟; env; envMint; apiLN; store; break
          ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
          ; apiCS; apiBF; apiTS; apiKA; apiLF )
  open D p using (Payload)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload})
    using (EventSet; par-brBoth; _∥⇘_⇙_; _∖_; _⦀_; ⦀Fin⁺)
  open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (Label; ev; τ; evl; √; evLabel; _─[_]─►_; sRet; sSil; sVis; sTau)
  open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
    using (Alpha; NoRet; NoRet-⦀)
  open import CSP.Laws.Traces.TraceLawsExtChoice (Net_Api-≟ {Payload}) using (NonRet)
  open import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload})
    using (Par-τ-elim; τL; τR; Par-ev-elim; evSync; evL; evR; evBoth; ev√)
  open import CSP.Laws.Traces.TraceLawsHide (Net_Api-≟ {Payload})
    using (Hide-τ-elim; hτP; hτH; Hide-ev-elim; heV; he√; fHide-ret-inv)
  open AS.Generic p t apiES using (Minted)
  open AI.Generic p t apiES using (NotMint)
  open ASC.Generic p t apiES using (Safe)
  open Safe
  open ASL.Generic p t apiES using (noRet→noTick)
  open BP.Generic p t apiES

  ------------------------------------------------------------------------
  -- The side condition
  ------------------------------------------------------------------------

  -- `Covers G`: every block-carrying label is in the guarantee alphabet — no rely
  -- is left.  This is `HideCov` with the whole alphabet for the hidden set.
  Covers : Alpha → Set₁
  Covers G = ∀ {X} {e : Net_Api Payload X} {a : X} {b}
           → Carries (X , e) a b → G (X , e) a

  -- a label that is not a mint leaves the minted set alone: `mintOf` answers `[]` on
  -- every shape but `env … envMint (just _ , _)`, and that shape is what `NotMint`
  -- refutes.  One clause per `Net_Api` constructor, because `mintOf`'s catch-all does
  -- not reduce until the constructor is known (as `hideKeep-ioES`).
  next-notMint : ∀ (a : Label (⊤ {0ℓ})) ms → NotMint a → next a ms ≡ ms
  next-notMint τ                                     _ _ = refl
  next-notMint (ev (√ _))                            _ _ = refl
  next-notMint (ev (evl (evLabel _ (input  _ _ _) _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (output _ _ _) _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (sndmsg _ _ _) _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (rcvmsg _ _ _) _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (tx     _ _ _) _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (sndack _ _ _) _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (rcvack _ _ _) _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (ack    _ _ _) _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (done   _ _ _) _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (apiCS  _ _ _) _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (apiBF  _ _ _) _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (apiTS  _ _ _) _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (apiKA  _ _ _) _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (apiLN  _ _ _) _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (apiLF  _ _ _) _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (store  _ _ _) _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (break  _)     _))) _ _ = refl
  next-notMint (ev (evl (evLabel _ (env _ _ envMint) (just _  , _)))) _ ()
  next-notMint (ev (evl (evLabel _ (env _ _ envMint) (nothing , _)))) _ _ = refl

  ------------------------------------------------------------------------
  -- The bridge
  ------------------------------------------------------------------------

  -- THE BRIDGE.  `gate` is the guarantee at the announce channel; each step spends
  -- `M`'s own guarantee as the step's `OK` (τ and `√` carry nothing, a mint is exempt
  -- by `blockOK-mint`, a visible label is covered by `Covers`), and the state `Wf`
  -- lands in is rewritten to the one `Safe` demands — `next-mint` on a mint,
  -- `next-notMint` otherwise.  `noTick` and its `√` case are `NoRet`'s.
  wf→safe : ∀ {G ms M} → Covers G → NoRet M → Wf G ms M → Safe ms M
  wf→safe cov nr w .gate st = nowW w ⊆-refl (cov c-ann) st c-ann
  wf→safe cov nr w .onτ st  = wf→safe cov (NoRet.stepNR nr st) (stepW w ⊆-refl st tt)
  wf→safe {G} {ms} cov nr w .onMint {M′ = M′} {mb = mb} st =
    wf→safe cov (NoRet.stepNR nr st)
      (subst (λ s → Wf G s M′) (next-mint mb ms) (stepW w ⊆-refl st blockOK-mint))
  wf→safe cov nr w .onOther {a = τ} nm st =
    wf→safe cov (NoRet.stepNR nr st) (stepW w ⊆-refl st tt)
  wf→safe cov nr w .onOther {a = ev (√ _)} nm st = ⊥-elim (noRet→noTick nr st)
  wf→safe {G} {ms} cov nr w .onOther {M′} {a = a@(ev (evl (evLabel _ _ _)))} nm st =
    wf→safe cov (NoRet.stepNR nr st)
      (subst (λ s → Wf G s M′) (next-notMint a ms nm)
             (stepW w ⊆-refl st (λ c → nowW w ⊆-refl (cov c) st c)))
  wf→safe cov nr w .noTick st = noRet→noTick nr st

  ------------------------------------------------------------------------
  -- `NoRet` closure, for the system's three operator shapes
  ------------------------------------------------------------------------

  -- `∥⇘ A ⇙` returns only when BOTH operands do, so a `NoRet` on the RIGHT operand
  -- alone forbids termination of the composite — the mirror image of
  -- `DRCongruenceRep.NoRet-Par`, with its collision-node companion
  NoRet-ParR   : ∀ (A : EventSet) {P Q : Proc} → NoRet Q → NoRet (P ∥⇘ A ⇙ Q)
  NoRet-brBothR : ∀ (A : EventSet) {P Q P′ Q′ : Proc} → NoRet Q → NoRet Q′
                → NoRet (ptree (react (λ _ _ → nothing) (par-brBoth A (λ _ _ → tt) P Q P′ Q′)))

  NoRet-ParR A {P} {Q} nrQ .NoRet.nowNR with PTree.force (P ∥⇘ A ⇙ Q) in eqPQ
  ... | sil _     = tt₀
  ... | react _ _ = tt₀
  ... | ret r     with Par-ev-elim A (λ _ _ → tt) P Q (sRet eqPQ)
  ...   | ev√ _ eqQ = subst NonRet eqQ (NoRet.nowNR nrQ)
  NoRet-ParR A {P} {Q} nrQ .NoRet.stepNR {l = τ} st with Par-τ-elim A (λ _ _ → tt) P Q st
  ... | τL P′ _   refl = NoRet-ParR A nrQ
  ... | τR Q′ Qst refl = NoRet-ParR A (NoRet.stepNR nrQ Qst)
  NoRet-ParR A {P} {Q} nrQ .NoRet.stepNR {l = ev _} st with Par-ev-elim A (λ _ _ → tt) P Q st
  ... | evSync _ _ Qst = NoRet-ParR A (NoRet.stepNR nrQ Qst)
  ... | evL    _ _     = NoRet-ParR A nrQ
  ... | evR    _ Qst   = NoRet-ParR A (NoRet.stepNR nrQ Qst)
  ... | evBoth _ _ Qst = NoRet-brBothR A nrQ (NoRet.stepNR nrQ Qst)
  ... | ev√    _ eqQ   = ⊥-elim (subst NonRet eqQ (NoRet.nowNR nrQ))

  NoRet-brBothR A nrQ nrQ′ .NoRet.nowNR = tt₀
  NoRet-brBothR A nrQ nrQ′ .NoRet.stepNR (sRet ())
  NoRet-brBothR A nrQ nrQ′ .NoRet.stepNR (sSil ())
  NoRet-brBothR A nrQ nrQ′ .NoRet.stepNR (sVis refl ())
  NoRet-brBothR A nrQ nrQ′ .NoRet.stepNR (sTau {i = _ , fin} {a = lift fzero} refl refl) =
    NoRet-ParR A nrQ
  NoRet-brBothR A nrQ nrQ′ .NoRet.stepNR (sTau {i = _ , fin} {a = lift (fsuc fzero)} refl refl) =
    NoRet-ParR A nrQ′
  NoRet-brBothR A nrQ nrQ′ .NoRet.stepNR (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl ())
  NoRet-brBothR A nrQ nrQ′ .NoRet.stepNR (sTau {i = _ , base _}   refl ())
  NoRet-brBothR A nrQ nrQ′ .NoRet.stepNR (sTau {i = _ , pair _ _} refl ())

  -- hiding returns exactly when its operand does
  NoRet-Hide : ∀ (A : EventSet) {P : Proc} → NoRet P → NoRet (P ∖ A)
  NoRet-Hide A {P} nr .NoRet.nowNR with PTree.force (P ∖ A) in eq
  ... | sil _     = tt₀
  ... | react _ _ = tt₀
  ... | ret r     = subst NonRet (fHide-ret-inv A P eq) (NoRet.nowNR nr)
  NoRet-Hide A {P} nr .NoRet.stepNR {l = τ} st with Hide-τ-elim A P st
  ... | hτP P′ stP   refl = NoRet-Hide A (NoRet.stepNR nr stP)
  ... | hτH P′ _ stP refl = NoRet-Hide A (NoRet.stepNR nr stP)
  NoRet-Hide A {P} nr .NoRet.stepNR {l = ev _} st with Hide-ev-elim A P st
  ... | heV P′ _ stP = NoRet-Hide A (NoRet.stepNR nr stP)
  ... | he√ eqP      = ⊥-elim (subst NonRet eqP (NoRet.nowNR nr))

  -- the head component of a replicated interleaving suffices (`⦀Fin⁺ (suc n) f =
  -- f fzero ⦀ …` is definitional; at `zero` it IS the head)
  NoRet-⦀Fin⁺ : ∀ n {f : Fin (suc n) → Proc} → NoRet (f fzero) → NoRet (⦀Fin⁺ n f)
  NoRet-⦀Fin⁺ zero    h = h
  NoRet-⦀Fin⁺ (suc n) h = NoRet-⦀ h
