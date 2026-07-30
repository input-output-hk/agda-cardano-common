{-# OPTIONS --guardedness --allow-unsolved-metas #-}

------------------------------------------------------------------------
-- SPIKE MODULE — Praos R2 Task 1: the ⊓-match feasibility gate.
--
--   * DISPOSABLE.  Imported by NOTHING; deleted after the report is
--     harvested.  `--allow-unsolved-metas` / postulates permitted HERE ONLY.
--   * NEVER forces any whole-node composite to WHNF.  The two node stubs and
--     the medium cell are hand-built minimal trees; every bisim step is
--     handled by SYMBOLIC step-inversion (`Par-ev-elim`/`Par-τ-elim`/
--     `Hide-τ-elim`/`Hide-ev-elim`) that destructures a hypothesised
--     `─[_]─►` step — never by evaluating the concrete composite.
--
-- ==================== WHAT THIS SETTLES =============================
-- Route2Spike (§2 RESIDUAL) left ONE thing unmechanised: in the `hidSync`
-- case the nodes side gives `N ─[io]─► N₁` with `N = A ⦀ (B ⦀ …)`; inverting
-- that inner `⦀` (= `Par ∅ES`) via `Par-ev-elim` returns the `evBoth`
-- overlap node `(A₁∥rest) ⊓ (A∥rest₁)` when two adjacent nodes both offer the
-- shared io event.  This `⊓` lives BELOW the top `∖ ioES` (a HIDDEN τ).
-- Route 1 DIED because the compositional `cong-⦀`'s `Sep` had to REFUTE this
-- overlap (impossible — adjacent nodes genuinely share the io alphabet).
--
-- Route 2's claim, MECHANISED here on a minimal 2-stub / 1-cell fragment:
-- a DIRECT `≈DR` bisim MATCHES the `⊓`-overlap to its abstract twin, using
-- weak-bisim τ-flexibility (each ⊓-branch's HIDDEN τ matched by the abstract
-- side doing 0 τ), with the one-place medium cell (empty→full) GATING which
-- leftover io can fire.  The overlap is MATCHED, not refuted.
------------------------------------------------------------------------

open import Level using (0ℓ; Lift; lift)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Function using (case_of_)

open import Process_Trees
open ExtI using (base; pair; fin)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

module CSP.Examples.Cardano_network.NetworkVerification.Praos.ChoiceMatchSpike where

open PTree

------------------------------------------------------------------------
-- The concrete alphabet under study (Phase-1, `examples/praos_liveness`).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; linkAB )
open import CSP.Examples.Cardano_network.Base using (Dir; IDs)
open Dir using (lo)
open IDs using (N2N_BlockFetch)
open import CSP.Examples.Cardano_network.Net p using (Net_Api; Net_Api-≟; Link; input; output)
open import CSP.Examples.Cardano_network.Data p using (Payload)
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _∖_; Par; EventSet; Stop; ∅ES; pchoice; par-brBoth )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; τ; evl; evLabel; sRet; sSil; sVis; sTau; Diverges )
open Diverges
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WSimF; _═[_]═►_; wτ; _─[τ*]─►_; τ*-refl )
open WSimF
open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( DRbisim; _≈DR_ )
open DRbisim

-- the process type of the fragment
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- the top-level ⊤-merge (definitionally what `∥⇘⇙`/`⦀` use)
⊤merge : ⊤ {0ℓ} → ⊤ {0ℓ} → ⊤ {0ℓ}
⊤merge _ _ = tt

-- the step-inversion machinery (SYMBOLIC — receives a step, destructures it)
open import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload})
  using ( ParevR; Par-ev-elim; ParτR; Par-τ-elim )
open ParevR
open ParτR
open import CSP.Laws.Traces.TraceLawsHide (Net_Api-≟ {Payload})
  using ( HideτR; Hide-τ-elim; HideevR; Hide-ev-elim )
open HideτR
open HideevR

------------------------------------------------------------------------
-- §0  The minimal fragment.
--
--   * `e₀ ∈ ioES` — ONE shared io event (a block-fetch `output`).
--   * `stubL`, `stubR` — two adjacent node stubs, BOTH offering `e₀` then
--     terminating (→ Stop).  (`pchoice` builds a stable, pure-visible react.)
--   * medium cell modelled by its FULL state as `deadlock`: after accepting
--     the first io the one-place cell offers no further SYNC on `e₀` (in the
--     minimal fragment there is no drain path) — the strongest form of the
--     "medium gates which io fires" behaviour.  (The campaign's full cell
--     instead offers the DUAL deliver-event, still refusing the leftover
--     `e₀`; the io-refutation below is identical either way.)
------------------------------------------------------------------------

-- a payload witness so the shared io event can actually fire (value is
-- irrelevant to the ⊓ structure — a spike stand-in for a concrete Payload).
postulate pay : Payload

-- the ONE shared io event (∈ ioES: `ioSet (_ , output …) = ⊤`)
e₀ : Net_Api Payload Payload
e₀ = output linkAB lo N2N_BlockFetch

-- both stubs offer every `output` event, continuing to Stop.
stubV : (at : AnyTypes (Net_Api Payload)) → proj₁ at → Maybe NetProc
stubV (_ , output _ _ _) _ = just Stop
stubV _                  _ = nothing

stubL stubR : NetProc
stubL = pchoice stubV
stubR = pchoice stubV

-- each stub genuinely steps on the shared io event.
stubL-step : stubL ─[ ev (evl (evLabel Payload e₀ pay)) ]─► Stop
stubL-step = sVis refl refl
stubR-step : stubR ─[ ev (evl (evLabel Payload e₀ pay)) ]─► Stop
stubR-step = sVis refl refl

-- e₀ ∈ ioES (io-membership witness)
e₀∈io : ioES .mem (Payload , e₀) pay
e₀∈io = tt

------------------------------------------------------------------------
-- §1  The evBoth overlap GENUINELY arises (connecting to the residual).
--
-- `Par-ev-elim ∅ES ⊤merge stubL stubR (step on e₀)` returns the `evBoth`
-- constructor, whose target is EXACTLY the ⊓-overlap node below.  This is the
-- node route 1 could not handle.  (`e₀ ∉ ∅ES` because the INNER interleave
-- has empty sync — that is why io surfaces as an interleave overlap there.)
------------------------------------------------------------------------

-- the ⊓-overlap node produced by evBoth on the nodes side
⊓node : NetProc
⊓node = ptree (react (λ _ _ → nothing) (par-brBoth ∅ES ⊤merge stubL stubR Stop Stop))

evBoth-arises :
  ParevR ∅ES ⊤merge stubL stubR ⊓node (evl (evLabel Payload e₀ pay))
evBoth-arises = evBoth (λ z → z) stubL-step stubR-step
-- ^ `λ z → z : ¬ ∅ES .mem (Payload , e₀) pay`  (∅ES .mem _ _ = ⊥)

------------------------------------------------------------------------
-- §2  The wrapped composite and its abstract twin.
--
-- After the top io-SYNC the residual is `(medium-full ∥⇘ ioES ⇙ ⊓node) ∖ ioES`
-- (the ⊓ now under a HIDDEN τ).  Its two commits go to the two branches.
------------------------------------------------------------------------

comp⊓ comp_L comp_R twin : NetProc
comp⊓  = (deadlock ∥⇘ ioES ⇙ ⊓node)             ∖ ioES
comp_L = (deadlock ∥⇘ ioES ⇙ (Stop ⦀ stubR))    ∖ ioES   -- brBoth-commitL residual
comp_R = (deadlock ∥⇘ ioES ⇙ (stubL ⦀ Stop))    ∖ ioES   -- brBoth-commitR residual
twin   = Stop                                            -- abstract twin (post-io quiescent)

------------------------------------------------------------------------
-- §3  Leaf lemmas (all GENUINE — no postulate).
------------------------------------------------------------------------

-- a node whose force is the everywhere-nothing react (Stop / deadlock) has NO step.
Stop-noStep : ∀ {l} {M} → ¬ (Stop ─[ l ]─► M)
Stop-noStep (sRet ())
Stop-noStep (sSil ())
Stop-noStep (sVis refl ())
Stop-noStep (sTau refl ())

deadlock-noStep : ∀ {l} {M} → ¬ (deadlock ─[ l ]─► M)
deadlock-noStep (sRet ())
deadlock-noStep (sSil ())
deadlock-noStep (sVis refl ())
deadlock-noStep (sTau refl ())

-- the ⊓-node offers NO visible event (its vis-part is everywhere-nothing).
⊓node-noEv : ∀ {X} {e : Net_Api Payload X} {a : X} {M}
           → ¬ (⊓node ─[ ev (evl (evLabel X e a)) ]─► M)
⊓node-noEv (sVis refl ())

-- GENUINE GATE: the full cell (deadlock stand-in) refuses every io event, so
-- an io ∈ ioES offered by ANY partner cannot fire at the top ioES-sync.  This
-- is the mechanism that collapses the ⊓ overlap (both leftover offers blocked).
medium-gates : ∀ {X} {e : Net_Api Payload X} {a : X} {N : NetProc} {M}
             → ioES .mem (X , e) a
             → ¬ ((deadlock ∥⇘ ioES ⇙ N) ─[ ev (evl (evLabel X e a)) ]─► M)
medium-gates {N = N} iomem step with Par-ev-elim ioES ⊤merge deadlock N step
... | evSync _ dEv _ = deadlock-noStep dEv
... | evL  _ dEv     = deadlock-noStep dEv
... | evR  ¬p _      = ¬p iomem
... | evBoth ¬p _ _  = ¬p iomem

-- a `just` result of `par-brBoth ∅ES ⊤merge` is one of its exactly-two targets.
par-brBoth-just-inv : ∀ {P Q P′ Q′ : NetProc} {i} {a : proj₁ i} {M}
                    → par-brBoth ∅ES ⊤merge P Q P′ Q′ i a ≡ just M
                    → (M ≡ Par ∅ES ⊤merge P′ Q) ⊎ (M ≡ Par ∅ES ⊤merge P Q′)
par-brBoth-just-inv {i = _ , fin}      {lift fzero}           eq = inj₁ (just-injective (sym eq))
par-brBoth-just-inv {i = _ , fin}      {lift (fsuc fzero)}    eq = inj₂ (just-injective (sym eq))
par-brBoth-just-inv {i = _ , fin}      {lift (fsuc (fsuc _))} eq = case eq of λ ()
par-brBoth-just-inv {i = _ , base _}   eq = case eq of λ ()
par-brBoth-just-inv {i = _ , pair _ _} eq = case eq of λ ()

------------------------------------------------------------------------
-- §4  Branch quiescence (medium-gated).
--
-- Each ⊓-branch composite (`comp_L`, `comp_R`) has NO transition: the leftover
-- stub still offers `e₀ ∈ ioES`, but the full medium refuses the sync
-- (`medium-gates`), so the branch quiesces.  The io-refusal case IS proven
-- (`medium-gates`); the remaining bookkeeping (deadlock/Stop/stub have no τ;
-- stubs offer only io ⇒ no non-io visible; no joint √) is the fragment's
-- evident quiescence — POSTULATED here as a peripheral lemma (the campaign's
-- OffersOnly-ioES + Par/Hide no-step bookkeeping discharges it routinely).
------------------------------------------------------------------------

postulate
  compL-noStep : ∀ {l} {M} → ¬ (comp_L ─[ l ]─► M)
  compR-noStep : ∀ {l} {M} → ¬ (comp_R ─[ l ]─► M)

------------------------------------------------------------------------
-- §5  τ-inversion of `comp⊓` (GENUINE — the CORE of the match).
--
-- Every τ of `comp⊓` is one of the ⊓'s two commits (→ comp_L / comp_R).  The
-- hidden-io case (`hτH`) is refuted by `medium-gates`; the medium's own τ
-- (`τL`) by `deadlock-noStep`.
------------------------------------------------------------------------

comp⊓-τ-target : ∀ {M} → comp⊓ ─[ τ ]─► M → (M ≡ comp_L) ⊎ (M ≡ comp_R)
comp⊓-τ-target st with Hide-τ-elim ioES (deadlock ∥⇘ ioES ⇙ ⊓node) st
... | hτH _ iomem ioStep _ = ⊥-elim (medium-gates iomem ioStep)
... | hτP _ inner eq with Par-τ-elim ioES ⊤merge deadlock ⊓node inner
...   | τL _ dτ _        = ⊥-elim (deadlock-noStep dτ)
...   | τR _ (sSil ()) _
...   | τR Q′ (sTau refl br) peq with par-brBoth-just-inv br
...     | inj₁ q≡ = inj₁ (trans eq (trans (cong (_∖ ioES) peq)
                              (cong (λ z → (Par ioES ⊤merge deadlock z) ∖ ioES) q≡)))
...     | inj₂ q≡ = inj₂ (trans eq (trans (cong (_∖ ioES) peq)
                              (cong (λ z → (Par ioES ⊤merge deadlock z) ∖ ioES) q≡)))

-- `comp⊓` has NO visible step (⊓node offers none; deadlock offers none).
comp⊓-noEv : ∀ {l} {M} → ¬ (comp⊓ ─[ ev l ]─► M)
comp⊓-noEv step with Hide-ev-elim ioES (deadlock ∥⇘ ioES ⇙ ⊓node) step
... | heV _ ¬mem evStep with Par-ev-elim ioES ⊤merge deadlock ⊓node evStep
...   | evSync mem _ _ = ¬mem mem
...   | evL  _ dEv     = deadlock-noStep dEv
...   | evR  _ nEv     = ⊓node-noEv nEv
...   | evBoth _ dEv _ = deadlock-noStep dEv
comp⊓-noEv step | he√ fEq = case fEq of λ ()

-- `comp⊓` does NOT diverge (one τ lands in a quiescent branch).
comp⊓-noDiv : ¬ Diverges comp⊓
comp⊓-noDiv d with comp⊓-τ-target (d .step)
... | inj₁ M≡ = compL-noStep (subst (λ z → z ─[ τ ]─► _) M≡ (d .rest .step))
... | inj₂ M≡ = compR-noStep (subst (λ z → z ─[ τ ]─► _) M≡ (d .rest .step))

------------------------------------------------------------------------
-- §6  Generic no-step ≈DR (both sides quiescent ⇒ bisimilar).
------------------------------------------------------------------------

noStep-match : (t s : NetProc)
             → (∀ {l} {M} → ¬ (t ─[ l ]─► M))
             → (∀ {l} {M} → ¬ (s ─[ l ]─► M))
             → t ≈DR s
noStep-match t s nt ns .fwd  .on-ev  st = ⊥-elim (nt st)
noStep-match t s nt ns .fwd  .on-tau st = ⊥-elim (nt st)
noStep-match t s nt ns .bwd  .on-ev  st = ⊥-elim (ns st)
noStep-match t s nt ns .bwd  .on-tau st = ⊥-elim (ns st)
noStep-match t s nt ns .div→ d = ⊥-elim (nt (d .step))
noStep-match t s nt ns .div← d = ⊥-elim (ns (d .step))

-- each branch is ≈DR the twin (both quiescent)
choiceMatch-L : comp_L ≈DR twin
choiceMatch-L = noStep-match comp_L twin compL-noStep Stop-noStep
choiceMatch-R : comp_R ≈DR twin
choiceMatch-R = noStep-match comp_R twin compR-noStep Stop-noStep

------------------------------------------------------------------------
-- §7  THE RESULT — the ⊓-overlap MATCHES its abstract twin.
--
-- fwd.on-tau: each ⊓-commit (a HIDDEN τ) is matched by the twin doing ZERO τ
--   (`wτ τ*-refl`), the residual being that branch ≈DR twin — this IS the
--   weak-bisim τ-flexibility route 1 could not use.
-- fwd.on-ev / bwd: vacuous (comp⊓ + Stop are quiescent up to the two τ's).
-- div→/div←: from evident convergence of both sides.
------------------------------------------------------------------------

choiceMatch : comp⊓ ≈DR twin
choiceMatch .fwd .on-ev  st = ⊥-elim (comp⊓-noEv st)
choiceMatch .fwd .on-tau st with comp⊓-τ-target st
... | inj₁ M≡ = twin , wτ τ*-refl , subst (λ z → z ≈DR twin) (sym M≡) choiceMatch-L
... | inj₂ M≡ = twin , wτ τ*-refl , subst (λ z → z ≈DR twin) (sym M≡) choiceMatch-R
choiceMatch .bwd .on-ev  st = ⊥-elim (Stop-noStep st)
choiceMatch .bwd .on-tau st = ⊥-elim (Stop-noStep st)
choiceMatch .div→ d = ⊥-elim (comp⊓-noDiv d)
choiceMatch .div← d = ⊥-elim (Stop-noStep (d .step))
