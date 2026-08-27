{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- SPIKE (Task 5, N-node campaign): does hiding `ioES` over a network of
-- LOOPING nodes create divergence?
--
-- The N-node assembly lemma must go through `Hide-mono-⊑FD-df`
-- (`CSP.Laws.FD.HideMonoFD`), whose side condition is
-- `∀ {s} → ¬ divergences (Q ∖ ioES) s`.  `Hide-mono-⊑FD` itself is FALSE.
-- So before the assembly lemma can even be STATED we must know whether
-- `(medium ∥⇘ ioES ⇙ nodes) ∖ ioES` can perform an infinite τ-run.
--
-- ANSWER (this module): NO.  The reason is structural, and it is the
-- reason the whole thing is affordable:
--
--   * `ioES` contains ONLY the `input`/`output` channels
--     (`NetCommon.ioSet`), so hiding does NOT hide the `api…` events;
--   * every cycle of every mini-protocol peer passes through an `api…`
--     event (`KeepAlive.clientStep` at `stClient` offers only
--     `apiKAev … sendKAMsg`/`sendKADone`; `KeepAlive.serverStep` at
--     `stClient` emits `apiKAev … recvKACookie` before it can loop).
--
-- So along any run of the hidden system the peers can only advance
-- finitely far before they must perform a VISIBLE event, which a τ-run
-- may not do.  The medium can loop on io forever, but only in lockstep
-- with the peers (io is the SYNCHRONISATION set), so it is pinned too.
--
-- This module turns that argument into machine-checked mathematics via
-- an "A-modulo accessibility" calculus (§1-§3): the inductive analogue,
-- for the relation "τ OR hidden A-event", of `Semantics.DivergenceFree`'s
-- `τ-Acc`.  §4 builds the smallest system with the suspect shape — two
-- nodes, ONE link, KeepAlive ONLY.
--
-- It is a spike: it is deliberately not `--safe` and need not be pretty,
-- but it contains NO `postulate` (a postulated divergence answer would
-- defeat the entire purpose of the exercise).
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.Spike.HideDiverge where

open import Level using (0ℓ; lift)
import Data.Unit as U
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees
  using (PTree; ptree; ExtI; base; pair; fin; AnyTypes; NodeKind; ret; sil; react)

open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using (Dir; lo; hi; IDs; N2N_KeepAlive)

-- decidable equality on the (level-0) unit type, the filler for every abstract domain
decEq⊤ : DecEq U.⊤
decEq⊤ ._≟_ U.tt U.tt = yes refl

-- the smallest interesting scenario: ONE link, running KeepAlive in both
-- directions and nothing else; every abstract data domain collapsed to ⊤
pKA : Params
pKA = record
  { Cookie = U.⊤ ; Block = U.⊤ ; Txid = U.⊤ ; LSlot = U.⊤
  ; VoterId = U.⊤ ; LFBitmap = U.⊤ ; VoteBlob = U.⊤
  ; Time = U.⊤ ; Length = U.⊤ ; time₀ = U.tt ; length₀ = U.tt
  ; numLinks = 1
  ; linkConfig = λ _ → (lo , N2N_KeepAlive) ∷ (hi , N2N_KeepAlive) ∷ []
  ; decCookie = decEq⊤ ; decBlock = decEq⊤ ; decTxid = decEq⊤
  ; decLSlot = decEq⊤ ; decVoterId = decEq⊤ ; decLFBitmap = decEq⊤
  ; decVoteBlob = decEq⊤ ; decTime = decEq⊤ ; decLength = decEq⊤ }

open import CSP.Examples.Cardano_network.Net pKA using (Link; Net_Api; Net_Api-≟)
open import CSP.Examples.Cardano_network.Data pKA using (Payload)
open import CSP.Examples.Cardano_network.NetCommon pKA using (CopySpecA; ioES)
open import CSP.Examples.Cardano_network.NetworkPar pKA
  using (nodeBundle; KAclientA; KAserverA)

open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload})
  using (_⦀_; _∥⇘_⇙_; _∖_; Par; Par⊤; EventSet; ∅ES; par-brBoth; Skip; ⦀⋆)

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_─[_]─►_; τ; ev; evl; evLabel; Event√; sSil; sTau; sVis; sRet)
open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (Diverges)
open import Semantics.DivergenceFree {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (τ-Acc; acc)

open import CSP.Laws.Traces.TraceLawsHide (Net_Api-≟ {Payload})
  using (HideτR; hτP; hτH; Hide-τ-elim)
open import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload})
  using (ParτR; τL; τR; Par-τ-elim; ParevR; evSync; evL; evR; evBoth; Par-ev-elim)
open import CSP.Laws.Traces.TraceLawsParallelTrace (Net_Api-≟ {Payload})
  using (brBoth-τ-elim; brBoth-no-ev)

-- the process type every definition in this module inhabits
Proc : Set₁
Proc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- the merge function every `Par` in this file uses (`Par⊤`'s)
mgT : ⊤ {0ℓ} → ⊤ {0ℓ} → ⊤ {0ℓ}
mgT _ _ = tt

------------------------------------------------------------------------
-- §1.  A-modulo steps and A-modulo accessibility.
--
-- `Hide-τ-elim` says a τ of `P ∖ A` is either a τ of `P` or a VISIBLE
-- `A`-event of `P`.  Call that combination an "A-modulo step".  Then
-- `Diverges (P ∖ A)` is exactly an infinite A-modulo path in `P`, and the
-- inductive certificate that rules it out is A-modulo accessibility —
-- the exact analogue of `τ-Acc` for the enlarged relation.  As with
-- `τ-Acc`, the INDUCTIVE form is what makes the operator closure lemmas
-- of §2 provable: `¬ Diverges` is a black box, `ModAcc` recurses.
------------------------------------------------------------------------

-- an A-modulo step of `t`: a τ, or a visible event that `A` hides
data ModAStep (A : EventSet) (t t′ : Proc) : Set₁ where
  maτ : t ─[ τ ]─► t′ → ModAStep A t t′
  maE : {B : Set} {e : Net_Api Payload B} {a : B}
      → EventSet.mem A (B , e) a
      → t ─[ ev (evl (evLabel B e a)) ]─► t′ → ModAStep A t t′

-- A-modulo accessibility: every A-modulo successor is again accessible
data ModAcc (A : EventSet) (t : Proc) : Set₁ where
  macc : (∀ {t′} → ModAStep A t t′ → ModAcc A t′) → ModAcc A t

-- follow an A-modulo step into the sub-certificate (the accessor)
maccSub : ∀ {A} {t t′ : Proc} → ModAcc A t → ModAStep A t t′ → ModAcc A t′
maccSub (macc f) st = f st

-- THE payoff: an A-modulo accessible process cannot diverge once `A` is
-- hidden.  Every τ of `t ∖ A` is decoded by `Hide-τ-elim` into an
-- A-modulo step of `t`, which strictly consumes the certificate.
modAcc→¬Div∖ : (A : EventSet) (t : Proc) → ModAcc A t → ¬ Diverges (t ∖ A)
modAcc→¬Div∖ A t (macc f) d with Hide-τ-elim A t (Diverges.step d)
... | hτP t′ tτ eq =
      modAcc→¬Div∖ A t′ (f (maτ tτ)) (subst Diverges eq (Diverges.rest d))
... | hτH t′ mem tev eq =
      modAcc→¬Div∖ A t′ (f (maE mem tev)) (subst Diverges eq (Diverges.rest d))

------------------------------------------------------------------------
-- §2.  Leaves: the states at which an A-modulo run must stop.
--
-- A state is A-modulo STUCK when it has no τ at all and every visible
-- event it offers lies OUTSIDE `A`.  That is exactly the shape of a
-- mini-protocol peer parked on an `api…` offer: `api…` ∉ `ioES`.
------------------------------------------------------------------------

-- no A-modulo step at all ⇒ vacuously accessible
stuck→ModAcc : ∀ {A} {t : Proc} → (∀ {t′} → ModAStep A t t′ → ⊥) → ModAcc A t
stuck→ModAcc ¬st = macc λ st → ⊥-elim (¬st st)

------------------------------------------------------------------------
-- §3.  The two closure lemmas — the mathematical content of the spike.
--
-- (a) INTERLEAVING (`_⦀_`, sync set `∅ES`).  An A-modulo step of `P ⦀ Q`
--     is a τ or a hidden A-event of ONE side (`evSync` is impossible: it
--     needs membership in `∅ES`).  `evBoth` — both sides offering the
--     same event — lands on the inline overlap node, whose only steps are
--     the two τ's back into `Par`.  So a lexicographic product of the two
--     `ModAcc` certificates discharges it.
--
-- (b) THE HIDE-OVER-SYNC PARALLEL (`P ∥⇘ A ⇙ Q` with the sync set EQUAL
--     to the hidden set).  This is the one that decides the campaign
--     question.  An A-modulo step is: a τ of `P`, a τ of `Q`, or an
--     `A`-event on which BOTH sides move (`evL`/`evR`/`evBoth` all
--     require NON-membership, so they are refuted outright).  Hence
--     EVERY A-modulo step other than a solo τ of `P` consumes an
--     A-modulo step of `Q`.  So `Q` (the nodes) needs full `ModAcc`,
--     while `P` (the medium) only needs to be unable to τ-diverge — at
--     `P` itself AND at every A-modulo successor of `P`, which is the
--     coinductive `ModStable` below.  The medium may loop on io forever;
--     it just may not loop on τ forever.
------------------------------------------------------------------------

-- `t` cannot τ-diverge, and neither can anything A-modulo reachable from
-- it.  Coinductive, because the io-loop of the medium is genuinely infinite.
record ModStable (A : EventSet) (t : Proc) : Set₁ where
  coinductive
  field
    msHere : τ-Acc t
    msNext : ∀ {t′} → ModAStep A t t′ → ModStable A t′
open ModStable

-- (a) interleaving.  `ModAcc-brBoth` handles the inline overlap node; it
-- is not recursive, so it costs nothing in the termination argument.
ModAcc-brBoth : (A : EventSet) (P Q P′ Q′ : Proc)
              → ModAcc A (Par ∅ES mgT P′ Q) → ModAcc A (Par ∅ES mgT P Q′)
              → ModAcc A (ptree (react (λ _ _ → nothing) (par-brBoth ∅ES mgT P Q P′ Q′)))
ModAcc-brBoth A P Q P′ Q′ a₁ a₂ = macc go
  where
  go : ∀ {M} → ModAStep A (ptree (react (λ _ _ → nothing) (par-brBoth ∅ES mgT P Q P′ Q′))) M
     → ModAcc A M
  go (maτ st) with brBoth-τ-elim ∅ES mgT P Q P′ Q′ st
  ... | inj₁ refl = a₁
  ... | inj₂ refl = a₂
  go (maE _ st) = ⊥-elim (brBoth-no-ev ∅ES mgT P Q P′ Q′ st)

ModAcc-⦀ : (A : EventSet) {P Q : Proc}
         → ModAcc A P → ModAcc A Q → ModAcc A (P ⦀ Q)
ModAcc-⦀ A {P} {Q} ap@(macc f) aq@(macc g) = macc go
  where
  go : ∀ {M} → ModAStep A (Par ∅ES mgT P Q) M → ModAcc A M
  go (maτ st) with Par-τ-elim ∅ES mgT P Q st
  ... | τL P′ pτ refl = ModAcc-⦀ A (f (maτ pτ)) aq
  ... | τR Q′ qτ refl = ModAcc-⦀ A ap (g (maτ qτ))
  go (maE mem st) with Par-ev-elim ∅ES mgT P Q st
  ... | evSync () _ _
  ... | evL  _ pev     = ModAcc-⦀ A (f (maE mem pev)) aq
  ... | evR  _ qev     = ModAcc-⦀ A ap (g (maE mem qev))
  ... | evBoth _ pev qev =
        ModAcc-brBoth A P Q _ _
          (ModAcc-⦀ A (f (maE mem pev)) aq)
          (ModAcc-⦀ A ap (g (maE mem qev)))

-- (b) the decisive one: sync set = hidden set.  THIS is the shape the
-- N-node assembly lemma needs.
--
-- The recursion is lexicographic on (`ModAcc A Q`, `τ-Acc P`).  It is
-- written as the standard `Acc`-idiom — the τ-Acc recursion is the inner
-- `loop`, sitting UNDER the outer `macc g` pattern — so that a solo τ of
-- `P` keeps the `ModAcc` column literally constant (a top-level call
-- would have to rebuild `macc g`, which the termination checker rejects).
ModAcc-∥ : (A : EventSet) (P Q : Proc)
         → ModStable A P → ModAcc A Q → ModAcc A (P ∥⇘ A ⇙ Q)
ModAcc-∥ A P Q ms (macc g) = loop P ms (msHere ms)
  where
  loop : (P′ : Proc) → ModStable A P′ → τ-Acc P′ → ModAcc A (Par A mgT P′ Q)
  loop P′ ms′ (acc h) = macc go
    where
    go : ∀ {M} → ModAStep A (Par A mgT P′ Q) M → ModAcc A M
    -- a τ is P′'s (stay in `loop`, τ-Acc shrinks) or Q′'s (restart, ModAcc shrinks)
    go (maτ st) with Par-τ-elim A mgT P′ Q st
    ... | τL P″ pτ refl = loop P″ (msNext ms′ (maτ pτ)) (h pτ)
    ... | τR Q″ qτ refl = ModAcc-∥ A P′ Q″ ms′ (g (maτ qτ))
    -- a HIDDEN event is in the sync set, so ONLY `evSync` is possible:
    -- every such step consumes an A-modulo step of Q as well
    go (maE mem st) with Par-ev-elim A mgT P′ Q st
    ... | evSync mem′ pev qev =
          ModAcc-∥ A _ _ (msNext ms′ (maE mem′ pev)) (g (maE mem′ qev))
    ... | evL  ¬mem _     = ⊥-elim (¬mem mem)
    ... | evR  ¬mem _     = ⊥-elim (¬mem mem)
    ... | evBoth ¬mem _ _ = ⊥-elim (¬mem mem)

-- …and its `¬ Diverges` corollary, the literal side condition of
-- `Hide-mono-⊑FD-df`.
hide-∥-no-Diverges : (A : EventSet) (P Q : Proc)
                   → ModStable A P → ModAcc A Q
                   → ¬ Diverges ((P ∥⇘ A ⇙ Q) ∖ A)
hide-∥-no-Diverges A P Q ms aq =
  modAcc→¬Div∖ A (P ∥⇘ A ⇙ Q) (ModAcc-∥ A P Q ms aq)

------------------------------------------------------------------------
-- §4.  The concrete spike system.
--
-- `nodeBundle l cl sv` is the config-driven peer bundle: the node plays
-- CLIENT on direction `cl` and SERVER on direction `sv`, over exactly the
-- instances listed in `linkConfig l` — here, KeepAlive in both
-- directions.  Both peers are `iter` LOOPS: neither ever leaves its cycle
-- of its own accord, which is precisely the "looping node" shape the
-- campaign is worried about.
--
-- No api-driving logic process is composed on top.  Synchronising the
-- bundle with a driver on `apiES` can only REMOVE behaviour (a `∥⇘ A ⇙`
-- with a τ-free driver adds no τ of its own), so the un-driven bundle is
-- the MORE permissive system for a divergence question: if this one
-- cannot diverge, no api-constrained refinement of it can either.
------------------------------------------------------------------------

-- the single link of the scenario
link0 : Link
link0 = fzero

-- node 1: KA client on `lo`, KA server on `hi`
node1 : Proc
node1 = nodeBundle link0 lo hi

-- node 2: KA client on `hi`, KA server on `lo`  (the mirror endpoint)
node2 : Proc
node2 = nodeBundle link0 hi lo

-- the un-hidden system: the copy medium synchronised with both nodes on {| input, output |}
spikeOpen : Proc
spikeOpen = CopySpecA ∥⇘ ioES ⇙ (node1 ⦀ node2)

-- the system under study: the same, with the io alphabet hidden.  THIS is
-- the shape whose divergence-freedom the assembly lemma would need.
spikeSystem : Proc
spikeSystem = spikeOpen ∖ ioES

------------------------------------------------------------------------
-- §5.  Reducing the node side to its individual peers.
--
-- `linkConfig` is CLOSED here, so `nodeBundle` computes: with `numLinks
-- = 1` and `linkConfig _ = (lo , KA) ∷ (hi , KA) ∷ []`, `⦀⋆` unfolds to a
-- two-peer bundle plus the `⦀⋆ []` unit.  Both equations hold by `refl`
-- — the `Dir` decision procedure reduces on closed constructors — which
-- is the machine-checked form of "the spike really is the client/server
-- pair the campaign is worried about".
------------------------------------------------------------------------

node1-unfold : node1 ≡ (KAclientA link0 lo ⦀ (KAserverA link0 hi ⦀ Skip))
node1-unfold = refl

node2-unfold : node2 ≡ (KAserverA link0 lo ⦀ (KAclientA link0 hi ⦀ Skip))
node2-unfold = refl

-- `Skip` is `Ret tt`: no τ (both τ-constructors need a `sil`/`react`
-- force) and no visible offer (`sVis` needs a `react`), so it is io-modulo
-- STUCK — the `⦀⋆ []` unit costs nothing.
skipAcc : ModAcc ioES (Skip {0ℓ})
skipAcc = stuck→ModAcc go
  where
  go : ∀ {t′} → ModAStep ioES (Skip {0ℓ}) t′ → ⊥
  go (maτ (sSil eqf))     = case eqf of λ ()
  go (maτ (sTau eqf _))   = case eqf of λ ()
  go (maE _ (sVis eqf _)) = case eqf of λ ()

------------------------------------------------------------------------
-- §6.  The residual leaf obligations.
--
-- These are the ONLY holes left.  Each is a FINITE, LOCAL check on one
-- peer (see the head comment for why each is true):
--
--   * a KA CLIENT parked at `stClient` offers `apiKAev … sendKAMsg` /
--     `sendKADone` and NOTHING else, and has no τ — `api…` renames to
--     `apiKA…`, and `ioSet (_ , apiKA _ _ _) = ⊥` (`NetCommon`), so the
--     client is io-modulo STUCK: certificate depth 0.
--   * a KA SERVER parked at `stClient` offers `receiveKA` only.  That IS
--     hidden (it renames to `output`), so it takes ONE io-modulo step —
--     and lands on `apiKAev … recvKACookie ! _ ⟶ …` (or on
--     `doneKA … ⟶₀ …`, which renames to the non-hidden `done` channel).
--     Either way the successor is io-modulo stuck: depth 1.
--
-- Discharging them mechanically means inverting a step through
-- `RenKA.renameMap` (`ren-τ-inv` / `ren-ev-inv`, `CSP.Rename`) and then
-- through `iter` (`iter-τ-elim`, `CSP.Laws.FSim.LoopCong`) down to the
-- `pchoice` of `KeepAlive.clientStep` / `serverStep`.  That plumbing is
-- NOT built here — it is the one thing this spike leaves open.
------------------------------------------------------------------------

-- BLOCKED ON: rename∘iter step inversion (see above).  The KA client is
-- io-modulo stuck because at `stClient` its `pchoice` offers only
-- `apiKAev`, and `api…` is not in `ioES`.
clientAcc : (l : Link) (d : Dir) → ModAcc ioES (KAclientA l d)
clientAcc l d = ?

-- BLOCKED ON: the same plumbing, one step deeper.  The KA server accepts
-- the hidden `receiveKA` and must then emit `apiKAev … recvKACookie`
-- (or the non-hidden `doneKA`), so its certificate has depth 1.
serverAcc : (l : Link) (d : Dir) → ModAcc ioES (KAserverA l d)
serverAcc l d = ?

-- BLOCKED ON: the same plumbing over `⦀Fin`/`iter` for the copy cells.
-- The medium loops on io FOREVER — that is fine and expected — but each
-- of its io steps is separated from the next by only finitely many τ's,
-- which is all `ModStable` asks.
mediumStable : ModStable ioES CopySpecA
mediumStable = ?

------------------------------------------------------------------------
-- §7.  The conclusion.
------------------------------------------------------------------------

-- both nodes, assembled from §5 and §6 by the interleaving closure
nodesAcc : ModAcc ioES (node1 ⦀ node2)
nodesAcc =
  ModAcc-⦀ ioES
    (ModAcc-⦀ ioES (clientAcc link0 lo) (ModAcc-⦀ ioES (serverAcc link0 hi) skipAcc))
    (ModAcc-⦀ ioES (serverAcc link0 lo) (ModAcc-⦀ ioES (clientAcc link0 hi) skipAcc))

-- OUTCOME (B): the hidden system is divergence-free.
spikeNoDiv : ¬ Diverges spikeSystem
spikeNoDiv = hide-∥-no-Diverges ioES CopySpecA (node1 ⦀ node2) mediumStable nodesAcc
