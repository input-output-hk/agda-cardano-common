{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the one-link, two-protocol PRIORITY property
-- P1 (Task 6 of the praos-over-leios plan): on a minimal `Params`
-- (`numLinks = 1`, one link running exactly BlockFetch + LeiosFetch), the
-- channel-level priority operator `Priᶜ bfOverLf` OFFERS BlockFetch's
-- `sndmsg` and PRUNES LeiosFetch's `sndmsg` at a representative send-buffered
-- state where both cells compete.
--
--   * `bothBuffered` — a representative send-queue state where each of the
--     two `Input` cells has consumed its `input` and now offers its
--     `sndmsg`. It is the interleaving `Pbf ⦀ Plf` of the two post-`input`
--     output cells (binary `⦀`, the `Skip` tail of `⦀⋆` folded away); it is
--     NOT proven reachable from `TxSideₗ-pri l₀`'s own transitions — see the
--     P3 note below.
--   * `pri-keeps-bf` — BlockFetch's `sndmsg` survives (`≤`-maximal on this
--     link, so `Priᶜ` leaves it untouched).
--   * `pri-prunes-lf` — LeiosFetch's `sndmsg` is dropped: its strict
--     dominator (this link's BlockFetch `sndmsg`) is concurrently offered.
--
-- ROUTE: the minimal `Params` is a fully CONCRETE record (all abstract data
-- domains fixed to `⊤`), so `Net-≟`, `dominatedᶜ?`, and the payload `DecEq`
-- all COMPUTE — every fact is by direct reduction of `Priᶜ`, exactly as the
-- generic `CSP.Examples.priority.MuxDelayedExample` demonstrates for `P ⦀ Q`.
-- `bothBuffered`/`fb` are rebuilt directly (the brief's fallback) rather than
-- threaded through `NetworkLinkPri`'s `fbInputsₗ`; `finBr-Output` (Task 4) is
-- reused for the per-cell certificate.  No ExactSupp needed on this route.
--
-- Not `--safe`: the Cardano/priority import chain carries a pre-existing
-- postulate elsewhere; this module introduces no `postulate`, no
-- `dne`/`Classical`, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero)
open import Data.Unit.Polymorphic using (⊤)
import Data.Unit as U
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _,_)
open import Relation.Nullary using (yes; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Function using (case_of_)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base
  using (IDs; N2N_BlockFetch; N2N_LeiosFetch; Dir; lo; Mode; FromInitiator)

module CSP.Examples.Cardano_network.Priority.TxSidePriOneLink where

------------------------------------------------------------------------
-- The minimal, fully concrete parameter bundle.
------------------------------------------------------------------------

-- decidable equality on the unit type (fixes every abstract data domain)
decEq⊤ : DecEq U.⊤
decEq⊤ ._≟_ U.tt U.tt = yes refl

-- minimal `Params`: one link running BlockFetch + LeiosFetch, all abstract
-- data domains collapsed to `⊤` so every `DecEq` computes to `yes refl`.
import Data.Maybe as PMaybe

p₀ : Params
p₀ = record
  { Cookie   = U.⊤ ; Block  = U.⊤ ; Txid = U.⊤ ; LSlot = U.⊤
  ; VoterId  = U.⊤ ; LFBitmap = U.⊤ ; VoteBlob = U.⊤
  ; Time     = U.⊤ ; Length = U.⊤
  ; time₀    = U.tt ; length₀ = U.tt
  ; numLinks = 1
  ; linkConfig = λ _ → (lo , N2N_BlockFetch) ∷ (lo , N2N_LeiosFetch) ∷ []
  ; decCookie = decEq⊤ ; decBlock = decEq⊤ ; decTxid = decEq⊤ ; decLSlot = decEq⊤
  ; decVoterId = decEq⊤ ; decLFBitmap = decEq⊤ ; decVoteBlob = decEq⊤
  ; decTime = decEq⊤ ; decLength = decEq⊤
  -- Leios EB domains, inert here: both ⊤, no RB ever announces an EB
  ; EB = U.⊤ ; EBHash = U.⊤ ; decEB = decEq⊤ ; decEBHash = decEq⊤
  ; ebHash = λ _ → U.tt ; announcedEB = λ _ → PMaybe.nothing }

------------------------------------------------------------------------
-- Alphabet, data, operator layer, priority order — all at `p₀`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Data p₀
  using (Payload; DecEq-Payload; leiosFetch; MsgLFDone)
open import CSP.Examples.Cardano_network.Net p₀
  using (Net; Net-≟; Link; input; sndmsg; rcvack)
open import CSP.Examples.Cardano_network.Priority.BfOverLf p₀ using (bfOverLf)

open import CSP.Operators (Net-≟ {Payload})
  using (Output; _⦀_; Skip; Prefix₀)

open import Semantics.LTS      {E = Net Payload} {I = ExtI (Net Payload)}
  using (Event√; evl; evLabel; sVis; ev; _─[_]─►_)
open import Semantics.Refusals {E = Net Payload} {I = ExtI (Net Payload)} using (Offers)
open import CSP.Priority.Base    {0ℓ} {0ℓ} {Net Payload} using (FinBr)
open import CSP.Priority.Channel (Net-≟ {Payload}) using (Priᶜ)
open import CSP.Priority.Closure (Net-≟ {Payload}) using (finBr-prefix₀; finBr-Skip; finBr-⦀)
open import CSP.Examples.Cardano_network.Priority.NetworkLinkPri p₀ using (finBr-Output; fbInputsₗ)
open import CSP.Examples.Cardano_network.NetworkLink p₀ Payload ⦃ DecEq-Payload ⦄
  using (Inputsₗ)

------------------------------------------------------------------------
-- The concrete link, direction, buffered value.
------------------------------------------------------------------------

-- the sole link (`Fin 1`)
l₀ : Link
l₀ = zero

-- the sole configured direction
d₀ : Dir
d₀ = lo

-- a concrete send payload (any inhabitant of the fully concrete `Payload`)
somePayload : Payload
somePayload = U.tt , FromInitiator , U.tt , leiosFetch MsgLFDone

------------------------------------------------------------------------
-- The two post-`input` (send-buffered) cells and their certificates.
--
-- Each cell is the `inputMenu` continuation reached after consuming `input`:
-- `Output (sndmsg l₀ d₀ id) somePayload (rcvack l₀ d₀ id ⟶₀ Skip)` — a stable
-- react node offering exactly `sndmsg l₀ d₀ id`.
------------------------------------------------------------------------

-- BlockFetch send-buffered cell: offers `sndmsg l₀ d₀ BlockFetch`
Pbf : PTree (Net Payload) (ExtI (Net Payload)) (⊤ {0ℓ})
Pbf = Output (sndmsg l₀ d₀ N2N_BlockFetch) somePayload (Prefix₀ (rcvack l₀ d₀ N2N_BlockFetch) Skip)

-- LeiosFetch send-buffered cell: offers `sndmsg l₀ d₀ LeiosFetch`
Plf : PTree (Net Payload) (ExtI (Net Payload)) (⊤ {0ℓ})
Plf = Output (sndmsg l₀ d₀ N2N_LeiosFetch) somePayload (Prefix₀ (rcvack l₀ d₀ N2N_LeiosFetch) Skip)

-- the reachable send-queue state: both cells buffered, interleaved
bothBuffered : PTree (Net Payload) (ExtI (Net Payload)) (⊤ {0ℓ})
bothBuffered = Pbf ⦀ Plf

-- per-cell FinBr certificates (reusing Task 4's `finBr-Output`)
fbBf : FinBr Pbf
fbBf = finBr-Output ⦃ DecEq-Payload ⦄ (finBr-prefix₀ finBr-Skip)
fbLf : FinBr Plf
fbLf = finBr-Output ⦃ DecEq-Payload ⦄ (finBr-prefix₀ finBr-Skip)

-- FinBr for the interleaving `bothBuffered`
fb : FinBr bothBuffered
fb = finBr-⦀ fbBf fbLf

------------------------------------------------------------------------
-- The two visible send labels under contention.
------------------------------------------------------------------------

-- BlockFetch's `sndmsg` (the dominating, ≤-maximal channel)
sBF : Event√ (⊤ {0ℓ})
sBF = evl (evLabel Payload (sndmsg l₀ d₀ N2N_BlockFetch) somePayload)

-- LeiosFetch's `sndmsg` (the dominated channel)
sLF : Event√ (⊤ {0ℓ})
sLF = evl (evLabel Payload (sndmsg l₀ d₀ N2N_LeiosFetch) somePayload)

------------------------------------------------------------------------
-- P1 — prune-under-contention.
------------------------------------------------------------------------

-- P1b: BlockFetch's `sndmsg` survives prioritisation (it is ≤-maximal, so
-- `dominatedᶜ? bfOverLf fb` is `false` on it and `Priᶜ` keeps the offer).
pri-keeps-bf : Offers (Priᶜ bfOverLf bothBuffered fb) sBF
pri-keeps-bf = _ , sVis refl refl

-- P1a: LeiosFetch's `sndmsg` is pruned — its strict dominator (this link's
-- BlockFetch `sndmsg`) is in `chan-supp fb`, so `dominatedᶜ? bfOverLf fb`
-- computes to `true` and `Priᶜ`'s visible map is `nothing` there.
pri-prunes-lf : ¬ Offers (Priᶜ bfOverLf bothBuffered fb) sLF
pri-prunes-lf (_ , sVis {v = v} eqf br) with react-injective eqf
... | veq , _ =
  case subst (λ w → w (Payload , sndmsg l₀ d₀ N2N_LeiosFetch) somePayload ≡ just _)
             (sym veq) br of λ ()

------------------------------------------------------------------------
-- P2 — delayed-not-lost: once BlockFetch's `sndmsg` fires and contention
-- clears, LeiosFetch's `sndmsg` is offered again.
------------------------------------------------------------------------

-- BlockFetch's cell after its `sndmsg` hands off: the `rcvack`-then-`Skip`
-- residual reached by firing `sBF` out of `Pbf` (no longer offers `sndmsg`).
Pbf′ : PTree (Net Payload) (ExtI (Net Payload)) (⊤ {0ℓ})
Pbf′ = Prefix₀ (rcvack l₀ d₀ N2N_BlockFetch) Skip

-- the post-BF-step state: BlockFetch drained, LeiosFetch's cell untouched
bfDrained : PTree (Net Payload) (ExtI (Net Payload)) (⊤ {0ℓ})
bfDrained = Pbf′ ⦀ Plf

-- FinBr for `bfDrained` (BlockFetch's residual now offers only `rcvack`)
fb′ : FinBr bfDrained
fb′ = finBr-⦀ (finBr-prefix₀ finBr-Skip) fbLf

-- the solo BlockFetch step out of `bothBuffered`, firing `sBF`: the genuine
-- transition witnessing that `bfDrained` is reached once BF hands off.
bf-fires : bothBuffered ─[ ev sBF ]─► bfDrained
bf-fires = sVis refl refl

-- P2: with BlockFetch drained, its dominating channel is absent from
-- `chan-supp fb′` (only `rcvack l₀ d₀ N2N_BlockFetch` and LeiosFetch's own
-- `sndmsg` remain), so `dominatedᶜ? bfOverLf fb′` computes to `false` at
-- `sLF` and `Priᶜ` no longer prunes it — LeiosFetch's `sndmsg` reappears.
pri-lf-reappears : Offers (Priᶜ bfOverLf bfDrained fb′) sLF
pri-lf-reappears = _ , sVis refl refl

------------------------------------------------------------------------
-- P3 — priority pruning never introduces deadlock: at each prioritised
-- state something is always offered.  (Full reachable-state
-- `DeadlockFree (TxSideₗ-pri l₀)` is out of scope here — `bothBuffered`/
-- `bfDrained` are hand-built representatives, not proven reachable from
-- `TxSideₗ-pri l₀`'s own transitions; that is a documented follow-on.)
------------------------------------------------------------------------

-- the contended state still offers something (BlockFetch's `sndmsg`,
-- via P1's `pri-keeps-bf`) — pruning LeiosFetch never empties the menu.
pri-no-deadlock-contended : Σ _ (Offers (Priᶜ bfOverLf bothBuffered fb))
pri-no-deadlock-contended = sBF , pri-keeps-bf

-- the drained state still offers something (LeiosFetch's `sndmsg`
-- reappearing, via P2's `pri-lf-reappears`) — delay is never loss.
pri-no-deadlock-drained : Σ _ (Offers (Priᶜ bfOverLf bfDrained fb′))
pri-no-deadlock-drained = sLF , pri-lf-reappears

-- the fresh prioritised send-queue head still offers `input`: `bfOverLf`
-- only relates `sndmsg` channels (`aboveBfLf` of an `input` channel is
-- `[]`), so `input l₀ d₀ N2N_BlockFetch` is incomparable ⇒ never pruned
-- ⇒ `Priᶜ`'s visible map at it is `just` (same reduction style as
-- `pri-keeps-bf`, now over the genuine `Inputsₗ l₀`/`fbInputsₗ l₀`).
head-offers-input : Offers (Priᶜ bfOverLf (Inputsₗ l₀) (fbInputsₗ l₀))
                           (evl (evLabel Payload (input l₀ d₀ N2N_BlockFetch) somePayload))
head-offers-input = _ , sVis refl refl
