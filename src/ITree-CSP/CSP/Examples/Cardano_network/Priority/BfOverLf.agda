{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — channel-level priority order `bfOverLf`:
-- per LINK, BlockFetch's `sndmsg` dominates LeiosFetch's `sndmsg`.
--
-- This is the ORDER consumed by the priority operator `Priᶜ`
-- (`CSP.Priority.Channel`) when it is applied to a `NetworkLink` send
-- queue (`NetworkLink.agda`, channel type `Net Payload`): under
-- contention on the SAME link, a pending BlockFetch `sndmsg` prunes a
-- concurrently offered LeiosFetch `sndmsg` on that link (delayed, not
-- lost — `Priᶜ` only prunes an offer that is itself dominated, so the
-- LeiosFetch send resurfaces once BlockFetch is no longer offered).
--
-- Every other pair of channels (different links, different message
-- kinds, any of `input`/`output`/`rcvmsg`/`tx`/`sndack`/`rcvack`/`ack`,
-- or a `sndmsg` not paired BlockFetch-over-LeiosFetch) is UNRELATED —
-- `Priᶜ` leaves them untouched.
--
-- Alphabet: `AnyTypes (Net Payload)`, the SAME channel type `NetworkLink`
-- (and Task 4's `Priᶜ` application) use — `Data` instantiated to the
-- shared `Payload` from `Data.agda`, over the SAME `Params p`.
--
-- Not `--safe`: the Cardano/priority import chain carries a pre-existing
-- postulate elsewhere in the project; this module itself introduces no
-- postulate, no `dne`/`Classical`, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees using (AnyTypes)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base
  using (N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission; N2N_KeepAlive
        ; N2N_LeiosNotify; N2N_LeiosFetch; FromInitiator)

-- parametrised by the SAME abstract data bundle `NetworkLink`/`Net`/`Data` use
module CSP.Examples.Cardano_network.Priority.BfOverLf (p : Params) where

open Params p using (time₀; length₀)
open import CSP.Examples.Cardano_network.Net p
  using (Net; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack)
open import CSP.Examples.Cardano_network.Data p
  using (Payload; leiosFetch; MsgLFDone)

open import Semantics.PriOrderC {0ℓ} {0ℓ} {Net Payload}

------------------------------------------------------------------------
-- The strict channel order: a link's LeiosFetch `sndmsg` is dominated by
-- the SAME link's BlockFetch `sndmsg`; every other pair is unrelated.
------------------------------------------------------------------------

-- `c <bfLf c′` holds iff `c` is `sndmsg l d LeiosFetch` and `c′` is
-- `sndmsg l d BlockFetch` on the SAME link/direction; else empty.
_<bfLf_ : AnyTypes (Net Payload) → AnyTypes (Net Payload) → Set
(_ , sndmsg l d N2N_LeiosFetch) <bfLf (_ , sndmsg l′ d′ N2N_BlockFetch) =
  (l ≡ l′) × (d ≡ d′)
_ <bfLf _ = ⊥

-- irreflexive: `c <bfLf c` always falls to the fallback `⊥` clause (the
-- two fixed IDs `N2N_LeiosFetch`/`N2N_BlockFetch` in the first clause can
-- never both be the SAME constructor, as `c <bfLf c` would require).
<bfLf-irrefl : ∀ {c} → ¬ (c <bfLf c)
<bfLf-irrefl {_ , input _ _ _}                ()
<bfLf-irrefl {_ , output _ _ _}               ()
<bfLf-irrefl {_ , sndmsg _ _ N2N_ChainSync}   ()
<bfLf-irrefl {_ , sndmsg _ _ N2N_BlockFetch}  ()
<bfLf-irrefl {_ , sndmsg _ _ N2N_TxSubmission} ()
<bfLf-irrefl {_ , sndmsg _ _ N2N_KeepAlive}   ()
<bfLf-irrefl {_ , sndmsg _ _ N2N_LeiosNotify} ()
<bfLf-irrefl {_ , sndmsg _ _ N2N_LeiosFetch}  ()
<bfLf-irrefl {_ , rcvmsg _ _ _}               ()
<bfLf-irrefl {_ , tx _ _ _}                   ()
<bfLf-irrefl {_ , sndack _ _ _}               ()
<bfLf-irrefl {_ , rcvack _ _ _}               ()
<bfLf-irrefl {_ , ack _ _ _}                  ()

-- transitive: the only way to chain two `<bfLf` steps is degenerate,
-- since a `<bfLf`-related pair's RIGHT side (`sndmsg … BlockFetch`) can
-- never itself be a `<bfLf`-related pair's LEFT side (`sndmsg … LeiosFetch`).
<bfLf-trans : ∀ {c d e} → c <bfLf d → d <bfLf e → c <bfLf e
<bfLf-trans {_ , sndmsg _ _ N2N_LeiosFetch} {_ , sndmsg _ _ N2N_BlockFetch} {_ , input _ _ _} _ ()
<bfLf-trans {_ , sndmsg _ _ N2N_LeiosFetch} {_ , sndmsg _ _ N2N_BlockFetch} {_ , output _ _ _} _ ()
<bfLf-trans {_ , sndmsg _ _ N2N_LeiosFetch} {_ , sndmsg _ _ N2N_BlockFetch} {_ , sndmsg _ _ N2N_ChainSync} _ ()
<bfLf-trans {_ , sndmsg _ _ N2N_LeiosFetch} {_ , sndmsg _ _ N2N_BlockFetch} {_ , sndmsg _ _ N2N_BlockFetch} _ ()
<bfLf-trans {_ , sndmsg _ _ N2N_LeiosFetch} {_ , sndmsg _ _ N2N_BlockFetch} {_ , sndmsg _ _ N2N_TxSubmission} _ ()
<bfLf-trans {_ , sndmsg _ _ N2N_LeiosFetch} {_ , sndmsg _ _ N2N_BlockFetch} {_ , sndmsg _ _ N2N_KeepAlive} _ ()
<bfLf-trans {_ , sndmsg _ _ N2N_LeiosFetch} {_ , sndmsg _ _ N2N_BlockFetch} {_ , sndmsg _ _ N2N_LeiosNotify} _ ()
<bfLf-trans {_ , sndmsg _ _ N2N_LeiosFetch} {_ , sndmsg _ _ N2N_BlockFetch} {_ , sndmsg _ _ N2N_LeiosFetch} _ ()
<bfLf-trans {_ , sndmsg _ _ N2N_LeiosFetch} {_ , sndmsg _ _ N2N_BlockFetch} {_ , rcvmsg _ _ _} _ ()
<bfLf-trans {_ , sndmsg _ _ N2N_LeiosFetch} {_ , sndmsg _ _ N2N_BlockFetch} {_ , tx _ _ _} _ ()
<bfLf-trans {_ , sndmsg _ _ N2N_LeiosFetch} {_ , sndmsg _ _ N2N_BlockFetch} {_ , sndack _ _ _} _ ()
<bfLf-trans {_ , sndmsg _ _ N2N_LeiosFetch} {_ , sndmsg _ _ N2N_BlockFetch} {_ , rcvack _ _ _} _ ()
<bfLf-trans {_ , sndmsg _ _ N2N_LeiosFetch} {_ , sndmsg _ _ N2N_BlockFetch} {_ , ack _ _ _} _ ()

------------------------------------------------------------------------
-- `aboveBfLf`: the dominators of a channel — the sibling BlockFetch
-- `sndmsg` for a LeiosFetch `sndmsg` on the same link, else none.
------------------------------------------------------------------------

-- dominating channels of `c`: `[sndmsg l d BlockFetch]` for `c = sndmsg
-- l d LeiosFetch`, `[]` otherwise.
aboveBfLf : AnyTypes (Net Payload) → List (AnyTypes (Net Payload))
aboveBfLf (_ , sndmsg l d N2N_LeiosFetch) = (Payload , sndmsg l d N2N_BlockFetch) ∷ []
aboveBfLf _ = []

-- sound: a channel listed by `aboveBfLf c` really dominates `c`.
aboveBfLf-sound : ∀ {c c′} → c′ ∈ aboveBfLf c → c <bfLf c′
aboveBfLf-sound {_ , sndmsg l d N2N_LeiosFetch} (here refl) = refl , refl
aboveBfLf-sound {_ , sndmsg l d N2N_LeiosFetch} (there ())
aboveBfLf-sound {_ , input _ _ _}                ()
aboveBfLf-sound {_ , output _ _ _}               ()
aboveBfLf-sound {_ , sndmsg _ _ N2N_ChainSync}   ()
aboveBfLf-sound {_ , sndmsg _ _ N2N_BlockFetch}  ()
aboveBfLf-sound {_ , sndmsg _ _ N2N_TxSubmission} ()
aboveBfLf-sound {_ , sndmsg _ _ N2N_KeepAlive}   ()
aboveBfLf-sound {_ , sndmsg _ _ N2N_LeiosNotify} ()
aboveBfLf-sound {_ , rcvmsg _ _ _}               ()
aboveBfLf-sound {_ , tx _ _ _}                   ()
aboveBfLf-sound {_ , sndack _ _ _}               ()
aboveBfLf-sound {_ , rcvack _ _ _}               ()
aboveBfLf-sound {_ , ack _ _ _}                  ()

-- complete: every dominator of `c` (per `_<bfLf_`) is listed by `aboveBfLf c`.
aboveBfLf-complete : ∀ {c c′} → c <bfLf c′ → c′ ∈ aboveBfLf c
aboveBfLf-complete {_ , sndmsg l d N2N_LeiosFetch} {_ , sndmsg l′ d′ N2N_BlockFetch} (refl , refl) = here refl

-- inhabited: the dominating channel's carrier `Payload` has a witness
-- (an arbitrary concrete `Time × Mode × Length × Messages` value).
aboveBfLf-inhabited : ∀ {c c′} → c′ ∈ aboveBfLf c → proj₁ c′
aboveBfLf-inhabited {_ , sndmsg l d N2N_LeiosFetch} (here refl) =
  time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone
aboveBfLf-inhabited {_ , sndmsg l d N2N_LeiosFetch} (there ())
aboveBfLf-inhabited {_ , input _ _ _}                ()
aboveBfLf-inhabited {_ , output _ _ _}               ()
aboveBfLf-inhabited {_ , sndmsg _ _ N2N_ChainSync}   ()
aboveBfLf-inhabited {_ , sndmsg _ _ N2N_BlockFetch}  ()
aboveBfLf-inhabited {_ , sndmsg _ _ N2N_TxSubmission} ()
aboveBfLf-inhabited {_ , sndmsg _ _ N2N_KeepAlive}   ()
aboveBfLf-inhabited {_ , sndmsg _ _ N2N_LeiosNotify} ()
aboveBfLf-inhabited {_ , rcvmsg _ _ _}               ()
aboveBfLf-inhabited {_ , tx _ _ _}                   ()
aboveBfLf-inhabited {_ , sndack _ _ _}               ()
aboveBfLf-inhabited {_ , rcvack _ _ _}               ()
aboveBfLf-inhabited {_ , ack _ _ _}                  ()

-- the channel-level priority order: per link, BlockFetch's `sndmsg`
-- dominates that SAME link's LeiosFetch `sndmsg`; everything else unrelated.
bfOverLf : PriOrderC 0ℓ
bfOverLf = record
  { prop = record { _<ᶜ_ = _<bfLf_ ; <ᶜ-irrefl = <bfLf-irrefl ; <ᶜ-trans = <bfLf-trans }
  ; aboveᶜ          = aboveBfLf
  ; aboveᶜ-sound    = aboveBfLf-sound
  ; aboveᶜ-complete = aboveBfLf-complete
  ; above-inhabited = aboveBfLf-inhabited
  }
