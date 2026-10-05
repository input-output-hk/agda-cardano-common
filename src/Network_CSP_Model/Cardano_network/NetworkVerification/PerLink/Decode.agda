{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — per-link mux DECODE (`PerLink.Decode`).
--
-- The second layer of the `perLink-single` campaign: it turns an abstract
-- `MuxState l` (from `PerLink.State`) into the concrete `NetProc` it stands
-- for, mirroring `NetworkLink.NetOneLink` operator-for-operator.  Every
-- non-home phase names its stepped-leaf derivative via the `succV`
-- successor trick (copied locally from `NetworkRefinementGen`, never
-- imported — the Gen module is over the memory ceiling), so the
-- `iter-bind`-wrapped normal form of a partly-run loop is never written by
-- hand.  The register decoders extend the spike's two-phase (free/hold)
-- decoders with the `grd` (loop-restart guard) phase Task 1's `MBuf`/`ABuf`
-- added: a guard state is the double-`succV` derivative reached after the
-- register has fired BOTH its receive and its send event (cf. Gen's
-- `decT Tg d = succV (succV Transmitter …) …`).
--
-- The contract exported for Tasks 3-4:
--   · `⟦_⟧ : MuxState l → NetProc`                    (full-stack decode)
--   · `dec-init : (l : Link) → ⟦ initial l ⟧ ≡ NetOneLink l`
-- `dec-init` is PROPOSITIONAL, not `refl`: `decInputs cfg (homeI cfg) ≡
-- ⦀⋆ (map … cfg)` is not definitional for an abstract `cfg = linkConfig l`
-- (both sides recurse on `cfg`, a free variable), so it is discharged by a
-- 3-line list induction per fold (`decInputs-home`/`decOutputs-home`) and a
-- `cong`/`cong₂` glue through the Par/Hide stack.  See the spike report
-- (docs/superpowers/specs/2026-07-10-perlink-phase2-spike-report.md, Q1).
--
-- No postulates, holes, or `NON_TERMINATING`.
------------------------------------------------------------------------

open import Level using (0ℓ)
import Data.Unit.Polymorphic as Poly
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Class.DecEq using (DecEq)

open import Process_Trees
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using (Dir; IDs)

module CSP.Examples.Cardano_network.NetworkVerification.PerLink.Decode
  (p : Params) (Data : Set) ⦃ _ : DecEq Data ⦄ where

open import CSP.Examples.Cardano_network.Net p
  using ( Net; Net-≟; Link
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack )
open Params p using (linkConfig)

import CSP.Operators {E = Net Data} (Net-≟ {Data}) as Op
open Op using (_∥⇘_⇙_; _⦀_; ⦀⋆; _∖_; chanSet; Skip)

open import CSP.Examples.Cardano_network.Network p Data
  using ( NetProc; Input; Output
        ; csSR; csSR-dec; csRS; csRS-dec; csTA; csTA-dec )
open import CSP.Examples.Cardano_network.NetworkLink p Data
  using ( Transmitterₗ; RcvAckₗ; Receiverₗ; SndAckₗ; NetOneLink )
open import CSP.Examples.Cardano_network.NetworkVerification.PerLink.State p Data

------------------------------------------------------------------------
-- The three value-level sync/hide sets, exactly the `Network.agda` forms
-- (definitionally equal to the `chanSet …` terms `NetworkLink` uses).
------------------------------------------------------------------------

-- {| sndmsg, rcvack |}, {| rcvmsg, sndack |}, {| tx, ack |}
csSR' csRS' csTA' : Op.EventSet
csSR' = chanSet csSR csSR-dec
csRS' = chanSet csRS csRS-dec
csTA' = chanSet csTA csTA-dec

------------------------------------------------------------------------
-- Semantic derivative helper `succV` (copied verbatim from
-- `NetworkRefinementGen`, so this module does not import the 3334-line
-- Gen): it COMPUTES the derivative of a process along one offered visible
-- event — the p1 trick that names a stepped leaf without writing its
-- `iter-bind`-wrapped normal form by hand.
------------------------------------------------------------------------

-- the process return type (unit on √)
NetR : Set
NetR = Poly.⊤ {0ℓ}

-- the visible-offer map of a node (empty for non-react nodes)
vis-of : NodeKind (Net Data) (ExtI (Net Data)) NetR
       → (at : AnyTypes (Net Data)) → proj₁ at → Maybe NetProc
vis-of (react v _) = v
vis-of _           = λ _ _ → nothing

-- visible successor of `p` along `at`/`a` (identity if not offered)
succV : NetProc → (at : AnyTypes (Net Data)) → proj₁ at → NetProc
succV p at a with vis-of (PTree.force p) at a
... | just t  = t
... | nothing = p

------------------------------------------------------------------------
-- Per-cell decoders: each non-home phase is a chain of `succV` steps
-- along the events that leaf fires between home and the current phase.
------------------------------------------------------------------------

-- decode one Input cell at its phase (input · sndmsg · rcvack chain)
decInput : (l : Link) → IPh → Dir → IDs → NetProc
decInput l i0     d id = Input l d id
decInput l (i1 x) d id = succV (Input l d id) (Data , input l d id) x
decInput l (i2 x) d id =
  succV (succV (Input l d id) (Data , input l d id) x) (Data , sndmsg l d id) x
decInput l (ig x) d id =
  succV (succV (succV (Input l d id) (Data , input l d id) x)
               (Data , sndmsg l d id) x)
        (⊤ , rcvack l d id) tt

-- decode one Output cell at its phase (rcvmsg · output · sndack chain)
decOutput : (l : Link) → OPh → Dir → IDs → NetProc
decOutput l o0     d id = Output l d id
decOutput l (o1 x) d id = succV (Output l d id) (Data , rcvmsg l d id) x
decOutput l (o2 x) d id =
  succV (succV (Output l d id) (Data , rcvmsg l d id) x) (Data , output l d id) x
decOutput l (og x) d id =
  succV (succV (succV (Output l d id) (Data , rcvmsg l d id) x)
               (Data , output l d id) x)
        (⊤ , sndack l d id) tt

------------------------------------------------------------------------
-- Register decoders: `free` is the loop head (refl-decode); `hold` is the
-- receive-event derivative; `grd` (Task 1's guard phase) is the double
-- derivative after BOTH the receive and the send event have fired, i.e.
-- the state whose only move is the loop-restart τ.
------------------------------------------------------------------------

-- decode the Transmitter register (tb): sndmsg in, tx out
decTrans : (l : Link) → MBuf → NetProc
decTrans l free          = Transmitterₗ l
decTrans l (hold d id x) = succV (Transmitterₗ l) (Data , sndmsg l d id) x
decTrans l (grd d id x)  =
  succV (succV (Transmitterₗ l) (Data , sndmsg l d id) x) (Data , tx l d id) x

-- decode the Receiver register (rb): tx in, rcvmsg out
decRcv : (l : Link) → MBuf → NetProc
decRcv l free          = Receiverₗ l
decRcv l (hold d id x) = succV (Receiverₗ l) (Data , tx l d id) x
decRcv l (grd d id x)  =
  succV (succV (Receiverₗ l) (Data , tx l d id) x) (Data , rcvmsg l d id) x

-- decode the SndAck register (sb): sndack in, ack out (⊤-carried)
decSnd : (l : Link) → ABuf → NetProc
decSnd l free        = SndAckₗ l
decSnd l (hold d id) = succV (SndAckₗ l) (⊤ , sndack l d id) tt
decSnd l (grd d id)  =
  succV (succV (SndAckₗ l) (⊤ , sndack l d id) tt) (⊤ , ack l d id) tt

-- decode the RcvAck register (ab): ack in, rcvack out (⊤-carried)
decRAck : (l : Link) → ABuf → NetProc
decRAck l free        = RcvAckₗ l
decRAck l (hold d id) = succV (RcvAckₗ l) (⊤ , ack l d id) tt
decRAck l (grd d id)  =
  succV (succV (RcvAckₗ l) (⊤ , ack l d id) tt) (⊤ , rcvack l d id) tt

------------------------------------------------------------------------
-- Fold decoders: rebuild the `⦀⋆` interleaving cell by cell, recursing in
-- lock-step with the phase vector (the representation choice that makes the
-- `*-home` lemmas one-liners — see the spike report Q1).
------------------------------------------------------------------------

-- fold-decode the Input cells (empty config ⇒ Skip)
decInputs : (l : Link) (xs : List (Dir × IDs)) → PhV IPh xs → NetProc
decInputs l []              []         = Skip
decInputs l ((d , id) ∷ xs) (ph ∷ phs) = decInput l ph d id ⦀ decInputs l xs phs

-- fold-decode the Output cells (empty config ⇒ Skip)
decOutputs : (l : Link) (xs : List (Dir × IDs)) → PhV OPh xs → NetProc
decOutputs l []              []         = Skip
decOutputs l ((d , id) ∷ xs) (ph ∷ phs) = decOutput l ph d id ⦀ decOutputs l xs phs

------------------------------------------------------------------------
-- Stack assembly, mirroring `NetworkLink.NetOneLink` operator-for-operator.
------------------------------------------------------------------------

-- the Tx side, in the EXACT operator form of `NetworkLink.TxSideₗ`
decTx : (l : Link) → PhV IPh (linkConfig l) → MBuf → ABuf → NetProc
decTx l iphs tb ab =
  (decInputs l (linkConfig l) iphs ∥⇘ csSR' ⇙ (decTrans l tb ⦀ decRAck l ab)) ∖ csSR'

-- the Rx side, in the EXACT operator form of `NetworkLink.RxSideₗ`
decRx : (l : Link) → PhV OPh (linkConfig l) → MBuf → ABuf → NetProc
decRx l ophs rb sb =
  (decOutputs l (linkConfig l) ophs ∥⇘ csRS' ⇙ (decRcv l rb ⦀ decSnd l sb)) ∖ csRS'

-- the full decode, mirroring `NetworkLink.NetOneLink`
⟦_⟧ : ∀ {l} → MuxState l → NetProc
⟦_⟧ {l} st =
  (decTx l (iph st) (tb st) (ab st) ∥⇘ csTA' ⇙ decRx l (oph st) (rb st) (sb st)) ∖ csTA'

------------------------------------------------------------------------
-- `dec-init`: the initial (all-home / all-free) state decodes to the
-- concrete `NetOneLink l`.  Propositional, via a list induction per fold
-- plus a `cong`/`cong₂` glue through the Par/Hide stack (the four register
-- `free` decodes are `refl`).
------------------------------------------------------------------------

-- all-home Input fold ≡ the concrete interleaved Input bundle
decInputs-home : (l : Link) (xs : List (Dir × IDs))
               → decInputs l xs (homeI xs)
                   ≡ ⦀⋆ (map (λ { (d , id) → Input l d id }) xs)
decInputs-home l []              = refl
decInputs-home l ((d , id) ∷ xs) = cong (Input l d id ⦀_) (decInputs-home l xs)

-- all-home Output fold ≡ the concrete interleaved Output bundle
decOutputs-home : (l : Link) (xs : List (Dir × IDs))
                → decOutputs l xs (homeO xs)
                    ≡ ⦀⋆ (map (λ { (d , id) → Output l d id }) xs)
decOutputs-home l []              = refl
decOutputs-home l ((d , id) ∷ xs) = cong (Output l d id ⦀_) (decOutputs-home l xs)

-- the decode of `initial l` is exactly `NetOneLink l`
dec-init : (l : Link) → ⟦ initial l ⟧ ≡ NetOneLink l
dec-init l = cong₂ (λ A B → (A ∥⇘ csTA' ⇙ B) ∖ csTA')
  (cong (λ Z → (Z ∥⇘ csSR' ⇙ (Transmitterₗ l ⦀ RcvAckₗ l)) ∖ csSR')
        (decInputs-home l (linkConfig l)))
  (cong (λ Z → (Z ∥⇘ csRS' ⇙ (Receiverₗ l ⦀ SndAckₗ l)) ∖ csRS')
        (decOutputs-home l (linkConfig l)))
