{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the visible-middle DRIVER-STEP preservation glue
-- (`Praos.PipeEvDriver`).
--
-- `PipeStepEmit.EvStep` reflects the SINGLE visible api-CSBF middle of a weak
-- move to a `PipeInv⁺`-preservation map.  On such a step the medium is FIXED
-- (`WalkDExpose.top-nodes-abs-expose` returns `med s ≡ med s′`), so BOTH copy
-- cells are fixed, and EXACTLY ONE leg driver of leg `l` advances by a genuine
-- SINGLE step — a `WalkMeasure.ProdAdv` (producer, node A), `WalkMeasure.CPAdv`
-- (relay, node B/C), or `WalkMeasure.ConsAdv` (consumer, node D) — while the
-- other two leg drivers are fixed.
--
-- THIS module turns such a genuine single-step driver advance (PLUS the fixed
-- component equalities the visible step supplies) into the `PipeInv⁺ l (toSys r)
-- → PipeInv⁺ l (toSys r′)` map, by CLASSIFYING the advance at the PHASE level
-- (the `WalkMeasure` `Adv` families have concrete phase indices, so a case split
-- resolves every `ProdSent`/`RelayHas`/`ConsRecv` gate DEFINITIONALLY) and
-- dispatching to the matching `PipeInv` core.
--
-- The TWO receive-boundary crossings (relay `recvBFBlock` `cp3→cp4`, consumer
-- `recvBFBlock` `cp3→cp4`) are NOT phase-derivable: they need the client-holds
-- fact `BFcHasBlk (upClient/dnClient l s)` (the receiving driver's local BF
-- CLIENT peer held the block).  Those are isolated as GUARDED hypotheses
-- (`wUp`/`wDn`), demanded only on the receive transition and vacuously
-- discharged on every other — exactly the receive-coupling obligation the caller
-- (`EvStep`, off the api node cone) must supply from the `recvBFBlock` label.
-- Symmetrically the upstream-client / downstream-client FIXITY (`eUp`/`eDn`) is
-- guarded by the NON-receive classification (on a receive the peer moves).
--
-- LIGHT (pure phase logic; imports only `PipeInv` cores + the `WalkMeasure`
-- adjacency families + `WalkPr`/`SysNode` phase carriers — NO node cone).  No
-- postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( _×_; _,_ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; subst )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriver (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA using
  ( ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
  ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
  ; CPPh; consuming; producing )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA using
  ( ProdAdv; a01; a12; a23; a34; a45; a56; a67; a78; a89
  ; ConsAdv; c01; c12; c23; c34; c45; c56
  ; CPAdv; cpC; cpB; cpP )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA using
  ( TwoLegs; phOf; InCp03 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA using
  ( PipeInv⁺; prodOf; relayOf; cellUp; cellDn; upClient; dnClient
  ; ProdSent; ProdNotSent; RelayPre; RelayHas; RelayFwd; ConsRecv; BFcHasBlk
  ; CellHasBlk; transImp
  ; pipeInv⁺-prod-move; pipeInv⁺-prod-send
  ; pipeInv-relay-move; pipeInv-relay-fwd; pipeInv⁺-relay-recv
  ; pipeInv-cons-move; pipeInv⁺-cons-recv )

------------------------------------------------------------------------
-- PRODUCER.  A genuine `ProdAdv a b` is EITHER a class-preserving move (both
-- not-sent `a01..a45`, or both sent `a67..a89`) or the `sendBFBlock` boundary
-- (`a56`, not-sent → sent).  The phase indices are concrete, so the maps reduce.
------------------------------------------------------------------------

-- the producer step's kind, carrying exactly the maps a `PipeInv` core consumes
data ProdStepKind (a b : ProdPh) : Set where
  pMove : (ProdNotSent a → ProdNotSent b) → (ProdSent a → ProdSent b) → ProdStepKind a b
  pSend : ProdNotSent a → ProdSent b → ProdStepKind a b

-- classify a genuine producer single step
prodadv-step : ∀ {a b} → ProdAdv a b → ProdStepKind a b
prodadv-step a01 = pMove (λ _ → tt) (λ ())
prodadv-step a12 = pMove (λ _ → tt) (λ ())
prodadv-step a23 = pMove (λ _ → tt) (λ ())
prodadv-step a34 = pMove (λ _ → tt) (λ ())
prodadv-step a45 = pMove (λ _ → tt) (λ ())
prodadv-step a56 = pSend tt tt
prodadv-step a67 = pMove (λ ()) (λ _ → tt)
prodadv-step a78 = pMove (λ ()) (λ _ → tt)
prodadv-step a89 = pMove (λ ()) (λ _ → tt)

-- PRODUCER preservation: node A fires on leg `l`; relay / cons / both cells /
-- both clients are all fixed (node A hosts no tracked client; medium fixed)
pres-prod : (l : TwoLegs) (s s′ : _)
  → ProdAdv (prodOf l s) (prodOf l s′)
  → relayOf  l s ≡ relayOf  l s′ → phOf     l s ≡ phOf     l s′
  → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
  → upClient l s ≡ upClient l s′ → dnClient l s ≡ dnClient l s′
  → PipeInv⁺ l s → PipeInv⁺ l s′
pres-prod l s s′ pa re ce cue cde ue de pinv with prodadv-step pa
... | pMove fN fS = pipeInv⁺-prod-move l s s′ re ce cue cde ue de fN fS pinv
... | pSend nN sS = pipeInv⁺-prod-send l s s′ re ce cde de nN sS pinv

------------------------------------------------------------------------
-- RELAY.  A genuine `CPAdv a b` is a consume-side advance (`cpC`), the
-- consume→produce bind hop (`cpB`), or a produce-side advance (`cpP`).  It
-- resolves to a class-preserving move, the FORWARD boundary (`cpP a56`,
-- producing `pp5→pp6`, holding → forwarded), or the RECEIVE boundary
-- (`cpC c34`, consuming `cp3→cp4`, pre → holding).  Only the receive needs the
-- upstream-client witness; only move/forward need upstream-client fixity — hence
-- the `RelayPre a × RelayHas b → ⊥` guard flagging "NOT a receive".
------------------------------------------------------------------------

-- the relay step's kind
data RelayStepKind (a b : CPPh) : Set where
  rMove : (RelayPre a → RelayPre b) → (RelayHas a → RelayHas b) → (RelayFwd a → RelayFwd b)
        → (RelayPre a × RelayHas b → ⊥) → RelayStepKind a b
  rFwd  : RelayHas a → RelayFwd b → (RelayPre a × RelayHas b → ⊥) → RelayStepKind a b
  rRecv : RelayPre a → RelayHas b → RelayStepKind a b

-- classify a genuine relay single step
cpadv-step : ∀ {a b} → CPAdv a b → RelayStepKind a b
cpadv-step (cpC c01) = rMove (λ _ → tt) (λ ()) (λ ()) (λ { (_ , ()) })
cpadv-step (cpC c12) = rMove (λ _ → tt) (λ ()) (λ ()) (λ { (_ , ()) })
cpadv-step (cpC c23) = rMove (λ _ → tt) (λ ()) (λ ()) (λ { (_ , ()) })
cpadv-step (cpC c34) = rRecv tt tt
cpadv-step (cpC c45) = rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
cpadv-step (cpC c56) = rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
cpadv-step cpB       = rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
cpadv-step (cpP a01) = rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
cpadv-step (cpP a12) = rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
cpadv-step (cpP a23) = rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
cpadv-step (cpP a34) = rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
cpadv-step (cpP a45) = rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
cpadv-step (cpP a56) = rFwd tt tt (λ { (() , _) })
cpadv-step (cpP a67) = rMove (λ ()) (λ ()) (λ _ → tt) (λ { (() , _) })
cpadv-step (cpP a78) = rMove (λ ()) (λ ()) (λ _ → tt) (λ { (() , _) })
cpadv-step (cpP a89) = rMove (λ ()) (λ ()) (λ _ → tt) (λ { (() , _) })

-- RELAY internal move (′): on the TWO non-`recvBFBlock` visible relay consume
-- moves (`sendBFRequestRange`, `sendBFClientDone`) the relay's OWN upstream BF
-- client fires WITH the relay — so `pipeInv⁺-relay-move`'s upstream-client fixity
-- (`ue`) is FALSE.  We instead take the SUCCESSOR-non-block premise `¬blk′`
-- (`¬ BFcHasBlk (upClient l s′)`; the client advanced to a ¬-block phase, never
-- ENTERS `bcBlk1` on a visible step) and discharge the upstream-client coupling
-- clause vacuously.  Built directly on the exposed base core `pipeInv-relay-move`.
pipeInv⁺-relay-move′ : (l : TwoLegs) (s s′ : _)
  → prodOf   l s ≡ prodOf   l s′ → phOf     l s ≡ phOf     l s′
  → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
  → dnClient l s ≡ dnClient l s′
  → (BFcHasBlk (upClient l s′) → ⊥)
  → (RelayPre (relayOf l s) → RelayPre (relayOf l s′))
  → (RelayHas (relayOf l s) → RelayHas (relayOf l s′))
  → (RelayFwd (relayOf l s) → RelayFwd (relayOf l s′))
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-relay-move′ l s s′ pe ce cue cde de ¬blk′ fP fH fF (pinv , cu , uc , cd , dc)
  = pipeInv-relay-move l s s′ pe ce fP fH fF pinv
  , transImp CellHasBlk ProdSent cue pe cu
  , (λ h → ⊥-elim (¬blk′ h))
  , (λ h → fF (cd (subst CellHasBlk    (sym cde) h)))
  , (λ h → fF (dc (subst BFcHasBlk (sym de)  h)))

-- RELAY forward (′): same successor-non-block treatment of the upstream-client
-- coupling clause (the forward step is produce-side, upstream client ¬-block at
-- s′); the two downstream clauses hold outright since the relay is now FORWARDED.
pipeInv⁺-relay-fwd′ : (l : TwoLegs) (s s′ : _)
  → prodOf l s ≡ prodOf l s′ → phOf l s ≡ phOf l s′
  → cellUp l s ≡ cellUp l s′
  → (BFcHasBlk (upClient l s′) → ⊥)
  → RelayHas (relayOf l s) → RelayFwd (relayOf l s′)
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-relay-fwd′ l s s′ pe ce cue ¬blk′ hHas hFwd (pinv , cu , uc , cd , dc)
  = pipeInv-relay-fwd l s s′ pe ce hHas hFwd pinv
  , transImp CellHasBlk ProdSent cue pe cu
  , (λ h → ⊥-elim (¬blk′ h))
  , (λ _ → hFwd) , (λ _ → hFwd)

-- RELAY preservation: node B/C fires on leg `l`; prod / cons / both cells fixed,
-- downstream client (node D) fixed.  `¬blk′` = the SUCCESSOR upstream client does
-- NOT hold a block (valid on every visible relay move/forward — the client only
-- ENTERS `bcBlk1` via a HIDDEN io delivery, never on a visible step); `wUp` = the
-- upstream client held the block, demanded only ON a receive.
pres-relay : (l : TwoLegs) (s s′ : _)
  → CPAdv (relayOf l s) (relayOf l s′)
  → prodOf   l s ≡ prodOf   l s′ → phOf     l s ≡ phOf     l s′
  → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
  → dnClient l s ≡ dnClient l s′
  → (BFcHasBlk (upClient l s′) → ⊥)
  → (RelayPre (relayOf l s) → RelayHas (relayOf l s′) → BFcHasBlk (upClient l s))
  → PipeInv⁺ l s → PipeInv⁺ l s′
pres-relay l s s′ ca pe ce cue cde de ¬blk′ wUp pinv with cpadv-step ca
... | rMove fP fH fF _ =
      pipeInv⁺-relay-move′ l s s′ pe ce cue cde de ¬blk′ fP fH fF pinv
... | rFwd hHas hFwd _ =
      pipeInv⁺-relay-fwd′ l s s′ pe ce cue ¬blk′ hHas hFwd pinv
... | rRecv hPre hHas =
      pipeInv⁺-relay-recv l s s′ pe ce cue cde de hPre (wUp hPre hHas) hHas pinv

------------------------------------------------------------------------
-- CONSUMER.  A genuine `ConsAdv a b` is class-preserving (pending advances
-- `c01..c23`, received-tail advances `c45..c56`) or the RECEIVE boundary
-- (`c34`, `cp3→cp4`, pending → received).  Only the receive needs the
-- downstream-client witness; only a non-receive keeps the downstream client
-- fixed — same `InCp03 a × ConsRecv b → ⊥` guard pattern as the relay.
------------------------------------------------------------------------

-- the consumer step's kind
data ConsStepKind (a b : ConsPh) : Set where
  cMove : (InCp03 a → InCp03 b) → (ConsRecv a → ConsRecv b) → (InCp03 a × ConsRecv b → ⊥)
        → ConsStepKind a b
  cRecv : InCp03 a → ConsRecv b → ConsStepKind a b

-- classify a genuine consumer single step
consadv-step : ∀ {a b} → ConsAdv a b → ConsStepKind a b
consadv-step c01 = cMove (λ _ → tt) (λ ()) (λ { (_ , ()) })
consadv-step c12 = cMove (λ _ → tt) (λ ()) (λ { (_ , ()) })
consadv-step c23 = cMove (λ _ → tt) (λ ()) (λ { (_ , ()) })
consadv-step c34 = cRecv tt tt
consadv-step c45 = cMove (λ ()) (λ _ → tt) (λ { (() , _) })
consadv-step c56 = cMove (λ ()) (λ _ → tt) (λ { (() , _) })

-- CONSUMER internal move (′): on the TWO non-`recvBFBlock` visible consume moves
-- (`sendBFRequestRange`, `sendBFClientDone`) node D's OWN downstream BF client
-- fires WITH it — so `pipeInv⁺-cons-move`'s downstream-client fixity (`de`) is
-- FALSE.  We take the SUCCESSOR-non-block premise `¬blk′` (`¬ BFcHasBlk
-- (dnClient l s′)`) and discharge the downstream-client coupling clause vacuously;
-- the UPSTREAM client (node B/C) is still fixed (`ue`, node D's fire does not move
-- it).  Built directly on the exposed base core `pipeInv-cons-move`.
pipeInv⁺-cons-move′ : (l : TwoLegs) (s s′ : _)
  → prodOf   l s ≡ prodOf   l s′ → relayOf  l s ≡ relayOf  l s′
  → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
  → upClient l s ≡ upClient l s′
  → (BFcHasBlk (dnClient l s′) → ⊥)
  → (InCp03   (phOf l s) → InCp03   (phOf l s′))
  → (ConsRecv (phOf l s) → ConsRecv (phOf l s′))
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-cons-move′ l s s′ pe re cue cde ue ¬blk′ fI fR (pinv , cu , uc , cd , dc)
  = pipeInv-cons-move l s s′ pe re fI fR pinv
  , transImp CellHasBlk    ProdSent cue pe cu
  , transImp BFcHasBlk ProdSent ue  pe uc
  , transImp CellHasBlk    RelayFwd cde re cd
  , (λ h → ⊥-elim (¬blk′ h))

-- CONSUMER preservation: node D fires on leg `l`; prod / relay / both cells
-- fixed, upstream client (node B/C) fixed.  `¬blk′` = the SUCCESSOR downstream
-- client does NOT hold a block (valid on every visible consume move); `wDn` = the
-- downstream client held the block (demanded only on a receive).
pres-cons : (l : TwoLegs) (s s′ : _)
  → ConsAdv (phOf l s) (phOf l s′)
  → prodOf   l s ≡ prodOf   l s′ → relayOf  l s ≡ relayOf  l s′
  → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
  → upClient l s ≡ upClient l s′
  → (BFcHasBlk (dnClient l s′) → ⊥)
  → (InCp03 (phOf l s) → ConsRecv (phOf l s′) → BFcHasBlk (dnClient l s))
  → PipeInv⁺ l s → PipeInv⁺ l s′
pres-cons l s s′ ca pe re cue cde ue ¬blk′ wDn pinv with consadv-step ca
... | cMove fI fR _ =
      pipeInv⁺-cons-move′ l s s′ pe re cue cde ue ¬blk′ fI fR pinv
... | cRecv hPre hRecv =
      pipeInv⁺-cons-recv l s s′ pe re cue cde ue hPre (wDn hPre hRecv) hRecv pinv
