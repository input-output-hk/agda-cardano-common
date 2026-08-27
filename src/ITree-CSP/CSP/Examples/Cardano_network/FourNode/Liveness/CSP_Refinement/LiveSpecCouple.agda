{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- `LiveSpecCouple` — the SPEC SIDE of the four-node block-liveness failure
-- simulation (design-doc step 3 / Phase-1 Task 4).
--
-- The CSP-refinement statement `LivenessSpec` (`CSP_Refinement.Spec`) is
--   ∀ b → LSpec b true true ⊑FD (breakableSystemOf b ∖ hidden b)
-- and the campaign proves it by a FAILURE SIMULATION (`FSimFromRel`,
-- `Semantics.BisimFromRel`) against the τ-free abstraction `abstractSystem`
-- (`R2_Bisim.AbstractSystem`).  This module supplies the three ingredients the
-- simulation's spec side needs, and NOTHING else:
--
--   1. `SpecPos` / `specPos` / `SpecOf` — the coupling proper: a reading of the
--      Spec's five state flags (`p1 g1 p2 g2` plus "already delivered") off the
--      abstract decode's own components, and the CSP-spec state they denote;
--   2. the FLAG-UPDATE lemmas (`specPos-break`, `specPos-produce₁/₂`,
--      `specPos-recv₁/₂`) — one per KEPT event class, each saying "if the
--      implementation step performed this class's state update, then `specPos`
--      of the target is exactly the update the Spec's own τ-map performs";
--   3. the SPEC-SIDE WEAK TRANSITIONS — for each (spec state class × kept
--      event), the two-step weak move (τ into the branch that owns the event,
--      then the event through that branch's menu) the simulation must return.
--
-- DELIBERATE IMPORT DISCIPLINE.  Only the CHEAP prefix of the R2 development is
-- imported: `SysMedium` / `SysNode` (the decode's component states),
-- `SysDecode` (`SysState`), `SysReach` (`RState`), plus the statement module
-- `CSP_Refinement.Spec`.  NONE of `SysBisim` / `SysOracle*` / `SysIoLink*` /
-- `Walk*` — those are the heavy suffix, and daily iteration on this module must
-- stay in the seconds range.
--
-- WHY THE FLAG LEMMAS TAKE STATE-LEVEL PREMISES.  `R2_Bisim.SysStep` provides
-- only OPERAND-GENERIC step reflections; the CONCRETE dispatcher ("which `s′`
-- does this event land on") is explicitly deferred to the heavy `SysBisim`
-- layer.  So the honest interface here is: the lemmas take, as HYPOTHESES, the
-- component-level state facts that a concrete step inversion yields (a break
-- marks one link broken and touches nothing else; A's kept produce sets that
-- link's produce flag; D's kept receive sets that link's receive flag), and
-- conclude the `specPos` update.  Phase 2's `LiveFSim` — which does have the
-- dispatcher — discharges the hypotheses.
--
-- ALL FIVE FLAGS ARE READABLE off the decode: `p1`/`p2` from node A's two
-- `produce`-driver phases (`ProdPh`, past `pp5` ⇒ the `sendBFBlock` fired),
-- `g1`/`g2` from `MedState`'s per-link `broken` bits, and "delivered" from node
-- D's two `consume`-driver phases together with the block each stored
-- (`ConsDPh`, past `cp3` with `cblk ≡ blkA` ⇒ a kept receive of `blkA` fired).
--
-- No postulates, holes, `--allow-unsolved-metas`, `NON_TERMINATING`, or
-- `mutual` blocks.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveSpecCouple
  (blkA : Block₃) where

import Data.Unit as U
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤ₚ)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Product using (_,_)
open import Level using (0ℓ; Lift; lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using ( PTree; ExtI; AnyTypes; ContinueType; react; fin )
open PTree

------------------------------------------------------------------------
-- The shared alphabet, the four link ids and the block domain.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; linkAB; linkAC; linkBD; linkCD; DecEq-Block₃ )
open import CSP.Examples.Cardano_network.Base using ( hi )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Link; apiBF; break; sendBFBlock; recvBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

------------------------------------------------------------------------
-- THE SPECIFICATION (the statement module) — the states this module couples to.
------------------------------------------------------------------------

-- `prodτ`/`idleτ` are imported for DOCUMENTATION only — the brief fixes them as
-- consumed interface — and appear ZERO times below: `brOf`/`visOf` reach the same
-- τ-maps structurally, by `.force` and pattern matching, never by name.
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.Spec
  using ( SpecProc; SpecMenu; Done; doneMenu; delivMenu
        ; Prod; prodτ; LSpec; idleτ; prodGo; isProd1 )

------------------------------------------------------------------------
-- The R2 abstract decode's component states (the CHEAP prefix only).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( broken )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA
  using ( ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
        ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
        ; ConsDPh; consD
        ; NodeStateA; prod-AB; prod-AC
        ; NodeStateD; cons-BD; cons-CD
        -- the two DRIVER DECODE TABLES themselves: imported so the phase
        -- thresholds `pastSend`/`pastRecv` can be machine-linked to the table
        -- sites that give them meaning (see the threshold-link tests at the end)
        ; decProd; decCons )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med; nA; nD; initial )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; toSys )

------------------------------------------------------------------------
-- The LTS + weak-transition vocabulary at the spec alphabet.
------------------------------------------------------------------------

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Event; evLabel; evl; Label; ev; τ; _─[_]─►_; sVis; sTau )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wev )

------------------------------------------------------------------------
-- STEP 1 — the coupling: `SpecPos`, `specPos`, `SpecOf`.
------------------------------------------------------------------------

-- the Spec's state up to its five flags: idle (`LSpec g1 g2`), produced
-- (`Prod p1 g1 p2 g2`), or discharged (`Done`).  A separate `posDone` rather
-- than a sixth flag, because `Done` carries no flags at all.
data SpecPos : Set where
  posIdle : Bool → Bool → SpecPos              -- g1 g2
  posProd : Bool → Bool → Bool → Bool → SpecPos -- p1 g1 p2 g2
  posDone : SpecPos

-- has this `produce` driver already fired its `apiBF … sendBFBlock`?  `decProd`
-- offers that event at phase `pp5`, so exactly `pp6 … pp9` are past it.
pastSend : ProdPh → Bool
pastSend pp0 = false
pastSend pp1 = false
pastSend pp2 = false
pastSend pp3 = false
pastSend pp4 = false
pastSend pp5 = false
pastSend pp6 = true
pastSend pp7 = true
pastSend pp8 = true
pastSend pp9 = true

-- has this `consume` driver already fired its `apiBF … recvBFBlock`?  `decCons`
-- offers that event at phase `cp3`, so exactly `cp4 … cp6` are past it.
pastRecv : ConsPh → Bool
pastRecv cp0 = false
pastRecv cp1 = false
pastRecv cp2 = false
pastRecv cp3 = false
pastRecv cp4 = true
pastRecv cp5 = true
pastRecv cp6 = true

-- flag `p1`: A produced on link AB (its AB `produce` driver is past its send)
prod1A : NodeStateA → Bool
prod1A na = pastSend (prod-AB na)

-- flag `p2`: A produced on link AC
prod2A : NodeStateA → Bool
prod2A na = pastSend (prod-AC na)

-- flag `g1`: path ABD is whole — neither AB nor BD has broken.  (Task 2's
-- observation: with only four links, `g1 ∧ g2` says no link is broken at all.)
g1F : (Link → Bool) → Bool
g1F brk = not (brk linkAB ∨ brk linkBD)

-- flag `g2`: path ACD is whole — neither AC nor CD has broken
g2F : (Link → Bool) → Bool
g2F brk = not (brk linkAC ∨ brk linkCD)

-- has this node-D `consume` driver already received exactly `blkA`?  The stored
-- block matters: `ConsDPh` carries `blkA` as a PLACEHOLDER before `cp4`, so the
-- phase test comes first and only then the payload test.
recvOf : ConsDPh → Bool
recvOf (consD b ph) = if pastRecv ph then ⌊ b ≟ blkA ⌋ else false

-- "delivered": a kept receive of `blkA` has fired at D, on BD or on CD
delivD : NodeStateD → Bool
delivD nd = recvOf (cons-BD nd) ∨ recvOf (cons-CD nd)

-- assemble the spec position from the five flags.  Delivery WINS (the single
-- localised `Done`-switch clause): `Done` is the `⊑FD`-top and every spec
-- `recvBFBlock` edge leads to it, so the coupling must switch to `posDone` on
-- the first kept receive.  Otherwise a set produce bit means `Prod`, and no
-- produce bit at all means the idle `LSpec`.
mkPos : Bool → Bool → Bool → Bool → Bool → SpecPos
mkPos true  _     _  _     _  = posDone
mkPos false true  g1 p2    g2 = posProd true g1 p2 g2
mkPos false false g1 true  g2 = posProd false g1 true g2
mkPos false false g1 false g2 = posIdle g1 g2

-- the spec position determined by the THREE decode components it reads: the
-- medium's break bits, node A's position, node D's position (the medium cell
-- phases and nodes B/C are deliberately NOT read)
posOf : (Link → Bool) → NodeStateA → NodeStateD → SpecPos
posOf brk na nd = mkPos (delivD nd) (prod1A na) (g1F brk) (prod2A na) (g2F brk)

-- the spec position of a whole-system abstract config
specPosS : SysState → SpecPos
specPosS s = posOf (broken (med s)) (nA s) (nD s)

-- THE COUPLING'S FLAG READER: the spec position of a REACHABLE config
specPos : RState → SpecPos
specPos r = specPosS (toSys r)

-- the CSP-spec process a position denotes
procOf : SpecPos → SpecProc
procOf (posIdle g1 g2)       = LSpec blkA g1 g2
procOf (posProd p1 g1 p2 g2) = Prod blkA p1 g1 p2 g2
procOf posDone               = Done blkA

-- THE COUPLING: the CSP-spec state a reachable config is coupled to
SpecOf : RState → SpecProc
SpecOf r = procOf (specPos r)

-- `SpecOf` at the initial-style all-clear idle position is the statement's LHS
-- `LSpec blkA true true` (the shape the refinement is stated at)
SpecOf-idle : (r : RState) → specPos r ≡ posIdle true true
            → SpecOf r ≡ LSpec blkA true true
SpecOf-idle r eq = cong procOf eq

------------------------------------------------------------------------
-- STEP 2 — the FLAG-UPDATE lemmas, one per kept-event class.
--
-- Shape: "if the implementation step from `r` to `r′` performed this event
-- class's component-level state update, then `specPos r′` is exactly the update
-- the Spec's own τ-map performs on `specPos r`".  The premises are the
-- component facts a concrete step inversion yields; Phase 2's `LiveFSim`
-- discharges them (see this module's header for why they are premises and not
-- derived here).
------------------------------------------------------------------------

-- three-argument congruence (the standard library ships only `cong₂`)
cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x x′ : A} {y y′ : B} {z z′ : C}
      → x ≡ x′ → y ≡ y′ → z ≡ z′ → f x y z ≡ f x′ y′ z′
cong₃ f refl refl refl = refl

-- five-argument congruence for `mkPos` (all five flags may move at once)
mkPos-cong : {dl dl′ p1 p1′ g1 g1′ p2 p2′ g2 g2′ : Bool}
           → dl ≡ dl′ → p1 ≡ p1′ → g1 ≡ g1′ → p2 ≡ p2′ → g2 ≡ g2′
           → mkPos dl p1 g1 p2 g2 ≡ mkPos dl′ p1′ g1′ p2′ g2′
mkPos-cong refl refl refl refl refl = refl

-- `blkA` decides equal to itself.  `blkA` is a MODULE PARAMETER, so `blkA ≟
-- blkA` is a neutral term that blocks every payload-matching reduction; this is
-- the one lemma that unblocks them, and every payload-carrying menu equation
-- below routes through it.
blkA-refl : ⌊ blkA ≟ blkA ⌋ ≡ true
blkA-refl with blkA ≟ blkA
... | yes _  = refl
... | no  ¬q = ⊥-elim (¬q refl)

------------------------------------------------------------------------
-- The Spec's own flag updates, as functions of `SpecPos`.
------------------------------------------------------------------------

-- the Spec's `g1` update on `break l`: path ABD goes down iff `l` is AB or BD
brkG1 : Link → Bool → Bool
brkG1 l g1 = if (⌊ l ≟ linkAB ⌋ ∨ ⌊ l ≟ linkBD ⌋) then false else g1

-- the Spec's `g2` update on `break l`: path ACD goes down iff `l` is AC or CD
brkG2 : Link → Bool → Bool
brkG2 l g2 = if (⌊ l ≟ linkAC ⌋ ∨ ⌊ l ≟ linkCD ⌋) then false else g2

-- the Spec's position update on `break l` (`Done` is a fixpoint: `doneMenu`
-- accepts every kept event back to `Done`)
brkPos : Link → SpecPos → SpecPos
brkPos l (posIdle g1 g2)       = posIdle (brkG1 l g1) (brkG2 l g2)
brkPos l (posProd p1 g1 p2 g2) = posProd p1 (brkG1 l g1) p2 (brkG2 l g2)
brkPos l posDone               = posDone

-- the Spec's position update on A's kept produce on AB (`idleτ` branch 5 enters
-- `Prod` with `p1` set and `p2` still false; `prodτ` branch 5 just sets `p1`)
setP1 : SpecPos → SpecPos
setP1 (posIdle g1 g2)       = posProd true g1 false g2
setP1 (posProd p1 g1 p2 g2) = posProd true g1 p2 g2
setP1 posDone               = posDone

-- the Spec's position update on A's kept produce on AC (the mirror)
setP2 : SpecPos → SpecPos
setP2 (posIdle g1 g2)       = posProd false g1 true g2
setP2 (posProd p1 g1 p2 g2) = posProd p1 g1 true g2
setP2 posDone               = posDone

-- the MEDIUM's break-bit update on a `break l`
brkSet : Link → (Link → Bool) → (Link → Bool)
brkSet l brk l′ = if ⌊ l ≟ l′ ⌋ then true else brk l′

------------------------------------------------------------------------
-- The per-flag computations behind the lemmas.
------------------------------------------------------------------------

-- marking `l` broken clears `g1` exactly when `l` is on path ABD.  The two
-- `with`s are on the OTHER link's bit: for a break on BD (resp. AB) the `∨` in
-- `g1F` is stuck on the sibling bit until it is split.
g1F-brk : (l : Link) (brk : Link → Bool) → g1F (brkSet l brk) ≡ brkG1 l (g1F brk)
g1F-brk fzero                      brk = refl
g1F-brk (fsuc fzero)               brk = refl
g1F-brk (fsuc (fsuc fzero))        brk with brk linkAB
... | true  = refl
... | false = refl
g1F-brk (fsuc (fsuc (fsuc fzero))) brk = refl

-- marking `l` broken clears `g2` exactly when `l` is on path ACD
g2F-brk : (l : Link) (brk : Link → Bool) → g2F (brkSet l brk) ≡ brkG2 l (g2F brk)
g2F-brk fzero                      brk = refl
g2F-brk (fsuc fzero)               brk = refl
g2F-brk (fsuc (fsuc fzero))        brk = refl
g2F-brk (fsuc (fsuc (fsuc fzero))) brk with brk linkAC
... | true  = refl
... | false = refl

-- `mkPos` commutes with the break update: the `g` flags are passed straight
-- through, so only the delivery and produce flags need splitting
mkPos-brk : (l : Link) (dl p1 g1 p2 g2 : Bool)
          → mkPos dl p1 (brkG1 l g1) p2 (brkG2 l g2) ≡ brkPos l (mkPos dl p1 g1 p2 g2)
mkPos-brk l true  _     _  _     _  = refl
mkPos-brk l false true  g1 p2    g2 = refl
mkPos-brk l false false g1 true  g2 = refl
mkPos-brk l false false g1 false g2 = refl

-- `mkPos` commutes with setting `p1`
mkPos-setP1 : (dl p1 g1 p2 g2 : Bool)
            → mkPos dl true g1 p2 g2 ≡ setP1 (mkPos dl p1 g1 p2 g2)
mkPos-setP1 true  _     _  _     _  = refl
mkPos-setP1 false true  g1 p2    g2 = refl
mkPos-setP1 false false g1 true  g2 = refl
mkPos-setP1 false false g1 false g2 = refl

-- `mkPos` commutes with setting `p2`
mkPos-setP2 : (dl p1 g1 p2 g2 : Bool)
            → mkPos dl p1 g1 true g2 ≡ setP2 (mkPos dl p1 g1 p2 g2)
mkPos-setP2 true  _     _  _     _  = refl
mkPos-setP2 false true  g1 p2    g2 = refl
mkPos-setP2 false false g1 true  g2 = refl
mkPos-setP2 false false g1 false g2 = refl

-- a set delivery flag pins the position to `posDone`
mkPos-done : (dl p1 g1 p2 g2 : Bool) → dl ≡ true → mkPos dl p1 g1 p2 g2 ≡ posDone
mkPos-done dl p1 g1 p2 g2 refl = refl

-- `posOf` commutes with the break update (the whole-position version)
posOf-brk : (l : Link) (brk : Link → Bool) (na : NodeStateA) (nd : NodeStateD)
          → posOf (brkSet l brk) na nd ≡ brkPos l (posOf brk na nd)
posOf-brk l brk na nd =
  trans (mkPos-cong refl refl (g1F-brk l brk) refl (g2F-brk l brk))
        (mkPos-brk l (delivD nd) (prod1A na) (g1F brk) (prod2A na) (g2F brk))

------------------------------------------------------------------------
-- Component-level witnesses (so a consumer holding a PHASE equation, which is
-- what step inversion yields, can discharge the lemmas' flag premises).
------------------------------------------------------------------------

-- A's AB driver at `pp6` (the phase right after its `sendBFBlock`) sets `p1`
prod1A-pp6 : (na : NodeStateA) → prod-AB na ≡ pp6 → prod1A na ≡ true
prod1A-pp6 na e = cong pastSend e

-- A's AC driver at `pp6` sets `p2`
prod2A-pp6 : (na : NodeStateA) → prod-AC na ≡ pp6 → prod2A na ≡ true
prod2A-pp6 na e = cong pastSend e

-- a node-D consume driver holding `blkA` past its receive has delivered
recvOf-hit : (ph : ConsPh) → pastRecv ph ≡ true → recvOf (consD blkA ph) ≡ true
recvOf-hit ph e = trans (cong (λ x → if x then ⌊ blkA ≟ blkA ⌋ else false) e) blkA-refl

-- a BD receive makes `delivD` true
delivD-BD : (nd : NodeStateD) → recvOf (cons-BD nd) ≡ true → delivD nd ≡ true
delivD-BD nd e = cong (λ x → x ∨ recvOf (cons-CD nd)) e

-- a CD receive makes `delivD` true (the BD bit must be split: `_∨_` matches on
-- its FIRST argument)
delivD-CD : (nd : NodeStateD) → recvOf (cons-CD nd) ≡ true → delivD nd ≡ true
delivD-CD nd e with recvOf (cons-BD nd)
... | true  = refl
... | false = e

------------------------------------------------------------------------
-- THE FIVE FLAG-UPDATE LEMMAS.
------------------------------------------------------------------------

-- KEPT `break l`: the medium marks `l` broken; nodes A and D are untouched
-- (the medium's cell phases and nodes B/C are not read by `specPos` at all)
specPos-break : (l : Link) (r r′ : RState)
              → broken (med (toSys r′)) ≡ brkSet l (broken (med (toSys r)))
              → nA (toSys r′) ≡ nA (toSys r)
              → nD (toSys r′) ≡ nD (toSys r)
              → specPos r′ ≡ brkPos l (specPos r)
specPos-break l r r′ eb ea ed =
  trans (cong₃ posOf eb ea ed)
        (posOf-brk l (broken (med (toSys r))) (nA (toSys r)) (nD (toSys r)))

-- THE POINTWISE VARIANT of `specPos-break`, for consumers whose break inversion
-- delivers the bit update ONE LINK AT A TIME.  A concrete step inversion names
-- the successor's `broken` map through a DIFFERENT (but pointwise-equal) update
-- function than `brkSet`, and there is no function extensionality in this
-- development, so the whole-map premise above is unreachable for them.  It is
-- not needed either: `posOf` reads `brk` at only the four link keys `linkAB`,
-- `linkBD`, `linkAC`, `linkCD` (through `g1F`/`g2F`), so four instances of the
-- pointwise premise rebuild both `g` flags by `cong₂` and the rest is
-- `posOf-brk` verbatim.
specPos-break′ : (l : Link) (r r′ : RState)
               → ((j : Link) → broken (med (toSys r′)) j
                               ≡ brkSet l (broken (med (toSys r))) j)
               → nA (toSys r′) ≡ nA (toSys r)
               → nD (toSys r′) ≡ nD (toSys r)
               → specPos r′ ≡ brkPos l (specPos r)
specPos-break′ l r r′ eb ea ed =
  trans (mkPos-cong (cong delivD ed) (cong prod1A ea)
           (cong₂ (λ x y → not (x ∨ y)) (eb linkAB) (eb linkBD))
           (cong prod2A ea)
           (cong₂ (λ x y → not (x ∨ y)) (eb linkAC) (eb linkCD)))
        (posOf-brk l (broken (med (toSys r))) (nA (toSys r)) (nD (toSys r)))

-- KEPT `apiBF linkAB hi sendBFBlock ! blkA`: A's AB produce flag goes up; the
-- medium, the AC produce flag and D's delivery flag are untouched
specPos-produce₁ : (r r′ : RState)
                 → broken (med (toSys r′)) ≡ broken (med (toSys r))
                 → prod1A (nA (toSys r′)) ≡ true
                 → prod2A (nA (toSys r′)) ≡ prod2A (nA (toSys r))
                 → delivD (nD (toSys r′)) ≡ delivD (nD (toSys r))
                 → specPos r′ ≡ setP1 (specPos r)
specPos-produce₁ r r′ eb e1 e2 ed =
  trans (mkPos-cong ed e1 (cong g1F eb) e2 (cong g2F eb))
        (mkPos-setP1 (delivD (nD (toSys r))) (prod1A (nA (toSys r)))
                     (g1F (broken (med (toSys r)))) (prod2A (nA (toSys r)))
                     (g2F (broken (med (toSys r)))))

-- KEPT `apiBF linkAC hi sendBFBlock ! blkA`: the AC mirror
specPos-produce₂ : (r r′ : RState)
                 → broken (med (toSys r′)) ≡ broken (med (toSys r))
                 → prod1A (nA (toSys r′)) ≡ prod1A (nA (toSys r))
                 → prod2A (nA (toSys r′)) ≡ true
                 → delivD (nD (toSys r′)) ≡ delivD (nD (toSys r))
                 → specPos r′ ≡ setP2 (specPos r)
specPos-produce₂ r r′ eb e1 e2 ed =
  trans (mkPos-cong ed e1 (cong g1F eb) e2 (cong g2F eb))
        (mkPos-setP2 (delivD (nD (toSys r))) (prod1A (nA (toSys r)))
                     (g1F (broken (med (toSys r)))) (prod2A (nA (toSys r)))
                     (g2F (broken (med (toSys r)))))

-- KEPT `apiBF linkBD hi recvBFBlock ! blkA`: the obligation is discharged, so
-- the coupling switches to `posDone` — the single localised `Done`-switch
-- (`Done` is the `⊑FD`-top and every spec receive edge leads there)
specPos-recv₁ : (r r′ : RState)
              → recvOf (cons-BD (nD (toSys r′))) ≡ true
              → specPos r′ ≡ posDone
specPos-recv₁ r r′ e = mkPos-done _ _ _ _ _ (delivD-BD (nD (toSys r′)) e)

-- KEPT `apiBF linkCD hi recvBFBlock ! blkA`: the CD mirror
specPos-recv₂ : (r r′ : RState)
              → recvOf (cons-CD (nD (toSys r′))) ≡ true
              → specPos r′ ≡ posDone
specPos-recv₂ r r′ e = mkPos-done _ _ _ _ _ (delivD-CD (nD (toSys r′)) e)

------------------------------------------------------------------------
-- STEP 3 — the SPEC-SIDE WEAK TRANSITIONS.
--
-- Every spec state is a PURE internal choice (`react ∅v τmap`) over eight
-- τ-branches, each of whose successors is a STABLE `react … ∅t` node.  So every
-- spec-side visible move is exactly two steps: one τ into the branch that owns
-- the event, then the event through that branch's menu.  The branch layout is
-- the one the coverage tests of `Spec.lagda.md:492-604` pin:
--
--   `idleτ`: 0 = Stop; 1-4 = break AB / BD / AC / CD; 5-6 = produce AB / AC.
--   `prodτ`: 0 = the bare (flag-gated) delivery — the MUST-offer; 1-4 = the
--            delivery + one break each (AB / BD / AC / CD); 5-6 = the delivery
--            + one repeat-produce each (AB / AC); 7 = the may-deliver branch,
--            offering BOTH receives unconditionally.
--   `Done` : 0 = Stop; 1 = the menu accepting every kept event back to `Done`.
------------------------------------------------------------------------

-- the τ-branch index of an 8-way internal choice (`ExtI`'s witness-free `fin`)
fin8 : AnyTypes (ExtI (Net_Api Payload))
fin8 = (Lift 0ℓ (Fin 8) , fin)

-- the eight branch selectors, named (see the layout comment above)
ix0 ix1 ix2 ix3 ix4 ix5 ix6 ix7 : Fin 8
ix0 = fzero
ix1 = fsuc fzero
ix2 = fsuc (fsuc fzero)
ix3 = fsuc (fsuc (fsuc fzero))
ix4 = fsuc (fsuc (fsuc (fsuc fzero)))
ix5 = fsuc (fsuc (fsuc (fsuc (fsuc fzero))))
ix6 = fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
ix7 = fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))

-- the visible-offer map of a spec process (everywhere-`nothing` off a `react`).
-- This is what lets a branch menu written as an INLINE extended lambda in
-- `prodτ`/`idleτ` be NAMED here: `visOf (brOf P k)` reduces to that very
-- lambda, so its equations become statable (an extended lambda cannot be
-- referred to directly, and two textually identical ones are not the same term).
-- the same, at an ARBITRARY return type: the threshold-link tests below probe
-- `decCons`, which returns `Block₃` rather than unit
visG : ∀ {ℓr} {R : Set ℓr}
     → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R
     → (at : AnyTypes (Net_Api Payload))
     → ContinueType at (Maybe (PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R))
visG P with force P
... | react v _ = v
... | _         = λ _ _ → nothing

visOf : SpecProc → SpecMenu
visOf P = visG P

-- the τ-branch map of a spec process (everywhere-`nothing` off a `react`)
tauOf : SpecProc → (i : AnyTypes (ExtI (Net_Api Payload)))
      → ContinueType i (Maybe SpecProc)
tauOf P with force P
... | react _ τc = τc
... | _          = λ _ _ → nothing

-- the successor along τ-branch `k` (`Done blkA` if that branch is absent —
-- never the case at any index used below)
brOf : SpecProc → Fin 8 → SpecProc
brOf P k = fromMaybe (Done blkA) (tauOf P fin8 (lift k))

------------------------------------------------------------------------
-- The three kept event labels.
------------------------------------------------------------------------

-- the label of a kept `break l`
evBrk : Link → Label (⊤ₚ {0ℓ})
evBrk l = ev (evl (evLabel U.⊤ (break l) U.tt))

-- the label of A's kept produce of `blkA` on link `l`
evPrd : Link → Label (⊤ₚ {0ℓ})
evPrd l = ev (evl (evLabel Block₃ (apiBF l hi sendBFBlock) blkA))

-- the label of D's kept receive of `blkA` on link `l`
evRcv : Link → Label (⊤ₚ {0ℓ})
evRcv l = ev (evl (evLabel Block₃ (apiBF l hi recvBFBlock) blkA))

------------------------------------------------------------------------
-- Menu computations (all payload-carrying ones route through `blkA-refl`).
------------------------------------------------------------------------

-- the produce dispatch fires on A's send of `blkA` on AB (`isProd1` matches the
-- link, the direction and the payload)
prodGo-AB : (q1 q2 q3 q4 : Bool)
          → prodGo blkA q1 q2 q3 q4
              (isProd1 linkAB blkA (Block₃ , apiBF linkAB hi sendBFBlock) blkA)
            ≡ just (Prod blkA q1 q2 q3 q4)
prodGo-AB q1 q2 q3 q4 with blkA ≟ blkA
... | yes _  = refl
... | no  ¬q = ⊥-elim (¬q refl)

-- the produce dispatch fires on A's send of `blkA` on AC
prodGo-AC : (q1 q2 q3 q4 : Bool)
          → prodGo blkA q1 q2 q3 q4
              (isProd1 linkAC blkA (Block₃ , apiBF linkAC hi sendBFBlock) blkA)
            ≡ just (Prod blkA q1 q2 q3 q4)
prodGo-AC q1 q2 q3 q4 with blkA ≟ blkA
... | yes _  = refl
... | no  ¬q = ⊥-elim (¬q refl)

-- the DELIVERY menu never fires on a `break` (both its offers are on `apiBF`
-- receive channels).  Nine clauses: `_∧_` matches on its first argument, so each
-- produce bit must be split, and each path bit only when its produce bit is set.
delivMenu-brk : (p1 g1 p2 g2 : Bool) (l : Link)
              → delivMenu blkA p1 g1 p2 g2 (U.⊤ , break l) U.tt ≡ nothing
delivMenu-brk false g1    false g2    l = refl
delivMenu-brk false g1    true  false l = refl
delivMenu-brk false g1    true  true  l = refl
delivMenu-brk true  false false g2    l = refl
delivMenu-brk true  false true  false l = refl
delivMenu-brk true  false true  true  l = refl
delivMenu-brk true  true  false g2    l = refl
delivMenu-brk true  true  true  false l = refl
delivMenu-brk true  true  true  true  l = refl

-- the delivery menu never fires on A's produce on AB (wrong link AND wrong tag)
delivMenu-prdAB : (p1 g1 p2 g2 : Bool)
                → delivMenu blkA p1 g1 p2 g2
                    (Block₃ , apiBF linkAB hi sendBFBlock) blkA ≡ nothing
delivMenu-prdAB false g1    false g2    = refl
delivMenu-prdAB false g1    true  false = refl
delivMenu-prdAB false g1    true  true  = refl
delivMenu-prdAB true  false false g2    = refl
delivMenu-prdAB true  false true  false = refl
delivMenu-prdAB true  false true  true  = refl
delivMenu-prdAB true  true  false g2    = refl
delivMenu-prdAB true  true  true  false = refl
delivMenu-prdAB true  true  true  true  = refl

-- the delivery menu never fires on A's produce on AC
delivMenu-prdAC : (p1 g1 p2 g2 : Bool)
                → delivMenu blkA p1 g1 p2 g2
                    (Block₃ , apiBF linkAC hi sendBFBlock) blkA ≡ nothing
delivMenu-prdAC false g1    false g2    = refl
delivMenu-prdAC false g1    true  false = refl
delivMenu-prdAC false g1    true  true  = refl
delivMenu-prdAC true  false false g2    = refl
delivMenu-prdAC true  false true  false = refl
delivMenu-prdAC true  false true  true  = refl
delivMenu-prdAC true  true  false g2    = refl
delivMenu-prdAC true  true  true  false = refl
delivMenu-prdAC true  true  true  true  = refl

-- the BD delivery offer FIRES when `p1 ∧ g1` (it is the first `⊕v` component,
-- so the CD guard is never even looked at)
delivMenu-rcvBD : (p2 g2 : Bool)
                → delivMenu blkA true true p2 g2
                    (Block₃ , apiBF linkBD hi recvBFBlock) blkA ≡ just (Done blkA)
delivMenu-rcvBD p2 g2 with blkA ≟ blkA
... | yes _  = refl
... | no  ¬q = ⊥-elim (¬q refl)

-- the CD delivery offer FIRES when `p2 ∧ g2`; the BD offer must first MISS, so
-- its guard is split (three clauses, `_∧_` again matching on `p1`)
delivMenu-rcvCD : (p1 g1 : Bool)
                → delivMenu blkA p1 g1 true true
                    (Block₃ , apiBF linkCD hi recvBFBlock) blkA ≡ just (Done blkA)
delivMenu-rcvCD false g1   with blkA ≟ blkA
... | yes _  = refl
... | no  ¬q = ⊥-elim (¬q refl)
delivMenu-rcvCD true  false with blkA ≟ blkA
... | yes _  = refl
... | no  ¬q = ⊥-elim (¬q refl)
delivMenu-rcvCD true  true  with blkA ≟ blkA
... | yes _  = refl
... | no  ¬q = ⊥-elim (¬q refl)

-- `doneMenu` accepts every `break` back to `Done` (`keptB` keeps every break
-- with no payload test at all)
doneMenu-brk : (l : Link) → doneMenu blkA (U.⊤ , break l) U.tt ≡ just (Done blkA)
doneMenu-brk l = refl

-- `doneMenu` accepts A's kept produce on AB back to `Done`
doneMenu-prdAB : doneMenu blkA (Block₃ , apiBF linkAB hi sendBFBlock) blkA
               ≡ just (Done blkA)
doneMenu-prdAB with blkA ≟ blkA
... | yes _  = refl
... | no  ¬q = ⊥-elim (¬q refl)

-- `doneMenu` accepts A's kept produce on AC back to `Done`
doneMenu-prdAC : doneMenu blkA (Block₃ , apiBF linkAC hi sendBFBlock) blkA
               ≡ just (Done blkA)
doneMenu-prdAC with blkA ≟ blkA
... | yes _  = refl
... | no  ¬q = ⊥-elim (¬q refl)

-- `doneMenu` accepts D's kept receive on BD back to `Done`
doneMenu-rcvBD : doneMenu blkA (Block₃ , apiBF linkBD hi recvBFBlock) blkA
               ≡ just (Done blkA)
doneMenu-rcvBD with blkA ≟ blkA
... | yes _  = refl
... | no  ¬q = ⊥-elim (¬q refl)

-- `doneMenu` accepts D's kept receive on CD back to `Done`
doneMenu-rcvCD : doneMenu blkA (Block₃ , apiBF linkCD hi recvBFBlock) blkA
               ≡ just (Done blkA)
doneMenu-rcvCD with blkA ≟ blkA
... | yes _  = refl
... | no  ¬q = ⊥-elim (¬q refl)

------------------------------------------------------------------------
-- The `prodτ` branch menus (branches 1-6), reached through `visOf`/`brOf`.
-- Each rewrites its `delivMenu` first-match away, then dispatches the one
-- break/produce that branch owns.
------------------------------------------------------------------------

-- branch 1: `break linkAB` downs path ABD
prodBr1 : (p1 g1 p2 g2 : Bool)
        → visOf (brOf (Prod blkA p1 g1 p2 g2) ix1) (U.⊤ , break linkAB) U.tt
          ≡ just (Prod blkA p1 false p2 g2)
prodBr1 p1 g1 p2 g2 rewrite delivMenu-brk p1 g1 p2 g2 linkAB = refl

-- branch 2: `break linkBD` also downs path ABD (BD is its exit link)
prodBr2 : (p1 g1 p2 g2 : Bool)
        → visOf (brOf (Prod blkA p1 g1 p2 g2) ix2) (U.⊤ , break linkBD) U.tt
          ≡ just (Prod blkA p1 false p2 g2)
prodBr2 p1 g1 p2 g2 rewrite delivMenu-brk p1 g1 p2 g2 linkBD = refl

-- branch 3: `break linkAC` downs path ACD
prodBr3 : (p1 g1 p2 g2 : Bool)
        → visOf (brOf (Prod blkA p1 g1 p2 g2) ix3) (U.⊤ , break linkAC) U.tt
          ≡ just (Prod blkA p1 g1 p2 false)
prodBr3 p1 g1 p2 g2 rewrite delivMenu-brk p1 g1 p2 g2 linkAC = refl

-- branch 4: `break linkCD` also downs path ACD
prodBr4 : (p1 g1 p2 g2 : Bool)
        → visOf (brOf (Prod blkA p1 g1 p2 g2) ix4) (U.⊤ , break linkCD) U.tt
          ≡ just (Prod blkA p1 g1 p2 false)
prodBr4 p1 g1 p2 g2 rewrite delivMenu-brk p1 g1 p2 g2 linkCD = refl

-- branch 5: A's repeat-produce on AB SETS `p1`
prodBr5 : (p1 g1 p2 g2 : Bool)
        → visOf (brOf (Prod blkA p1 g1 p2 g2) ix5)
            (Block₃ , apiBF linkAB hi sendBFBlock) blkA
          ≡ just (Prod blkA true g1 p2 g2)
prodBr5 p1 g1 p2 g2 rewrite delivMenu-prdAB p1 g1 p2 g2 = prodGo-AB true g1 p2 g2

-- branch 6: A's repeat-produce on AC SETS `p2`
prodBr6 : (p1 g1 p2 g2 : Bool)
        → visOf (brOf (Prod blkA p1 g1 p2 g2) ix6)
            (Block₃ , apiBF linkAC hi sendBFBlock) blkA
          ≡ just (Prod blkA p1 g1 true g2)
prodBr6 p1 g1 p2 g2 rewrite delivMenu-prdAC p1 g1 p2 g2 = prodGo-AC p1 g1 true g2

------------------------------------------------------------------------
-- The `idleτ` branch menus (branches 1-6).  `LSpec` carries no obligation, so
-- these menus are the bare break/produce dispatch — no `delivMenu` to clear.
------------------------------------------------------------------------

-- branch 5: A's produce on AB enters `Prod` with `p1` set and `p2` STILL FALSE
idleBr5 : (g1 g2 : Bool)
        → visOf (brOf (LSpec blkA g1 g2) ix5)
            (Block₃ , apiBF linkAB hi sendBFBlock) blkA
          ≡ just (Prod blkA true g1 false g2)
idleBr5 g1 g2 = prodGo-AB true g1 false g2

-- branch 6: A's produce on AC enters `Prod` with `p2` set and `p1` still false
idleBr6 : (g1 g2 : Bool)
        → visOf (brOf (LSpec blkA g1 g2) ix6)
            (Block₃ , apiBF linkAC hi sendBFBlock) blkA
          ≡ just (Prod blkA false g1 true g2)
idleBr6 g1 g2 = prodGo-AC false g1 true g2

------------------------------------------------------------------------
-- THE SPEC-SIDE WEAK TRANSITIONS — one per (spec state class × kept event).
------------------------------------------------------------------------

-- IDLE + `break l`: the path flags are updated, the state stays idle
spec-ev-break : (l : Link) (g1 g2 : Bool)
              → LSpec blkA g1 g2 ═[ evBrk l ]═► LSpec blkA (brkG1 l g1) (brkG2 l g2)
spec-ev-break fzero g1 g2 =
  wev (τ*-step (sTau {i = fin8} {a = lift ix1} refl refl) τ*-refl) (sVis refl refl) τ*-refl
spec-ev-break (fsuc fzero) g1 g2 =
  wev (τ*-step (sTau {i = fin8} {a = lift ix3} refl refl) τ*-refl) (sVis refl refl) τ*-refl
spec-ev-break (fsuc (fsuc fzero)) g1 g2 =
  wev (τ*-step (sTau {i = fin8} {a = lift ix2} refl refl) τ*-refl) (sVis refl refl) τ*-refl
spec-ev-break (fsuc (fsuc (fsuc fzero))) g1 g2 =
  wev (τ*-step (sTau {i = fin8} {a = lift ix4} refl refl) τ*-refl) (sVis refl refl) τ*-refl

-- PRODUCED + `break l`: same path-flag update, the produce bits are monotone
spec-ev-break-prod : (l : Link) (p1 g1 p2 g2 : Bool)
                   → Prod blkA p1 g1 p2 g2
                     ═[ evBrk l ]═► Prod blkA p1 (brkG1 l g1) p2 (brkG2 l g2)
spec-ev-break-prod fzero p1 g1 p2 g2 =
  wev (τ*-step (sTau {i = fin8} {a = lift ix1} refl refl) τ*-refl)
      (sVis refl (prodBr1 p1 g1 p2 g2)) τ*-refl
spec-ev-break-prod (fsuc fzero) p1 g1 p2 g2 =
  wev (τ*-step (sTau {i = fin8} {a = lift ix3} refl refl) τ*-refl)
      (sVis refl (prodBr3 p1 g1 p2 g2)) τ*-refl
spec-ev-break-prod (fsuc (fsuc fzero)) p1 g1 p2 g2 =
  wev (τ*-step (sTau {i = fin8} {a = lift ix2} refl refl) τ*-refl)
      (sVis refl (prodBr2 p1 g1 p2 g2)) τ*-refl
spec-ev-break-prod (fsuc (fsuc (fsuc fzero))) p1 g1 p2 g2 =
  wev (τ*-step (sTau {i = fin8} {a = lift ix4} refl refl) τ*-refl)
      (sVis refl (prodBr4 p1 g1 p2 g2)) τ*-refl

-- DISCHARGED + `break l`: the `Done` self-loop
spec-ev-break-done : (l : Link) → Done blkA ═[ evBrk l ]═► Done blkA
spec-ev-break-done l =
  wev (τ*-step (sTau {i = fin8} {a = lift ix1} refl refl) τ*-refl)
      (sVis refl (doneMenu-brk l)) τ*-refl

-- IDLE + A's produce on AB: enter `Prod` with `p1` set only
spec-ev-produce₁ : (g1 g2 : Bool)
                 → LSpec blkA g1 g2 ═[ evPrd linkAB ]═► Prod blkA true g1 false g2
spec-ev-produce₁ g1 g2 =
  wev (τ*-step (sTau {i = fin8} {a = lift ix5} refl refl) τ*-refl)
      (sVis refl (idleBr5 g1 g2)) τ*-refl

-- IDLE + A's produce on AC: enter `Prod` with `p2` set only
spec-ev-produce₂ : (g1 g2 : Bool)
                 → LSpec blkA g1 g2 ═[ evPrd linkAC ]═► Prod blkA false g1 true g2
spec-ev-produce₂ g1 g2 =
  wev (τ*-step (sTau {i = fin8} {a = lift ix6} refl refl) τ*-refl)
      (sVis refl (idleBr6 g1 g2)) τ*-refl

-- PRODUCED + A's produce on AB: set `p1` (this is what raises the ABD
-- obligation when A produced on AC first)
spec-ev-produce₁-prod : (p1 g1 p2 g2 : Bool)
                      → Prod blkA p1 g1 p2 g2 ═[ evPrd linkAB ]═► Prod blkA true g1 p2 g2
spec-ev-produce₁-prod p1 g1 p2 g2 =
  wev (τ*-step (sTau {i = fin8} {a = lift ix5} refl refl) τ*-refl)
      (sVis refl (prodBr5 p1 g1 p2 g2)) τ*-refl

-- PRODUCED + A's produce on AC: set `p2`
spec-ev-produce₂-prod : (p1 g1 p2 g2 : Bool)
                      → Prod blkA p1 g1 p2 g2 ═[ evPrd linkAC ]═► Prod blkA p1 g1 true g2
spec-ev-produce₂-prod p1 g1 p2 g2 =
  wev (τ*-step (sTau {i = fin8} {a = lift ix6} refl refl) τ*-refl)
      (sVis refl (prodBr6 p1 g1 p2 g2)) τ*-refl

-- DISCHARGED + A's produce on AB / AC: the `Done` self-loops
spec-ev-produce₁-done : Done blkA ═[ evPrd linkAB ]═► Done blkA
spec-ev-produce₁-done =
  wev (τ*-step (sTau {i = fin8} {a = lift ix1} refl refl) τ*-refl)
      (sVis refl doneMenu-prdAB) τ*-refl

spec-ev-produce₂-done : Done blkA ═[ evPrd linkAC ]═► Done blkA
spec-ev-produce₂-done =
  wev (τ*-step (sTau {i = fin8} {a = lift ix1} refl refl) τ*-refl)
      (sVis refl doneMenu-prdAC) τ*-refl

-- PRODUCED + D's receive on BD, OBLIGATED (`prodτ` branch 0, the must-offer):
-- available exactly because `p1 ∧ g1` — A produced on AB and path ABD is whole
spec-ev-recv₁-obl : (p2 g2 : Bool)
                  → Prod blkA true true p2 g2 ═[ evRcv linkBD ]═► Done blkA
spec-ev-recv₁-obl p2 g2 =
  wev (τ*-step (sTau {i = fin8} {a = lift ix0} refl refl) τ*-refl)
      (sVis refl (delivMenu-rcvBD p2 g2)) τ*-refl

-- PRODUCED + D's receive on CD, OBLIGATED (`p2 ∧ g2`)
spec-ev-recv₂-obl : (p1 g1 : Bool)
                  → Prod blkA p1 g1 true true ═[ evRcv linkCD ]═► Done blkA
spec-ev-recv₂-obl p1 g1 =
  wev (τ*-step (sTau {i = fin8} {a = lift ix0} refl refl) τ*-refl)
      (sVis refl (delivMenu-rcvCD p1 g1)) τ*-refl

-- PRODUCED + D's receive on BD, UNOBLIGATED (`prodτ` branch 7, the may-deliver
-- branch): legal at ANY flags — the block may have crossed a since-broken link
-- before it broke, a fact hidden from the Spec
spec-ev-recv₁-may : (p1 g1 p2 g2 : Bool)
                  → Prod blkA p1 g1 p2 g2 ═[ evRcv linkBD ]═► Done blkA
spec-ev-recv₁-may p1 g1 p2 g2 =
  wev (τ*-step (sTau {i = fin8} {a = lift ix7} refl refl) τ*-refl)
      (sVis refl (delivMenu-rcvBD true true)) τ*-refl

-- PRODUCED + D's receive on CD, UNOBLIGATED (branch 7)
spec-ev-recv₂-may : (p1 g1 p2 g2 : Bool)
                  → Prod blkA p1 g1 p2 g2 ═[ evRcv linkCD ]═► Done blkA
spec-ev-recv₂-may p1 g1 p2 g2 =
  wev (τ*-step (sTau {i = fin8} {a = lift ix7} refl refl) τ*-refl)
      (sVis refl (delivMenu-rcvCD true true)) τ*-refl

-- DISCHARGED + D's receive on BD / CD: the `Done` self-loops
spec-ev-recv₁-done : Done blkA ═[ evRcv linkBD ]═► Done blkA
spec-ev-recv₁-done =
  wev (τ*-step (sTau {i = fin8} {a = lift ix1} refl refl) τ*-refl)
      (sVis refl doneMenu-rcvBD) τ*-refl

spec-ev-recv₂-done : Done blkA ═[ evRcv linkCD ]═► Done blkA
spec-ev-recv₂-done =
  wev (τ*-step (sTau {i = fin8} {a = lift ix1} refl refl) τ*-refl)
      (sVis refl doneMenu-rcvCD) τ*-refl

------------------------------------------------------------------------
-- SANITY TESTS.  Each is falsifiable: a swapped `g1`/`g2`, a wrong `ProdPh`
-- threshold, a `p1`/`p2` swap in `setP1`/`setP2`, or a `posIdle`/`posProd`
-- confusion in `mkPos` fails one of them.
------------------------------------------------------------------------

-- the REAL initial config is idle with both paths whole: every one of the five
-- readers computes at `SysDecode.initial` (all-`empty`/unbroken medium, both
-- produce drivers at `pp0`, both node-D consume drivers at `cp0`)
_ : specPosS initial ≡ posIdle true true
_ = refl

-- the produce threshold is the `sendBFBlock` step: `pp5` (still offering it) is
-- NOT past it, `pp6` (right after) is
_ : pastSend pp5 ≡ false
_ = refl
_ : pastSend pp6 ≡ true
_ = refl

-- the receive threshold is the `recvBFBlock` step: `cp3` offers it, `cp4` is past
_ : pastRecv cp3 ≡ false
_ = refl
_ : pastRecv cp4 ≡ true
_ = refl

------------------------------------------------------------------------
-- THRESHOLD LINKS.  The four tests above pin `pastSend`/`pastRecv` only against
-- THEMSELVES: nothing in them refers to the decode tables that give `pp5`/`pp6`
-- and `cp3`/`cp4` their meaning, so an edit to `decProd`/`decCons` could move an
-- offer position and leave `specPos` silently wrong with every test still green.
--
-- The four tests below close that gap: they probe the REAL tables
-- (`SysNode.decProd:799-830`, `SysNode.decCons:933-958`), asserting that the
-- kept event is OFFERED at the phase `pastSend`/`pastRecv` calls "not yet" and
-- is GONE at the phase they call "already", and — stronger — that its
-- continuation is exactly the next phase's table entry.  If either chain ever
-- moves, THIS MODULE goes red.
------------------------------------------------------------------------

-- `decProd` offers `sendBFBlock ! blkA` at `pp5`, continuing at exactly `pp6`
prodOffer-pp5 : visG (decProd linkAB hi blkA pp5)
                  (Block₃ , apiBF linkAB hi sendBFBlock) blkA
              ≡ just (decProd linkAB hi blkA pp6)
prodOffer-pp5 with blkA ≟ blkA
... | yes _  = refl
... | no  ¬q = ⊥-elim (¬q refl)

-- ... and at `pp6` the send is no longer offered at all — so `pp6` really is the
-- first phase for which `pastSend` may answer `true`
_ : visG (decProd linkAB hi blkA pp6) (Block₃ , apiBF linkAB hi sendBFBlock) blkA
    ≡ nothing
_ = refl

-- `decCons` offers `recvBFBlock` at `cp3`, and receiving `blkA` continues at
-- exactly `cp4` WITH `blkA` STORED — which is precisely the pair of facts
-- `recvOf` reads (the phase test AND the stored-block test)
consOffer-cp3 : visG (decCons linkBD hi blkA cp3)
                  (Block₃ , apiBF linkBD hi recvBFBlock) blkA
              ≡ just (decCons linkBD hi blkA cp4)
consOffer-cp3 = refl

-- ... and at `cp4` the receive is no longer offered
_ : visG (decCons linkBD hi blkA cp4) (Block₃ , apiBF linkBD hi recvBFBlock) blkA
    ≡ nothing
_ = refl

-- THE SOUNDNESS LINK, over EVERY phase rather than just the boundary: wherever
-- `pastSend` answers `true`, the `sendBFBlock` offer is GONE from `decProd`.  So
-- flag `p1` can never mean "A's send is still pending" — and since `decProd` is a
-- straight, non-looping chain, the only way past that offer is to have fired it.
-- This is the property `specPos` actually depends on, and it is checked against
-- the real table at all ten phases.
pastSend-gone : (ph : ProdPh) → pastSend ph ≡ true
              → visG (decProd linkAB hi blkA ph)
                  (Block₃ , apiBF linkAB hi sendBFBlock) blkA ≡ nothing
pastSend-gone pp0 ()
pastSend-gone pp1 ()
pastSend-gone pp2 ()
pastSend-gone pp3 ()
pastSend-gone pp4 ()
pastSend-gone pp5 ()
pastSend-gone pp6 refl = refl
pastSend-gone pp7 refl = refl
pastSend-gone pp8 refl = refl
pastSend-gone pp9 refl = refl

-- the mirror for `pastRecv` against `decCons`, over all seven phases
pastRecv-gone : (ph : ConsPh) → pastRecv ph ≡ true
              → visG (decCons linkBD hi blkA ph)
                  (Block₃ , apiBF linkBD hi recvBFBlock) blkA ≡ nothing
pastRecv-gone cp0 ()
pastRecv-gone cp1 ()
pastRecv-gone cp2 ()
pastRecv-gone cp3 ()
pastRecv-gone cp4 refl = refl
pastRecv-gone cp5 refl = refl
pastRecv-gone cp6 refl = refl

-- breaking BD downs path ABD only; breaking AC downs path ACD only (swap-catchers)
_ : g1F (brkSet linkBD (λ _ → false)) ≡ false
_ = refl
_ : g2F (brkSet linkBD (λ _ → false)) ≡ true
_ = refl
_ : g1F (brkSet linkAC (λ _ → false)) ≡ true
_ = refl
_ : g2F (brkSet linkAC (λ _ → false)) ≡ false
_ = refl

-- `brkPos` clears exactly one path flag and touches no produce bit
_ : brkPos linkAB (posProd true true true true) ≡ posProd true false true true
_ = refl
_ : brkPos linkCD (posProd true true true true) ≡ posProd true true true false
_ = refl
_ : brkPos linkAB posDone ≡ posDone
_ = refl

-- a produce out of idle sets exactly ONE produce bit (the heart of the Spec's
-- FIX 1: `⟨send@AB⟩` must not obligate D's receive on CD)
_ : setP1 (posIdle true true) ≡ posProd true true false true
_ = refl
_ : setP2 (posIdle true true) ≡ posProd false true true true
_ = refl

-- a delivery is absorbing: `Done` is the `⊑FD`-top
_ : setP1 posDone ≡ posDone
_ = refl
_ : mkPos true false true false true ≡ posDone
_ = refl

-- `procOf` realises the coupling's three cases at the Spec's own processes
_ : procOf (posIdle true true) ≡ LSpec blkA true true
_ = refl
_ : procOf (posProd true false true false) ≡ Prod blkA true false true false
_ = refl
_ : procOf posDone ≡ Done blkA
_ = refl
