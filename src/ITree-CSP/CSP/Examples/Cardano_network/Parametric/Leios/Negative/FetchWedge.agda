{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — NEGATIVE FACT 2: THE POINTER-DRIVEN FETCH
-- WEDGE (the spec's correction C2).
--
-- A fetch thread driven by the EB-STORE POINTER asks its neighbour for the
-- k-th announced point whether or not the neighbour holds that body.  With
-- one outstanding LeiosFetch request per endpoint, the neighbour's LF
-- server then sits at `stGetBody h` for a body it does not hold — and the
-- body store offers nothing on that channel.  Both are in `storeES`, so
-- the pair has NO transition whatsoever: `wedge-stuck` below.
--
-- Re-pointed to the leios-prototype peers (`apiLP`) on branch
-- `examples/leios_prototype_protocols`; the wedge is a property of the
-- POINTER-DRIVEN fetch design and is equally true of the old `apiLF` pair,
-- which is why correction C2 survives the protocol change.
--
-- THAT IS WHY `MsgLNPBlockOffer` EXISTS, and why `NodeLogicL` fetches only
-- what a neighbour has OFFERED (`bodyOfferLoop` offers a body only once the
-- node holds it, so `ebServeLoop`'s `stGetBody h` never blocks) — DESIGN
-- RATIONALE, not proved here; no positive counterpart is built in this
-- module, and this paragraph must not be quoted as a result.
--
-- LEVEL: a PAIR plus ONE STEP.  The wedged process is the UNCHANGED
-- `NodeLogicL.ebServeLoop` thread of node 0's only endpoint, ONE visible
-- step after it has received `lfpReqBlockRequest ! qBad` (the report a
-- pointer-driven fetch at the far end would produce), synchronised on
-- `storeES` with `NodeLogicL.bodyStore` holding NO body of hash `hBad`.
-- This is NOT a `systemOf` fact and NOT a statement "on a three-node line":
-- the spec's §5.4.2 asks for the wedge at system level and that is NOT
-- established here (the plan's Open Question 5).  Nothing below is a claim
-- about `leiosSystemL`.
--
-- NOTE ON THE HIDE.  No hiding operator appears here.  The wedge is the
-- ABSENCE of every transition, visible and silent alike, so hiding any
-- alphabet cannot create one; the brief's hide would only weaken the
-- statement.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.Leios.Negative.FetchWedge where

open import Level using (0ℓ; lift)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
import Data.Unit as U
open import Function.Base using (case_of_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (refl)

open import Process_Trees using (ExtI; base; pair; fin)
open import CSP.Examples.Cardano_network.Parametric.Leios.LeiosInstanceL
  using (leiosLParams; leiosLP; leiosLLine)
open import CSP.Examples.Cardano_network.Base using (lo; hi)
open import CSP.Examples.Cardano_network.Net leiosLParams
  using (Net_Api; Net_Api-≟; apiLP; lfpReqBlockRequest)
open import CSP.Examples.Cardano_network.Data leiosLParams using (Payload)
open import CSP.Examples.Cardano_network.ApiAlphabet leiosLParams using (apiES)
open import CSP.Examples.Cardano_network.Parametric.Node leiosLParams leiosLLine apiES
  using (Proc)
open import CSP.Examples.Cardano_network.Params using (Params)
open Params leiosLParams using (EB; EBHash; LSlot)

import CSP.Examples.Cardano_network.Parametric.NodeLogic as NL
open NL.Generic leiosLParams leiosLLine apiES using (storeES)
import CSP.Examples.Cardano_network.Parametric.Leios.NodeLogicL as NLL
open NLL.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using (getBodyEv; putBodyEv; bodyStore; ebServeLoop)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (EventSet; _∥⇘_⇙_)

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_─[_]─►_; Label; Event√; ev; τ; evl; evLabel; sVis; sSil; sTau)
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload})
  using (Par-soloL)
open import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload})
  using (Par-τ-elim; τL; τR; Par-ev-elim; evSync; evL; evR; evBoth; ev√)
open import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload})
  using (loop-pfx-ev-inv)

------------------------------------------------------------------------
-- The wedged configuration and the step that reaches it
------------------------------------------------------------------------

-- node 0 of the Leios line: degree 1, its only endpoint is `(link 0 , lo)`, so its
-- LeiosFetch SERVER peer sits at `hi`
nA : Fin 3
nA = fzero

-- the ONE body this node holds (`EB = EBHash = Bool` and `ebHash = id` at
-- `leiosLParams`, so this body's hash is `true`)
ebGood : EB
ebGood = true

-- THE POINT the far end asks for: `LSlot = U.⊤` at `leiosLParams`, so a point is just
-- its EB hash, and this one names a body the node does NOT hold (`bodySt` holds `ebGood`)
qBad : EBHash × LSlot
qBad = false , U.tt

-- the api channel on which node 0's REPORTING prototype LeiosFetch producer hands the
-- request it took off the wire to `ebServeLoop` (`Leios.PeersPSanity.lfpP-reports-request`)
reqEv : Net_Api Payload (EBHash × LSlot)
reqEv = apiLP fzero hi lfpReqBlockRequest

-- THE REQUEST A POINTER-DRIVEN FETCH WOULD PRODUCE: the far end asks for `qBad`
-- because its EB-store pointer reached that entry, not because this node offered it
evReq : Event√ (⊤ {0ℓ})
evReq = evl (evLabel (EBHash × LSlot) reqEv qBad)

-- the EB hash inside the requested point: what `ebServeBody` then blocks on
hBad : EBHash
hBad = proj₁ qBad

-- node 0's UNCHANGED EB-serve thread at its loop head
ebServeThread : Proc
ebServeThread = ebServeLoop nA (fzero , lo)

-- node 0's UNCHANGED EB-body store, holding exactly `ebGood`
bodySt : Proc
bodySt = bodyStore nA (ebGood ∷ [])

-- the serve thread against the body store, before any request
ebServePair : Proc
ebServePair = ebServeThread ∥⇘ storeES ⇙ bodySt

-- THE SERVE THREAD ONE STEP IN, read off the LTS rule rather than written down: after
-- `loop0` fires once the thread sits in `iter`'s `iter-bind` form, which `CSP.Operators`
-- gives no closed name to (`loop`'s step function is `where`-bound)
threadAfter : Σ[ T ∈ Proc ] (ebServeThread ─[ ev evReq ]─► T)
threadAfter = _ , sVis refl refl

-- THE WEDGED SERVE THREAD: `ebServeBody` waiting at `stGetBody hBad`
wedgedThread : Proc
wedgedThread = proj₁ threadAfter

-- THE WEDGED CONFIGURATION: that thread against a body store that holds only `ebGood`
wedged : Proc
wedged = wedgedThread ∥⇘ storeES ⇙ bodySt

-- THE WEDGE IS REACHED, not postulated: one request for a foreign point puts the pair
-- there.  `apiLP ∉ storeES`, so the thread takes the request alone.
wedge-reachable : ebServePair ─[ ev evReq ]─► wedged
wedge-reachable =
  Par-soloL storeES _ ebServeThread bodySt {e = reqEv} {a = qBad}
            (λ ()) (proj₂ threadAfter) refl

------------------------------------------------------------------------
-- Stability: neither operand has a silent move
------------------------------------------------------------------------

-- the wedged serve thread has no silent move: its head is the pure-visible
-- `stGetBody hBad` prefix, whose τ-map is `∅t` under one `>>=` and one `iter`, so it
-- is `nothing` at EVERY τ-index without any case analysis
thread-no-τ : ∀ {M : Proc} → ¬ (wedgedThread ─[ τ ]─► M)
thread-no-τ (sSil ())
thread-no-τ (sTau refl ())

-- the body store has no silent move at its menu either: `bodyStep` is a `□` of
-- pure-visible prefixes, and `□`'s τ-map (`□-mt`) needs the τ-index split open before
-- it reduces — tag0 reads the `stPutBody` prefix's `∅t`, tag1 the nested `□` of the
-- `stGetBody` output and `Stop`, both of which are `∅t` again
store-no-τ : ∀ {M : Proc} → ¬ (bodySt ─[ τ ]─► M)
store-no-τ (sSil ())
store-no-τ (sTau {i = _ , base _}            refl ())
store-no-τ (sTau {i = _ , fin}               refl ())
store-no-τ (sTau {i = _ , pair (base _) _}   refl ())
store-no-τ (sTau {i = _ , pair (pair _ _) _} refl ())
store-no-τ (sTau {i = _ , pair fin _} {a = lift fzero , _}           refl ())
store-no-τ (sTau {i = _ , pair fin _} {a = lift (fsuc (fsuc _)) , _} refl ())
store-no-τ (sTau {i = _ , pair fin (base _)}
                 {a = lift (fsuc fzero) , _} refl ())
store-no-τ (sTau {i = _ , pair fin fin}
                 {a = lift (fsuc fzero) , _} refl ())
store-no-τ (sTau {i = _ , pair fin (pair (base _) _)}
                 {a = lift (fsuc fzero) , _} refl ())
store-no-τ (sTau {i = _ , pair fin (pair (pair _ _) _)}
                 {a = lift (fsuc fzero) , _} refl ())
store-no-τ (sTau {i = _ , pair fin (pair fin _)}
                 {a = lift (fsuc fzero) , (lift fzero , _)} refl ())
store-no-τ (sTau {i = _ , pair fin (pair fin _)}
                 {a = lift (fsuc fzero) , (lift (fsuc fzero) , _)} refl ())
store-no-τ (sTau {i = _ , pair fin (pair fin _)}
                 {a = lift (fsuc fzero) , (lift (fsuc (fsuc _)) , _)} refl ())

------------------------------------------------------------------------
-- The two offer facts about the body store
------------------------------------------------------------------------

-- THE LOAD-BEARING COMPUTATION: the body store offers NOTHING on `stGetBody hBad`.
-- It holds only `ebGood`, so its menu names `stGetBody (ebHash ebGood)` = `stGetBody
-- true`, and `Net_Api-≟` separates that from `stGetBody false` through
-- `DecEq-StoreTag`; the branch is definitionally `nothing`.
store-no-bad : ∀ {eb : EB} {M : Proc}
             → ¬ (bodySt ─[ ev (evl (evLabel EB (getBodyEv nA hBad) eb)) ]─► M)
store-no-bad (sVis refl ())

-- every event the body store offers is a `store` event, hence in `storeES`: its menu
-- is exactly `stPutBody` and `stGetBody true`, and nothing else reduces to an offer
store-in-storeES : ∀ {X : Set} {e : Net_Api Payload X} {a : X} {M : Proc}
                 → bodySt ─[ ev (evl (evLabel X e a)) ]─► M
                 → EventSet.mem storeES (X , e) a
store-in-storeES {X = X} {e = e} (sVis refl br)
  with Net_Api-≟ (EB , putBodyEv nA) (X , e)
... | yes refl = tt
... | no _ with Net_Api-≟ (EB , getBodyEv nA ebGood) (X , e)
...   | yes refl = tt
...   | no _     = case br of λ ()

------------------------------------------------------------------------
-- The refutation
------------------------------------------------------------------------

-- a rendezvous is impossible: the thread's ONLY offer is `stGetBody hBad`, and the
-- store does not offer that
wedge-sync : ∀ {X : Set} {e : Net_Api Payload X} {a : X} {P' M : Proc}
           → wedgedThread ─[ ev (evl (evLabel X e a)) ]─► P'
           → bodySt ─[ ev (evl (evLabel X e a)) ]─► M → ⊥
wedge-sync stP stQ with loop-pfx-ev-inv (getBodyEv nA hBad) _ _ stP
... | _ , refl , _ = store-no-bad stQ

-- a solo move of the thread is impossible: its only offer IS in `storeES`
wedge-solo : ∀ {X : Set} {e : Net_Api Payload X} {a : X} {P' : Proc}
           → ¬ (EventSet.mem storeES (X , e) a)
           → wedgedThread ─[ ev (evl (evLabel X e a)) ]─► P' → ⊥
wedge-solo ¬m stP with loop-pfx-ev-inv (getBodyEv nA hBad) _ _ stP
... | _ , refl , _ = ¬m tt

-- THE WEDGE: the pair has NO transition of ANY label — not a visible one, not a τ.
-- A τ is one operand's τ, and neither has one.  A visible event is a rendezvous
-- (refuted: they never agree on a store event), a solo or a collision (refuted: every
-- offer of either operand IS in `storeES`), or a joint `√` (refuted: neither operand
-- is at `ret`).
wedge-stuck : ∀ {l : Label (⊤ {0ℓ})} {M : Proc} → ¬ (wedged ─[ l ]─► M)
wedge-stuck {l = τ} st with Par-τ-elim storeES _ wedgedThread bodySt st
... | τL _ stP _ = thread-no-τ stP
... | τR _ stQ _ = store-no-τ stQ
wedge-stuck {l = ev _} st with Par-ev-elim storeES _ wedgedThread bodySt st
... | evSync _ stP stQ = wedge-sync stP stQ
... | evL ¬m stP       = wedge-solo ¬m stP
... | evR ¬m stQ       = ¬m (store-in-storeES stQ)
... | evBoth ¬m stP _  = wedge-solo ¬m stP
... | ev√ () _
