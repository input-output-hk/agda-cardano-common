{-# OPTIONS --guardedness #-}

-- M1 accounting kernel for network 2f1c154f248659b89523d5679ca532f442e7ed2a.
-- Egress.hs:239-257,298-309,340-402; Mux.hs:918-941; Types.hs:305-306.
-- Held counts are signed BATCH counts. Wire bytes use the explicit finite,
-- non-overflow profile of MigrationProfile.md; grants/refunds belong to M4.
module ConnectionManagement.Rules.MuxEgress where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊓_)
import Data.Nat as Nat
open import Data.Integer using (ℤ; +_)
import Data.Integer as Int
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (refl)
open import Class.DecEq using (DecEq; _≟_)
open import Class.DecEq.Instances using (DecEq-ℕ)
open import ConnectionManagement.Store using (Store; lookup; put)

data Lane : Set where
  directLane scheduledLane sliceLane : Lane
instance
  DecEq-Lane : DecEq Lane
  DecEq-Lane ._≟_ directLane directLane = yes refl
  DecEq-Lane ._≟_ directLane scheduledLane = no (λ ())
  DecEq-Lane ._≟_ directLane sliceLane = no (λ ())
  DecEq-Lane ._≟_ scheduledLane directLane = no (λ ())
  DecEq-Lane ._≟_ scheduledLane scheduledLane = yes refl
  DecEq-Lane ._≟_ scheduledLane sliceLane = no (λ ())
  DecEq-Lane ._≟_ sliceLane directLane = no (λ ())
  DecEq-Lane ._≟_ sliceLane scheduledLane = no (λ ())
  DecEq-Lane ._≟_ sliceLane sliceLane = yes refl

data Layout : Set where
  plainLayout : Layout
  scheduledLayout : Bool → Layout
lanes : Layout → List Lane
lanes plainLayout = scheduledLane ∷ []
lanes (scheduledLayout false) = directLane ∷ scheduledLane ∷ []
lanes (scheduledLayout true) = directLane ∷ scheduledLane ∷ sliceLane ∷ []
route : Layout → Lane → Lane
route plainLayout _ = scheduledLane
route (scheduledLayout false) sliceLane = directLane
route (scheduledLayout _) lane = lane

headerBytes softLimit maxBatchSDUs : ℕ
headerBytes = 8
softLimit = 262143
maxBatchSDUs = 100
positive : ℤ → Bool
positive (+ (suc _)) = true
positive _ = false
isZero : ℤ → Bool
isZero n = does (n Int.≟ + 0)

module Kernel (Key : Set) ⦃ keyEquality : DecEq Key ⦄ where
  record Cell : Set where
    constructor cell
    field fixedLane : Lane
          keyHeld : ℤ
          sent : ℕ
  open Cell public
  record Wanton : Set where
    constructor wanton
    field key : Key
          payload : ℕ
  open Wanton public
  data Phase : Set where
    building ready failed written : Phase
  record Batch : Set where
    constructor batch
    field lane : Lane
          members : Store Key ℕ
          pending : Maybe ℕ
          phase : Phase
          sdus : ℕ
  open Batch public
  record State : Set where
    constructor state
    field layout : Layout
          fragmentLimit batchLimit : ℕ
          cells : Store Key Cell
          wantons : Store ℕ Wanton
          queues : Store Lane (List ℕ)
          batches : Store ℕ Batch
          runHeld : ℤ
          nextBatch : ℕ
  open State public

  -- Key cells are created once; duplicate configuration is rejected.
  makeCells : Layout → List (Key × Lane) → Maybe (Store Key Cell)
  makeCells plan [] = just []
  makeCells plan ((k , requested) ∷ ks) with makeCells plan ks
  ... | nothing = nothing
  ... | just cs with lookup k cs
  ...   | just _ = nothing
  ...   | nothing = just ((k , cell (route plan requested) (+ 0) 0) ∷ cs)
  emptyQueues : List Lane → Store Lane (List ℕ)
  emptyQueues [] = []
  emptyQueues (l ∷ ls) = (l , []) ∷ emptyQueues ls
  initial : Layout → ℕ → ℕ → List (Key × Lane) → Maybe State
  initial plan limit bound ks with makeCells plan ks
  ... | nothing = nothing
  ... | just cs = just (state plan limit bound cs [] (emptyQueues (lanes plan)) [] (+ 0) 0)

  -- Failed batches stay owned and do not make their lane available again.
  laneBusy : Lane → Store ℕ Batch → Bool
  laneBusy l [] = false
  laneBusy l ((_ , b) ∷ bs) with l ≟ lane b
  ... | no _ = laneBusy l bs
  ... | yes _ with phase b
  ...   | written = laneBusy l bs
  ...   | _ = true
  queuesEmpty : Store Lane (List ℕ) → Bool
  queuesEmpty [] = true
  queuesEmpty ((_ , []) ∷ qs) = queuesEmpty qs
  queuesEmpty ((_ , (_ ∷ _)) ∷ _) = false
  protocolReady : ℕ → State → Bool
  protocolReady w s with lookup w (wantons s)
  ... | nothing = false
  ... | just f with lookup (key f) (cells s) | payload f
  ...   | just c | zero = isZero (keyHeld c)
  ...   | _ | _ = false
  drainReady : State → Bool
  drainReady s = queuesEmpty (queues s) ∧ isZero (runHeld s)

  -- Requeue only an actual remaining payload; empty fragments still have a
  -- header and acquire held ownership, just as takeSingleWanton does.
  remainderQueue : ℕ → ℕ → List ℕ → List ℕ
  remainderQueue w zero rest = rest
  remainderQueue w (suc _) rest = rest ++ (w ∷ [])
  -- A producer may fill the queue between selectDemand and takeFragment.
  -- A required requeue then retries the WHOLE fragment transaction.
  canRequeue : ℕ → List ℕ → Bool
  canRequeue zero q = true
  canRequeue (suc _) q = does (length q Nat.<? 100)
  create : ℕ → Key → State → Maybe State
  create w k s with lookup w (wantons s) | lookup k (cells s)
  ... | nothing | just _ = just (record s { wantons = put w (wanton k 0) (wantons s) })
  ... | _ | _ = nothing
  send : ℕ → ℕ → State → Maybe State
  send w bytes s with lookup w (wantons s)
  ... | nothing = nothing
  ... | just f with does (payload f Nat.<? softLimit)
  ...   | false = nothing
  ...   | true with payload f
  ...     | suc n = just (record s { wantons = put w (wanton (key f) (suc n + bytes)) (wantons s) })
  ...     | zero with lookup (key f) (cells s)
  ...       | nothing = nothing
  ...       | just c with lookup (fixedLane c) (queues s)
  ...         | nothing = nothing
  ...         | just q with does (length q Nat.<? 100)
  ...           | false = nothing
  ...           | true = just (record s
    { wantons = put w (wanton (key f) bytes) (wantons s)
    ; queues = put (fixedLane c) (q ++ (w ∷ [])) (queues s) })

  openBatch : Lane → State → Maybe State
  openBatch l s with laneBusy l (batches s) | lookup l (queues s) | lookup (nextBatch s) (batches s)
  ... | false | just (w ∷ rest) | nothing with lookup w (wantons s)
  ...   | nothing = nothing
  ...   | just f with lookup (key f) (cells s)
  ...     | nothing = nothing
  ...     | just c = just (record s
    { cells = put (key f) (cell (fixedLane c) (keyHeld c Int.+ + 1) (sent c)) (cells s)
    ; wantons = put w (wanton (key f) left) (wantons s)
    ; queues = put l (remainderQueue w left rest) (queues s)
    ; batches = put (nextBatch s) (batch l ((key f , headerBytes + taken) ∷ []) nothing building 1) (batches s)
    ; runHeld = runHeld s Int.+ + 1; nextBatch = suc (nextBatch s) })
    where
    taken = fragmentLimit s ⊓ payload f
    left = payload f Nat.∸ taken
  openBatch l s | _ | _ | _ = nothing

  -- The wire cap is checked BEFORE selecting another demand. A completed
  -- empty-queue observation seals the batch even if the queue later grows.
  wireTotal : Store Key ℕ → ℕ
  wireTotal [] = 0
  wireTotal ((_ , n) ∷ ms) = n + wireTotal ms
  belowCaps : Batch → State → Bool
  belowCaps b s = does (sdus b Nat.<? maxBatchSDUs) ∧
    does (wireTotal (members b) Nat.<? batchLimit s)
  finishBuilding : ℕ → State → Maybe State
  finishBuilding ident s with lookup ident (batches s)
  ... | nothing = nothing
  ... | just b with phase b | pending b | belowCaps b s
  ...   | building | nothing | false = just (record s
    { batches = put ident (record b { phase = ready }) (batches s) })
  ...   | _ | _ | _ = nothing

  -- Subsequent queue selection is a separate committed source transaction.
  selectNext : ℕ → State → Maybe State
  selectNext ident s with lookup ident (batches s)
  ... | nothing = nothing
  ... | just b with phase b | pending b | belowCaps b s
  ...   | building | nothing | true with lookup (lane b) (queues s)
  ...     | just (w ∷ rest) = just (record s
    { queues = put (lane b) rest (queues s)
    ; batches = put ident (record b { pending = just w }) (batches s) })
  ...     | just [] = just (record s
    { batches = put ident (record b { phase = ready }) (batches s) })
  ...     | nothing = nothing
  selectNext ident s | just b | _ | _ | _ = nothing

  extendBatch : ℕ → State → Maybe State
  extendBatch ident s with lookup ident (batches s)
  ... | nothing = nothing
  ... | just b with phase b | pending b
  ...   | building | just w with lookup w (wantons s) | lookup (lane b) (queues s)
  ...     | just f | just q with lookup (key f) (cells s) | lookup (key f) (members b)
  ...       | just c | previous with canRequeue (payload f Nat.∸ (fragmentLimit s ⊓ payload f)) q
  ...         | false = nothing
  ...         | true = just (record s
    { cells = put (key f) (cell (fixedLane c) newHeld (sent c)) (cells s)
    ; wantons = put w (wanton (key f) left) (wantons s)
    ; queues = put (lane b) (remainderQueue w left q) (queues s)
    ; batches = put ident (record b { members = put (key f) total (members b)
      ; pending = nothing; sdus = suc (sdus b) }) (batches s) })
    where
    taken = fragmentLimit s ⊓ payload f
    left = payload f Nat.∸ taken
    total = headerBytes + taken + maybeBytes previous
      where
      maybeBytes : Maybe ℕ → ℕ
      maybeBytes nothing = 0
      maybeBytes (just n) = n
    newHeld = caseMembership previous
      where
      caseMembership : Maybe ℕ → ℤ
      caseMembership nothing = keyHeld c Int.+ + 1
      caseMembership (just _) = keyHeld c
  extendBatch ident s | just b | building | just w | just f | just q | nothing | _ = nothing
  extendBatch ident s | just b | building | just w | _ | _ = nothing
  extendBatch ident s | just b | _ | _ = nothing

  -- This is the observed successful masked write/account boundary. There is
  -- no exposed post-success state admitting cancellation before accounting.
  account : Store Key ℕ → Store Key Cell → Maybe (Store Key Cell)
  account [] cs = just cs
  account ((k , bytes) ∷ ms) cs with lookup k cs
  ... | nothing = nothing
  ... | just c with positive (keyHeld c)
  ...   | false = nothing
  ...   | true = account ms (put k (cell (fixedLane c) (keyHeld c Int.- + 1) (sent c + bytes)) cs)
  commitWrite : ℕ → State → Maybe State
  commitWrite ident s with lookup ident (batches s)
  ... | nothing = nothing
  ... | just b with phase b | pending b | positive (runHeld s)
  ...   | ready | nothing | true with account (members b) (cells s)
  ...     | nothing = nothing
  ...     | just cs = just (record s { cells = cs; runHeld = runHeld s Int.- + 1
    ; batches = put ident (record b { phase = written }) (batches s) })
  commitWrite ident s | just b | _ | _ | _ = nothing
  failBatch : ℕ → State → Maybe State
  failBatch ident s with lookup ident (batches s)
  ... | just b with phase b
  ...   | building = just (record s { batches = put ident (record b { phase = failed }) (batches s) })
  ...   | ready = just (record s { batches = put ident (record b { phase = failed }) (batches s) })
  ...   | _ = nothing
  failBatch ident s | nothing = nothing

  data Action : Set where
    createWanton : ℕ → Key → Action
    appendPayload : ℕ → ℕ → Action
    takeFirst : Lane → Action
    selectDemand takeFragment finishBatch writeAccount writeFailed : ℕ → Action
  step : Action → State → Maybe State
  step (createWanton w k) = create w k
  step (appendPayload w n) = send w n
  step (takeFirst l) = openBatch l
  step (selectDemand b) = selectNext b
  step (takeFragment b) = extendBatch b
  step (finishBatch b) = finishBuilding b
  step (writeAccount b) = commitWrite b
  step (writeFailed b) = failBatch b
