{-# OPTIONS --guardedness #-}

-- Generic data-only snapshots. Keeping the classifier and original capture
-- abstract avoids elaborating the entire concrete controller in record builders.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId; WorkerId)
import ConnectionManagement.State as S
module ConnectionManagement.Negative.MuxHandlerExitFixtures
  (isBearerClosed : ErrorId → Bool) (owner : WorkerId) (captured : S.HandlerStart) where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import ConnectionManagement.Domain using (ident)
open import ConnectionManagement.Store using (put)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.MuxHandlerExit as Exit
private
  module W = Exit isBearerClosed
  module G = W.G
at : G.State → W.Phase → S.State → W.State
at g pc world = W.handlerExitState (G.setSource
  (record (G.source g) { core = record (O.core (G.source g)) { world = world } }) g)
  ((owner , W.exitFrame captured pc nothing) ∷ [])
plain : G.State → W.Phase → W.State
plain g pc = W.handlerExitState g ((owner , W.exitFrame captured pc nothing) ∷ [])
world0 : G.State → S.State
world0 g = Machine.world (O.core (G.source g))
table : S.ConnMap
table = S.insertConnection (S.handlerKey captured) (ident 0) []
lease : S.Lease
lease = S.lease owner table
world1 world2 world3 world4 world5 world6 : S.State → S.State
world1 g = record g { cleanups = (owner , S.cleanupAcquire) ∷ [] }
world2 g = record g
  { cm = record (S.cm g) { mapCell = S.taken owner }
  ; cleanups = (owner , S.cleanupSelect lease) ∷ [] }
world3 g = record g
  { cm = record (S.cm g) { mapCell = S.taken owner; entries = (ident 0 , S.terminated nothing) ∷ [] }
  ; cleanups = (owner , S.cleanupClose lease [] S.countImmediately) ∷ [] }
world4 g = record (world3 g)
  { sockets = put (S.handlerSocket captured) S.closed (S.sockets g)
  ; cleanups = (owner , S.cleanupPublish lease [] S.countImmediately) ∷ [] }
world5 g = record (world4 g)
  { cm = record (S.cm (world3 g)) { mapCell = S.full [] }
  ; cleanups = (owner , S.cleanupCount S.cleanupNormal) ∷ [] }
world6 g = record (world5 g) { cleanups = (owner , S.cleanupDone S.cleanupNormal) ∷ [] }
