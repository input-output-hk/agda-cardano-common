{-# OPTIONS --guardedness #-}

-- Data-only snapshots over an abstract classifier/capture. These builders are
-- not transition or reachability claims; acceptance proves each actual step.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId; WorkerId; MuxId)
import ConnectionManagement.State as Shared
module ConnectionManagement.Negative.MuxStartupUnwindFixtures
  (isBearerClosed : ErrorId → Bool) (worker : WorkerId)
  (captured : Shared.HandlerStart) (mid : MuxId) where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
import ConnectionManagement.MuxStartupUnwind as Unwind
import ConnectionManagement.MuxExitCancellation as Cancellation
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.CMShutdown as Close
private
  module R = Unwind isBearerClosed
  module X = Cancellation isBearerClosed
  module W = Exit isBearerClosed
  module G = W.G
  module M = G.M
  module P = G.P
  module S = G.Startup
wrapP : P.State → R.State
wrapP p = R.unwinding (W.handlerExitState (G.shutdownState (M.monitorState p []) []) []) []
selected : P.State → S.PC → Mux.Callback → R.Route → R.Exception → R.PC → R.State
selected p pc cb scope result stage = R.unwinding (R.base (wrapP p))
  ((worker , R.fault captured mid pc cb scope result stage) ∷ [])
withExit : W.Phase → R.State → R.State
withExit pc s = record s { base = record (R.base s)
  { exits = (worker , W.exitFrame captured pc nothing) ∷ [] } }
withWorld : Shared.State → R.State → R.State
withWorld world s = R.setSource (record (R.source s)
  { core = record (O.core (R.source s)) { world = world } }) s
shared : R.State → Shared.State
shared s = Machine.world (O.core (R.source s))
withShutdown : Close.State → R.State → R.State
withShutdown pc s = record s { base = W.setShutdown pc (R.base s) }

mark : X.State → S.PC → Mux.Callback → R.Route → R.Exception → R.PC → R.State
mark x pc cb scope result stage = R.unwinding x
  ((worker , R.fault captured mid pc cb scope result stage) ∷ [])
