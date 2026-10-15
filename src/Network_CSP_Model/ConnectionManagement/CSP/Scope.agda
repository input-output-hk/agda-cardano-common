{-# OPTIONS --guardedness #-}

-- Diagnostics only: never offered as events or converted into Skip/self-loops.
-- Absence of a local frontier is NOT a completeness or deadlock certificate.
module ConnectionManagement.CSP.Scope where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.RemoteState as Remote
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.State
open import ConnectionManagement.Domain using (WorkerId)

data Frontier : Set where
  acceptLoop serverReturn admissionUnwind handlerBody handlerUnwind
    cleanupReturn igRemoteAssertion igReleaseAssertion igHandleSetup igCMCall igExceptionUnwind muxShutdownCompletion ogSubsystem : Frontier

admissionFrontier : AdmissionPC → Maybe Frontier
admissionFrontier (finished _) = just acceptLoop
admissionFrontier (completedHandshake _) = just serverReturn
admissionFrontier impossibleHandshake = just admissionUnwind
admissionFrontier _ = nothing

-- Nothing means no cleanup has begun; negotiation/mux execution is abstract.
handlerFrontier : Maybe CleanupPC → Maybe Frontier
handlerFrontier nothing = just handlerBody
handlerFrontier (just (cleanupDone _)) = just cleanupReturn
handlerFrontier (just _) = nothing

-- Batch selection and startup now execute against stored runtime state.
-- Missing handle setup and the remaining CM calls are incomplete continuations.
igFrontier : IG.Runtime → Maybe Frontier
igFrontier ig with IG.continuation ig
... | IG.startResponders _ info _ _ _ with lookup (IG.negotiatedHandle info) (IG.handles (IG.execution ig))
...   | nothing = just igHandleSetup
...   | just h with lookup (M.muxRef h) (IG.muxes (IG.execution ig))
...     | nothing = just igHandleSetup
...     | just _ = nothing
igFrontier ig | IG.needsCM _ _ (commitRemote _) _ = nothing
igFrontier ig | IG.needsCM _ _ (awakeRemote _) _ = nothing
igFrontier ig | IG.needsCM _ _ (waitIdleRemote _) _ = nothing
igFrontier ig | IG.needsCM _ _ _ _ = just igCMCall
igFrontier ig | IG.exited = just igExceptionUnwind
igFrontier ig | _ = nothing

muxFrontier : M.Mux → Maybe Frontier
muxFrontier m with M.callback m | M.status m
... | M.tracerFailed _ | _ = just handlerUnwind
... | _ | M.stopping = just muxShutdownCompletion
... | _ | _ = nothing

publicationFrontier : List WorkerId → Maybe Frontier
publicationFrontier [] = nothing
publicationFrontier (_ ∷ _) = just handlerUnwind

-- The complete intended subsystem is not implemented, irrespective of whether
-- a particular fixture currently requests an outbound connection.
remainingSubsystem : Frontier
remainingSubsystem = ogSubsystem

-- An enabled-assertion exception needs the future IG unwind/supervision model.
releaseFrontier : Maybe Release.Frame → Maybe Frontier
releaseFrontier nothing = nothing
releaseFrontier (just f) with Release.pc f
... | Release.assertionRaised = just igReleaseAssertion
... | _ = nothing

remoteFrontier : Maybe Remote.Frame → Maybe Frontier
remoteFrontier nothing = nothing
remoteFrontier (just f) with Remote.pc f
... | Remote.assertionRaised = just igRemoteAssertion
... | _ = nothing
