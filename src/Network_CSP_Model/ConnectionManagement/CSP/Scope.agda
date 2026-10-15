{-# OPTIONS --guardedness #-}

-- Diagnostics only: never offered as events or converted into Skip/self-loops.
-- Absence of a local frontier is NOT a completeness or deadlock certificate.
module ConnectionManagement.CSP.Scope where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import ConnectionManagement.Rules.IGRegistration as IG
open import ConnectionManagement.State
open import ConnectionManagement.Domain using (WorkerId)

data Frontier : Set where
  acceptLoop serverReturn admissionUnwind handlerBody handlerUnwind
    cleanupReturn igResponderStartup igNextBatch igInactivity ogSubsystem : Frontier

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

-- Registration now has executable prefix rules. The success boundary still
-- abstracts responder startup; empty/repeated IG iterations are not implemented.
igFrontier : IG.Runtime → Maybe Frontier
igFrontier ig with IG.continuation ig
... | IG.startResponders _ _ _ _ _ = just igResponderStartup
... | IG.readNext _ [] = just igNextBatch
... | IG.awaitFirstBatch _ _ = just igInactivity
... | _ = nothing

publicationFrontier : List WorkerId → Maybe Frontier
publicationFrontier [] = nothing
publicationFrontier (_ ∷ _) = just handlerUnwind

-- The complete intended subsystem is not implemented, irrespective of whether
-- a particular fixture currently requests an outbound connection.
remainingSubsystem : Frontier
remainingSubsystem = ogSubsystem
