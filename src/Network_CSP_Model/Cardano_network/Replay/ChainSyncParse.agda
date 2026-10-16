{-# OPTIONS --safe #-}

-- Strict control-only parsing, with original ChainSync tracer namespaces.
module Cardano_network.Replay.ChainSyncParse where

open import Data.Nat.Show renaming (show to showℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.String using (String; words; _++_)
open import Cardano_network.Replay.ChainSyncSession

-- Recognise all eight wire message kinds exactly.
parseKind : String → Maybe Kind
parseKind "RequestNext" = just requestNext
parseKind "AwaitReply" = just awaitReply
parseKind "RollForward" = just rollForward
parseKind "RollBackward" = just rollBackward
parseKind "FindIntersect" = just findIntersect
parseKind "IntersectFound" = just intersectFound
parseKind "IntersectNotFound" = just intersectNotFound
parseKind "Done" = just doneK
parseKind _ = nothing

-- Keep invalid agency observable so the checker can reject it.
parsePair : String → Kind → Maybe E
parsePair "Send" m = just (Send , m)
parsePair "Recv" m = just (Recv , m)
parsePair _ _ = nothing

-- Expand only exact ChainSync namespaces.
expand : List String → List String
expand ("ChainSync.Remote.Send.RequestNext" ∷ xs) = "Send" ∷ "RequestNext" ∷ xs
expand ("ChainSync.Remote.Send.AwaitReply" ∷ xs) = "Send" ∷ "AwaitReply" ∷ xs
expand ("ChainSync.Remote.Send.RollForward" ∷ xs) = "Send" ∷ "RollForward" ∷ xs
expand ("ChainSync.Remote.Send.RollBackward" ∷ xs) = "Send" ∷ "RollBackward" ∷ xs
expand ("ChainSync.Remote.Send.FindIntersect" ∷ xs) = "Send" ∷ "FindIntersect" ∷ xs
expand ("ChainSync.Remote.Send.IntersectFound" ∷ xs) = "Send" ∷ "IntersectFound" ∷ xs
expand ("ChainSync.Remote.Send.IntersectNotFound" ∷ xs) = "Send" ∷ "IntersectNotFound" ∷ xs
expand ("ChainSync.Remote.Send.Done" ∷ xs) = "Send" ∷ "Done" ∷ xs
expand ("ChainSync.Remote.Receive.RequestNext" ∷ xs) = "Recv" ∷ "RequestNext" ∷ xs
expand ("ChainSync.Remote.Receive.AwaitReply" ∷ xs) = "Recv" ∷ "AwaitReply" ∷ xs
expand ("ChainSync.Remote.Receive.RollForward" ∷ xs) = "Recv" ∷ "RollForward" ∷ xs
expand ("ChainSync.Remote.Receive.RollBackward" ∷ xs) = "Recv" ∷ "RollBackward" ∷ xs
expand ("ChainSync.Remote.Receive.FindIntersect" ∷ xs) = "Recv" ∷ "FindIntersect" ∷ xs
expand ("ChainSync.Remote.Receive.IntersectFound" ∷ xs) = "Recv" ∷ "IntersectFound" ∷ xs
expand ("ChainSync.Remote.Receive.IntersectNotFound" ∷ xs) = "Recv" ∷ "IntersectNotFound" ∷ xs
expand ("ChainSync.Remote.Receive.Done" ∷ xs) = "Recv" ∷ "Done" ∷ xs
expand xs = xs

-- Extra payload tokens are errors, not supposedly validated chain data.
parseEvent : String → Maybe E
parseEvent s with expand (words s)
... | d ∷ m ∷ [] with parseKind m
...   | just k = parsePair d k
...   | nothing = nothing
parseEvent s | _ = nothing

-- Print each control message using its canonical tracer spelling.
showKind : Kind → String
showKind requestNext = "RequestNext"
showKind awaitReply = "AwaitReply"
showKind rollForward = "RollForward"
showKind rollBackward = "RollBackward"
showKind findIntersect = "FindIntersect"
showKind intersectFound = "IntersectFound"
showKind intersectNotFound = "IntersectNotFound"
showKind doneK = "Done"

-- Print the endpoint-relative wire direction.
showDir : Direction → String
showDir Send = "Send"
showDir Recv = "Recv"

-- Canonical wire event in rejection diagnostics.
showEvent : E → String
showEvent (d , m) = showDir d ++ " " ++ showKind m

-- Expose the oldest request's reply phase.
showPhase : Phase → String
showPhase canAwait = "can-await"
showPhase mustReply = "must-reply"

-- Report pending work without implying any chain-content validation.
showState : St → String
showState (pending n ph) = "outstanding " ++ showℕ n ++ ", " ++ showPhase ph
showState intersect = "awaiting intersection result"
showState closed = "closed"
