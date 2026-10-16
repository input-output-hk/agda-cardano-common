{-# OPTIONS --safe #-}

-- Strict TxSubmission2 control grammar: missing blocking/emptiness is an error.
module Cardano_network.Replay.TxSubmission2Parse where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.String using (String; words; _++_; intersperse)
open import Cardano_network.Replay.TxSubmission2Session

-- Include the two control distinctions omitted by ordinary node tracing.
parseKind : List String → Maybe Kind
parseKind ("Init" ∷ []) = just init
parseKind ("RequestTxIds" ∷ "Blocking" ∷ []) = just requestBlocking
parseKind ("RequestTxIds" ∷ "NonBlocking" ∷ []) = just requestNonBlocking
parseKind ("ReplyTxIds" ∷ "Empty" ∷ []) = just replyIdsEmpty
parseKind ("ReplyTxIds" ∷ "NonEmpty" ∷ []) = just replyIdsNonEmpty
parseKind ("RequestTxs" ∷ []) = just requestTxs
parseKind ("ReplyTxs" ∷ []) = just replyTxs
parseKind ("Done" ∷ []) = just doneK
parseKind _ = nothing

-- Preserve direction independently of agency so illegal directions reject.
parsePair : String → Kind → Maybe E
parsePair "Send" m = just (Send , m)
parsePair "Recv" m = just (Recv , m)
parsePair _ _ = nothing

-- Expand only the pinned tracer's exact protocol namespace and message names.
expand : List String → List String
expand ("TxSubmission.Remote.Send.MsgInit" ∷ xs) = "Send" ∷ "Init" ∷ xs
expand ("TxSubmission.Remote.Send.RequestTxIds" ∷ xs) = "Send" ∷ "RequestTxIds" ∷ xs
expand ("TxSubmission.Remote.Send.ReplyTxIds" ∷ xs) = "Send" ∷ "ReplyTxIds" ∷ xs
expand ("TxSubmission.Remote.Send.RequestTxs" ∷ xs) = "Send" ∷ "RequestTxs" ∷ xs
expand ("TxSubmission.Remote.Send.ReplyTxs" ∷ xs) = "Send" ∷ "ReplyTxs" ∷ xs
expand ("TxSubmission.Remote.Send.Done" ∷ xs) = "Send" ∷ "Done" ∷ xs
expand ("TxSubmission.Remote.Receive.MsgInit" ∷ xs) = "Recv" ∷ "Init" ∷ xs
expand ("TxSubmission.Remote.Receive.RequestTxIds" ∷ xs) = "Recv" ∷ "RequestTxIds" ∷ xs
expand ("TxSubmission.Remote.Receive.ReplyTxIds" ∷ xs) = "Recv" ∷ "ReplyTxIds" ∷ xs
expand ("TxSubmission.Remote.Receive.RequestTxs" ∷ xs) = "Recv" ∷ "RequestTxs" ∷ xs
expand ("TxSubmission.Remote.Receive.ReplyTxs" ∷ xs) = "Recv" ∷ "ReplyTxs" ∷ xs
expand ("TxSubmission.Remote.Receive.Done" ∷ xs) = "Recv" ∷ "Done" ∷ xs
expand xs = xs

-- Reject incomplete shapes, foreign namespaces, and unexpected payload tokens.
parseEvent : String → Maybe E
parseEvent txt with expand (words txt)
... | d ∷ xs with parseKind xs
...   | just k = parsePair d k
...   | nothing = nothing
parseEvent txt | [] = nothing

-- Show the exact retained control shape.
showKind : Kind → String
showKind init = "Init"
showKind requestBlocking = "RequestTxIds Blocking"
showKind requestNonBlocking = "RequestTxIds NonBlocking"
showKind replyIdsEmpty = "ReplyTxIds Empty"
showKind replyIdsNonEmpty = "ReplyTxIds NonEmpty"
showKind requestTxs = "RequestTxs"
showKind replyTxs = "ReplyTxs"
showKind doneK = "Done"

-- Endpoint-relative direction labels.
showDir : Direction → String
showDir Send = "Send"
showDir Recv = "Recv"

-- Canonical event in rejection diagnostics.
showEvent : E → String
showEvent (d , m) = showDir d ++ " " ++ showKind m

-- Show every expected reply in FIFO order for diagnosis of mixed pipelines.
showQueue : List Reply → List String
showQueue [] = []
showQueue (ids ∷ q) = "ids" ∷ showQueue q
showQueue (txs ∷ q) = "txs" ∷ showQueue q

-- Expose Init, exclusive blocking, and the oldest unanswered operation.
showState : St → String
showState awaitingInit = "awaiting Init"
showState (pending q) = "pending [" ++ intersperse ", " (showQueue q) ++ "]"
showState blocking = "blocking IDs (nonempty reply or Done required)"
showState closed = "closed"
