{-# OPTIONS --safe #-}

-- Expand exact original tracer namespaces into the legacy event tokens.
-- Unknown or cross-protocol namespaces stay unchanged and fail payload parsing.
module Cardano_network.Replay.Namespaces where

open import Data.List using (List; []; _∷_)
open import Data.String using (String)

-- Accepted LeiosFetch namespaces, preserving wire direction.
fetch : List String → List String
fetch ("LeiosFetch.Remote.Send.BlockRequest" ∷ xs) = "Send" ∷ "BlockRequest" ∷ xs
fetch ("LeiosFetch.Remote.Send.Block" ∷ xs) = "Send" ∷ "Block" ∷ xs
fetch ("LeiosFetch.Remote.Send.BlockTxsRequest" ∷ xs) = "Send" ∷ "BlockTxsRequest" ∷ xs
fetch ("LeiosFetch.Remote.Send.BlockTxs" ∷ xs) = "Send" ∷ "BlockTxs" ∷ xs
fetch ("LeiosFetch.Remote.Send.Done" ∷ xs) = "Send" ∷ "Done" ∷ xs
fetch ("LeiosFetch.Remote.Receive.BlockRequest" ∷ xs) = "Recv" ∷ "BlockRequest" ∷ xs
fetch ("LeiosFetch.Remote.Receive.Block" ∷ xs) = "Recv" ∷ "Block" ∷ xs
fetch ("LeiosFetch.Remote.Receive.BlockTxsRequest" ∷ xs) = "Recv" ∷ "BlockTxsRequest" ∷ xs
fetch ("LeiosFetch.Remote.Receive.BlockTxs" ∷ xs) = "Recv" ∷ "BlockTxs" ∷ xs
fetch ("LeiosFetch.Remote.Receive.Done" ∷ xs) = "Recv" ∷ "Done" ∷ xs
fetch xs = xs

-- Accepted LeiosNotify namespaces, preserving wire direction.
notify : List String → List String
notify ("LeiosNotify.Remote.Send.RequestNext" ∷ xs) = "Send" ∷ "RequestNext" ∷ xs
notify ("LeiosNotify.Remote.Send.NotificationRequestNext" ∷ xs) = "Send" ∷ "RequestNext" ∷ xs
notify ("LeiosNotify.Remote.Send.BlockAnnouncement" ∷ xs) = "Send" ∷ "BlockAnnouncement" ∷ xs
notify ("LeiosNotify.Remote.Send.BlockOffer" ∷ xs) = "Send" ∷ "BlockOffer" ∷ xs
notify ("LeiosNotify.Remote.Send.BlockTxsOffer" ∷ xs) = "Send" ∷ "BlockTxsOffer" ∷ xs
notify ("LeiosNotify.Remote.Send.Votes" ∷ xs) = "Send" ∷ "Votes" ∷ xs
notify ("LeiosNotify.Remote.Send.Done" ∷ xs) = "Send" ∷ "Done" ∷ xs
notify ("LeiosNotify.Remote.Receive.RequestNext" ∷ xs) = "Recv" ∷ "RequestNext" ∷ xs
notify ("LeiosNotify.Remote.Receive.NotificationRequestNext" ∷ xs) = "Recv" ∷ "RequestNext" ∷ xs
notify ("LeiosNotify.Remote.Receive.BlockAnnouncement" ∷ xs) = "Recv" ∷ "BlockAnnouncement" ∷ xs
notify ("LeiosNotify.Remote.Receive.BlockOffer" ∷ xs) = "Recv" ∷ "BlockOffer" ∷ xs
notify ("LeiosNotify.Remote.Receive.BlockTxsOffer" ∷ xs) = "Recv" ∷ "BlockTxsOffer" ∷ xs
notify ("LeiosNotify.Remote.Receive.Votes" ∷ xs) = "Recv" ∷ "Votes" ∷ xs
notify ("LeiosNotify.Remote.Receive.Done" ∷ xs) = "Recv" ∷ "Done" ∷ xs
notify xs = xs
