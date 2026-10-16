{-# OPTIONS --safe #-}

-- Roles and wire directions shared by prototype mini-protocol replay.
module Cardano_network.Replay.Common where

-- Direction is relative to the node whose log is being replayed.
data Direction : Set where
  Send Recv : Direction

-- Roles follow each protocol: TxSubmission2 client submits transactions,
-- while its server requests them (the reverse data flow of ChainSync).
data Role : Set where
  client server : Role
