{-# OPTIONS --safe #-}

-- Roles and wire directions shared by prototype mini-protocol replay.
module Cardano_network.Replay.Common where

-- Direction is relative to the node whose log is being replayed.
data Direction : Set where
  Send Recv : Direction

-- Client means initiator/consumer; server means responder/producer.
data Role : Set where
  client server : Role
