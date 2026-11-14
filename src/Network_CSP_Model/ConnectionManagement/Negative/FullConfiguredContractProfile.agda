{-# OPTIONS --guardedness #-}

-- Instantiate the contract/frontend wrapper once. Slices import this module
-- alias directly instead of copying the large parametrized module application.
module ConnectionManagement.Negative.FullConfiguredContractProfile where

open import ConnectionManagement.Negative.FullConfiguredProfile
import ConnectionManagement.ConfiguredProtocols as Contracts
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
module B = Contracts I.bearerClosed classify capability
