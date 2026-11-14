{-# OPTIONS --guardedness #-}

-- One shared responder-wrapper instance; phases import the profile directly.
module ConnectionManagement.Negative.InboundConfiguredSupport where

open import ConnectionManagement.Negative.FullConfiguredProfile
import ConnectionManagement.ConfiguredResponders as Contracts
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
module B = Contracts I.bearerClosed classify capability

-- Default is accepted only when the separate just/refl edge also checks.
afterContract : B.Action → B.State → B.State
afterContract a s with B.step a s
... | just t = t
... | nothing = s
