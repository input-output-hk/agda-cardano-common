{-# OPTIONS --guardedness #-}

-- Peer-job interleavings preserve existing historical resource identities.
module ConnectionManagement.Properties.PeerJobResources where

open import ConnectionManagement.Domain using (WorkerId)
import ConnectionManagement.State as S
import ConnectionManagement.Properties.PeerJobInvariant as Jobs
import ConnectionManagement.Properties.OutboundRuntimeResources as Runtime

module For (q : WorkerId) (captured : S.HandlerStart) where
  open Jobs.Lift (Runtime.For.RuntimeValid q captured) (Runtime.For.advance-preserves q captured) public
