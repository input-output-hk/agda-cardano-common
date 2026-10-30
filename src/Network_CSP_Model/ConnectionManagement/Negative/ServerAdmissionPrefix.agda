{-# OPTIONS --guardedness #-}

-- Aggregate the independently checked initialized prefix histories. Separate
-- proof modules bound elaboration memory without changing the public claims.
module ConnectionManagement.Negative.ServerAdmissionPrefix where

import ConnectionManagement.Negative.ServerAdmissionPrefixHardLimit as Limits
import ConnectionManagement.Negative.ServerAdmissionPrefixFork as Fork
import ConnectionManagement.Negative.ServerAdmissionPrefixForbidden as Denied
module HardLimit = Limits.HardLimit
module ForkFailure = Fork.ForkFailure
module Forbidden = Denied.Forbidden
