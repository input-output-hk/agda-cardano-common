{-# OPTIONS --guardedness #-}

-- Compatibility entry point for the governor-owned WithQueue pool.
module ConnectionManagement.Rules.JobPoolLifecycle (Result : Set) where

open import Data.Bool using (true)
open import ConnectionManagement.Rules.JobPoolKernel Result true public
