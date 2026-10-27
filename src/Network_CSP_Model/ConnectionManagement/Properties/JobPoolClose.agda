{-# OPTIONS --guardedness #-}

-- The existing governor-pool certificate is the WithQueue specialization.
module ConnectionManagement.Properties.JobPoolClose (Result : Set) where

open import Data.Bool using (true)
open import ConnectionManagement.Properties.JobPoolCloseKernel Result true public
