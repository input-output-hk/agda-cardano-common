{-# OPTIONS --guardedness #-}

-- Membership in exhaustive bounded reachability, proved without materializing
-- the search tree. Initialization and every real edge come from the old run.
module ConnectionManagement.Exploration.TwoPeer where

open import Data.List using (_++_)
open import Data.Product using (_,_)
open import ConnectionManagement.Exploration.Finite using (_∈_)
import ConnectionManagement.Negative.ConcurrentLifecycleSupport as Support
import ConnectionManagement.Negative.ConcurrentLifecycles as Run
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Exploration.Supervised as Supervised
module Model = Supervised I.bearerClosed Support.classify Support.capability
module W = Model.Witness Support.initial Run.final Run.schedule

-- Allocation bound is the executable maximum footprint along this schedule;
-- each of the four finite ID carriers is [0, W.budget). It is not unbounded.
allocation-bound = W.budget
depth-bound = 294
abstract
  initialized-witness-found : (W.actions , W.end) ∈
    W.Find.reach 294 allocation-bound W.start
  initialized-witness-found = W.within-length 294 Run.step-count Run.initialized-to-completion
