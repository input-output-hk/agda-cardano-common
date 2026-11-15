{-# OPTIONS --guardedness #-}

-- Membership in exhaustive bounded reachability, proved without materializing
-- the search tree. Initialization and every real edge come from the old run.
module ConnectionManagement.Exploration.Overlap where

open import Data.List using (_++_)
open import Data.Product using (_,_)
open import ConnectionManagement.Exploration.Finite using (_∈_)
import ConnectionManagement.Negative.InboundCleanLifecycleSupport as Support
import ConnectionManagement.Negative.OverlapInitialized as Run
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Exploration.Supervised as Supervised
module Model = Supervised I.bearerClosed Support.classify Support.capability
module W = Model.Witness Support.initial Run.final Run.schedule

-- Allocation bound is the executable maximum footprint along this schedule;
-- each of the four finite ID carriers is [0, W.budget). It is not unbounded.
allocation-bound = W.budget
depth-bound = 303
abstract
  initialized-witness-found : (W.actions , W.end) ∈
    W.Find.reach 303 allocation-bound W.start
  initialized-witness-found = W.within-length 303 Run.step-count Run.initialized-to-overlap
