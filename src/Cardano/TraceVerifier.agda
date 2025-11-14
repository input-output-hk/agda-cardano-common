open import Prelude

module Cardano.TraceVerifier (Result : Set → Set → Set) where

  record Specification : Set₁ where
    field
      State Input Output : Set
      _-⟦_/_⟧⇀_          : State → Input → Output → State → Set

  open Specification

  record TraceVerifier (specification : Specification) : Set₁ where
    field
      Action : Set

    Trace = List (Action × specification .Output)

    WrongTrace : Trace → specification .State → Set
    WrongTrace = {!!} -- just as in the current code (i.e., `Err-verifyTrace`)

    ValidTrace : Trace → specification .State → Set
    ValidTrace = {!!} -- just as in the current code (ultimately calls `specification ._-⟦_/_⟧⇀_`)

    VerifyTrace = (t : Trace) (s : specification. State) → Result (WrongTrace t s) (ValidTrace t s)

    defaultVerifyTrace : VerifyTrace
    defaultVerifyTrace = {!!} -- similar to what's in the current code, that is, for each trace item:
                              --
                              -- 1. Get the rule associated to the trace event
                              -- 2. Check that inputs match
                              -- 3. Check that the rule premises are met
                              -- 4. Execute rule to get the rule conclusion, output and new state

    field
      verifyTrace : WithDefault defaultVerifyTrace -- can be overriden

  open TraceVerifier

  record Component : Set₁ where
    field
      specification : Specification
      traceVerifier : TraceVerifier specification

  open Component

  module Node (consensus ledger network : Component) where

    nodeSpecification : Specification
    nodeSpecification = record
      { State      = NodeState  -- this may contain <component> .specification .State
      ; Input      = {!!}
      ; Output     = {!!}
      ; _-⟦_/_⟧⇀_  = {!!}       -- this should call <component> .specification ._-⟦_/_⟧⇀_
      }
      where
        -- For example:
        NodeState =
            consensus .specification .State
          × ledger    .specification .State
          × network   .specification .State

    nodeTraceVerifier : TraceVerifier nodeSpecification
    nodeTraceVerifier = record
      { Action       = NodeTraceVerifierAction -- this may contain <component> .traceVerifier .Action, etc.
      ; verifyTrace  = {!!}
          --
          -- Discussion: Should this either
          --
          -- ∘ Grep the trace with each <component> .traceVerifier .Action and then call the correspondent
          --   <component> .traceVerifier .verifyTrace; or
          -- ∘ Do what the current Leios trace verifier is doing but using nodeSpecification ._-⟦_/_⟧⇀_
          --
          -- ? Are the two options equivalent?
      }
      where
        -- For example:
        NodeTraceVerifierAction =
            consensus .traceVerifier .Action
          ⊎ ledger    .traceVerifier .Action
          ⊎ network   .traceVerifier .Action

    node : Component
    node = record
      { specification = nodeSpecification
      ; traceVerifier = nodeTraceVerifier
      }
