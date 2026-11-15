{-# OPTIONS --guardedness #-}

-- Selected source policy constants: Policies.hs:170-171 at network 2f1c154.
-- Existing FullConfigured* fixtures are retained as the reduced-60 profile.
module ConnectionManagement.SourceInputs.Policy where
open import ConnectionManagement.Negative.FullConfiguredProfile
import ConnectionManagement.Rules.OutboundGovernor as Governor
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.SourceInputs.Negotiation as Negotiation
open import Data.List using (map)
open import Data.Nat using (_+_)
open import Data.Product using (_×_; _,_)

-- This translation is only certified by the individual reached edges below;
-- it is not a simulation for arbitrary clocks, states or policy inputs.
deadline : Maybe ℕ → Maybe ℕ
deadline (just n) = just (n + 60)
deadline nothing = nothing
known : PeerAddr × Governor.Known → PeerAddr × Governor.Known
known (p , k) = p , record k { clearFailuresAt = deadline (Governor.clearFailuresAt k) }
state : Governor.State → Governor.State
state s = record s { knownPeers = map known (Governor.knownPeers s) }
-- Pending policy decisions retain a governor snapshot until applyAt.
selected : Sub.Selected → Sub.Selected
selected (Sub.policy d) = Sub.policy (record d { nextState = state (Governor.nextState d) })
selected x = x
program : Sub.PC → Sub.PC
program (Sub.cancelTimer x) = Sub.cancelTimer (selected x)
program (Sub.apply x) = Sub.apply (selected x)
program x = x
context : C.SubContext → C.SubContext
context c = record c { maxRetries = 5; clearFailDelay = 120
  ; privateState = state (C.SubContext.privateState c)
  ; publicState = state (C.SubContext.publicState c)
  ; pc = program (C.SubContext.pc c) }
runtime : V.Runtime → V.Runtime
runtime s = record s { base = record (V.base s)
  { context = record (K.context (V.base s))
    { subsystem = context (C.subsystem (K.context (V.base s))) } } }

-- Source initialization configures the empty usual initialized infrastructure,
-- before any step; no reached midpoint is used as the initial state.
initialize : O.Configuration → Governor.State → Maybe V.Runtime
initialize c g with V.initialize c g
... | nothing = nothing
... | just s = just (runtime s)
reduced60 : V.Runtime
reduced60 = initial
source120 : V.Runtime
source120 = runtime initial
source-initializer : initialize (O.initial c₀) settings ≡ just source120
source-initializer = refl
source-delay : Sub.clearFailDelay (PS.machine (K.peers (V.base source120))) ≡ 120
source-delay = refl
source-retries : Sub.maxRetries (PS.machine (K.peers (V.base source120))) ≡ 5
source-retries = refl
