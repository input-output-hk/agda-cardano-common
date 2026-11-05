{-# OPTIONS --guardedness #-}

-- The explicit empty-acquisition initializer closes outbound origin discovery.
-- Physical inversion stays in this thin consumer, outside the prefix observer.
module ConnectionManagement.Properties.CollectedOutboundOrigin where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (WorkerId; ErrorId; HandleId; ident)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.HandlerResourceFacts using (Facts)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundGovernor as Governor
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.Properties.HandlerAuxFrontend as Membership
import ConnectionManagement.Properties.HandlerBirthBacking as Birth
import ConnectionManagement.Properties.CollectedHandlerBirth as Collected
import ConnectionManagement.Properties.CollectedInboundOrigin as Inbound
import ConnectionManagement.Properties.InboundBirthLabels as Labels
import ConnectionManagement.Properties.OutboundBirthResources as BirthResources
import ConnectionManagement.Properties.OutboundOriginFrontend as FrontendModel
import ConnectionManagement.Properties.OutboundOriginHistory as HistoryModel
import ConnectionManagement.Properties.ServerPeersHandlerResources as OriginalResources

module Frontend (b io : ErrorId → Bool) (capability : HandleId → ℕ → Bool) where
 private
  module T = Combined.Protocols b io capability using (Runtime; Event; Runs; stop; more; initialize; advance)
  module W = ExitModel b using (shutdown)
  module R = UnwindModel b using (base)
  module Member = Membership.Frontend b io capability using (unwind)
  module Back = Birth.Frontend b io capability using (Backing)
  module CollectedBirth = Collected.Frontend b io capability using (initialized-birth)
  module Prior = Inbound.Frontend b io capability using (InboundOrigin; from-inbound-occurrence)
  module Label = Labels.Frontend b io capability using (Decomposition; decompose)
  module D = Labels.Frontend.Decomposition using (before; born; label; prefix; suffix; decomposition; prefix-run; actual; suffix-run)
  module Bridge = BirthResources.Frontend b io capability using (Outbound; classify; resources)
  module Owner = BirthResources.Frontend.Outbound using (caller; request; entry; promise; key; before-PC)
  module Observe = FrontendModel.Frontend b io capability using (source; core; shared; initialized-empty; to-runs)
  module Trace = FrontendModel.Frontend.History b io capability using (Origin; origin)
  module Origin = FrontendModel.Frontend.History.Origin b io capability using (allocationBefore; allocationAfter; allocation)
  module Allocation = HistoryModel.Allocation using (beforeFrame; before-PC; actual; promise-input)
 open Observe public using (source; core; shared)

 private
  -- Promise membership is historical at the actual allocating source write.
  -- The counter input is not a global absence/freshness premise.
  allocated-cell : ∀ caller mode savedFrame world {entry afterFrame afterWorld} →
    A.pc savedFrame ≡ A.allocatePromise entry →
    A.step caller mode A.newPromise savedFrame world ≡ just (afterFrame , afterWorld) →
    ident (S.nextPromise world) ∈ S.promises afterWorld
  allocated-cell caller mode savedFrame world beforePC actual rewrite beforePC
    with lookup (ident (S.nextPromise world)) (S.handshakeResults world)
  ... | just existing = case actual of λ ()
  ... | nothing with just-injective actual
  ...   | refl = here refl
  retain : ∀ worker captured {before events after} → T.Runs before events after →
    Facts worker captured (shared before) → Facts worker captured (shared after)
  retain worker captured = OriginalResources.For.Frontend.run-preserves b io worker captured capability

 -- Current state/event suffixes are deliberately absent from this packet's
 -- parameters: later checkpoints copy the exact same original occurrence.
 record BirthPacket (input : M.Configuration) (governor : Governor.State)
   (start : T.Runtime) (worker : WorkerId) (captured : S.HandlerStart) : Set where
  field
   initialized : T.initialize (O.initial input) governor ≡ just start
   before born : T.Runtime
   label : T.Event
   prefix : List T.Event
   prefix-run : T.Runs start prefix before
   actual : T.advance label before ≡ just born
   owner : Bridge.Outbound before born worker captured
   reconstructed : Trace.Origin start before prefix (Owner.caller owner) (Owner.request owner)
     (Owner.entry owner) (Owner.promise owner) (Owner.key owner)
   promise-allocated : Owner.promise owner ∈ S.promises (shared (Origin.allocationAfter reconstructed))
   at-birth : Facts worker captured (shared born)

 record OutboundOrigin (input : M.Configuration) (governor : Governor.State)
   (start current : T.Runtime) (events : List T.Event) (worker : WorkerId) (captured : S.HandlerStart) : Set where
  field
   packet : BirthPacket input governor start worker captured
   suffix : List T.Event
   decomposition : events ≡ BirthPacket.prefix packet ++ (BirthPacket.label packet ∷ suffix)
   suffix-run : T.Runs (BirthPacket.born packet) suffix current
   retained : Facts worker captured (shared current)

 private
  recover : ∀ input governor {start current events worker captured} →
    T.initialize (O.initial input) governor ≡ just start →
    (occurrence : Label.Decomposition start current events worker captured) →
    Bridge.Outbound (D.before occurrence) (D.born occurrence) worker captured →
    OutboundOrigin input governor start current events worker captured
  recover input governor {start = start} {worker = worker} {captured = captured} initialized occurrence owner = record
    { packet = record
      { initialized = initialized; before = D.before occurrence; born = D.born occurrence
      ; label = D.label occurrence; prefix = D.prefix occurrence; prefix-run = D.prefix-run occurrence
      ; actual = D.actual occurrence; owner = owner; reconstructed = reconstructed
      ; promise-allocated = allocated; at-birth = bornFacts }
    ; suffix = D.suffix occurrence; decomposition = D.decomposition occurrence
    ; suffix-run = D.suffix-run occurrence; retained = retain worker captured (D.suffix-run occurrence) bornFacts }
    where
    reconstructed : Trace.Origin start (D.before occurrence) (D.prefix occurrence) (Owner.caller owner) (Owner.request owner)
      (Owner.entry owner) (Owner.promise owner) (Owner.key owner)
    reconstructed = Trace.origin (Observe.initialized-empty input governor initialized)
      (Observe.to-runs (D.prefix-run occurrence)) (Owner.before-PC owner)
    allocated : Owner.promise owner ∈ S.promises (shared (Origin.allocationAfter reconstructed))
    allocated = subst (λ promise → promise ∈ S.promises (shared (Origin.allocationAfter reconstructed)))
      (sym (Allocation.promise-input (Origin.allocation reconstructed)))
      (allocated-cell (Owner.caller owner) (M.responder (core (Origin.allocationBefore reconstructed)))
        (Allocation.beforeFrame (Origin.allocation reconstructed)) (shared (Origin.allocationBefore reconstructed))
        (Allocation.before-PC (Origin.allocation reconstructed)) (Allocation.actual (Origin.allocation reconstructed)))
    bornFacts : Facts worker captured (shared (D.born occurrence))
    bornFacts = Bridge.resources initialized (D.prefix-run occurrence) owner

 -- An explicit actual backing supports positive controls without forcing a
 -- long opaque collected trace to normalize. The closed API below discovers it.
 from-backing : ∀ input governor {start current events worker captured} →
   T.initialize (O.initial input) governor ≡ just start → Back.Backing start current events worker captured →
   Prior.InboundOrigin (O.initial input) governor start current events worker captured ⊎
     OutboundOrigin input governor start current events worker captured
 from-backing input governor initialized birthHistory with Bridge.classify birthHistory
 ... | inj₁ owner = inj₁ (Prior.from-inbound-occurrence (O.initial input) governor initialized (Label.decompose birthHistory) owner)
 ... | inj₂ owner = inj₂ (recover input governor initialized (Label.decompose birthHistory) owner)

 record Discovery (input : M.Configuration) (governor : Governor.State)
   (start current : T.Runtime) (events : List T.Event) (worker : WorkerId) : Set where
  field
   captured : S.HandlerStart
   backing : Back.Backing start current events worker captured
   origin : Prior.InboundOrigin (O.initial input) governor start current events worker captured ⊎
     OutboundOrigin input governor start current events worker captured

 initialize-origin : ∀ {input governor start current events worker} →
   T.initialize (O.initial input) governor ≡ just start → T.Runs start events current →
   worker ∈ Close.collected (W.shutdown (R.base (Member.unwind current))) →
   Discovery input governor start current events worker
 initialize-origin {input} {governor} initialized path member with CollectedBirth.initialized-birth initialized path member
 ... | captured , birthHistory = record
   { captured = captured; backing = birthHistory; origin = from-backing input governor initialized birthHistory }

 append : ∀ {start prefix middle suffix current} → T.Runs start prefix middle → T.Runs middle suffix current → T.Runs start (prefix ++ suffix) current
 append T.stop rest = rest
 append (T.more actual path) rest = T.more actual (append path rest)
 extend-outbound : ∀ {input governor start middle events worker captured current tail} →
   T.Runs middle tail current → OutboundOrigin input governor start middle events worker captured →
   OutboundOrigin input governor start current (events ++ tail) worker captured
 extend-outbound {worker = worker} {captured = captured} {tail = tail} path origin = record
   { packet = OutboundOrigin.packet origin; suffix = OutboundOrigin.suffix origin ++ tail
   ; decomposition = trans (cong (_++ tail) (OutboundOrigin.decomposition origin))
       (++-assoc (BirthPacket.prefix (OutboundOrigin.packet origin))
         (BirthPacket.label (OutboundOrigin.packet origin) ∷ OutboundOrigin.suffix origin) tail)
   ; suffix-run = append (OutboundOrigin.suffix-run origin) path
   ; retained = retain worker captured path (OutboundOrigin.retained origin) }
 extend-packet : ∀ {input governor start middle events worker captured current tail}
   (path : T.Runs middle tail current) (origin : OutboundOrigin input governor start middle events worker captured) →
   OutboundOrigin.packet (extend-outbound path origin) ≡ OutboundOrigin.packet origin
 extend-packet path origin = refl
 execution : ∀ {input governor start current events worker captured} →
   OutboundOrigin input governor start current events worker captured → T.Runs start events current
 execution {start = start} {current = current} origin = subst (λ events → T.Runs start events current)
   (sym (OutboundOrigin.decomposition origin))
   (append (BirthPacket.prefix-run (OutboundOrigin.packet origin))
     (T.more (BirthPacket.actual (OutboundOrigin.packet origin)) (OutboundOrigin.suffix-run origin)))
