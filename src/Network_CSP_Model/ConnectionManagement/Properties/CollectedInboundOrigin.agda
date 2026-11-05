{-# OPTIONS --guardedness #-}

-- Thin composition only: discover an actual collected birth, recover its
-- inbound source history, and keep the genuine outbound alternative explicit.
module ConnectionManagement.Properties.CollectedInboundOrigin where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain using (WorkerId; ErrorId; HandleId)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.HandlerResourceFacts using (Facts)
import ConnectionManagement.State as S
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.OutboundGovernor as Governor
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.Properties.HandlerAuxFrontend as Membership
import ConnectionManagement.Properties.HandlerBirthBacking as Birth
import ConnectionManagement.Properties.CollectedHandlerBirth as Collected
import ConnectionManagement.Properties.InboundBirthLabels as Labels
import ConnectionManagement.Properties.InboundOriginRuntime as Runtime
import ConnectionManagement.Properties.InboundOriginResources as Resources
import ConnectionManagement.Properties.ServerPeersHandlerResources as OriginalResources

module Frontend (b io : ErrorId → Bool) (capability : HandleId → ℕ → Bool) where
 private
  module T = Combined.Protocols b io capability using (Runtime; Event; Runs; stop; more; advance; initialize)
  module W = ExitModel b using (shutdown)
  module R = UnwindModel b using (base)
  module Member = Membership.Frontend b io capability using (unwind)
  module Back = Birth.Frontend b io capability using (Backing)
  module CollectedBirth = Collected.Frontend b io capability using (initialized-birth)
  module Label = Labels.Frontend b io capability using (Inbound; Outbound; Decomposition; decompose)
  module D = Labels.Frontend.Decomposition using (before; born; label; prefix; suffix; decomposition; prefix-run; actual; suffix-run; branch)
  module Owner = Labels.Frontend.Inbound using (parent; request; heldLease; promise; entry; before-PC; source; worker; descriptor)
  module Closed = Runtime.Frontend b io capability using (core; shared)
  module Located = Runtime.Frontend.Located b io capability using (ForkOrigin; from-runs; initialized-fork-origin)
  module F = Runtime.Frontend.Located.ForkOrigin b io capability using (request; heldLease; promise; entry; selection; fork-event; fork-source)
  module Selection = Runtime.Frontend.Located.History.SelectedOrigin b io capability using (allocationBefore; allocationAfter; before-allocation-PC; allocation-source; promise-input; selectionBefore; selectionAfter; before-selection-PC; selection-source; selected-PC; forkGap; fork-gap-run; current-PC)
  module Resource = Resources.Frontend b io capability using (at-fork; retain)
  module Original = OriginalResources b io using (allocated-frame)
 open Closed public using (core; shared)

 -- Equality of the recovered terminal row aligns both the child and the exact
 -- descriptor. It does not assert freshness or ownership of a live connection.
 private
  -- Resource consequences depend on the recovered primitive occurrence, not
  -- on the spelling of its frontend label. Birth adapters derive this packet
  -- from their actual source operation, preserving the observed event verbatim.
  recovered-promise : ∀ {start observed before born parent label}
    (origin : Located.ForkOrigin start observed before born parent label) →
    F.promise origin ∈ S.promises (shared (Selection.allocationAfter (F.selection origin)))
  recovered-promise {parent = parent} origin = subst
    (λ promise → promise ∈ S.promises (shared (Selection.allocationAfter selected)))
    (sym (Selection.promise-input selected))
    (proj₂ (Original.allocated-frame parent (F.request origin) (F.heldLease origin)
      (core (Selection.allocationBefore selected)) (Selection.before-allocation-PC selected) (Selection.allocation-source selected)))
    where
    selected = F.selection origin

  -- The exact descriptor obtained from that occurrence has the stored birth
  -- resources. No map ownership, freshness or current promise membership follows.
  recovered-at-birth : ∀ {start observed before born parent label}
    (origin : Located.ForkOrigin start observed before born parent label) →
    Facts (S.child (F.request origin))
      (S.handlerStart (F.entry origin) (S.socketRef (F.request origin))
        (F.promise origin) (S.key (F.request origin))) (shared born)
  recovered-at-birth {before = before} {born} {parent} origin =
    Resource.at-fork parent (F.request origin) (F.heldLease origin) (F.promise origin) (F.entry origin)
      {beforeSelect = Selection.selectionBefore selected} {selected = Selection.selectionAfter selected}
      {beforeFork = before} {born = born} {gap = Selection.forkGap selected}
      (Selection.before-selection-PC selected) (Selection.selection-source selected) (Selection.selected-PC selected)
      (Located.from-runs (Selection.fork-gap-run selected)) (Selection.current-PC selected) (F.fork-source origin)
    where
    selected = F.selection origin

  row-alignment : ∀ {request saved promise entry request′ saved′ promise′ entry′} →
    S.admissionWorker request (S.forkHandler saved promise entry) ≡
      S.admissionWorker request′ (S.forkHandler saved′ promise′ entry′) →
    S.child request ≡ S.child request′ ×
      S.handlerStart entry (S.socketRef request) promise (S.key request) ≡
      S.handlerStart entry′ (S.socketRef request′) promise′ (S.key request′)
  row-alignment refl = refl , refl

 record InboundOrigin (input : O.Configuration) (governor : Governor.State)
   (start current : T.Runtime) (events : List T.Event) (worker : WorkerId) (captured : S.HandlerStart) : Set where
  field
   initialized : T.initialize input governor ≡ just start
   before born : T.Runtime
   parent : WorkerId
   label : T.Event
   prefix suffix : List T.Event
   decomposition : events ≡ prefix ++ (label ∷ suffix)
   prefix-run : T.Runs start prefix before
   suffix-run : T.Runs born suffix current
   reconstructed : Located.ForkOrigin start prefix before born parent label
   child-matches : worker ≡ S.child (F.request reconstructed)
   descriptor : captured ≡ S.handlerStart (F.entry reconstructed)
     (S.socketRef (F.request reconstructed)) (F.promise reconstructed) (S.key (F.request reconstructed))
   promise-allocated : F.promise reconstructed ∈ S.promises
     (shared (Selection.allocationAfter (F.selection reconstructed)))
   at-birth : Facts worker captured (shared born)
   retained : Facts worker captured (shared current)

 -- An outbound result retains the same original frontend occurrence plus the
 -- actual physical acquire/forkOK equation. No inbound resource claim is made.
 record OutboundOrigin (start current : T.Runtime) (events : List T.Event)
   (worker : WorkerId) (captured : S.HandlerStart) : Set where
  field
   occurrence : Label.Decomposition start current events worker captured
   physical-birth : Label.Outbound (D.before occurrence) (D.born occurrence) worker captured

 private
  recover : ∀ input governor {start current events worker captured} →
    T.initialize input governor ≡ just start →
    (occurrence : Label.Decomposition start current events worker captured) →
    Label.Inbound (D.before occurrence) (D.born occurrence) worker captured →
    InboundOrigin input governor start current events worker captured
  recover input governor {start = start} {current = current} {worker = worker} {captured = captured} initialized occurrence owner = record
    { initialized = initialized; before = D.before occurrence; born = D.born occurrence
    ; parent = Owner.parent owner; label = D.label occurrence; prefix = D.prefix occurrence; suffix = D.suffix occurrence
    ; decomposition = D.decomposition occurrence; prefix-run = D.prefix-run occurrence; suffix-run = D.suffix-run occurrence
    ; reconstructed = reconstructed; child-matches = child-matches; descriptor = descriptor
    ; promise-allocated = recovered-promise reconstructed
    ; at-birth = at-birth; retained = Resource.retain worker captured (D.suffix-run occurrence) at-birth }
    where
    reconstructed : Located.ForkOrigin start (D.prefix occurrence) (D.before occurrence) (D.born occurrence) (Owner.parent owner) (D.label occurrence)
    reconstructed = Located.initialized-fork-origin input governor
      {start = start} {observed = D.prefix occurrence} {before = D.before occurrence} {born = D.born occurrence}
      {parent = Owner.parent owner} {label = D.label occurrence}
      initialized (D.prefix-run occurrence) (D.actual occurrence) (Owner.source owner)
    aligned : S.child (F.request reconstructed) ≡ S.child (Owner.request owner) ×
      S.handlerStart (F.entry reconstructed) (S.socketRef (F.request reconstructed)) (F.promise reconstructed) (S.key (F.request reconstructed)) ≡
      S.handlerStart (Owner.entry owner) (S.socketRef (Owner.request owner)) (Owner.promise owner) (S.key (Owner.request owner))
    aligned = row-alignment (just-injective (trans
      (sym (Selection.current-PC (F.selection reconstructed))) (Owner.before-PC owner)))
    child-matches : worker ≡ S.child (F.request reconstructed)
    child-matches = trans (Owner.worker owner) (sym (proj₁ aligned))
    descriptor : captured ≡ S.handlerStart (F.entry reconstructed) (S.socketRef (F.request reconstructed)) (F.promise reconstructed) (S.key (F.request reconstructed))
    descriptor = trans (Owner.descriptor owner) (sym (proj₂ aligned))
    at-birth : Facts worker captured (shared (D.born occurrence))
    at-birth = subst (λ queried → Facts queried captured (shared (D.born occurrence))) (sym child-matches)
      (subst (λ stored → Facts (S.child (F.request reconstructed)) stored (shared (D.born occurrence)))
        (sym descriptor) (recovered-at-birth reconstructed))

 -- This entry point is useful for an already discovered backing, including
 -- initialized profiles that genuinely permit a preloaded outbound acquisition.
 from-backing : ∀ input governor {start current events worker captured} →
   T.initialize input governor ≡ just start → Back.Backing start current events worker captured →
   InboundOrigin input governor start current events worker captured ⊎ OutboundOrigin start current events worker captured
 from-backing input governor initialized birthHistory with Label.decompose birthHistory
 ... | occurrence with D.branch occurrence
 ...   | inj₁ owner = inj₁ (recover input governor initialized occurrence owner)
 ...   | inj₂ outbound = inj₂ (record { occurrence = occurrence; physical-birth = outbound })

 -- Collected membership supplies the physical birth internally. Neither a
 -- physical lookup, fork PC nor resource certificate is an input to this API.
 record Discovery (input : O.Configuration) (governor : Governor.State)
   (start current : T.Runtime) (events : List T.Event) (worker : WorkerId) : Set where
  field
   captured : S.HandlerStart
   backing : Back.Backing start current events worker captured
   origin : InboundOrigin input governor start current events worker captured ⊎ OutboundOrigin start current events worker captured

 initialize-origin : ∀ {input governor start current events worker} →
   T.initialize input governor ≡ just start → T.Runs start events current →
   worker ∈ Close.collected (W.shutdown (R.base (Member.unwind current))) →
   Discovery input governor start current events worker
 initialize-origin {input} {governor} initialized path member with CollectedBirth.initialized-birth initialized path member
 ... | captured , birthHistory = record
   { captured = captured; backing = birthHistory; origin = from-backing input governor initialized birthHistory }

 -- Later checkpoints retain exactly this recovered occurrence and descriptor.
 append : ∀ {start prefix middle suffix current} → T.Runs start prefix middle → T.Runs middle suffix current → T.Runs start (prefix ++ suffix) current
 append T.stop rest = rest
 append (T.more actual path) rest = T.more actual (append path rest)
 extend-inbound : ∀ {input governor start middle events worker captured current tail} →
   T.Runs middle tail current → InboundOrigin input governor start middle events worker captured →
   InboundOrigin input governor start current (events ++ tail) worker captured
 extend-inbound {worker = worker} {captured = captured} {tail = tail} path origin = record
   { initialized = InboundOrigin.initialized origin; before = InboundOrigin.before origin; born = InboundOrigin.born origin
   ; parent = InboundOrigin.parent origin; label = InboundOrigin.label origin; prefix = InboundOrigin.prefix origin
   ; suffix = InboundOrigin.suffix origin ++ tail
   ; decomposition = trans (cong (_++ tail) (InboundOrigin.decomposition origin))
       (++-assoc (InboundOrigin.prefix origin) (InboundOrigin.label origin ∷ InboundOrigin.suffix origin) tail)
   ; prefix-run = InboundOrigin.prefix-run origin; suffix-run = append (InboundOrigin.suffix-run origin) path
   ; reconstructed = InboundOrigin.reconstructed origin; child-matches = InboundOrigin.child-matches origin
   ; descriptor = InboundOrigin.descriptor origin; promise-allocated = InboundOrigin.promise-allocated origin
   ; at-birth = InboundOrigin.at-birth origin
   ; retained = Resource.retain worker captured path (InboundOrigin.retained origin) }
 extend-reconstruction : ∀ {input governor start middle events worker captured current tail}
   (path : T.Runs middle tail current) (origin : InboundOrigin input governor start middle events worker captured) →
   InboundOrigin.reconstructed (extend-inbound path origin) ≡ InboundOrigin.reconstructed origin
 extend-reconstruction path origin = refl
 execution : ∀ {input governor start current events worker captured} →
   InboundOrigin input governor start current events worker captured → T.Runs start events current
 execution {start = start} {current = current} origin = subst (λ events → T.Runs start events current) (sym (InboundOrigin.decomposition origin))
   (append (InboundOrigin.prefix-run origin) (T.more (F.fork-event (InboundOrigin.reconstructed origin)) (InboundOrigin.suffix-run origin)))
