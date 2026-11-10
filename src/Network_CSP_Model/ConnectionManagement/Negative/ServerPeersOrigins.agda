{-# OPTIONS --guardedness #-}

-- Dependent origin acceptance reuses the complete ServerPeers suite through
-- its checked interface, keeping the combined elaboration footprint bounded.
module ConnectionManagement.Negative.ServerPeersOrigins where

open import ConnectionManagement.Negative.ServerPeers using (module Protocols)

-- Increment61: the collected endpoint discovers the birth itself; the explicit
-- same-event Backing controls isolate positive branch recovery from search cost.
module CollectedInboundOriginChecks where
  open import Data.Bool using (false)
  open import Data.List using (List; []; _∷_; _++_; take; drop; map)
  open import Data.Maybe using (just; nothing)
  open import Data.Product using (Σ; _,_; proj₁)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Unit using (⊤; tt)
  open import Data.Empty using (⊥)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
  open import ConnectionManagement.Domain hiding (worker; local; mux; job)
  open import ConnectionManagement.Store using (lookup)
  import ConnectionManagement.State as Shared
  import ConnectionManagement.Machine as Machine
  import ConnectionManagement.OutboundMachine as O
  import ConnectionManagement.HandlerSupervision as H
  import ConnectionManagement.OutboundHandlerSupervision as B
  import ConnectionManagement.ServerPeers as Combined
  import ConnectionManagement.ServerAdmission as Server
  import ConnectionManagement.ServerIGExit as Exit
  import ConnectionManagement.MuxPublicationUnwind as Publication
  import ConnectionManagement.MuxStartupUnwind as Unwind
  import ConnectionManagement.MuxHandlerExit as Physical
  import ConnectionManagement.Rules.Server as Admission
  import ConnectionManagement.Rules.CMShutdown as Close
  import ConnectionManagement.Scenarios.Admission as A
  import ConnectionManagement.CSP.GovernorLifecycle as L
  import ConnectionManagement.Negative.GovernorPool as Prior
  import ConnectionManagement.Negative.ServerAdmissionPrefixFixtures as Prefix
  import ConnectionManagement.Negative.ServerIGExitRelease as Render
  import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
  import ConnectionManagement.Properties.HandlerBirthBacking as Birth
  import ConnectionManagement.Properties.HandlerBirthEffects as BirthEffects
  import ConnectionManagement.Properties.ServerPeersHandlerResources as Resources
  import ConnectionManagement.Properties.ServerPeersMonitorJoins as JoinModel
  import ConnectionManagement.Properties.CollectedInboundOrigin as OriginModel
  import ConnectionManagement.Properties.InboundOriginRuntime as RuntimeModel
  import ConnectionManagement.Properties.HandlerResourceFacts as ResourceFacts
  private
    module Parent = Protocols using (capability; initial; initializer; wrap; prefixActions)
    module Old = Protocols.HandlerResourceOriginChecks using (beforeAllocation; forkPrefix; entryPrefix; initialized-entry)
    module Gap = Protocols.InboundTwoGapOriginChecks using (gapAllocated; gapAfterClock; gapSelected; gapBeforeFork; gapBorn; gapAllocateEvent; gapSelectEvent; gapForkEvent; clockGapEvent; timerGapEvent; gapAllocation; clockBetweenAllocationAndSelection; gapSelection; timerBetweenSelectionAndFork; gapFork; twoGapEvents; earlyBridgeEvents; gapBirthToCMEntry; finalPhysicalDescriptor)
    module Wait = Protocols.CMResultLifecycleChecks using (poolActions; catchActions; finalizerActions; actual-pool-path; actual-catch-path; actual-finalizer-path; no-wait-at-receipt; no-wait-before-publication)
    module D = Protocols.Reactivation.Shutdown using (cmEntry; receipt1; receipt2; receipt3; receipt4; receipt5; receiptEdge1; receiptEdge2; receiptEdge3; receiptEdge4; receiptEdge5; shutdownError; handler9; handler10; finalCM; handlerFinishEdge11)
    module Pre = Protocols.PreloadedAcquisitionForkControl using (seededConfiguration; preloadedStart; preloadedForked; preloadedInitializer; preloadedForkEvent; preloadedActualFork; preloadedForkRun; preloadedPhysicalDescriptor; preCaller; preChild; preDescriptor; preloadedResourcesImpossible; missingCapturedPromise; forkHasNotCollected; missingEntryPreventsLowerCommit; forkedWorld; ordinaryImmediateForkRefused)
    module K = Combined I.bearerClosed Prior.classify using (coreStep; server)
    module V = Combined.Protocols I.bearerClosed Prior.classify Parent.capability using (Runtime; Event; Runs; advance; dispatch; base; more; stop)
    module S = Server I.bearerClosed using (State; base)
    module E = Exit I.bearerClosed using (base)
    module N = Publication I.bearerClosed using (raw)
    module R = Unwind I.bearerClosed using (base)
    module W = Physical I.bearerClosed using (shutdown; shutdownStep; deliverShutdownMux; publishAsyncResult)
    module F = Prefix 10 A.key₁ using (empty; p2; p3; p4; p5)
    module Drop = Resources.Frontend I.bearerClosed Prior.classify Parent.capability using (event; discard-prefix)
    module Join = JoinModel.Frontend I.bearerClosed Prior.classify Parent.capability using (handler-event; server-event; server-runs)
    module Back = Birth.Frontend I.bearerClosed Prior.classify Parent.capability using (Backing; ForkStep; Selected; chosen-birth; inherited-birth; actual-fork; execution; view; physical-state; initialized-birth; capture-of-found)
    module Origin = OriginModel.Frontend I.bearerClosed Prior.classify Parent.capability using (InboundOrigin; OutboundOrigin; Discovery; initialize-origin; from-backing; extend-inbound; extend-reconstruction; execution; shared; append)
    module Found = OriginModel.Frontend.Discovery using (captured; backing; origin)
    module Inbound = OriginModel.Frontend.InboundOrigin using (before; born; parent; reconstructed; retained; label; prefix; suffix; decomposition)
    module Located = RuntimeModel.Frontend.Located I.bearerClosed Prior.classify Parent.capability using (ForkOrigin)

  inputConfig : O.Configuration
  inputConfig = O.initial (Machine.initial Shared.responderMode F.empty)
  plain : S.State → V.Runtime
  plain s = Parent.wrap (Render.base s)
  coreEvent : Admission.AdmissionAction → V.Event
  coreEvent action = V.dispatch (K.coreStep (O.inbound (Machine.admissionStep A.w₀ action)))
  coreAllocation : V.advance (coreEvent Admission.allocatePromise) (plain F.p2) ≡ just (plain F.p3)
  coreAllocation = refl
  coreSelection : V.advance (coreEvent Admission.chooseEntry) (plain F.p3) ≡ just (plain F.p4)
  coreSelection = refl
  coreFork : V.advance (coreEvent Admission.fork) (plain F.p4) ≡ just (plain F.p5)
  coreFork = refl
  coreGapSelection : V.advance (coreEvent Admission.chooseEntry) Gap.gapAfterClock ≡ just Gap.gapSelected
  coreGapSelection = refl
  coreGapFork : V.advance (coreEvent Admission.fork) Gap.gapBeforeFork ≡ just Gap.gapBorn
  coreGapFork = refl

  data Route : Set where
    canonicalEmpty coreEmpty canonicalGapped coreGapped : Route
  beforeFork bornAt : Route → V.Runtime
  beforeFork canonicalEmpty = plain F.p4
  beforeFork coreEmpty = plain F.p4
  beforeFork canonicalGapped = Gap.gapBeforeFork
  beforeFork coreGapped = Gap.gapBeforeFork
  bornAt canonicalEmpty = plain F.p5
  bornAt coreEmpty = plain F.p5
  bornAt canonicalGapped = Gap.gapBorn
  bornAt coreGapped = Gap.gapBorn
  forkEvent : Route → V.Event
  forkEvent canonicalEmpty = Drop.event A.w₀ Admission.fork
  forkEvent coreEmpty = coreEvent Admission.fork
  forkEvent canonicalGapped = Drop.event A.w₀ Admission.fork
  forkEvent coreGapped = coreEvent Admission.fork
  observed : Route → List V.Event
  observed canonicalEmpty = take 6 Parent.prefixActions
  observed coreEmpty = take 4 Parent.prefixActions ++ (coreEvent Admission.allocatePromise ∷ coreEvent Admission.chooseEntry ∷ [])
  observed canonicalGapped = take 4 Parent.prefixActions ++
    (Gap.gapAllocateEvent ∷ Gap.clockGapEvent ∷ Gap.gapSelectEvent ∷ Gap.timerGapEvent ∷ [])
  observed coreGapped = take 4 Parent.prefixActions ++
    (coreEvent Admission.allocatePromise ∷ Gap.clockGapEvent ∷ coreEvent Admission.chooseEntry ∷ Gap.timerGapEvent ∷ [])
  birthEvents : Route → List V.Event
  birthEvents route = observed route ++ (forkEvent route ∷ [])
  actualFork : ∀ route → V.advance (forkEvent route) (beforeFork route) ≡ just (bornAt route)
  actualFork canonicalEmpty = Protocols.p7
  actualFork coreEmpty = coreFork
  actualFork canonicalGapped = Gap.gapFork
  actualFork coreGapped = coreGapFork
  abstract
    prefixRun : ∀ route → V.Runs Parent.initial (observed route) (beforeFork route)
    prefixRun canonicalEmpty = Origin.append Old.beforeAllocation (V.more Protocols.p5 (V.more Protocols.p6 V.stop))
    prefixRun coreEmpty = Origin.append Old.beforeAllocation (V.more coreAllocation (V.more coreSelection V.stop))
    prefixRun canonicalGapped = Origin.append Old.beforeAllocation
      (V.more Gap.gapAllocation (V.more Gap.clockBetweenAllocationAndSelection
        (V.more Gap.gapSelection (V.more Gap.timerBetweenSelectionAndFork V.stop))))
    prefixRun coreGapped = Origin.append Old.beforeAllocation
      (V.more coreAllocation (V.more Gap.clockBetweenAllocationAndSelection
        (V.more coreGapSelection (V.more Gap.timerBetweenSelectionAndFork V.stop))))
    birthRun : ∀ route → V.Runs Parent.initial (birthEvents route) (bornAt route)
    birthRun route = Origin.append (prefixRun route) (V.more (actualFork route) V.stop)

  entryTail : Route → List V.Event
  entryTail canonicalEmpty = drop 7 Old.entryPrefix
  entryTail coreEmpty = drop 7 Old.entryPrefix
  entryTail canonicalGapped = Gap.earlyBridgeEvents ++ drop 22 Old.entryPrefix
  entryTail coreGapped = Gap.earlyBridgeEvents ++ drop 22 Old.entryPrefix
  receiptEvents afterReceiptEvents waitEvents : List V.Event
  receiptEvents = Join.handler-event (W.shutdownStep Close.captureSnapshot) ∷
    Join.handler-event (W.shutdownStep Close.readEntry) ∷
    Join.handler-event (W.shutdownStep Close.requestCancellation) ∷
    Join.handler-event (W.deliverShutdownMux D.shutdownError) ∷ []
  afterReceiptEvents = Join.handler-event (W.shutdownStep Close.finishTraversal) ∷
    (map Join.server-event Wait.poolActions ++
      (map Join.server-event Wait.catchActions ++ map Join.server-event Wait.finalizerActions))
  waitEvents = Join.handler-event (W.shutdownStep Close.finishClose) ∷ []
  abstract
    birthToEntry : ∀ route → V.Runs (bornAt route) (entryTail route) D.cmEntry
    birthToEntry canonicalEmpty = Drop.discard-prefix {suffix = drop 7 Old.entryPrefix} Old.forkPrefix Old.initialized-entry
    birthToEntry coreEmpty = birthToEntry canonicalEmpty
    birthToEntry canonicalGapped = Gap.gapBirthToCMEntry
    birthToEntry coreGapped = Gap.gapBirthToCMEntry
    entryToReceipt : V.Runs D.cmEntry receiptEvents D.receipt4
    entryToReceipt = V.more D.receiptEdge1 (V.more D.receiptEdge2 (V.more D.receiptEdge3 (V.more D.receiptEdge4 V.stop)))
    receiptToPublication : V.Runs D.receipt4 afterReceiptEvents D.handler10
    receiptToPublication = V.more D.receiptEdge5
      (Origin.append (Join.server-runs Wait.actual-pool-path)
        (Origin.append (Join.server-runs Wait.actual-catch-path) (Join.server-runs Wait.actual-finalizer-path)))
    publicationToWait : V.Runs D.handler10 waitEvents D.finalCM
    publicationToWait = V.more D.handlerFinishEdge11 V.stop

  receiptIndex publicationIndex finalIndex : Route → List V.Event
  receiptIndex route = (birthEvents route ++ entryTail route) ++ receiptEvents
  publicationIndex route = receiptIndex route ++ afterReceiptEvents
  finalIndex route = publicationIndex route ++ waitEvents
  abstract
    atReceiptRun : ∀ route → V.Runs Parent.initial (receiptIndex route) D.receipt4
    atReceiptRun route = Origin.append (Origin.append (birthRun route) (birthToEntry route)) entryToReceipt
    atPublicationRun : ∀ route → V.Runs Parent.initial (publicationIndex route) D.handler10
    atPublicationRun route = Origin.append (atReceiptRun route) receiptToPublication
    atWaitRun : ∀ route → V.Runs Parent.initial (finalIndex route) D.finalCM
    atWaitRun route = Origin.append (atPublicationRun route) publicationToWait

  coordinator : V.Runtime → Close.State
  coordinator state = W.shutdown (R.base (N.raw (S.base (E.base (K.server (V.base state))))))
  collectedAtReceipt : A.child₀ ∈ Close.collected (coordinator D.receipt4)
  collectedAtReceipt = here refl
  collectedAtPublication : A.child₀ ∈ Close.collected (coordinator D.handler10)
  collectedAtPublication = here refl
  collectedAtWait : A.child₀ ∈ Close.collected (coordinator D.finalCM)
  collectedAtWait = here refl
  abstract
    closedAtReceipt : ∀ route → Origin.Discovery inputConfig L.settings Parent.initial D.receipt4 (receiptIndex route) A.child₀
    closedAtReceipt route = Origin.initialize-origin Parent.initializer (atReceiptRun route) collectedAtReceipt
    closedAtPublication : ∀ route → Origin.Discovery inputConfig L.settings Parent.initial D.handler10 (publicationIndex route) A.child₀
    closedAtPublication route = Origin.initialize-origin Parent.initializer (atPublicationRun route) collectedAtPublication
    closedAtWait : ∀ route → Origin.Discovery inputConfig L.settings Parent.initial D.finalCM (finalIndex route) A.child₀
    closedAtWait route = Origin.initialize-origin Parent.initializer (atWaitRun route) collectedAtWait

  physicalAtReceipt : lookup A.child₀ (B.threads (Back.physical-state D.receipt4)) ≡ just (H.handlerThread I.captured H.handshaking)
  physicalAtReceipt = refl
  physicalAtPublication : lookup A.child₀ (B.threads (Back.physical-state D.handler10)) ≡ just (H.handlerThread I.captured H.handshaking)
  physicalAtPublication = refl
  descriptorAtReceipt : ∀ route → Found.captured (closedAtReceipt route) ≡ I.captured
  descriptorAtReceipt route = sym (Back.capture-of-found (Found.backing (closedAtReceipt route)) physicalAtReceipt)
  descriptorAtPublication : ∀ route → Found.captured (closedAtPublication route) ≡ I.captured
  descriptorAtPublication route = sym (Back.capture-of-found (Found.backing (closedAtPublication route)) physicalAtPublication)
  descriptorAtWait : ∀ route → Found.captured (closedAtWait route) ≡ I.captured
  descriptorAtWait route = sym (Back.capture-of-found (Found.backing (closedAtWait route)) Gap.finalPhysicalDescriptor)

  prematureAtReceipt : V.advance (Join.handler-event (W.shutdownStep Close.finishClose)) D.receipt5 ≡ nothing
  prematureAtReceipt = Wait.no-wait-at-receipt
  prematureBeforePublication : V.advance (Join.handler-event (W.shutdownStep Close.finishClose)) D.handler9 ≡ nothing
  prematureBeforePublication = Wait.no-wait-before-publication
  duplicateReceipt : V.advance (Join.handler-event (W.deliverShutdownMux D.shutdownError)) D.receipt4 ≡ nothing
  duplicateReceipt = refl
  duplicatePublication : V.advance (Join.handler-event (W.publishAsyncResult A.child₀)) D.handler10 ≡ nothing
  duplicatePublication = refl

  -- Selection tags certify only the actual chosen wrappers. No source PC or
  -- allocation/resource certificate is supplied to the new recovery API.
  private
    module MuxTag = BirthEffects.MuxLayer using (inherited-birth)
    module JobTag = BirthEffects.ProtocolLayer using (inherited-birth)
    module MonitorTag = BirthEffects.MonitorLayer I.bearerClosed using (inherited-birth)
    module GroupTag = BirthEffects.GroupLayer I.bearerClosed using (inherited-birth)
    module ExitTag = BirthEffects.ExitLayer I.bearerClosed using (chosen-birth; inherited-plan)
    module CancelTag = BirthEffects.CancellationLayer I.bearerClosed using (inherited-birth)
    module UnwindTag = BirthEffects.UnwindLayer I.bearerClosed using (chosen-birth; inherited-plan)
    module DeltaTag = BirthEffects.DeltaQLayer I.bearerClosed using (inherited-birth)
    module CatchTag = BirthEffects.CatchLayer I.bearerClosed using (inherited-birth)
    module PublicationTag = BirthEffects.PublicationLayer I.bearerClosed using (inherited-birth)
    module ServerTag = BirthEffects.ServerLayer I.bearerClosed using (inherited-birth)
    module IGTag = BirthEffects.IGExitLayer I.bearerClosed using (chosen-birth; delegated-birth)
    module SharedTag = BirthEffects.SharedLayer I.bearerClosed Prior.classify using (server-birth; core-birth)
  selectedFork : ∀ route → Back.Selected (forkEvent route) (beforeFork route)
  selectedFork canonicalEmpty = Back.chosen-birth refl (Back.inherited-birth (SharedTag.server-birth (IGTag.chosen-birth refl (IGTag.delegated-birth (ServerTag.inherited-birth (PublicationTag.inherited-birth (CatchTag.inherited-birth (DeltaTag.inherited-birth (UnwindTag.chosen-birth refl (UnwindTag.inherited-plan (CancelTag.inherited-birth (ExitTag.chosen-birth refl (ExitTag.inherited-plan (GroupTag.inherited-birth (MonitorTag.inherited-birth (JobTag.inherited-birth (MuxTag.inherited-birth (BirthEffects.inbound-physical A.w₀))))))))))))))))))
  selectedFork coreEmpty = Back.chosen-birth refl (Back.inherited-birth (SharedTag.core-birth (IGTag.chosen-birth refl (IGTag.delegated-birth (ServerTag.inherited-birth (PublicationTag.inherited-birth (CatchTag.inherited-birth (DeltaTag.inherited-birth (UnwindTag.chosen-birth refl (UnwindTag.inherited-plan (CancelTag.inherited-birth (ExitTag.chosen-birth refl (ExitTag.inherited-plan (GroupTag.inherited-birth (MonitorTag.inherited-birth (JobTag.inherited-birth (MuxTag.inherited-birth (BirthEffects.inbound-physical A.w₀))))))))))))))))))
  selectedFork canonicalGapped = Back.chosen-birth refl (Back.inherited-birth (SharedTag.server-birth (IGTag.chosen-birth refl (IGTag.delegated-birth (ServerTag.inherited-birth (PublicationTag.inherited-birth (CatchTag.inherited-birth (DeltaTag.inherited-birth (UnwindTag.chosen-birth refl (UnwindTag.inherited-plan (CancelTag.inherited-birth (ExitTag.chosen-birth refl (ExitTag.inherited-plan (GroupTag.inherited-birth (MonitorTag.inherited-birth (JobTag.inherited-birth (MuxTag.inherited-birth (BirthEffects.inbound-physical A.w₀))))))))))))))))))
  selectedFork coreGapped = Back.chosen-birth refl (Back.inherited-birth (SharedTag.core-birth (IGTag.chosen-birth refl (IGTag.delegated-birth (ServerTag.inherited-birth (PublicationTag.inherited-birth (CatchTag.inherited-birth (DeltaTag.inherited-birth (UnwindTag.chosen-birth refl (UnwindTag.inherited-plan (CancelTag.inherited-birth (ExitTag.chosen-birth refl (ExitTag.inherited-plan (GroupTag.inherited-birth (MonitorTag.inherited-birth (JobTag.inherited-birth (MuxTag.inherited-birth (BirthEffects.inbound-physical A.w₀))))))))))))))))))

  absentBeforeFork : ∀ route → lookup A.child₀ (Back.view (beforeFork route)) ≡ nothing
  absentBeforeFork canonicalEmpty = refl
  absentBeforeFork coreEmpty = refl
  absentBeforeFork canonicalGapped = refl
  absentBeforeFork coreGapped = refl
  captureAtBirth : ∀ route → lookup A.child₀ (Back.view (bornAt route)) ≡ just I.captured
  captureAtBirth canonicalEmpty = refl
  captureAtBirth coreEmpty = refl
  captureAtBirth canonicalGapped = refl
  captureAtBirth coreGapped = refl
  IsInbound : ∀ {X Y : Set} → X ⊎ Y → Set
  IsInbound (inj₁ origin) = ⊤
  IsInbound (inj₂ origin) = ⊥
  takeInbound : ∀ {X Y : Set} (choice : X ⊎ Y) → IsInbound choice → X
  takeInbound (inj₁ origin) proof = origin
  takeInbound (inj₂ origin) ()
  IsOutbound : ∀ {X Y : Set} → X ⊎ Y → Set
  IsOutbound (inj₁ origin) = ⊥
  IsOutbound (inj₂ origin) = ⊤
  takeOutbound : ∀ {X Y : Set} (choice : X ⊎ Y) → IsOutbound choice → Y
  takeOutbound (inj₁ origin) ()
  takeOutbound (inj₂ origin) proof = origin

  -- Package the reconstruction WITH all dependent indices. The uniform type
  -- allows identity across opaque packets without silently equating their
  -- separately projected prefix/before/born/parent/label indices.
  record BirthPacket : Set where
    field
      prefix : List V.Event
      before born : V.Runtime
      parent : WorkerId
      label : V.Event
      reconstructed : Located.ForkOrigin Parent.initial prefix before born parent label
  packet : ∀ {current events} → Origin.InboundOrigin inputConfig L.settings Parent.initial
    current events A.child₀ I.captured → BirthPacket
  packet origin = record
    { prefix = Inbound.prefix origin; before = Inbound.before origin; born = Inbound.born origin
    ; parent = Inbound.parent origin; label = Inbound.label origin; reconstructed = Inbound.reconstructed origin }

  -- Prove field-copy once on VARIABLES. Concrete lifecycle laws apply this
  -- theorem instead of comparing two materialized recovered origins by refl.
  packet-copy : ∀ {before after events tail}
    (path : V.Runs before tail after)
    (origin : Origin.InboundOrigin inputConfig L.settings Parent.initial before events A.child₀ I.captured) →
    packet (Origin.extend-inbound path origin) ≡ packet origin
  packet-copy path origin = refl

  -- The location is built from the ORIGINAL opaque prefix and ORIGINAL actual
  -- fork. Its operation is the existing inversion of exactly that selected event.
  -- Consequently classifying this packet never searches the prefix proof.
  -- This named child is a genuine abstraction boundary: parent extension
  -- proofs cannot unfold its abstract birth-recovery definitions.
  module BirthPackets where
    abstract
      explicitBacking : ∀ route → Back.Backing Parent.initial (bornAt route) (birthEvents route) A.child₀ I.captured
      explicitBacking route = record
        { location = record
          { before = beforeFork route; after = bornAt route; action = forkEvent route
          ; prefix = observed route; suffix = []; decomposition = refl
          ; prefix-run = Back.execution (prefixRun route); actual = actualFork route; selected = selectedFork route
          ; absent-before = absentBeforeFork route; at-birth = captureAtBirth route
          ; suffix-run = Back.execution V.stop; retained-descriptor = captureAtBirth route }
        ; operation = Back.actual-fork (forkEvent route) (beforeFork route) (actualFork route) (selectedFork route)
        ; selected-operation = refl
        ; at-physical-fork = trans
          (cong (lookup A.child₀) (Back.ForkStep.captures-after
            (Back.actual-fork (forkEvent route) (beforeFork route) (actualFork route) (selectedFork route))))
          (captureAtBirth route) }
      classifiedAtBirth : ∀ route →
        Origin.InboundOrigin inputConfig L.settings Parent.initial (bornAt route) (birthEvents route) A.child₀ I.captured ⊎
        Origin.OutboundOrigin Parent.initial (bornAt route) (birthEvents route) A.child₀ I.captured
      classifiedAtBirth route = Origin.from-backing inputConfig L.settings Parent.initializer (explicitBacking route)
      inboundBranchAtBirth : ∀ route → IsInbound (classifiedAtBirth route)
      inboundBranchAtBirth canonicalEmpty = tt
      inboundBranchAtBirth coreEmpty = tt
      inboundBranchAtBirth canonicalGapped = tt
      inboundBranchAtBirth coreGapped = tt
      sameInboundAtBirth : ∀ route → Origin.InboundOrigin inputConfig L.settings Parent.initial
        (bornAt route) (birthEvents route) A.child₀ I.captured
      sameInboundAtBirth route = takeInbound (classifiedAtBirth route) (inboundBranchAtBirth route)
  open BirthPackets public using (explicitBacking; classifiedAtBirth; inboundBranchAtBirth; sameInboundAtBirth)

  -- Compose the generic copy law for later checkpoints; each proof uses
  -- existing packet identities instead of reducing the discovery body.
  abstract
    sameInboundAtEntry : ∀ route → Origin.InboundOrigin inputConfig L.settings Parent.initial
      D.cmEntry (birthEvents route ++ entryTail route) A.child₀ I.captured
    sameInboundAtEntry route = Origin.extend-inbound (birthToEntry route) (sameInboundAtBirth route)
    sameInboundAtReceipt : ∀ route → Origin.InboundOrigin inputConfig L.settings Parent.initial
      D.receipt4 (receiptIndex route) A.child₀ I.captured
    sameInboundAtReceipt route = Origin.extend-inbound entryToReceipt (sameInboundAtEntry route)
    sameInboundAtPublication : ∀ route → Origin.InboundOrigin inputConfig L.settings Parent.initial
      D.handler10 (publicationIndex route) A.child₀ I.captured
    sameInboundAtPublication route = Origin.extend-inbound receiptToPublication (sameInboundAtReceipt route)
    sameInboundAtWait : ∀ route → Origin.InboundOrigin inputConfig L.settings Parent.initial
      D.finalCM (finalIndex route) A.child₀ I.captured
    sameInboundAtWait route = Origin.extend-inbound publicationToWait (sameInboundAtPublication route)
    sameReconstructionAtEntry : ∀ route → packet (sameInboundAtEntry route) ≡ packet (sameInboundAtBirth route)
    sameReconstructionAtEntry route = packet-copy (birthToEntry route) (sameInboundAtBirth route)
    sameReconstructionAtReceipt : ∀ route → packet (sameInboundAtReceipt route) ≡ packet (sameInboundAtBirth route)
    sameReconstructionAtReceipt route = trans
      (packet-copy entryToReceipt (sameInboundAtEntry route)) (sameReconstructionAtEntry route)
    sameReconstructionAtPublication : ∀ route → packet (sameInboundAtPublication route) ≡ packet (sameInboundAtBirth route)
    sameReconstructionAtPublication route = trans
      (packet-copy receiptToPublication (sameInboundAtReceipt route)) (sameReconstructionAtReceipt route)
    sameReconstructionAtWait : ∀ route → packet (sameInboundAtWait route) ≡ packet (sameInboundAtBirth route)
    sameReconstructionAtWait route = trans
      (packet-copy publicationToWait (sameInboundAtPublication route)) (sameReconstructionAtPublication route)
    sameOriginalLabel : ∀ route → Inbound.label (sameInboundAtWait route) ≡ Inbound.label (sameInboundAtBirth route)
    sameOriginalLabel route = cong BirthPacket.label (sameReconstructionAtWait route)
    sameOriginalPrefix : ∀ route → Inbound.prefix (sameInboundAtWait route) ≡ Inbound.prefix (sameInboundAtBirth route)
    sameOriginalPrefix route = cong BirthPacket.prefix (sameReconstructionAtWait route)

  -- Explicit output types keep resource transports outside opaque constructors.
  fixedResourcesAtReceipt : ∀ route → ResourceFacts.Facts A.child₀ I.captured (Origin.shared D.receipt4)
  fixedResourcesAtReceipt route = Inbound.retained (sameInboundAtReceipt route)
  fixedResourcesAtPublication : ∀ route → ResourceFacts.Facts A.child₀ I.captured (Origin.shared D.handler10)
  fixedResourcesAtPublication route = Inbound.retained (sameInboundAtPublication route)
  fixedResourcesAtWait : ∀ route → ResourceFacts.Facts A.child₀ I.captured (Origin.shared D.finalCM)
  fixedResourcesAtWait route = Inbound.retained (sameInboundAtWait route)
  exactSameExecution : ∀ route → V.Runs Parent.initial (finalIndex route) D.finalCM
  exactSameExecution route = Origin.execution (sameInboundAtWait route)

  -- Preloaded outbound acquisition is a real initialized physical birth with
  -- missing captured resources. It is classified, never forced into inbound.
  preloadedSelected : Back.Selected Pre.preloadedForkEvent Pre.preloadedStart
  preloadedSelected = Back.chosen-birth refl (Back.inherited-birth (SharedTag.core-birth (IGTag.chosen-birth refl (IGTag.delegated-birth (ServerTag.inherited-birth (PublicationTag.inherited-birth (CatchTag.inherited-birth (DeltaTag.inherited-birth (UnwindTag.chosen-birth refl (UnwindTag.inherited-plan (CancelTag.inherited-birth (ExitTag.chosen-birth refl (ExitTag.inherited-plan (GroupTag.inherited-birth (MonitorTag.inherited-birth (JobTag.inherited-birth (MuxTag.inherited-birth (BirthEffects.outbound-physical Pre.preCaller))))))))))))))))))
  abstract
    preloadedExplicitBacking : Back.Backing Pre.preloadedStart Pre.preloadedForked
      (Pre.preloadedForkEvent ∷ []) Pre.preChild Pre.preDescriptor
    preloadedExplicitBacking = record
      { location = record
        { before = Pre.preloadedStart; after = Pre.preloadedForked; action = Pre.preloadedForkEvent
        ; prefix = []; suffix = []; decomposition = refl
        ; prefix-run = Back.execution V.stop; actual = Pre.preloadedActualFork; selected = preloadedSelected
        ; absent-before = refl; at-birth = refl; suffix-run = Back.execution V.stop; retained-descriptor = refl }
      ; operation = Back.actual-fork Pre.preloadedForkEvent Pre.preloadedStart Pre.preloadedActualFork preloadedSelected
      ; selected-operation = refl
      ; at-physical-fork = trans
        (cong (lookup Pre.preChild) (Back.ForkStep.captures-after
          (Back.actual-fork Pre.preloadedForkEvent Pre.preloadedStart Pre.preloadedActualFork preloadedSelected))) refl }
    classifiedPreloaded :
      Origin.InboundOrigin Pre.seededConfiguration L.settings Pre.preloadedStart Pre.preloadedForked
        (Pre.preloadedForkEvent ∷ []) Pre.preChild Pre.preDescriptor ⊎
      Origin.OutboundOrigin Pre.preloadedStart Pre.preloadedForked
        (Pre.preloadedForkEvent ∷ []) Pre.preChild Pre.preDescriptor
    classifiedPreloaded = Origin.from-backing Pre.seededConfiguration L.settings Pre.preloadedInitializer preloadedExplicitBacking
    genuineOutboundBranch : IsOutbound classifiedPreloaded
    genuineOutboundBranch = tt
    preloadedOutboundOccurrence : Origin.OutboundOrigin Pre.preloadedStart Pre.preloadedForked
      (Pre.preloadedForkEvent ∷ []) Pre.preChild Pre.preDescriptor
    preloadedOutboundOccurrence = takeOutbound classifiedPreloaded genuineOutboundBranch
  noUnconditionalPreloadedResources : ResourceFacts.Facts Pre.preChild Pre.preDescriptor Pre.forkedWorld → ⊥
  noUnconditionalPreloadedResources = Pre.preloadedResourcesImpossible
  preloadedRemainsUncollected : Close.collected (coordinator Pre.preloadedForked) ≡ []
  preloadedRemainsUncollected = Pre.forkHasNotCollected

-- Increment62: the explicit O.initial profile closes outbound origins.
module CollectedOutboundOriginChecks where
  open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
  open import Data.List using (List; []; _∷_; _++_; take; drop)
  open import Data.Maybe using (just; nothing)
  open import Data.Product using (_,_)
  open import Data.Empty using (⊥)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Unit using (⊤; tt)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
  open import ConnectionManagement.Domain using (WorkerId; ident; local)
  open import ConnectionManagement.Store using (lookup)
  import ConnectionManagement.State as Shared
  import ConnectionManagement.Machine as Machine
  import ConnectionManagement.OutboundMachine as O
  import ConnectionManagement.HandlerSupervision as H
  import ConnectionManagement.OutboundHandlerSupervision as B
  import ConnectionManagement.ServerPeers as Combined
  import ConnectionManagement.MuxHandlerExit as Physical
  import ConnectionManagement.Rules.OutboundAcquire as Acquire
  import ConnectionManagement.Rules.CMShutdown as Close
  import ConnectionManagement.Rules.IGRegistration as IG
  import ConnectionManagement.Scenarios.Admission as A
  import ConnectionManagement.CSP.GovernorLifecycle as L
  import ConnectionManagement.CSP.OutboundAdmission as OA
  import ConnectionManagement.Negative.OutboundHandlerSupervision as OB
  import ConnectionManagement.Negative.GovernorPool as Prior
  import ConnectionManagement.Negative.ServerAdmissionPrefixFixtures as Prefix
  import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
  import ConnectionManagement.Properties.ServerPeersHandlerResources as Resources
  import ConnectionManagement.Properties.ServerPeersMonitorJoins as Joins
  import ConnectionManagement.Properties.HandlerBirthBacking as Birth
  import ConnectionManagement.Properties.HandlerBirthEffects as BirthEffects
  import ConnectionManagement.Properties.HandlerResourceFacts as Facts
  import ConnectionManagement.Properties.CollectedOutboundOrigin as OriginModel
  import ConnectionManagement.Properties.CollectedInboundOrigin as InboundModel

  private
    module Parent = Protocols using (capability)
    module Out = Protocols.OutboundHandlerResourceOriginChecks using (start; outbound-initialized; outbound3; outbound4; outbound5; outbound6; outbound7; outbound8; outbound9; outbound10; outbound11; outbound15; outbound16; outbound24; outbound25; outbound26; outbound27; outbound28; outbound-scope18; outbound-finalizer-events; call; edge1; edge2; edge3; edge4; edge5; edge6; edge7; edge8; edge9; edge10; child-enters; edge16; edge26; edge27; edge28; through-cleanup; cleanup-events; waiting-before-publication; early-fork-refused; early-publication-refused; early-wait-refused; duplicate-publication-refused)
    module Mixed = Protocols.OutboundHandlerResourceOriginChecks.Interference using (mixed; clock-view; mixed-prefix-events; mixed-route-events; mixed-prefix; mixed-allocation; mixed-route; mixed-edge10; mixed-child-enters; mixed-open; mixed-edge6; mixed-edge7; mixed-edge8; mixed-edge9; raw-acquisition-alias-refused; premature-mixed-fork-refused)
    module Known = Protocols.HandlerBirthBackingChecks using (outbound-birth-events; outbound-birth-path)
    module Shutdown = Protocols.HandlerBirthBackingChecks.ShutdownBatch using (before-scope-events; before-scope-run; delivered-prefix; cleanup-after-ack-events; cleanup-after-ack)
    module Pre = Protocols.PreloadedAcquisitionForkControl using (seededConfiguration; seededCore; ordinaryConfiguration; ordinaryImmediateForkRefused; preloadedStart; preloadedForked; preloadedForkEvent; preloadedActualFork; preloadedInitializer; ordinaryStart; ordinaryInitializer; forkedWorld; preChild; preDescriptor; preloadedResourcesImpossible; forkHasNotCollected; missingEntryPreventsLowerCommit)
    module K = Combined I.bearerClosed Prior.classify using (coreStep)
    module V = Combined.Protocols I.bearerClosed Prior.classify Parent.capability using (Runtime; Event; Runs; advance; more; stop; initialize; dispatch)
    module W = Physical I.bearerClosed using (shutdown; shutdownStep)
    module F = Prefix 10 A.key₁ using (empty)
    module Resource = Resources.Frontend I.bearerClosed Prior.classify Parent.capability using (call-event; acquireCall; handler-event; outbound-physical-action; discard-prefix; shared)
    module Join = Joins.Frontend I.bearerClosed Prior.classify Parent.capability using (physical; handler-event)
    module Back = Birth.Frontend I.bearerClosed Prior.classify Parent.capability using (Backing; ForkStep; Selected; chosen-birth; inherited-birth; actual-fork; execution; view; physical-state; capture-of-found)
    module Origin = OriginModel.Frontend I.bearerClosed Prior.classify Parent.capability using (OutboundOrigin; Discovery; BirthPacket; from-backing; initialize-origin; extend-outbound; extend-packet; execution; shared)
    module Inbound = InboundModel.Frontend I.bearerClosed Prior.classify Parent.capability using (InboundOrigin)
    module Found = OriginModel.Frontend.Discovery using (captured; backing; origin)
    module Outbound = OriginModel.Frontend.OutboundOrigin using (packet; retained)
    module Packet = OriginModel.Frontend.BirthPacket using (label; prefix; reconstructed; promise-allocated; at-birth)


  inputCore : Machine.Configuration
  inputCore = Machine.initial Shared.responderMode F.empty
  ordinaryInitialized : V.initialize (O.initial inputCore) L.settings ≡ just Out.start
  ordinaryInitialized = Out.outbound-initialized

  -- Empty/nonempty here refer to unrelated interference, not omission of the
  -- mandatory open/configure/connect/address operations between allocation/fork.
  data Route : Set where
    ordinary interfering coreGap : Route
  beforeFork bornAt : Route → V.Runtime
  beforeFork ordinary = Out.outbound9
  beforeFork interfering = Mixed.clock-view (Mixed.mixed Out.outbound9)
  beforeFork coreGap = beforeFork interfering
  bornAt ordinary = Out.outbound10
  bornAt interfering = Mixed.clock-view (Mixed.mixed Out.outbound10)
  bornAt coreGap = bornAt interfering
  forkEvent : V.Event
  forkEvent = Out.call Acquire.forkOK
  coreClockEvent : V.Event
  coreClockEvent = V.dispatch (K.coreStep (O.inbound (Machine.igStep (IG.captureTime 10))))
  coreClock : V.advance coreClockEvent (Mixed.mixed Out.outbound5) ≡
    just (Mixed.clock-view (Mixed.mixed Out.outbound5))
  coreClock = refl
  coreRouteEvents : List V.Event
  coreRouteEvents = Out.call Acquire.openOK ∷ coreClockEvent ∷ Out.call Acquire.configureOK ∷
    Out.call Acquire.connectOK ∷ Out.call (Acquire.gotLocal (local A.key₀)) ∷
    Out.call Acquire.updateLocalAddress ∷ []
  abstract
    coreRoute : V.Runs (Mixed.mixed Out.outbound4) coreRouteEvents (beforeFork coreGap)
    coreRoute = V.more Mixed.mixed-open (V.more coreClock (V.more Mixed.mixed-edge6
      (V.more Mixed.mixed-edge7 (V.more Mixed.mixed-edge8 (V.more Mixed.mixed-edge9 V.stop)))))
  observed : Route → List V.Event
  observed ordinary = take 9 Known.outbound-birth-events
  observed interfering = Mixed.mixed-prefix-events ++
    (Out.call Acquire.newPromise ∷ Mixed.mixed-route-events)
  observed coreGap = Mixed.mixed-prefix-events ++ (Out.call Acquire.newPromise ∷ coreRouteEvents)
  birthEvents : Route → List V.Event
  birthEvents route = observed route ++ (forkEvent ∷ [])
  actualFork : ∀ route → V.advance forkEvent (beforeFork route) ≡ just (bornAt route)
  actualFork ordinary = Out.edge10
  actualFork interfering = Mixed.mixed-edge10
  actualFork coreGap = Mixed.mixed-edge10
  -- A small local append keeps the future packet tests independent of proof
  -- namespace aliases and never replays or renames an observed event.
  append : ∀ {s t u left right} → V.Runs s left t → V.Runs t right u → V.Runs s (left ++ right) u
  append V.stop right = right
  append (V.more edge left) right = V.more edge (append left right)
  abstract
    prefixRun : ∀ route → V.Runs Out.start (observed route) (beforeFork route)
    prefixRun ordinary = V.more Out.edge1 (V.more Out.edge2 (V.more Out.edge3
      (V.more Out.edge4 (V.more Out.edge5 (V.more Out.edge6 (V.more Out.edge7
      (V.more Out.edge8 (V.more Out.edge9 V.stop))))))))
    prefixRun interfering = append Mixed.mixed-prefix (V.more Mixed.mixed-allocation Mixed.mixed-route)
    prefixRun coreGap = append Mixed.mixed-prefix (V.more Mixed.mixed-allocation coreRoute)

  abstract
    actualBirth : ∀ route → V.Runs Out.start (birthEvents route) (bornAt route)
    actualBirth route = append (prefixRun route) (V.more (actualFork route) V.stop)

  receiptTail : List V.Event
  receiptTail = drop 10 Shutdown.before-scope-events ++ take 4 Out.outbound-finalizer-events
  publicationTail : List V.Event
  publicationTail = Shutdown.cleanup-after-ack-events ++ (Resource.handler-event (H.publishAsyncResult OA.child) ∷ [])
  waitTail : List V.Event
  waitTail = Join.handler-event (W.shutdownStep Close.finishTraversal) ∷
    Join.handler-event (W.shutdownStep Close.finishClose) ∷ []
  abstract
    birthToReceipt : V.Runs Out.outbound10 receiptTail Out.outbound16
    birthToReceipt = append
      (Resource.discard-prefix {suffix = drop 10 Shutdown.before-scope-events}
        Known.outbound-birth-path Shutdown.before-scope-run) Shutdown.delivered-prefix
    receiptToPublication : V.Runs Out.outbound16 publicationTail Out.outbound26
    receiptToPublication = append Shutdown.cleanup-after-ack (V.more Out.edge26 V.stop)
    publicationToWait : V.Runs Out.outbound26 waitTail Out.outbound28
    publicationToWait = V.more Out.edge27 (V.more Out.edge28 V.stop)

  capturedAtReceipt : lookup OA.child (B.threads (Back.physical-state Out.outbound16)) ≡
    just (H.handlerThread OB.captured (H.caughtCancellation OB.err))
  capturedAtReceipt = refl
  capturedAtPublication : lookup OA.child (B.threads (Back.physical-state Out.outbound26)) ≡
    just (H.handlerThread OB.captured (H.resultAvailable OB.err Shared.cleanupNormal))
  capturedAtPublication = refl
  capturedAtWait : lookup OA.child (B.threads (Back.physical-state Out.outbound28)) ≡
    just (H.handlerThread OB.captured (H.resultAvailable OB.err Shared.cleanupNormal))
  capturedAtWait = refl
  collectedAtReceipt : OA.child ∈ Close.collected (W.shutdown (Join.physical Out.outbound16))
  collectedAtReceipt = here refl
  collectedAtPublication : OA.child ∈ Close.collected (W.shutdown (Join.physical Out.outbound26))
  collectedAtPublication = here refl
  collectedAtWait : OA.child ∈ Close.collected (W.shutdown (Join.physical Out.outbound28))
  collectedAtWait = here refl

  -- The malformed initializer is accepted by the open runtime, but is outside
  -- every O.initial-core profile. This does not invent a collected cleanup suffix.
  preloadedExcluded : ∀ core → Pre.seededConfiguration ≡ O.initial core → ⊥
  preloadedExcluded core equality with cong O.acquiring equality
  ... | ()
  noUnconditionalResources : Facts.Facts Pre.preChild Pre.preDescriptor Pre.forkedWorld → ⊥
  noUnconditionalResources = Pre.preloadedResourcesImpossible
  preloadedUncollected : Close.collected (W.shutdown (Join.physical Pre.preloadedForked)) ≡ []
  preloadedUncollected = Pre.forkHasNotCollected
  sameCoreImmediateForkRefused : V.advance Pre.preloadedForkEvent
    (Protocols.PreloadedAcquisitionForkControl.ordinaryStart) ≡ nothing
  sameCoreImmediateForkRefused = Pre.ordinaryImmediateForkRefused

  prematureFork : V.advance forkEvent Out.outbound3 ≡ nothing
  prematureFork = Out.early-fork-refused
  prematurePublication : V.advance (Resource.handler-event (H.publishAsyncResult OA.child)) Out.outbound24 ≡ nothing
  prematurePublication = Out.early-publication-refused
  prematureWait : V.advance (Join.handler-event (W.shutdownStep Close.finishClose)) Out.waiting-before-publication ≡ nothing
  prematureWait = Out.early-wait-refused
  duplicatePublication : V.advance (Resource.handler-event (H.publishAsyncResult OA.child)) Out.outbound26 ≡ nothing
  duplicatePublication = Out.duplicate-publication-refused
  duplicateReceipt : V.advance (Resource.handler-event (H.deliverShutdownHandshake OB.err)) Out.outbound16 ≡ nothing
  duplicateReceipt = refl
  rawOutboundAliasRefused : V.advance
    (Join.handler-event (Resource.outbound-physical-action (O.acquire OA.caller Acquire.newPromise)))
    (Mixed.mixed Out.outbound3) ≡ nothing
  rawOutboundAliasRefused = Mixed.raw-acquisition-alias-refused

  -- Selection tags certify only the actual chosen wrappers. No source PC or
  -- allocation/resource certificate is supplied to the new recovery API.
  private
    module MuxTag = BirthEffects.MuxLayer using (inherited-birth)
    module JobTag = BirthEffects.ProtocolLayer using (inherited-birth)
    module MonitorTag = BirthEffects.MonitorLayer I.bearerClosed using (inherited-birth)
    module GroupTag = BirthEffects.GroupLayer I.bearerClosed using (inherited-birth)
    module ExitTag = BirthEffects.ExitLayer I.bearerClosed using (chosen-birth; inherited-plan)
    module CancelTag = BirthEffects.CancellationLayer I.bearerClosed using (inherited-birth)
    module UnwindTag = BirthEffects.UnwindLayer I.bearerClosed using (chosen-birth; inherited-plan)
    module DeltaTag = BirthEffects.DeltaQLayer I.bearerClosed using (inherited-birth)
    module CatchTag = BirthEffects.CatchLayer I.bearerClosed using (inherited-birth)
    module PublicationTag = BirthEffects.PublicationLayer I.bearerClosed using (inherited-birth)
    module ServerTag = BirthEffects.ServerLayer I.bearerClosed using (inherited-birth)
    module IGTag = BirthEffects.IGExitLayer I.bearerClosed using (chosen-birth; delegated-birth)
    module SharedTag = BirthEffects.SharedLayer I.bearerClosed Prior.classify using (server-birth; core-birth)
  selectedFork : ∀ route → Back.Selected forkEvent (beforeFork route)
  selectedFork ordinary = Back.chosen-birth refl (Back.inherited-birth (SharedTag.core-birth (IGTag.chosen-birth refl (IGTag.delegated-birth (ServerTag.inherited-birth (PublicationTag.inherited-birth (CatchTag.inherited-birth (DeltaTag.inherited-birth (UnwindTag.chosen-birth refl (UnwindTag.inherited-plan (CancelTag.inherited-birth (ExitTag.chosen-birth refl (ExitTag.inherited-plan (GroupTag.inherited-birth (MonitorTag.inherited-birth (JobTag.inherited-birth (MuxTag.inherited-birth (BirthEffects.outbound-physical OA.caller))))))))))))))))))
  selectedFork interfering = Back.chosen-birth refl (Back.inherited-birth (SharedTag.core-birth (IGTag.chosen-birth refl (IGTag.delegated-birth (ServerTag.inherited-birth (PublicationTag.inherited-birth (CatchTag.inherited-birth (DeltaTag.inherited-birth (UnwindTag.chosen-birth refl (UnwindTag.inherited-plan (CancelTag.inherited-birth (ExitTag.chosen-birth refl (ExitTag.inherited-plan (GroupTag.inherited-birth (MonitorTag.inherited-birth (JobTag.inherited-birth (MuxTag.inherited-birth (BirthEffects.outbound-physical OA.caller))))))))))))))))))
  selectedFork coreGap = Back.chosen-birth refl (Back.inherited-birth (SharedTag.core-birth (IGTag.chosen-birth refl (IGTag.delegated-birth (ServerTag.inherited-birth (PublicationTag.inherited-birth (CatchTag.inherited-birth (DeltaTag.inherited-birth (UnwindTag.chosen-birth refl (UnwindTag.inherited-plan (CancelTag.inherited-birth (ExitTag.chosen-birth refl (ExitTag.inherited-plan (GroupTag.inherited-birth (MonitorTag.inherited-birth (JobTag.inherited-birth (MuxTag.inherited-birth (BirthEffects.outbound-physical OA.caller))))))))))))))))))

  absentBeforeFork : ∀ route → lookup OA.child (Back.view (beforeFork route)) ≡ nothing
  absentBeforeFork ordinary = refl
  absentBeforeFork interfering = refl
  absentBeforeFork coreGap = refl
  captureAtBirth : ∀ route → lookup OA.child (Back.view (bornAt route)) ≡ just OB.captured
  captureAtBirth ordinary = refl
  captureAtBirth interfering = refl
  captureAtBirth coreGap = refl

  IsOutbound : ∀ {X Y : Set} → X ⊎ Y → Set
  IsOutbound (inj₁ value) = ⊥
  IsOutbound (inj₂ value) = ⊤
  takeOutbound : ∀ {X Y : Set} (choice : X ⊎ Y) → IsOutbound choice → Y
  takeOutbound (inj₁ value) ()
  takeOutbound (inj₂ value) proof = value

  -- Name the child boundary so later abstract extension laws cannot unfold
  -- this birth reconstruction. Its input is the genuine original selected step.
  module BirthPackets where
    abstract
      explicitBacking : ∀ route → Back.Backing Out.start (bornAt route) (birthEvents route) OA.child OB.captured
      explicitBacking route = record
        { location = record
          { before = beforeFork route; after = bornAt route; action = forkEvent
          ; prefix = observed route; suffix = []; decomposition = refl
          ; prefix-run = Back.execution (prefixRun route); actual = actualFork route; selected = selectedFork route
          ; absent-before = absentBeforeFork route; at-birth = captureAtBirth route
          ; suffix-run = Back.execution V.stop; retained-descriptor = captureAtBirth route }
        ; operation = Back.actual-fork forkEvent (beforeFork route) (actualFork route) (selectedFork route)
        ; selected-operation = refl
        ; at-physical-fork = trans
          (cong (lookup OA.child) (Back.ForkStep.captures-after
            (Back.actual-fork forkEvent (beforeFork route) (actualFork route) (selectedFork route))))
          (captureAtBirth route) }
      classifiedAtBirth : ∀ route →
        Inbound.InboundOrigin (O.initial inputCore) L.settings Out.start (bornAt route) (birthEvents route) OA.child OB.captured ⊎
        Origin.OutboundOrigin inputCore L.settings Out.start (bornAt route) (birthEvents route) OA.child OB.captured
      classifiedAtBirth route = Origin.from-backing inputCore L.settings ordinaryInitialized (explicitBacking route)
      outboundBranchAtBirth : ∀ route → IsOutbound (classifiedAtBirth route)
      outboundBranchAtBirth ordinary = tt
      outboundBranchAtBirth interfering = tt
      outboundBranchAtBirth coreGap = tt
      sameOutboundAtBirth : ∀ route → Origin.OutboundOrigin inputCore L.settings Out.start
        (bornAt route) (birthEvents route) OA.child OB.captured
      sameOutboundAtBirth route = takeOutbound (classifiedAtBirth route) (outboundBranchAtBirth route)
      originalBirthLabel : ∀ route → Packet.label (Outbound.packet (sameOutboundAtBirth route)) ≡ forkEvent
      originalBirthLabel ordinary = refl
      originalBirthLabel interfering = refl
      originalBirthLabel coreGap = refl
      originalBirthPrefix : ∀ route → Packet.prefix (Outbound.packet (sameOutboundAtBirth route)) ≡ observed route
      originalBirthPrefix ordinary = refl
      originalBirthPrefix interfering = refl
      originalBirthPrefix coreGap = refl
  open BirthPackets public using (explicitBacking; classifiedAtBirth; outboundBranchAtBirth; sameOutboundAtBirth; originalBirthLabel; originalBirthPrefix)

  -- Closed queries retain the complete resource-bearing inbound/outbound sum.
  -- Their opaque discoveries need not compute a selected branch by reflexivity.
  receiptIndex publicationIndex finalIndex : List V.Event
  receiptIndex = birthEvents ordinary ++ receiptTail
  publicationIndex = receiptIndex ++ publicationTail
  finalIndex = publicationIndex ++ waitTail
  abstract
    atReceiptRun : V.Runs Out.start receiptIndex Out.outbound16
    atReceiptRun = append (actualBirth ordinary) birthToReceipt
    atPublicationRun : V.Runs Out.start publicationIndex Out.outbound26
    atPublicationRun = append atReceiptRun receiptToPublication
    atWaitRun : V.Runs Out.start finalIndex Out.outbound28
    atWaitRun = append atPublicationRun publicationToWait
    closedAtReceipt : Origin.Discovery inputCore L.settings Out.start Out.outbound16 receiptIndex OA.child
    closedAtReceipt = Origin.initialize-origin ordinaryInitialized atReceiptRun collectedAtReceipt
    closedAtPublication : Origin.Discovery inputCore L.settings Out.start Out.outbound26 publicationIndex OA.child
    closedAtPublication = Origin.initialize-origin ordinaryInitialized atPublicationRun collectedAtPublication
    closedAtWait : Origin.Discovery inputCore L.settings Out.start Out.outbound28 finalIndex OA.child
    closedAtWait = Origin.initialize-origin ordinaryInitialized atWaitRun collectedAtWait

  descriptorAtReceipt : Found.captured closedAtReceipt ≡ OB.captured
  descriptorAtReceipt = sym (Back.capture-of-found (Found.backing closedAtReceipt) capturedAtReceipt)
  descriptorAtPublication : Found.captured closedAtPublication ≡ OB.captured
  descriptorAtPublication = sym (Back.capture-of-found (Found.backing closedAtPublication) capturedAtPublication)
  descriptorAtWait : Found.captured closedAtWait ≡ OB.captured
  descriptorAtWait = sym (Back.capture-of-found (Found.backing closedAtWait) capturedAtWait)

  -- Each suffix extends the SAME immutable original packet. The generic copy
  -- theorem avoids comparing materialized history-search terms by reduction.
  abstract
    sameOutboundAtReceipt : Origin.OutboundOrigin inputCore L.settings Out.start Out.outbound16 receiptIndex OA.child OB.captured
    sameOutboundAtReceipt = Origin.extend-outbound birthToReceipt (sameOutboundAtBirth ordinary)
    sameOutboundAtPublication : Origin.OutboundOrigin inputCore L.settings Out.start Out.outbound26 publicationIndex OA.child OB.captured
    sameOutboundAtPublication = Origin.extend-outbound receiptToPublication sameOutboundAtReceipt
    sameOutboundAtWait : Origin.OutboundOrigin inputCore L.settings Out.start Out.outbound28 finalIndex OA.child OB.captured
    sameOutboundAtWait = Origin.extend-outbound publicationToWait sameOutboundAtPublication
    samePacketAtReceipt : Outbound.packet sameOutboundAtReceipt ≡ Outbound.packet (sameOutboundAtBirth ordinary)
    samePacketAtReceipt = Origin.extend-packet birthToReceipt (sameOutboundAtBirth ordinary)
    samePacketAtPublication : Outbound.packet sameOutboundAtPublication ≡ Outbound.packet (sameOutboundAtBirth ordinary)
    samePacketAtPublication = trans (Origin.extend-packet receiptToPublication sameOutboundAtReceipt) samePacketAtReceipt
    samePacketAtWait : Outbound.packet sameOutboundAtWait ≡ Outbound.packet (sameOutboundAtBirth ordinary)
    samePacketAtWait = trans (Origin.extend-packet publicationToWait sameOutboundAtPublication) samePacketAtPublication
    sameOriginalLabel : Packet.label (Outbound.packet sameOutboundAtWait) ≡ forkEvent
    sameOriginalLabel = trans (cong Packet.label samePacketAtWait) (originalBirthLabel ordinary)
    sameOriginalPrefix : Packet.prefix (Outbound.packet sameOutboundAtWait) ≡ observed ordinary
    sameOriginalPrefix = trans (cong Packet.prefix samePacketAtWait) (originalBirthPrefix ordinary)

  fixedResourcesAtBirth : ∀ route → Facts.Facts OA.child OB.captured (Origin.shared (bornAt route))
  fixedResourcesAtBirth route = Outbound.retained (sameOutboundAtBirth route)
  fixedResourcesAtReceipt : Facts.Facts OA.child OB.captured (Origin.shared Out.outbound16)
  fixedResourcesAtReceipt = Outbound.retained sameOutboundAtReceipt
  fixedResourcesAtPublication : Facts.Facts OA.child OB.captured (Origin.shared Out.outbound26)
  fixedResourcesAtPublication = Outbound.retained sameOutboundAtPublication
  fixedResourcesAtWait : Facts.Facts OA.child OB.captured (Origin.shared Out.outbound28)
  fixedResourcesAtWait = Outbound.retained sameOutboundAtWait
  exactSameExecution : V.Runs Out.start finalIndex Out.outbound28
  exactSameExecution = Origin.execution sameOutboundAtWait

  -- Interference examples stop at the actual restored child handshake. No old
  -- shutdown suffix is pasted onto their distinct admission/IG source state.
  restoredAt : Route → V.Runtime
  restoredAt ordinary = Out.outbound11
  restoredAt interfering = Mixed.clock-view (Mixed.mixed Out.outbound11)
  restoredAt coreGap = restoredAt interfering
  childEvent : V.Event
  childEvent = Resource.handler-event (H.enterHandshake OA.child)
  childActual : ∀ route → V.advance childEvent (bornAt route) ≡ just (restoredAt route)
  childActual ordinary = Out.child-enters
  childActual interfering = Mixed.mixed-child-enters
  childActual coreGap = Mixed.mixed-child-enters
  abstract
    restoredOrigin : ∀ route → Origin.OutboundOrigin inputCore L.settings Out.start (restoredAt route)
      (birthEvents route ++ (childEvent ∷ [])) OA.child OB.captured
    restoredOrigin route = Origin.extend-outbound (V.more {a = childEvent} (childActual route) V.stop) (sameOutboundAtBirth route)
    restoredPacket : ∀ route → Outbound.packet (restoredOrigin route) ≡ Outbound.packet (sameOutboundAtBirth route)
    restoredPacket route = Origin.extend-packet (V.more {a = childEvent} (childActual route) V.stop) (sameOutboundAtBirth route)
  restoredResources : ∀ route → Facts.Facts OA.child OB.captured (Origin.shared (restoredAt route))
  restoredResources route = Outbound.retained (restoredOrigin route)

  permissivePreloadedInitialization : V.initialize Pre.seededConfiguration L.settings ≡ just Pre.preloadedStart
  permissivePreloadedInitialization = Pre.preloadedInitializer
  malformedActualFork : V.advance Pre.preloadedForkEvent Pre.preloadedStart ≡ just Pre.preloadedForked
  malformedActualFork = Pre.preloadedActualFork
  sameCoreProfileInitialization : V.initialize (O.initial Pre.seededCore) L.settings ≡ just Pre.ordinaryStart
  sameCoreProfileInitialization = Pre.ordinaryInitializer

module FinishedTargetChecks where
  open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
  open import Data.Bool using (true; false)
  open import Data.List using (List; []; _∷_; _++_)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here)
  open import Data.Maybe using (just; nothing)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import ConnectionManagement.Domain using (ident)
  open import ConnectionManagement.Store using (lookup)
  import ConnectionManagement.State as Shared
  import ConnectionManagement.ServerPeers as Combined
  import ConnectionManagement.ServerAdmission as Server
  import ConnectionManagement.HandlerSupervision as H
  import ConnectionManagement.OutboundHandlerSupervision as B
  import ConnectionManagement.MuxHandlerExit as Physical
  import ConnectionManagement.Rules.Cleanup as Cleanup
  import ConnectionManagement.Rules.CMShutdown as Close
  import ConnectionManagement.CSP.OutboundAdmission as OA
  import ConnectionManagement.Negative.OutboundHandlerSupervision as OB
  import ConnectionManagement.Negative.GovernorPool as Prior
  import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
  import ConnectionManagement.Properties.ServerPeersHandlerResources as Resources
  import ConnectionManagement.Properties.ServerPeersMonitorJoins as Joins

  private
    module Parent = Protocols using (capability)
    module Out = Protocols.OutboundHandlerResourceOriginChecks using (start; outbound10; outbound12; outbound13; outbound14; outbound15; outbound26; outbound27; outbound28; outbound-initialized; outbound-owned-at; outbound-exited-ig; outbound-scope18; outbound-connected-events; outbound-connected-path; outbound-peer-events; outbound-peer-path; outbound-scope-events; outbound-scope-path; edge13; edge14; edge27; edge28)
    module V = Combined.Protocols I.bearerClosed Prior.classify Parent.capability using (Runtime; Event; Runs; advance; more; stop)
    module W = Physical I.bearerClosed using (shutdown; physical; resultReady; shutdownStep; acknowledgeFinished)
    module Resource = Resources.Frontend I.bearerClosed Prior.classify Parent.capability using (handler-event; shared)
    module Join = Joins.Frontend I.bearerClosed Prior.classify Parent.capability using (handler-event; physical)
    module S = Server I.bearerClosed using (closingCM)

  -- Expected states preserve one coordinator continuation while independent
  -- physical actions run. Every edge below is an actual guarded frontend step;
  -- this renderer is not an executable reset or an injected Async result.
  held : B.State → Close.State → V.Runtime
  held physical coordinator = Out.outbound-owned-at (record physical { shutdown = coordinator }) S.closingCM false Out.outbound-exited-ig

  liveTarget finishedTarget finishedPending : V.Runtime
  liveTarget = Out.outbound14
  finishedTarget = held OB.p26 OB.ownerRead
  finishedPending = held OB.p26 OB.ownerSending

  -- The bounded pre-handshake profile has no normal-return action. An
  -- independent handshake cancellation supplies a real body exit here;
  -- it does not acknowledge this CM coordinator's later throwTo request.
  independentDelivery : V.Event
  independentDelivery = Resource.handler-event (H.deliverHandshakeCancellation OA.child OB.err)
  completionEvents : List V.Event
  completionEvents = Resource.handler-event (H.deliverHandshakeCancellation OA.child OB.err) ∷
    Resource.handler-event (H.publishCaught OA.child) ∷
    Resource.handler-event (H.rethrowCaught OA.child) ∷
    Resource.handler-event (H.enterFinalizer OA.child) ∷
    Resource.handler-event (H.cleanup OA.child Cleanup.takeCleanupMap) ∷
    Resource.handler-event (H.cleanup OA.child Cleanup.selectCleanupEntry) ∷
    Resource.handler-event (H.cleanup OA.child Cleanup.closeHandlerSocket) ∷
    Resource.handler-event (H.cleanup OA.child Cleanup.publishCleanupMap) ∷
    Resource.handler-event (H.cleanup OA.child Cleanup.readCleanupCounters) ∷
    Resource.handler-event (H.finishCleanup OA.child) ∷
    Resource.handler-event (H.publishAsyncResult OA.child) ∷ []

  finish1 : ∀ coordinator → V.advance (Resource.handler-event (H.deliverHandshakeCancellation OA.child OB.err)) (held OB.p14 coordinator) ≡ just (held OB.p16 coordinator)
  finish1 coordinator = refl
  finish2 : ∀ coordinator → V.advance (Resource.handler-event (H.publishCaught OA.child)) (held OB.p16 coordinator) ≡ just (held OB.p17 coordinator)
  finish2 coordinator = refl
  finish3 : ∀ coordinator → V.advance (Resource.handler-event (H.rethrowCaught OA.child)) (held OB.p17 coordinator) ≡ just (held OB.p18 coordinator)
  finish3 coordinator = refl
  finish4 : ∀ coordinator → V.advance (Resource.handler-event (H.enterFinalizer OA.child)) (held OB.p18 coordinator) ≡ just (held OB.p19 coordinator)
  finish4 coordinator = refl
  finish5 : ∀ coordinator → V.advance (Resource.handler-event (H.cleanup OA.child Cleanup.takeCleanupMap)) (held OB.p19 coordinator) ≡ just (held OB.p20 coordinator)
  finish5 coordinator = refl
  finish6 : ∀ coordinator → V.advance (Resource.handler-event (H.cleanup OA.child Cleanup.selectCleanupEntry)) (held OB.p20 coordinator) ≡ just (held OB.p21 coordinator)
  finish6 coordinator = refl
  finish7 : ∀ coordinator → V.advance (Resource.handler-event (H.cleanup OA.child Cleanup.closeHandlerSocket)) (held OB.p21 coordinator) ≡ just (held OB.p22 coordinator)
  finish7 coordinator = refl
  finish8 : ∀ coordinator → V.advance (Resource.handler-event (H.cleanup OA.child Cleanup.publishCleanupMap)) (held OB.p22 coordinator) ≡ just (held OB.p23 coordinator)
  finish8 coordinator = refl
  finish9 : ∀ coordinator → V.advance (Resource.handler-event (H.cleanup OA.child Cleanup.readCleanupCounters)) (held OB.p23 coordinator) ≡ just (held OB.p24 coordinator)
  finish9 coordinator = refl
  finish10 : ∀ coordinator → V.advance (Resource.handler-event (H.finishCleanup OA.child)) (held OB.p24 coordinator) ≡ just (held OB.p25 coordinator)
  finish10 coordinator = refl
  finish11 : ∀ coordinator → V.advance (Resource.handler-event (H.publishAsyncResult OA.child)) (held OB.p25 coordinator) ≡ just (held OB.p26 coordinator)
  finish11 coordinator = refl

  append : ∀ {start middle current first last} → V.Runs start first middle → V.Runs middle last current → V.Runs start (first ++ last) current
  append V.stop rest = rest
  append (V.more actual path) rest = V.more actual (append path rest)

  abstract
    actualIndependentCompletion : ∀ coordinator → V.Runs (held OB.p14 coordinator) completionEvents (held OB.p26 coordinator)
    actualIndependentCompletion coordinator = V.more {a = Resource.handler-event (H.deliverHandshakeCancellation OA.child OB.err)} (finish1 coordinator) (V.more {a = Resource.handler-event (H.publishCaught OA.child)} (finish2 coordinator) (V.more {a = Resource.handler-event (H.rethrowCaught OA.child)} (finish3 coordinator) (V.more {a = Resource.handler-event (H.enterFinalizer OA.child)} (finish4 coordinator) (V.more {a = Resource.handler-event (H.cleanup OA.child Cleanup.takeCleanupMap)} (finish5 coordinator) (V.more {a = Resource.handler-event (H.cleanup OA.child Cleanup.selectCleanupEntry)} (finish6 coordinator) (V.more {a = Resource.handler-event (H.cleanup OA.child Cleanup.closeHandlerSocket)} (finish7 coordinator) (V.more {a = Resource.handler-event (H.cleanup OA.child Cleanup.publishCleanupMap)} (finish8 coordinator) (V.more {a = Resource.handler-event (H.cleanup OA.child Cleanup.readCleanupCounters)} (finish9 coordinator) (V.more {a = Resource.handler-event (H.finishCleanup OA.child)} (finish10 coordinator) (V.more {a = Resource.handler-event (H.publishAsyncResult OA.child)} (finish11 coordinator) (V.stop)))))))))))

  beforeCMEvents : List V.Event
  beforeCMEvents = Out.outbound-connected-events ++ (Out.outbound-peer-events ++ Out.outbound-scope-events)
  captureReadEvents : List V.Event
  captureReadEvents = Join.handler-event (W.shutdownStep Close.captureSnapshot) ∷ Join.handler-event (W.shutdownStep Close.readEntry) ∷ []
  receiptEvents : List V.Event
  receiptEvents = Join.handler-event (W.shutdownStep Close.requestCancellation) ∷ Join.handler-event W.acknowledgeFinished ∷ []
  waitEvents : List V.Event
  waitEvents = Join.handler-event (W.shutdownStep Close.finishTraversal) ∷ Join.handler-event (W.shutdownStep Close.finishClose) ∷ []
  requestFinished : V.advance (Join.handler-event (W.shutdownStep Close.requestCancellation)) finishedTarget ≡ just finishedPending
  requestFinished = refl
  acknowledgeFinished : V.advance (Join.handler-event W.acknowledgeFinished) finishedPending ≡ just Out.outbound26
  acknowledgeFinished = refl
  abstract
    actualBeforeCM : V.Runs Out.outbound10 beforeCMEvents Out.outbound-scope18
    actualBeforeCM = append Out.outbound-connected-path (append Out.outbound-peer-path Out.outbound-scope-path)
    actualCaptureRead : V.Runs Out.outbound-scope18 captureReadEvents liveTarget
    actualCaptureRead = V.more {a = Join.handler-event (W.shutdownStep Close.captureSnapshot)} Out.edge13
      (V.more {a = Join.handler-event (W.shutdownStep Close.readEntry)} Out.edge14 V.stop)
    actualFinishCaptured : V.Runs liveTarget completionEvents finishedTarget
    actualFinishCaptured = actualIndependentCompletion OB.ownerRead
    actualReceipt : V.Runs finishedTarget receiptEvents Out.outbound26
    actualReceipt = V.more {a = Join.handler-event (W.shutdownStep Close.requestCancellation)} requestFinished
      (V.more {a = Join.handler-event W.acknowledgeFinished} acknowledgeFinished V.stop)
    actualFinalWait : V.Runs Out.outbound26 waitEvents Out.outbound28
    actualFinalWait = V.more {a = Join.handler-event (W.shutdownStep Close.finishTraversal)} Out.edge27
      (V.more {a = Join.handler-event (W.shutdownStep Close.finishClose)} Out.edge28 V.stop)

  throughReceiptEvents : List V.Event
  throughReceiptEvents = beforeCMEvents ++ (captureReadEvents ++ (completionEvents ++ receiptEvents))
  throughFinalEvents : List V.Event
  throughFinalEvents = throughReceiptEvents ++ waitEvents
  abstract
    actualThroughReceipt : V.Runs Out.outbound10 throughReceiptEvents Out.outbound26
    actualThroughReceipt = append actualBeforeCM (append actualCaptureRead (append actualFinishCaptured actualReceipt))
    actualThroughFinal : V.Runs Out.outbound10 throughFinalEvents Out.outbound28
    actualThroughFinal = append actualThroughReceipt actualFinalWait

  capturedStillSendReady : Close.phase (W.shutdown (Join.physical finishedTarget)) ≡ Close.sendReady (ident 0) OA.child
  capturedStillSendReady = refl
  noReceiptDuringCompletion : Close.collected (W.shutdown (Join.physical finishedTarget)) ≡ []
  noReceiptDuringCompletion = refl
  actualPhysicalResult : lookup OA.child (B.threads (W.physical (Join.physical finishedTarget))) ≡ just (H.handlerThread OB.captured (H.resultAvailable OB.err Shared.cleanupNormal))
  actualPhysicalResult = refl
  resultReadyBeforeRequest : W.resultReady OA.child (Join.physical finishedTarget) ≡ true
  resultReadyBeforeRequest = refl
  capturedEntryNowTerminated : lookup (ident 0) (Shared.entries (Shared.cm (Resource.shared finishedTarget))) ≡ just (Shared.terminated nothing)
  capturedEntryNowTerminated = refl
  actualCollectedAtReceipt : OA.child ∈ Close.collected (W.shutdown (Join.physical Out.outbound26))
  actualCollectedAtReceipt = here refl
  actualClosed : Close.phase (W.shutdown (Join.physical Out.outbound28)) ≡ Close.closed
  actualClosed = refl

  -- The same captured entry is late-read only after the same genuine completion.
  -- Its finalizer removed map aliases, but the original snapshot is retained.
  lateFinished lateSkipped lateAwaiting lateClosed : V.Runtime
  lateFinished = held OB.p26 OB.ownerCaptured
  lateSkipped = held OB.p26 (record OB.ownerCaptured { remaining = [] })
  lateAwaiting = held OB.p26 (record OB.ownerCaptured { remaining = []; phase = Close.awaitResults })
  lateClosed = held OB.p26 (record OB.ownerCaptured { remaining = []; phase = Close.closed })
  lateRead : V.advance (Join.handler-event (W.shutdownStep Close.readEntry)) lateFinished ≡ just lateSkipped
  lateRead = refl
  lateTraverse : V.advance (Join.handler-event (W.shutdownStep Close.finishTraversal)) lateSkipped ≡ just lateAwaiting
  lateTraverse = refl
  lateWait : V.advance (Join.handler-event (W.shutdownStep Close.finishClose)) lateAwaiting ≡ just lateClosed
  lateWait = refl
  lateEvents : List V.Event
  lateEvents = Join.handler-event (W.shutdownStep Close.captureSnapshot) ∷
    (completionEvents ++ (Join.handler-event (W.shutdownStep Close.readEntry) ∷
      Join.handler-event (W.shutdownStep Close.finishTraversal) ∷ Join.handler-event (W.shutdownStep Close.finishClose) ∷ []))
  abstract
    actualLateReadControl : V.Runs Out.outbound-scope18 lateEvents lateClosed
    actualLateReadControl = V.more {a = Join.handler-event (W.shutdownStep Close.captureSnapshot)} Out.edge13
      (append (actualIndependentCompletion OB.ownerCaptured)
        (V.more {a = Join.handler-event (W.shutdownStep Close.readEntry)} lateRead
          (V.more {a = Join.handler-event (W.shutdownStep Close.finishTraversal)} lateTraverse
            (V.more {a = Join.handler-event (W.shutdownStep Close.finishClose)} lateWait V.stop))))
  lateSnapshotPreserved : Close.snapshot (W.shutdown (Join.physical lateFinished)) ≡ (ident 0) ∷ []
  lateSnapshotPreserved = refl
  lateTerminatedReadSkips : Close.collected (W.shutdown (Join.physical lateClosed)) ≡ []
  lateTerminatedReadSkips = refl
  lateReadCannotRequest : V.advance (Join.handler-event (W.shutdownStep Close.requestCancellation)) lateSkipped ≡ nothing
  lateReadCannotRequest = refl
  lateReadCannotAcknowledge : V.advance (Join.handler-event W.acknowledgeFinished) lateSkipped ≡ nothing
  lateReadCannotAcknowledge = refl

  -- Refusal controls retain the actual publication and coordinator boundaries.
  finishedNotRequestedCannotAcknowledge : V.advance (Join.handler-event W.acknowledgeFinished) finishedTarget ≡ nothing
  finishedNotRequestedCannotAcknowledge = refl
  unavailableResultCannotAcknowledge : V.advance (Join.handler-event W.acknowledgeFinished) Out.outbound15 ≡ nothing
  unavailableResultCannotAcknowledge = refl
  beforeAsyncPending : V.Runtime
  beforeAsyncPending = held OB.p25 OB.ownerSending
  requestBeforeAsync : V.advance (Join.handler-event (W.shutdownStep Close.requestCancellation)) (held OB.p25 OB.ownerRead) ≡ just beforeAsyncPending
  requestBeforeAsync = refl
  cleanupIsNotAsyncResult : V.advance (Join.handler-event W.acknowledgeFinished) beforeAsyncPending ≡ nothing
  cleanupIsNotAsyncResult = refl
  prematureAsyncPublication : V.advance (Resource.handler-event (H.publishAsyncResult OA.child)) (held OB.p24 OB.ownerRead) ≡ nothing
  prematureAsyncPublication = refl
  duplicateAsyncPublication : V.advance (Resource.handler-event (H.publishAsyncResult OA.child)) finishedTarget ≡ nothing
  duplicateAsyncPublication = refl
  duplicateReceipt : V.advance (Join.handler-event W.acknowledgeFinished) Out.outbound26 ≡ nothing
  duplicateReceipt = refl
  noTraversalBeforeReceipt : V.advance (Join.handler-event (W.shutdownStep Close.finishTraversal)) finishedPending ≡ nothing
  noTraversalBeforeReceipt = refl
  noWaitBeforeTraversal : V.advance (Join.handler-event (W.shutdownStep Close.finishClose)) Out.outbound26 ≡ nothing
  noWaitBeforeTraversal = refl
  duplicateWait : V.advance (Join.handler-event (W.shutdownStep Close.finishClose)) Out.outbound28 ≡ nothing
  duplicateWait = refl
  directReceiptAliasRefused : V.advance (Join.handler-event (W.shutdownStep Close.acknowledgeDelivery)) finishedPending ≡ nothing
  directReceiptAliasRefused = refl

  open import Data.Product using (Σ; _×_; _,_)
  open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)
  import Data.List.Relation.Unary.All as All
  import ConnectionManagement.Properties.CollectedOutboundOrigin as OriginModel
  import ConnectionManagement.Properties.HandlerBirthBacking as Birth
  import ConnectionManagement.Properties.HandlerResourceFacts as ResourceFacts
  import ConnectionManagement.Properties.ServerPeersFinishedReceipt as FinishedFacts
  import ConnectionManagement.Properties.MuxHandlerExit as WaitModel
  import ConnectionManagement.CSP.GovernorLifecycle as L
  private
    module Previous = CollectedOutboundOriginChecks using
      (inputCore; ordinaryInitialized; ordinary; birthEvents; actualBirth;
       sameOutboundAtBirth; explicitBacking; originalBirthLabel; originalBirthPrefix;
       capturedAtPublication; capturedAtWait; forkEvent; observed)
    module Origin = OriginModel.Frontend I.bearerClosed Prior.classify Parent.capability using
      (OutboundOrigin; BirthPacket; Discovery; FinishedDiscovery; initialize-origin;
       initialize-finished; extend-outbound; extend-packet; execution; shared)
    module Outbound = OriginModel.Frontend.OutboundOrigin using (packet; retained)
    module Packet = OriginModel.Frontend.BirthPacket using (label; prefix)
    module Found = OriginModel.Frontend.Discovery using (captured; backing)
    module FinishedFound = OriginModel.Frontend.FinishedDiscovery using (receipt; discovered)
    module Finished = FinishedFacts I.bearerClosed Prior.classify using
      (Receipt; observed-worker; observed-entry; receipt-member; Ready)
    module Receipt = FinishedFacts.Receipt using (worker; entry; ready; result)
    module Back = Birth.Frontend I.bearerClosed Prior.classify Parent.capability using
      (Backing; ForkStep; follow; follow-operation; capture-of-found; current-thread; physical-state)
    module Wait = Joins.Frontend I.bearerClosed Prior.classify Parent.capability using (physical-wait)
    module WaitFacts = WaitModel I.bearerClosed using (PhysicalWait)
    module ObservedWait = WaitModel.PhysicalWait using (observed-results)

  -- Initialization and exact original events precede the real guarded receipt.
  -- No worker, physical lookup, resource fact or collected membership is passed
  -- to initialize-finished.
  finishedTail : List V.Event
  finishedTail = beforeCMEvents ++ (captureReadEvents ++ completionEvents)
  pendingTail : List V.Event
  pendingTail = finishedTail ++ (Join.handler-event (W.shutdownStep Close.requestCancellation) ∷ [])
  pendingIndex : List V.Event
  pendingIndex = Previous.birthEvents Previous.ordinary ++ pendingTail
  receiptIndex : List V.Event
  receiptIndex = pendingIndex ++ (Join.handler-event W.acknowledgeFinished ∷ [])
  finalIndex : List V.Event
  finalIndex = receiptIndex ++ waitEvents
  abstract
    birthToFinished : V.Runs Out.outbound10 finishedTail finishedTarget
    birthToFinished = append actualBeforeCM (append actualCaptureRead actualFinishCaptured)
    birthToPending : V.Runs Out.outbound10 pendingTail finishedPending
    birthToPending = append birthToFinished
      (V.more {a = Join.handler-event (W.shutdownStep Close.requestCancellation)} requestFinished V.stop)
    initializedPending : V.Runs Out.start pendingIndex finishedPending
    initializedPending = append (Previous.actualBirth Previous.ordinary) birthToPending
    initializedReceipt : V.Runs Out.start receiptIndex Out.outbound26
    initializedReceipt = append initializedPending
      (V.more {a = Join.handler-event W.acknowledgeFinished} acknowledgeFinished V.stop)
    initializedWait : V.Runs Out.start finalIndex Out.outbound28
    initializedWait = append initializedReceipt actualFinalWait

    closedReceipt : Origin.FinishedDiscovery Previous.inputCore L.settings Out.start finishedPending Out.outbound26 pendingIndex
    closedReceipt = Origin.initialize-finished Previous.ordinaryInitialized initializedPending acknowledgeFinished
    receiptWorker : Receipt.worker (FinishedFound.receipt closedReceipt) ≡ OA.child
    receiptWorker = Finished.observed-worker (FinishedFound.receipt closedReceipt) refl
    receiptEntry : Receipt.entry (FinishedFound.receipt closedReceipt) ≡ ident 0
    receiptEntry = Finished.observed-entry (FinishedFound.receipt closedReceipt) refl
    discoveredAtReceipt : Origin.Discovery Previous.inputCore L.settings Out.start Out.outbound26 receiptIndex OA.child
    discoveredAtReceipt = subst
      (λ worker → Origin.Discovery Previous.inputCore L.settings Out.start Out.outbound26 receiptIndex worker)
      receiptWorker (FinishedFound.discovered closedReceipt)
    discoveredAtWait : Origin.Discovery Previous.inputCore L.settings Out.start Out.outbound28 finalIndex OA.child
    discoveredAtWait = Origin.initialize-origin Previous.ordinaryInitialized initializedWait (here refl)

  originalDescriptorAtReceipt : Found.captured discoveredAtReceipt ≡ OB.captured
  originalDescriptorAtReceipt = sym (Back.capture-of-found (Found.backing discoveredAtReceipt) Previous.capturedAtPublication)
  originalDescriptorAtWait : Found.captured discoveredAtWait ≡ OB.captured
  originalDescriptorAtWait = sym (Back.capture-of-found (Found.backing discoveredAtWait) Previous.capturedAtWait)

  -- Existing generic copy laws keep the same opaque origin and actual physical
  -- fork through the new receipt path; no old delivery suffix is substituted.
  abstract
    sameOriginPending : Origin.OutboundOrigin Previous.inputCore L.settings Out.start finishedPending pendingIndex OA.child OB.captured
    sameOriginPending = Origin.extend-outbound birthToPending (Previous.sameOutboundAtBirth Previous.ordinary)
    sameOriginReceipt : Origin.OutboundOrigin Previous.inputCore L.settings Out.start Out.outbound26 receiptIndex OA.child OB.captured
    sameOriginReceipt = Origin.extend-outbound
      (V.more {a = Join.handler-event W.acknowledgeFinished} acknowledgeFinished V.stop) sameOriginPending
    sameOriginWait : Origin.OutboundOrigin Previous.inputCore L.settings Out.start Out.outbound28 finalIndex OA.child OB.captured
    sameOriginWait = Origin.extend-outbound actualFinalWait sameOriginReceipt
    packetPending : Outbound.packet sameOriginPending ≡ Outbound.packet (Previous.sameOutboundAtBirth Previous.ordinary)
    packetPending = Origin.extend-packet birthToPending (Previous.sameOutboundAtBirth Previous.ordinary)
    packetReceipt : Outbound.packet sameOriginReceipt ≡ Outbound.packet (Previous.sameOutboundAtBirth Previous.ordinary)
    packetReceipt = trans
      (Origin.extend-packet (V.more {a = Join.handler-event W.acknowledgeFinished} acknowledgeFinished V.stop) sameOriginPending) packetPending
    packetWait : Outbound.packet sameOriginWait ≡ Outbound.packet (Previous.sameOutboundAtBirth Previous.ordinary)
    packetWait = trans (Origin.extend-packet actualFinalWait sameOriginReceipt) packetReceipt
    sameBirthLabel : Packet.label (Outbound.packet sameOriginWait) ≡ Previous.forkEvent
    sameBirthLabel = trans (cong Packet.label packetWait) (Previous.originalBirthLabel Previous.ordinary)
    sameBirthPrefix : Packet.prefix (Outbound.packet sameOriginWait) ≡ Previous.observed Previous.ordinary
    sameBirthPrefix = trans (cong Packet.prefix packetWait) (Previous.originalBirthPrefix Previous.ordinary)

    backedPending : Back.Backing Out.start finishedPending pendingIndex OA.child OB.captured
    backedPending = Back.follow birthToPending (Previous.explicitBacking Previous.ordinary)
    backedReceipt : Back.Backing Out.start Out.outbound26 receiptIndex OA.child OB.captured
    backedReceipt = Back.follow (V.more {a = Join.handler-event W.acknowledgeFinished} acknowledgeFinished V.stop) backedPending
    backedWait : Back.Backing Out.start Out.outbound28 finalIndex OA.child OB.captured
    backedWait = Back.follow actualFinalWait backedReceipt

  -- Project to an unindexed command before composing equalities, since the
  -- location parameters of opaque Backing values retain their own indices.
  birthCommand : ∀ {start current events worker captured} → Back.Backing start current events worker captured → B.Action
  birthCommand history = Back.ForkStep.command (Birth.Frontend.Backing.operation history)
  commandCopy : ∀ {start before after events tail worker captured}
    (path : V.Runs before tail after) (history : Back.Backing start before events worker captured) →
    birthCommand (Back.follow path history) ≡ birthCommand history
  commandCopy path history = cong Back.ForkStep.command (Back.follow-operation path history)
  abstract
    commandPending : birthCommand backedPending ≡ birthCommand (Previous.explicitBacking Previous.ordinary)
    commandPending = commandCopy birthToPending (Previous.explicitBacking Previous.ordinary)
    commandReceipt : birthCommand backedReceipt ≡ birthCommand (Previous.explicitBacking Previous.ordinary)
    commandReceipt = trans
      (commandCopy (V.more {a = Join.handler-event W.acknowledgeFinished} acknowledgeFinished V.stop) backedPending) commandPending
    commandWait : birthCommand backedWait ≡ birthCommand (Previous.explicitBacking Previous.ordinary)
    commandWait = trans (commandCopy actualFinalWait backedReceipt) commandReceipt

  resourcesAtReceipt : ResourceFacts.Facts OA.child OB.captured (Origin.shared Out.outbound26)
  resourcesAtReceipt = Outbound.retained sameOriginReceipt
  resourcesAtWait : ResourceFacts.Facts OA.child OB.captured (Origin.shared Out.outbound28)
  resourcesAtWait = Outbound.retained sameOriginWait
  exactSameExecution : V.Runs Out.start finalIndex Out.outbound28
  exactSameExecution = Origin.execution sameOriginWait
  physicalFinalWait : WaitFacts.PhysicalWait (Join.physical Out.outbound27) (Join.physical Out.outbound28)
  physicalFinalWait = Wait.physical-wait Out.outbound27 Out.edge28
  actualFinalResultOracle : W.resultReady OA.child (Join.physical Out.outbound27) ≡ true
  actualFinalResultOracle = All.lookup (ObservedWait.observed-results physicalFinalWait) (here refl)

-- Increment64: actual negotiated outbound mux shutdown in the shared frontend.
module OutboundMuxChecks where

  module PhysicalPrefix where
    open import Data.Bool using (true)
    open import ConnectionManagement.Domain using (local)
    open import ConnectionManagement.Scenarios.Admission using (key₀)
    import ConnectionManagement.OutboundHandlerSupervision as B
    import ConnectionManagement.HandlerSupervision as H
    import ConnectionManagement.Rules.OutboundAcquire as A
    open import Data.List using (List; []; _∷_; _++_; map)
    open import Data.Maybe using (just; nothing)
    open import Data.Product using (_,_)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    import ConnectionManagement.OutboundMachine as O
    import ConnectionManagement.Machine as Machine
    import ConnectionManagement.Rules.IGRegistration as IG
    import ConnectionManagement.MuxProtocolJobs as P
    private module U = P.U
    import ConnectionManagement.MuxResultMonitor as Monitor
    import ConnectionManagement.MuxGroupShutdown as Group
    import ConnectionManagement.MuxHandlerExit as Exit
    import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
    import ConnectionManagement.Negative.MuxProtocolJobs as Old
    import ConnectionManagement.Negative.MuxResultMonitor as RF
    import ConnectionManagement.Negative.MuxGroupShutdown as GF

    module M = Monitor RF.bearerClosed using (run)
    module G = Group RF.bearerClosed using (State; run)
    module W = Exit RF.bearerClosed using (State; Action; run; step; initial; Executes; done; next; delegateAllowed; source; setSource)
    private module Lift = ExitFacts RF.bearerClosed using (wrap; lift-step; lift-path; append)

    -- Exact existing component snapshots through the empty outer wrappers.
    wrapP : P.State → W.State
    wrapP p = Lift.wrap (GF.wrap (RF.wrap p))
    wrapG : G.State → W.State
    wrapG = Lift.wrap
    runP : P.Action → W.Action
    runP a = W.run (G.run (M.run a))
    initial : W.State
    initial = wrapP Old.b0
    beforeFork born entered handedPhysical : W.State
    beforeFork = wrapP Old.b9
    born = wrapP Old.b10
    entered = wrapP Old.b11
    handedPhysical = wrapP Old.b12
    beforeAbort : W.State
    beforeAbort = wrapG GF.abortGroup0

    actual-initializer : W.initial (O.initial Old.F.start) ≡ just initial
    actual-initializer = refl

    liftP-step : ∀ action before {after} → GF.prefixSafeP action ≡ true →
      W.delegateAllowed (G.run (M.run action)) ≡ true → P.step action before ≡ just after →
      W.step (runP action) (wrapP before) ≡ just (wrapP after)
    liftP-step action before safe safeExit actual = Lift.lift-step (G.run (M.run action)) (GF.wrap (RF.wrap before)) safeExit
      (GF.lift-step (M.run action) (RF.wrap before) safe (RF.lift-step action before actual))

    birth1 : W.step (runP (P.run (U.run (B.outbound (O.beginAcquire Old.Fixture.caller Old.Fixture.req))))) (wrapP Old.b0) ≡ just (wrapP Old.b1)
    birth1 = liftP-step (P.run (U.run (B.outbound (O.beginAcquire Old.Fixture.caller Old.Fixture.req)))) Old.b0 refl refl Old.birth1
    birth2 : W.step (runP (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller (A.select nothing)))))) (wrapP Old.b1) ≡ just (wrapP Old.b2)
    birth2 = liftP-step (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller (A.select nothing))))) Old.b1 refl refl Old.birth2
    birth3 : W.step (runP (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.readCounters))))) (wrapP Old.b2) ≡ just (wrapP Old.b3)
    birth3 = liftP-step (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.readCounters)))) Old.b2 refl refl Old.birth3
    birth4 : W.step (runP (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.newPromise))))) (wrapP Old.b3) ≡ just (wrapP Old.b4)
    birth4 = liftP-step (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.newPromise)))) Old.b3 refl refl Old.birth4
    birth5 : W.step (runP (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.openOK))))) (wrapP Old.b4) ≡ just (wrapP Old.b5)
    birth5 = liftP-step (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.openOK)))) Old.b4 refl refl Old.birth5
    birth6 : W.step (runP (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.configureOK))))) (wrapP Old.b5) ≡ just (wrapP Old.b6)
    birth6 = liftP-step (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.configureOK)))) Old.b5 refl refl Old.birth6
    birth7 : W.step (runP (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.connectOK))))) (wrapP Old.b6) ≡ just (wrapP Old.b7)
    birth7 = liftP-step (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.connectOK)))) Old.b6 refl refl Old.birth7
    birth8 : W.step (runP (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller (A.gotLocal (local key₀))))))) (wrapP Old.b7) ≡ just (wrapP Old.b8)
    birth8 = liftP-step (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller (A.gotLocal (local key₀)))))) Old.b7 refl refl Old.birth8
    birth9 : W.step (runP (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.updateLocalAddress))))) (wrapP Old.b8) ≡ just (wrapP Old.b9)
    birth9 = liftP-step (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.updateLocalAddress)))) Old.b8 refl refl Old.birth9
    birth10 : W.step (runP (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.forkOK))))) (wrapP Old.b9) ≡ just (wrapP Old.b10)
    birth10 = liftP-step (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.forkOK)))) Old.b9 refl refl Old.birth10
    birth11 : W.step (runP (P.run (U.run (B.handler (H.enterHandshake Old.owner))))) (wrapP Old.b10) ≡ just (wrapP Old.b11)
    birth11 = liftP-step (P.run (U.run (B.handler (H.enterHandshake Old.owner)))) Old.b10 refl refl Old.birth11
    birth12 : W.step (runP (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.commitConnected))))) (wrapP Old.b11) ≡ just (wrapP Old.b12)
    birth12 = liftP-step (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.commitConnected)))) Old.b11 refl refl Old.birth12

    -- Post-fork source operations keep their existing PCs and primitive steps.
    -- The combined frontend inserts a context-only handoff before birth12 above.
    postBirthP : List P.Action
    postBirthP = (Old.publicationPathActions ++ Old.callerPathActions) ++ Old.startupPathActions
    postBirthActions : List W.Action
    postBirthActions = map W.run (map G.run (map M.run postBirthP))
    monitorPrefixActions : List W.Action
    monitorPrefixActions = map W.run (map G.run RF.errorPrefixActions)
    groupPrefixActions : List W.Action
    groupPrefixActions = map W.run GF.normalPrefix7Actions
    postBirthPrefixActions : List W.Action
    postBirthPrefixActions = (postBirthActions ++ monitorPrefixActions) ++ groupPrefixActions

    abstract
      postBirth : W.Executes handedPhysical postBirthActions (wrapP Old.z12)
      postBirth = Lift.lift-path
        (GF.lift-path (RF.lift-path (Old.append (Old.append Old.publicationPath Old.callerPath) Old.startupPath)) refl) refl
      monitorPrefix : W.Executes (wrapP Old.z12) monitorPrefixActions (wrapG GF.normal0)
      monitorPrefix = Lift.lift-path (GF.lift-path RF.errorPrefixPath refl) refl
      groupPrefix : W.Executes (wrapG GF.normal0) groupPrefixActions beforeAbort
      groupPrefix = Lift.lift-path GF.normalPrefix7 refl
      postBirthPrefix : W.Executes handedPhysical postBirthPrefixActions beforeAbort
      postBirthPrefix = Lift.append (Lift.append postBirth monitorPrefix) groupPrefix

    -- Caller-core operations use combined coreStep events, whereas negotiation,
    -- IG registration, startup and group control use inherited physical events.
    caller1 : W.step (runP (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.readCounters))))) (wrapP Old.b15) ≡ just (wrapP Old.c1)
    caller1 = liftP-step (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.readCounters)))) Old.b15 refl refl Old.caller1
    caller2 : W.step (runP (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.readResult))))) (wrapP Old.c1) ≡ just (wrapP Old.c2)
    caller2 = liftP-step (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.readResult)))) Old.c1 refl refl Old.caller2
    caller3 : W.step (runP (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.commitHandshake))))) (wrapP Old.c2) ≡ just (wrapP Old.c3)
    caller3 = liftP-step (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.commitHandshake)))) Old.c2 refl refl Old.caller3
    caller4 : W.step (runP (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.readCounters))))) (wrapP Old.c3) ≡ just (wrapP Old.c4)
    caller4 = liftP-step (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.readCounters)))) Old.c3 refl refl Old.caller4
    caller5 : W.step (runP (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.returnResult))))) (wrapP Old.c4) ≡ just (wrapP Old.c5)
    caller5 = liftP-step (P.run (U.run (B.outbound (O.acquire Old.Fixture.caller A.returnResult)))) Old.c4 refl refl Old.caller5

    registrationP : List P.Action
    registrationP =
      P.run (U.run (B.handler (H.run (Machine.igStep (IG.captureTime 0))))) ∷
      P.run (U.run (B.handler (H.run (Machine.igStep IG.registerInactivity)))) ∷
      P.run (U.run (B.handler (H.run (Machine.igStep IG.selectBatch)))) ∷
      P.run (U.run (B.handler (H.run (Machine.igStep IG.readEvent)))) ∷
      P.run (U.run (B.handler (H.run (Machine.igStep IG.registerIdleTimer)))) ∷
      P.run (U.run (B.handler (H.run (Machine.igStep IG.runResponders)))) ∷ []
    registrationActions : List W.Action
    registrationActions = map runP registrationP
    publicationActions : List W.Action
    publicationActions = map runP Old.publicationPathActions
    startupActions : List W.Action
    startupActions = map runP Old.startupPathActions
    abstract
      registration : W.Executes (wrapP Old.c5) registrationActions (wrapP Old.c11)
      registration = Lift.lift-path (GF.lift-path (RF.lift-path path) refl) refl
        where
        path : P.Executes Old.c5 registrationP Old.c11
        path = P.next Old.caller6 (P.next Old.caller7 (P.next Old.caller8 (P.next Old.caller9 (P.next Old.caller10 (P.next Old.caller11 P.done)))))
      publication : W.Executes (wrapP Old.b12) publicationActions (wrapP Old.b15)
      publication = Lift.lift-path (GF.lift-path (RF.lift-path Old.publicationPath) refl) refl
      startup : W.Executes (wrapP Old.c11) startupActions (wrapP Old.z12)
      startup = Lift.lift-path (GF.lift-path (RF.lift-path Old.startupPath) refl) refl


    -- The old component fixture begins after two unrelated accepted-socket handoffs.
    -- The combined Server initializer instead starts before any admission. Keep
    -- only this outbound witness's socket in expected snapshots; no transition is
    -- justified by this data projection alone.
    import ConnectionManagement.State as Shared
    open import ConnectionManagement.Domain using (SocketId)
    open import ConnectionManagement.Store using (Store; lookup)
    keepSocket : Store SocketId Shared.SocketOwner → Store SocketId Shared.SocketOwner
    keepSocket sockets with lookup Old.Fixture.sock sockets
    ... | nothing = []
    ... | just owner = (Old.Fixture.sock , owner) ∷ []
    cleanWorld : Shared.State → Shared.State
    cleanWorld world = record world { admissions = []; sockets = keepSocket (Shared.sockets world) }
    cleanSource : O.Configuration → O.Configuration
    cleanSource source = record source { core = Machine.replaceWorld (O.core source) (cleanWorld (Machine.world (O.core source))) }
    inputCore : Machine.Configuration
    inputCore = Machine.replaceWorld Old.F.start (cleanWorld (Machine.world Old.F.start))
    clean : W.State → W.State
    clean physical = W.setSource (cleanSource (W.source physical)) physical
    clean-initialized : W.initial (O.initial inputCore) ≡ just (clean initial)
    clean-initialized = refl

  module ServingPrefix where
    open import Data.Bool using (true)
    open import Data.List using (List; []; _∷_; _++_)
    open import Data.Maybe using (just; nothing)
    open import Data.Product using (_,_)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    open import ConnectionManagement.Domain using (WorkerId; local)
    open import ConnectionManagement.Scenarios.Admission using (key₀)
    open import ConnectionManagement.Store using (Store)
    open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
    import ConnectionManagement.OutboundMachine as O
    import ConnectionManagement.Machine as Machine
    import ConnectionManagement.OutboundHandlerSupervision as B
    import ConnectionManagement.HandlerSupervision as H
    import ConnectionManagement.Rules.OutboundAcquire as Acquire
    import ConnectionManagement.Rules.CallerCancellation as Cancel
    import ConnectionManagement.ServerPeers as Combined
    import ConnectionManagement.ServerAdmission as Server
    import ConnectionManagement.ServerIGExit as IGExit
    import ConnectionManagement.PeerContext as ContextModel
    import ConnectionManagement.PeerSupervision as PeerModel
    import ConnectionManagement.GovernorPool as GovernorPoolModel
    import ConnectionManagement.Properties.ServerPeersMuxEmbedding as Embedding
    import ConnectionManagement.Negative.GovernorPool as Prior
    import ConnectionManagement.CSP.GovernorLifecycle as L
    import ConnectionManagement.Negative.MuxProtocolJobs as Old
    import ConnectionManagement.Negative.MuxResultMonitor as RF
    import ConnectionManagement.Negative.MuxGroupShutdown as GF
    module Physical = PhysicalPrefix
    private
     module Parent = Protocols using (capability)
     module C = ContextModel Prior.classify using (Context; capture)
     module PS = PeerModel Prior.classify using (initial; run)
     module GP = GovernorPoolModel Prior.classify using (handoff)
     module K = Combined RF.bearerClosed Prior.classify using (coreStep; peerStep)
     module S = Server RF.bearerClosed using (serving)
     module E = IGExit RF.bearerClosed using (emptyExit)
    module T = Combined.Protocols RF.bearerClosed Prior.classify Parent.capability using
     (Runtime; Event; Front; frontend; empty; initialize; advance; dispatch; Runs; more; stop)
    private
     module Emb = Embedding.Frontend RF.bearerClosed Prior.classify Parent.capability using
      (embed; event; nextFront; Allowed; lift-step)
    module W = Physical.W using (State; Action; run; step)
    module G = Physical.G using (run)
    module M = Physical.M using (run)
    inputCore : Machine.Configuration
    inputCore = Physical.inputCore
    context0 : C.Context
    context0 = C.capture (PS.initial (O.initial inputCore) L.settings)
    ordinary forked : Store WorkerId Cancel.Context
    ordinary = (Old.Fixture.caller , Cancel.ordinary) ∷ []
    forked = (Old.Fixture.caller , Cancel.forkedBeforeHandoff) ∷ []
    serve : W.State → Store WorkerId Cancel.Context → T.Front → T.Runtime
    serve physical regions front = Emb.embed (Physical.clean physical) (record context0 { regions = regions }) front S.serving true E.emptyExit
    preparedFront : T.Front
    preparedFront = T.frontend [] ((Old.owner , []) ∷ []) []
    start beforeFork born entered handed beforeAbort : T.Runtime
    start = serve Physical.initial [] T.empty
    beforeFork = serve Physical.beforeFork ordinary T.empty
    born = serve Physical.born forked T.empty
    entered = serve Physical.entered forked T.empty
    handed = serve Physical.entered ordinary T.empty
    beforeAbort = serve Physical.beforeAbort ordinary preparedFront
    initialized : T.initialize (O.initial inputCore) L.settings ≡ just start
    initialized = refl
    legacyInitializerRejected : T.initialize (O.initial Old.F.start) L.settings ≡ nothing
    legacyInitializerRejected = refl
    coreEvent : O.Action → T.Event
    coreEvent action = T.dispatch (K.coreStep action)
    call : Acquire.Action → T.Event
    call action = coreEvent (O.acquire Old.Fixture.caller action)
    physicalEvent : W.Action → T.Event
    physicalEvent = Emb.event
    handoffEvent : T.Event
    handoffEvent = T.dispatch (K.peerStep (PS.run (GP.handoff Old.Fixture.caller)))
    handoff : T.advance handoffEvent entered ≡ just handed
    handoff = refl
    append : ∀ {start middle current left right} → T.Runs start left middle → T.Runs middle right current → T.Runs start (left ++ right) current
    append T.stop path = path
    append (T.more actual path) rest = T.more actual (append path rest)
    core1 : T.advance (coreEvent (O.beginAcquire Old.Fixture.caller Old.Fixture.req)) (serve (Physical.wrapP Old.b0) [] T.empty) ≡ just (serve (Physical.wrapP Old.b1) ordinary T.empty)
    core1 = refl
    core2 : T.advance (coreEvent (O.acquire Old.Fixture.caller (Acquire.select nothing))) (serve (Physical.wrapP Old.b1) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.b2) ordinary T.empty)
    core2 = refl
    core3 : T.advance (coreEvent (O.acquire Old.Fixture.caller Acquire.readCounters)) (serve (Physical.wrapP Old.b2) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.b3) ordinary T.empty)
    core3 = refl
    core4 : T.advance (coreEvent (O.acquire Old.Fixture.caller Acquire.newPromise)) (serve (Physical.wrapP Old.b3) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.b4) ordinary T.empty)
    core4 = refl
    core5 : T.advance (coreEvent (O.acquire Old.Fixture.caller Acquire.openOK)) (serve (Physical.wrapP Old.b4) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.b5) ordinary T.empty)
    core5 = refl
    core6 : T.advance (coreEvent (O.acquire Old.Fixture.caller Acquire.configureOK)) (serve (Physical.wrapP Old.b5) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.b6) ordinary T.empty)
    core6 = refl
    core7 : T.advance (coreEvent (O.acquire Old.Fixture.caller Acquire.connectOK)) (serve (Physical.wrapP Old.b6) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.b7) ordinary T.empty)
    core7 = refl
    core8 : T.advance (coreEvent (O.acquire Old.Fixture.caller (Acquire.gotLocal (local key₀)))) (serve (Physical.wrapP Old.b7) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.b8) ordinary T.empty)
    core8 = refl
    core9 : T.advance (coreEvent (O.acquire Old.Fixture.caller Acquire.updateLocalAddress)) (serve (Physical.wrapP Old.b8) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.b9) ordinary T.empty)
    core9 = refl
    core10 : T.advance (coreEvent (O.acquire Old.Fixture.caller Acquire.forkOK)) (serve (Physical.wrapP Old.b9) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.b10) forked T.empty)
    core10 = refl
    import ConnectionManagement.MuxProtocolJobs as P
    private module U = P.U
    childEnters : T.advance (physicalEvent (Physical.runP (P.run (U.run (B.handler (H.enterHandshake Old.owner)))))) born ≡ just entered
    childEnters = Emb.lift-step (Physical.runP (P.run (U.run (B.handler (H.enterHandshake Old.owner))))) (Physical.clean Physical.born) (record context0 { regions = forked }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    commitConnected : T.advance (call Acquire.commitConnected) handed ≡ just (serve Physical.handedPhysical ordinary T.empty)
    commitConnected = refl
    open import ConnectionManagement.Domain using (ident; duplex)
    import ConnectionManagement.Negative.MuxProtocolFixtures as PF
    publication1 : T.advance (physicalEvent (Physical.runP (P.run (U.negotiate Old.owner PF.ps duplex)))) (serve (Physical.wrapP Old.b12) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.b13) ordinary T.empty)
    publication1 = Emb.lift-step (Physical.runP (P.run (U.negotiate Old.owner PF.ps duplex))) (Physical.clean (Physical.wrapP Old.b12)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    publication2 : T.advance (physicalEvent (Physical.runP (P.run (U.allocateHandle Old.owner (ident 0) Old.mid)))) (serve (Physical.wrapP Old.b13) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.b14) ordinary T.empty)
    publication2 = Emb.lift-step (Physical.runP (P.run (U.allocateHandle Old.owner (ident 0) Old.mid))) (Physical.clean (Physical.wrapP Old.b13)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    publication3 : T.advance (physicalEvent (Physical.runP (P.run (U.publishSuccess Old.owner)))) (serve (Physical.wrapP Old.b14) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.b15) ordinary T.empty)
    publication3 = Emb.lift-step (Physical.runP (P.run (U.publishSuccess Old.owner))) (Physical.clean (Physical.wrapP Old.b14)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    caller1 : T.advance (call Acquire.readCounters) (serve (Physical.wrapP Old.b15) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.c1) ordinary T.empty)
    caller1 = refl
    caller2 : T.advance (call Acquire.readResult) (serve (Physical.wrapP Old.c1) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.c2) ordinary T.empty)
    caller2 = refl
    caller3 : T.advance (call Acquire.commitHandshake) (serve (Physical.wrapP Old.c2) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.c3) ordinary T.empty)
    caller3 = refl
    caller4 : T.advance (call Acquire.readCounters) (serve (Physical.wrapP Old.c3) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.c4) ordinary T.empty)
    caller4 = refl
    caller5 : T.advance (call Acquire.returnResult) (serve (Physical.wrapP Old.c4) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.c5) ordinary T.empty)
    caller5 = refl
    import ConnectionManagement.Rules.IGRegistration as IG
    registration6 : T.advance (physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.captureTime 0)))))))) (serve (Physical.wrapP Old.c5) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.c6) ordinary T.empty)
    registration6 = Emb.lift-step (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.captureTime 0))))))) (Physical.clean (Physical.wrapP Old.c5)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    registration7 : T.advance (physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.registerInactivity)))))))) (serve (Physical.wrapP Old.c6) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.c7) ordinary T.empty)
    registration7 = Emb.lift-step (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.registerInactivity))))))) (Physical.clean (Physical.wrapP Old.c6)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    registration8 : T.advance (physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.selectBatch)))))))) (serve (Physical.wrapP Old.c7) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.c8) ordinary T.empty)
    registration8 = Emb.lift-step (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.selectBatch))))))) (Physical.clean (Physical.wrapP Old.c7)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    registration9 : T.advance (physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.readEvent)))))))) (serve (Physical.wrapP Old.c8) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.c9) ordinary T.empty)
    registration9 = Emb.lift-step (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.readEvent))))))) (Physical.clean (Physical.wrapP Old.c8)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    registration10 : T.advance (physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.registerIdleTimer)))))))) (serve (Physical.wrapP Old.c9) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.c10) ordinary T.empty)
    registration10 = Emb.lift-step (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.registerIdleTimer))))))) (Physical.clean (Physical.wrapP Old.c9)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    registration11 : T.advance (physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.runResponders)))))))) (serve (Physical.wrapP Old.c10) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.c11) ordinary T.empty)
    registration11 = Emb.lift-step (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.runResponders))))))) (Physical.clean (Physical.wrapP Old.c10)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    private module Startup = P.Startup
    startup1 : T.advance (physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.allocateBuffer))))) (serve (Physical.wrapP Old.c11) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.z1) ordinary T.empty)
    startup1 = Emb.lift-step (Physical.runP (P.run (U.startupStep Old.owner (Startup.allocateBuffer)))) (Physical.clean (Physical.wrapP Old.c11)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    startup2 : T.advance (physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.createBearer))))) (serve (Physical.wrapP Old.z1) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.z2) ordinary T.empty)
    startup2 = Emb.lift-step (Physical.runP (P.run (U.startupStep Old.owner (Startup.createBearer)))) (Physical.clean (Physical.wrapP Old.z1)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    startup3 : T.advance (physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.enterRun))))) (serve (Physical.wrapP Old.z2) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.z3) ordinary T.empty)
    startup3 = Emb.lift-step (Physical.runP (P.run (U.startupStep Old.owner (Startup.enterRun)))) (Physical.clean (Physical.wrapP Old.z2)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    startup4 : T.advance (physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.traceStarting))))) (serve (Physical.wrapP Old.z3) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.z4) ordinary T.empty)
    startup4 = Emb.lift-step (Physical.runP (P.run (U.startupStep Old.owner (Startup.traceStarting)))) (Physical.clean (Physical.wrapP Old.z3)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    startup5 : T.advance (physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.allocateEgress))))) (serve (Physical.wrapP Old.z4) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.z5) ordinary T.empty)
    startup5 = Emb.lift-step (Physical.runP (P.run (U.startupStep Old.owner (Startup.allocateEgress)))) (Physical.clean (Physical.wrapP Old.z4)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    startup6 : T.advance (physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.openPool))))) (serve (Physical.wrapP Old.z5) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.z6) ordinary T.empty)
    startup6 = Emb.lift-step (Physical.runP (P.run (U.startupStep Old.owner (Startup.openPool)))) (Physical.clean (Physical.wrapP Old.z5)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    startup7 : T.advance (physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.forkMuxer Old.j₀))))) (serve (Physical.wrapP Old.z6) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.z7) ordinary T.empty)
    startup7 = Emb.lift-step (Physical.runP (P.run (U.startupStep Old.owner (Startup.forkMuxer Old.j₀)))) (Physical.clean (Physical.wrapP Old.z6)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    startup8 : T.advance (physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.registerMuxer))))) (serve (Physical.wrapP Old.z7) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.z8) ordinary T.empty)
    startup8 = Emb.lift-step (Physical.runP (P.run (U.startupStep Old.owner (Startup.registerMuxer)))) (Physical.clean (Physical.wrapP Old.z7)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    startup9 : T.advance (physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.forkDemuxer Old.j₁))))) (serve (Physical.wrapP Old.z8) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.z9) ordinary T.empty)
    startup9 = Emb.lift-step (Physical.runP (P.run (U.startupStep Old.owner (Startup.forkDemuxer Old.j₁)))) (Physical.clean (Physical.wrapP Old.z8)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    startup10 : T.advance (physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.registerDemuxer))))) (serve (Physical.wrapP Old.z9) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.z10) ordinary T.empty)
    startup10 = Emb.lift-step (Physical.runP (P.run (U.startupStep Old.owner (Startup.registerDemuxer)))) (Physical.clean (Physical.wrapP Old.z9)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    startup11 : T.advance (physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.traceMature))))) (serve (Physical.wrapP Old.z10) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.z11) ordinary T.empty)
    startup11 = Emb.lift-step (Physical.runP (P.run (U.startupStep Old.owner (Startup.traceMature)))) (Physical.clean (Physical.wrapP Old.z10)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    startup12 : T.advance (physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.enterMonitor))))) (serve (Physical.wrapP Old.z11) ordinary T.empty) ≡ just (serve (Physical.wrapP Old.z12) ordinary T.empty)
    startup12 = Emb.lift-step (Physical.runP (P.run (U.startupStep Old.owner (Startup.enterMonitor)))) (Physical.clean (Physical.wrapP Old.z11)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
    private module Lift = ExitFacts RF.bearerClosed using (lift-step)
    monitor1 : T.advance (physicalEvent (W.run (G.run (M.run (P.control Old.owner P.selectCommand))))) (serve (Physical.wrapP Old.z12) ordinary T.empty) ≡ just (serve (Physical.wrapG (GF.wrap RF.error1)) ordinary preparedFront)
    monitor1 = Emb.lift-step (W.run (G.run (M.run (P.control Old.owner P.selectCommand)))) (Physical.clean (Physical.wrapP Old.z12)) (record context0 { regions = ordinary }) T.empty S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    monitor2 : T.advance (physicalEvent (W.run (G.run (M.run (P.control Old.owner (P.demand 1)))))) (serve (Physical.wrapG (GF.wrap RF.error1)) ordinary preparedFront) ≡ just (serve (Physical.wrapG (GF.wrap RF.error2)) ordinary preparedFront)
    monitor2 = Emb.lift-step (W.run (G.run (M.run (P.control Old.owner (P.demand 1))))) (Physical.clean (Physical.wrapG (GF.wrap RF.error1))) (record context0 { regions = ordinary }) preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    monitor3 : T.advance (physicalEvent (W.run (G.run (M.run (P.control Old.owner P.sampleTracer))))) (serve (Physical.wrapG (GF.wrap RF.error2)) ordinary preparedFront) ≡ just (serve (Physical.wrapG (GF.wrap RF.error3)) ordinary preparedFront)
    monitor3 = Emb.lift-step (W.run (G.run (M.run (P.control Old.owner P.sampleTracer)))) (Physical.clean (Physical.wrapG (GF.wrap RF.error2))) (record context0 { regions = ordinary }) preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    monitor4 : T.advance (physicalEvent (W.run (G.run (M.run (P.control Old.owner P.commitTracer))))) (serve (Physical.wrapG (GF.wrap RF.error3)) ordinary preparedFront) ≡ just (serve (Physical.wrapG (GF.wrap RF.error4)) ordinary preparedFront)
    monitor4 = Emb.lift-step (W.run (G.run (M.run (P.control Old.owner P.commitTracer)))) (Physical.clean (Physical.wrapG (GF.wrap RF.error3))) (record context0 { regions = ordinary }) preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    monitor5 : T.advance (physicalEvent (W.run (G.run (M.run (P.control Old.owner P.finishStart))))) (serve (Physical.wrapG (GF.wrap RF.error4)) ordinary preparedFront) ≡ just (serve (Physical.wrapG (GF.wrap RF.error5)) ordinary preparedFront)
    monitor5 = Emb.lift-step (W.run (G.run (M.run (P.control Old.owner P.finishStart)))) (Physical.clean (Physical.wrapG (GF.wrap RF.error4))) (record context0 { regions = ordinary }) preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    monitor6 : T.advance (physicalEvent (W.run (G.run (M.run (P.forkResponder Old.owner Old.j₁₀ Old.r₀))))) (serve (Physical.wrapG (GF.wrap RF.error5)) ordinary preparedFront) ≡ just (serve (Physical.wrapG (GF.wrap RF.error6)) ordinary preparedFront)
    monitor6 = Emb.lift-step (W.run (G.run (M.run (P.forkResponder Old.owner Old.j₁₀ Old.r₀)))) (Physical.clean (Physical.wrapG (GF.wrap RF.error5))) (record context0 { regions = ordinary }) preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    monitor7 : T.advance (physicalEvent (W.run (G.run (M.run (P.registerProtocol Old.j₁₀))))) (serve (Physical.wrapG (GF.wrap RF.error6)) ordinary preparedFront) ≡ just (serve (Physical.wrapG (GF.wrap RF.error7)) ordinary preparedFront)
    monitor7 = Emb.lift-step (W.run (G.run (M.run (P.registerProtocol Old.j₁₀)))) (Physical.clean (Physical.wrapG (GF.wrap RF.error6))) (record context0 { regions = ordinary }) preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    group1 : T.advance (physicalEvent (W.run (GF.W.requestShutdown Old.owner))) (serve (Physical.wrapG GF.normal0) ordinary preparedFront) ≡ just (serve (Physical.wrapG GF.normal1) ordinary preparedFront)
    group1 = Emb.lift-step (W.run (GF.W.requestShutdown Old.owner)) (Physical.clean (Physical.wrapG GF.normal0)) (record context0 { regions = ordinary }) preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    group2 : T.advance (physicalEvent (W.run (GF.W.selectShutdown Old.owner))) (serve (Physical.wrapG GF.normal1) ordinary preparedFront) ≡ just (serve (Physical.wrapG GF.normal2) ordinary preparedFront)
    group2 = Emb.lift-step (W.run (GF.W.selectShutdown Old.owner)) (Physical.clean (Physical.wrapG GF.normal1)) (record context0 { regions = ordinary }) preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    group3 : T.advance (physicalEvent (W.run (GF.W.observeStoppingTrace Old.owner))) (serve (Physical.wrapG GF.normal2) ordinary preparedFront) ≡ just (serve (Physical.wrapG GF.normal3) ordinary preparedFront)
    group3 = Emb.lift-step (W.run (GF.W.observeStoppingTrace Old.owner)) (Physical.clean (Physical.wrapG GF.normal2)) (record context0 { regions = ordinary }) preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    group4 : T.advance (physicalEvent (W.run (GF.W.writeStopping Old.owner))) (serve (Physical.wrapG GF.normal3) ordinary preparedFront) ≡ just (serve (Physical.wrapG GF.normal4) ordinary preparedFront)
    group4 = Emb.lift-step (W.run (GF.W.writeStopping Old.owner)) (Physical.clean (Physical.wrapG GF.normal3)) (record context0 { regions = ordinary }) preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    group5 : T.advance (physicalEvent (W.run (GF.W.captureGroup Old.owner (Old.j₁₀ ∷ [])))) (serve (Physical.wrapG GF.normal4) ordinary preparedFront) ≡ just (serve (Physical.wrapG GF.normal5) ordinary preparedFront)
    group5 = Emb.lift-step (W.run (GF.W.captureGroup Old.owner (Old.j₁₀ ∷ []))) (Physical.clean (Physical.wrapG GF.normal4)) (record context0 { regions = ordinary }) preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    group6 : T.advance (physicalEvent (W.run (GF.W.requestGroupCancel Old.owner))) (serve (Physical.wrapG GF.normal5) ordinary preparedFront) ≡ just (serve (Physical.wrapG GF.normal6) ordinary preparedFront)
    group6 = Emb.lift-step (W.run (GF.W.requestGroupCancel Old.owner)) (Physical.clean (Physical.wrapG GF.normal5)) (record context0 { regions = ordinary }) preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    group7 : T.advance (physicalEvent (W.run (GF.W.deliverGroup Old.owner))) (serve (Physical.wrapG GF.normal6) ordinary preparedFront) ≡ just (serve (Physical.wrapG GF.normal7) ordinary preparedFront)
    group7 = Emb.lift-step (W.run (GF.W.deliverGroup Old.owner)) (Physical.clean (Physical.wrapG GF.normal6)) (record context0 { regions = ordinary }) preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
    beforeForkEvents : List T.Event
    beforeForkEvents = coreEvent (O.beginAcquire Old.Fixture.caller Old.Fixture.req) ∷ coreEvent (O.acquire Old.Fixture.caller (Acquire.select nothing)) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.readCounters) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.newPromise) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.openOK) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.configureOK) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.connectOK) ∷ coreEvent (O.acquire Old.Fixture.caller (Acquire.gotLocal (local key₀))) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.updateLocalAddress) ∷ []
    birthEvents : List T.Event
    birthEvents = coreEvent (O.beginAcquire Old.Fixture.caller Old.Fixture.req) ∷ coreEvent (O.acquire Old.Fixture.caller (Acquire.select nothing)) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.readCounters) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.newPromise) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.openOK) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.configureOK) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.connectOK) ∷ coreEvent (O.acquire Old.Fixture.caller (Acquire.gotLocal (local key₀))) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.updateLocalAddress) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.forkOK) ∷ []
    afterBirthEvents : List T.Event
    afterBirthEvents = physicalEvent (Physical.runP (P.run (U.run (B.handler (H.enterHandshake Old.owner))))) ∷ handoffEvent ∷ call Acquire.commitConnected ∷ physicalEvent (Physical.runP (P.run (U.negotiate Old.owner PF.ps duplex))) ∷ physicalEvent (Physical.runP (P.run (U.allocateHandle Old.owner (ident 0) Old.mid))) ∷ physicalEvent (Physical.runP (P.run (U.publishSuccess Old.owner))) ∷ call Acquire.readCounters ∷ call Acquire.readResult ∷ call Acquire.commitHandshake ∷ call Acquire.readCounters ∷ call Acquire.returnResult ∷ physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.captureTime 0))))))) ∷ physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.registerInactivity))))))) ∷ physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.selectBatch))))))) ∷ physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.readEvent))))))) ∷ physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.registerIdleTimer))))))) ∷ physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.runResponders))))))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.allocateBuffer)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.createBearer)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.enterRun)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.traceStarting)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.allocateEgress)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.openPool)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.forkMuxer Old.j₀)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.registerMuxer)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.forkDemuxer Old.j₁)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.registerDemuxer)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.traceMature)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.enterMonitor)))) ∷ physicalEvent (W.run (G.run (M.run (P.control Old.owner P.selectCommand)))) ∷ physicalEvent (W.run (G.run (M.run (P.control Old.owner (P.demand 1))))) ∷ physicalEvent (W.run (G.run (M.run (P.control Old.owner P.sampleTracer)))) ∷ physicalEvent (W.run (G.run (M.run (P.control Old.owner P.commitTracer)))) ∷ physicalEvent (W.run (G.run (M.run (P.control Old.owner P.finishStart)))) ∷ physicalEvent (W.run (G.run (M.run (P.forkResponder Old.owner Old.j₁₀ Old.r₀)))) ∷ physicalEvent (W.run (G.run (M.run (P.registerProtocol Old.j₁₀)))) ∷ physicalEvent (W.run (GF.W.requestShutdown Old.owner)) ∷ physicalEvent (W.run (GF.W.selectShutdown Old.owner)) ∷ physicalEvent (W.run (GF.W.observeStoppingTrace Old.owner)) ∷ physicalEvent (W.run (GF.W.writeStopping Old.owner)) ∷ physicalEvent (W.run (GF.W.captureGroup Old.owner (Old.j₁₀ ∷ []))) ∷ physicalEvent (W.run (GF.W.requestGroupCancel Old.owner)) ∷ physicalEvent (W.run (GF.W.deliverGroup Old.owner)) ∷ []
    prefixEvents : List T.Event
    prefixEvents = coreEvent (O.beginAcquire Old.Fixture.caller Old.Fixture.req) ∷ coreEvent (O.acquire Old.Fixture.caller (Acquire.select nothing)) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.readCounters) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.newPromise) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.openOK) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.configureOK) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.connectOK) ∷ coreEvent (O.acquire Old.Fixture.caller (Acquire.gotLocal (local key₀))) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.updateLocalAddress) ∷ coreEvent (O.acquire Old.Fixture.caller Acquire.forkOK) ∷ physicalEvent (Physical.runP (P.run (U.run (B.handler (H.enterHandshake Old.owner))))) ∷ handoffEvent ∷ call Acquire.commitConnected ∷ physicalEvent (Physical.runP (P.run (U.negotiate Old.owner PF.ps duplex))) ∷ physicalEvent (Physical.runP (P.run (U.allocateHandle Old.owner (ident 0) Old.mid))) ∷ physicalEvent (Physical.runP (P.run (U.publishSuccess Old.owner))) ∷ call Acquire.readCounters ∷ call Acquire.readResult ∷ call Acquire.commitHandshake ∷ call Acquire.readCounters ∷ call Acquire.returnResult ∷ physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.captureTime 0))))))) ∷ physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.registerInactivity))))))) ∷ physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.selectBatch))))))) ∷ physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.readEvent))))))) ∷ physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.registerIdleTimer))))))) ∷ physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.runResponders))))))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.allocateBuffer)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.createBearer)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.enterRun)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.traceStarting)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.allocateEgress)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.openPool)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.forkMuxer Old.j₀)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.registerMuxer)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.forkDemuxer Old.j₁)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.registerDemuxer)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.traceMature)))) ∷ physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.enterMonitor)))) ∷ physicalEvent (W.run (G.run (M.run (P.control Old.owner P.selectCommand)))) ∷ physicalEvent (W.run (G.run (M.run (P.control Old.owner (P.demand 1))))) ∷ physicalEvent (W.run (G.run (M.run (P.control Old.owner P.sampleTracer)))) ∷ physicalEvent (W.run (G.run (M.run (P.control Old.owner P.commitTracer)))) ∷ physicalEvent (W.run (G.run (M.run (P.control Old.owner P.finishStart)))) ∷ physicalEvent (W.run (G.run (M.run (P.forkResponder Old.owner Old.j₁₀ Old.r₀)))) ∷ physicalEvent (W.run (G.run (M.run (P.registerProtocol Old.j₁₀)))) ∷ physicalEvent (W.run (GF.W.requestShutdown Old.owner)) ∷ physicalEvent (W.run (GF.W.selectShutdown Old.owner)) ∷ physicalEvent (W.run (GF.W.observeStoppingTrace Old.owner)) ∷ physicalEvent (W.run (GF.W.writeStopping Old.owner)) ∷ physicalEvent (W.run (GF.W.captureGroup Old.owner (Old.j₁₀ ∷ []))) ∷ physicalEvent (W.run (GF.W.requestGroupCancel Old.owner)) ∷ physicalEvent (W.run (GF.W.deliverGroup Old.owner)) ∷ []
    abstract
      actualBeforeFork : T.Runs start beforeForkEvents beforeFork
      actualBeforeFork = T.more {a = coreEvent (O.beginAcquire Old.Fixture.caller Old.Fixture.req)} core1 (T.more {a = coreEvent (O.acquire Old.Fixture.caller (Acquire.select nothing))} core2 (T.more {a = coreEvent (O.acquire Old.Fixture.caller Acquire.readCounters)} core3 (T.more {a = coreEvent (O.acquire Old.Fixture.caller Acquire.newPromise)} core4 (T.more {a = coreEvent (O.acquire Old.Fixture.caller Acquire.openOK)} core5 (T.more {a = coreEvent (O.acquire Old.Fixture.caller Acquire.configureOK)} core6 (T.more {a = coreEvent (O.acquire Old.Fixture.caller Acquire.connectOK)} core7 (T.more {a = coreEvent (O.acquire Old.Fixture.caller (Acquire.gotLocal (local key₀)))} core8 (T.more {a = coreEvent (O.acquire Old.Fixture.caller Acquire.updateLocalAddress)} core9 (T.stop)))))))))
      actualBirth : T.Runs start birthEvents born
      actualBirth = T.more {a = coreEvent (O.beginAcquire Old.Fixture.caller Old.Fixture.req)} core1 (T.more {a = coreEvent (O.acquire Old.Fixture.caller (Acquire.select nothing))} core2 (T.more {a = coreEvent (O.acquire Old.Fixture.caller Acquire.readCounters)} core3 (T.more {a = coreEvent (O.acquire Old.Fixture.caller Acquire.newPromise)} core4 (T.more {a = coreEvent (O.acquire Old.Fixture.caller Acquire.openOK)} core5 (T.more {a = coreEvent (O.acquire Old.Fixture.caller Acquire.configureOK)} core6 (T.more {a = coreEvent (O.acquire Old.Fixture.caller Acquire.connectOK)} core7 (T.more {a = coreEvent (O.acquire Old.Fixture.caller (Acquire.gotLocal (local key₀)))} core8 (T.more {a = coreEvent (O.acquire Old.Fixture.caller Acquire.updateLocalAddress)} core9 (T.more {a = coreEvent (O.acquire Old.Fixture.caller Acquire.forkOK)} core10 (T.stop))))))))))
      actualAfterBirth : T.Runs born afterBirthEvents beforeAbort
      actualAfterBirth = T.more {a = physicalEvent (Physical.runP (P.run (U.run (B.handler (H.enterHandshake Old.owner)))))} childEnters (T.more {a = handoffEvent} handoff (T.more {a = call Acquire.commitConnected} commitConnected (T.more {a = physicalEvent (Physical.runP (P.run (U.negotiate Old.owner PF.ps duplex)))} publication1 (T.more {a = physicalEvent (Physical.runP (P.run (U.allocateHandle Old.owner (ident 0) Old.mid)))} publication2 (T.more {a = physicalEvent (Physical.runP (P.run (U.publishSuccess Old.owner)))} publication3 (T.more {a = call Acquire.readCounters} caller1 (T.more {a = call Acquire.readResult} caller2 (T.more {a = call Acquire.commitHandshake} caller3 (T.more {a = call Acquire.readCounters} caller4 (T.more {a = call Acquire.returnResult} caller5 (T.more {a = physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.captureTime 0)))))))} registration6 (T.more {a = physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.registerInactivity)))))))} registration7 (T.more {a = physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.selectBatch)))))))} registration8 (T.more {a = physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.readEvent)))))))} registration9 (T.more {a = physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.registerIdleTimer)))))))} registration10 (T.more {a = physicalEvent (Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep (IG.runResponders)))))))} registration11 (T.more {a = physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.allocateBuffer))))} startup1 (T.more {a = physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.createBearer))))} startup2 (T.more {a = physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.enterRun))))} startup3 (T.more {a = physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.traceStarting))))} startup4 (T.more {a = physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.allocateEgress))))} startup5 (T.more {a = physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.openPool))))} startup6 (T.more {a = physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.forkMuxer Old.j₀))))} startup7 (T.more {a = physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.registerMuxer))))} startup8 (T.more {a = physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.forkDemuxer Old.j₁))))} startup9 (T.more {a = physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.registerDemuxer))))} startup10 (T.more {a = physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.traceMature))))} startup11 (T.more {a = physicalEvent (Physical.runP (P.run (U.startupStep Old.owner (Startup.enterMonitor))))} startup12 (T.more {a = physicalEvent (W.run (G.run (M.run (P.control Old.owner P.selectCommand))))} monitor1 (T.more {a = physicalEvent (W.run (G.run (M.run (P.control Old.owner (P.demand 1)))))} monitor2 (T.more {a = physicalEvent (W.run (G.run (M.run (P.control Old.owner P.sampleTracer))))} monitor3 (T.more {a = physicalEvent (W.run (G.run (M.run (P.control Old.owner P.commitTracer))))} monitor4 (T.more {a = physicalEvent (W.run (G.run (M.run (P.control Old.owner P.finishStart))))} monitor5 (T.more {a = physicalEvent (W.run (G.run (M.run (P.forkResponder Old.owner Old.j₁₀ Old.r₀))))} monitor6 (T.more {a = physicalEvent (W.run (G.run (M.run (P.registerProtocol Old.j₁₀))))} monitor7 (T.more {a = physicalEvent (W.run (GF.W.requestShutdown Old.owner))} group1 (T.more {a = physicalEvent (W.run (GF.W.selectShutdown Old.owner))} group2 (T.more {a = physicalEvent (W.run (GF.W.observeStoppingTrace Old.owner))} group3 (T.more {a = physicalEvent (W.run (GF.W.writeStopping Old.owner))} group4 (T.more {a = physicalEvent (W.run (GF.W.captureGroup Old.owner (Old.j₁₀ ∷ [])))} group5 (T.more {a = physicalEvent (W.run (GF.W.requestGroupCancel Old.owner))} group6 (T.more {a = physicalEvent (W.run (GF.W.deliverGroup Old.owner))} group7 (T.stop)))))))))))))))))))))))))))))))))))))))))))
      actualPrefix : T.Runs start prefixEvents beforeAbort
      actualPrefix = append actualBirth actualAfterBirth

  module PhysicalSuffix where
    module Prefix = PhysicalPrefix
    open import Data.Bool using (true; false)
    open import Data.List using (List; []; _∷_; _++_; map; take; drop)
    open import Data.List.Membership.Propositional using (_∈_)
    open import Data.List.Relation.Unary.Any using (here)
    open import Data.Maybe using (just; nothing)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    open import ConnectionManagement.Domain using (ident)
    open import ConnectionManagement.Store using (lookup)
    import ConnectionManagement.State as Shared
    import ConnectionManagement.Rules.CMShutdown as Close
    import ConnectionManagement.Rules.Cleanup as Cleanup
    import ConnectionManagement.HandlerSupervision as H
    import ConnectionManagement.OutboundHandlerSupervision as B
    import ConnectionManagement.MuxHandlerExit as Exit
    import ConnectionManagement.MuxGroupShutdown as Group
    import ConnectionManagement.MuxResultMonitor as Monitor
    import ConnectionManagement.MuxProtocolJobs as P
    import ConnectionManagement.Negative.MuxProtocolJobs as Old
    import ConnectionManagement.Negative.MuxGroupShutdown as GF
    import ConnectionManagement.Negative.MuxHandlerExit as EF
    import ConnectionManagement.Negative.MuxResultMonitor as RF
    import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
    import ConnectionManagement.Rules.MuxJobTypes as Types
    import ConnectionManagement.Rules.MuxRuntime as Mux
    import ConnectionManagement.Rules.IGRegistration as IG
    import ConnectionManagement.OutboundMachine as O
    import ConnectionManagement.Machine as Machine
    open import Data.Product using (_,_)


    module W = Exit RF.bearerClosed
    module G = Group RF.bearerClosed
    module M = Monitor RF.bearerClosed
    private module Lift = ExitFacts RF.bearerClosed using (wrap)
    owner = Old.owner
    err = Old.err

    -- The real IG exit changes its active flag, loop continuation and queue.
    -- After deactivation, a sampled Dead callback skips the IG tracer transaction,
    -- retaining its previously sampled counters. These are expected snapshots;
    -- every inherited action must still prove its own guarded equation below.
    inactiveCallback : Mux.Callback → Mux.Callback
    inactiveCallback (Mux.commitTrace flag trace) = Mux.commitTrace false trace
    inactiveCallback callback = callback
    inactiveMux : Mux.Mux → Mux.Mux
    inactiveMux savedMux = record savedMux
     { callback = inactiveCallback (Mux.callback savedMux)
     ; traceCounters = Mux.traceCounters Old.m6 }
    exited : W.State → W.State
    exited original = W.setSource (record source
     { core = record core
      { inboundGovernor = record governor
       { continuation = IG.exited
       ; execution = record (IG.execution governor)
        { active = false
        ; muxes = map (λ { (mid , savedMux) → mid , inactiveMux savedMux }) (IG.muxes (IG.execution governor)) } }
      ; world = record (Machine.world core) { inboundInfo = [] } } }) physical
     where
     physical = Prefix.clean original
     source = W.source physical
     core = O.core source
     governor = Machine.inboundGovernor core

    -- CM metadata stays fixed only across noncoordinator actions. It is not an
    -- executable reset: the quantified equations below certify each real write.
    hold : Close.State → W.State → W.State
    hold coordinator physical = W.setShutdown coordinator (exited physical)

    wrap : G.State → W.State
    wrap = Lift.wrap

    captured selected requested acknowledged awaiting closed : Close.State
    captured = Close.shutdownState Close.reading (ident 0 ∷ []) (ident 0 ∷ []) []
    selected = Close.shutdownState (Close.sendReady (ident 0) owner) (ident 0 ∷ []) [] []
    requested = Close.shutdownState (Close.awaitDelivery (ident 0) owner) (ident 0 ∷ []) [] []
    acknowledged = Close.shutdownState Close.reading (ident 0 ∷ []) [] (owner ∷ [])
    awaiting = record acknowledged { phase = Close.awaitResults }
    closed = record acknowledged { phase = Close.closed }

    beforeCM capturedCM selectedCM requestedCM receiptCM : W.State
    beforeCM = exited (wrap GF.abortGroup0)
    capturedCM = hold captured beforeCM
    selectedCM = hold selected beforeCM
    requestedCM = hold requested beforeCM
    receiptCM = hold acknowledged (wrap GF.abortGroup1)

    capture : W.step (W.shutdownStep Close.captureSnapshot) beforeCM ≡ just capturedCM
    capture = refl
    read : W.step (W.shutdownStep Close.readEntry) capturedCM ≡ just selectedCM
    read = refl
    request : W.step (W.shutdownStep Close.requestCancellation) selectedCM ≡ just requestedCM
    request = refl
    receipt : W.step (W.deliverShutdownMux err) requestedCM ≡ just receiptCM
    receipt = refl

    group2 : ∀ coordinator → W.step (W.run (G.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []))) (hold coordinator (wrap GF.abortGroup1)) ≡ just (hold coordinator (wrap GF.abortGroup2))
    group2 coordinator = refl

    group3 : ∀ coordinator → W.step (W.run (G.requestWholeCancel owner)) (hold coordinator (wrap GF.abortGroup2)) ≡ just (hold coordinator (wrap GF.abortGroup3))
    group3 coordinator = refl

    group4 : ∀ coordinator → W.step (W.run (G.finishChildUnwind Old.j₁₀)) (hold coordinator (wrap GF.abortGroup3)) ≡ just (hold coordinator (wrap GF.abortGroup4))
    group4 coordinator = refl

    group5 : ∀ coordinator → W.step (W.run (G.run (M.run (P.deregisterProtocol Old.j₁₀)))) (hold coordinator (wrap GF.abortGroup4)) ≡ just (hold coordinator (wrap GF.abortGroup5))
    group5 coordinator = refl

    group6 : ∀ coordinator → W.step (W.run (G.run (M.run (P.asyncProtocolResult Old.j₁₀)))) (hold coordinator (wrap GF.abortGroup5)) ≡ just (hold coordinator (wrap GF.abortGroup6))
    group6 coordinator = refl

    group7 : ∀ coordinator → W.step (W.run (G.joinWhole owner)) (hold coordinator (wrap GF.abortGroup6)) ≡ just (hold coordinator (wrap GF.abortGroup7))
    group7 coordinator = refl

    group8 : ∀ coordinator → W.step (W.run (G.requestWholeCancel owner)) (hold coordinator (wrap GF.abortGroup7)) ≡ just (hold coordinator (wrap GF.abortGroup8))
    group8 coordinator = refl

    group9 : ∀ coordinator → W.step (W.run (G.deliverWhole owner)) (hold coordinator (wrap GF.abortGroup8)) ≡ just (hold coordinator (wrap GF.abortGroup9))
    group9 coordinator = refl

    group10 : ∀ coordinator → W.step (W.run (G.finishChildUnwind Old.j₁)) (hold coordinator (wrap GF.abortGroup9)) ≡ just (hold coordinator (wrap GF.abortGroup10))
    group10 coordinator = refl

    group11 : ∀ coordinator → W.step (W.run (G.run (M.run (P.deregisterInfra owner Types.demuxer)))) (hold coordinator (wrap GF.abortGroup10)) ≡ just (hold coordinator (wrap GF.abortGroup11))
    group11 coordinator = refl

    group12 : ∀ coordinator → W.step (W.run (G.run (M.run (P.asyncInfraResult owner Types.demuxer)))) (hold coordinator (wrap GF.abortGroup11)) ≡ just (hold coordinator (wrap GF.abortGroup12))
    group12 coordinator = refl

    group13 : ∀ coordinator → W.step (W.run (G.joinWhole owner)) (hold coordinator (wrap GF.abortGroup12)) ≡ just (hold coordinator (wrap GF.abortGroup13))
    group13 coordinator = refl

    group14 : ∀ coordinator → W.step (W.run (G.requestWholeCancel owner)) (hold coordinator (wrap GF.abortGroup13)) ≡ just (hold coordinator (wrap GF.abortGroup14))
    group14 coordinator = refl

    group15 : ∀ coordinator → W.step (W.run (G.deliverWhole owner)) (hold coordinator (wrap GF.abortGroup14)) ≡ just (hold coordinator (wrap GF.abortGroup15))
    group15 coordinator = refl

    group16 : ∀ coordinator → W.step (W.run (G.finishChildUnwind Old.j₀)) (hold coordinator (wrap GF.abortGroup15)) ≡ just (hold coordinator (wrap GF.abortGroup16))
    group16 coordinator = refl

    group17 : ∀ coordinator → W.step (W.run (G.run (M.run (P.deregisterInfra owner Types.muxer)))) (hold coordinator (wrap GF.abortGroup16)) ≡ just (hold coordinator (wrap GF.abortGroup17))
    group17 coordinator = refl

    group18 : ∀ coordinator → W.step (W.run (G.run (M.run (P.asyncInfraResult owner Types.muxer)))) (hold coordinator (wrap GF.abortGroup17)) ≡ just (hold coordinator (wrap GF.abortGroup18))
    group18 coordinator = refl

    group19 : ∀ coordinator → W.step (W.run (G.joinWhole owner)) (hold coordinator (wrap GF.abortGroup18)) ≡ just (hold coordinator (wrap GF.abortGroup19))
    group19 coordinator = refl

    group20 : ∀ coordinator → W.step (W.run (G.finishWholeClose owner)) (hold coordinator (wrap GF.abortGroup19)) ≡ just (hold coordinator (wrap GF.abortGroup20))
    group20 coordinator = refl

    group21 : ∀ coordinator → W.step (W.run (G.writeAsyncFailure owner)) (hold coordinator (wrap GF.abortGroup20)) ≡ just (hold coordinator (wrap GF.abortGroup21))
    group21 coordinator = refl

    group22 : ∀ coordinator → W.step (W.run (G.beginAsyncDead owner)) (hold coordinator (wrap GF.abortGroup21)) ≡ just (hold coordinator (wrap GF.abortGroup22))
    group22 coordinator = refl

    group23 : ∀ coordinator → W.step (W.run (G.sampleAsyncTracer owner)) (hold coordinator (wrap GF.abortGroup22)) ≡ just (hold coordinator (wrap GF.abortGroup23))
    group23 coordinator = refl

    group24 : ∀ coordinator → W.step (W.run (G.commitAsyncTracer owner)) (hold coordinator (wrap GF.abortGroup23)) ≡ just (hold coordinator (wrap GF.abortGroup24))
    group24 coordinator = refl

    group25 : ∀ coordinator → W.step (W.run (G.finishAsyncDead owner)) (hold coordinator (wrap GF.abortGroup24)) ≡ just (hold coordinator (wrap GF.abortGroup25))
    group25 coordinator = refl


    abortTailActions : List W.Action
    abortTailActions = map W.run (drop 1 GF.abortGroupActions)

    abstract
     abortTail : ∀ coordinator → W.Executes (hold coordinator (wrap GF.abortGroup1)) abortTailActions (hold coordinator EF.async0)
     abortTail coordinator = W.next {a = W.run (G.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []))} (group2 coordinator) (W.next {a = W.run (G.requestWholeCancel owner)} (group3 coordinator) (W.next {a = W.run (G.finishChildUnwind Old.j₁₀)} (group4 coordinator) (W.next {a = W.run (G.run (M.run (P.deregisterProtocol Old.j₁₀)))} (group5 coordinator) (W.next {a = W.run (G.run (M.run (P.asyncProtocolResult Old.j₁₀)))} (group6 coordinator) (W.next {a = W.run (G.joinWhole owner)} (group7 coordinator) (W.next {a = W.run (G.requestWholeCancel owner)} (group8 coordinator) (W.next {a = W.run (G.deliverWhole owner)} (group9 coordinator) (W.next {a = W.run (G.finishChildUnwind Old.j₁)} (group10 coordinator) (W.next {a = W.run (G.run (M.run (P.deregisterInfra owner Types.demuxer)))} (group11 coordinator) (W.next {a = W.run (G.run (M.run (P.asyncInfraResult owner Types.demuxer)))} (group12 coordinator) (W.next {a = W.run (G.joinWhole owner)} (group13 coordinator) (W.next {a = W.run (G.requestWholeCancel owner)} (group14 coordinator) (W.next {a = W.run (G.deliverWhole owner)} (group15 coordinator) (W.next {a = W.run (G.finishChildUnwind Old.j₀)} (group16 coordinator) (W.next {a = W.run (G.run (M.run (P.deregisterInfra owner Types.muxer)))} (group17 coordinator) (W.next {a = W.run (G.run (M.run (P.asyncInfraResult owner Types.muxer)))} (group18 coordinator) (W.next {a = W.run (G.joinWhole owner)} (group19 coordinator) (W.next {a = W.run (G.finishWholeClose owner)} (group20 coordinator) (W.next {a = W.run (G.writeAsyncFailure owner)} (group21 coordinator) (W.next {a = W.run (G.beginAsyncDead owner)} (group22 coordinator) (W.next {a = W.run (G.sampleAsyncTracer owner)} (group23 coordinator) (W.next {a = W.run (G.commitAsyncTracer owner)} (group24 coordinator) (W.next {a = W.run (G.finishAsyncDead owner)} (group25 coordinator) (W.done))))))))))))))))))))))))

    async1 : ∀ coordinator → W.step (W.beginExit owner) (hold coordinator EF.async0) ≡ just (hold coordinator EF.async1)
    async1 coordinator = refl

    async2 : ∀ coordinator → W.step (W.observeBufferReturn owner) (hold coordinator EF.async1) ≡ just (hold coordinator EF.async2)
    async2 coordinator = refl

    async3 : ∀ coordinator → W.step (W.enterFinalizer owner) (hold coordinator EF.async2) ≡ just (hold coordinator EF.async3)
    async3 coordinator = refl

    async4 : ∀ coordinator → W.step (W.cleanup owner Cleanup.takeCleanupMap) (hold coordinator EF.async3) ≡ just (hold coordinator EF.async4)
    async4 coordinator = refl

    async5 : ∀ coordinator → W.step (W.cleanup owner Cleanup.selectCleanupEntry) (hold coordinator EF.async4) ≡ just (hold coordinator EF.async5)
    async5 coordinator = refl

    async6 : ∀ coordinator → W.step (W.cleanup owner Cleanup.closeHandlerSocket) (hold coordinator EF.async5) ≡ just (hold coordinator EF.async6)
    async6 coordinator = refl

    async7 : ∀ coordinator → W.step (W.cleanup owner Cleanup.publishCleanupMap) (hold coordinator EF.async6) ≡ just (hold coordinator EF.async7)
    async7 coordinator = refl

    async8 : ∀ coordinator → W.step (W.cleanup owner Cleanup.readCleanupCounters) (hold coordinator EF.async7) ≡ just (hold coordinator EF.async8)
    async8 coordinator = refl

    async9 : ∀ coordinator → W.step (W.finishCleanup owner) (hold coordinator EF.async8) ≡ just (hold coordinator EF.async9)
    async9 coordinator = refl

    async10 : ∀ coordinator → W.step (W.publishAsyncResult owner) (hold coordinator EF.async9) ≡ just (hold coordinator EF.async10)
    async10 coordinator = refl


    cleanupActions : List W.Action
    cleanupActions = take 9 EF.asyncActions
    abstract
     cleanupPath : ∀ coordinator → W.Executes (hold coordinator EF.async0) cleanupActions (hold coordinator EF.async9)
     cleanupPath coordinator = W.next {a = (W.beginExit owner)} (async1 coordinator) (W.next {a = (W.observeBufferReturn owner)} (async2 coordinator) (W.next {a = (W.enterFinalizer owner)} (async3 coordinator) (W.next {a = (W.cleanup owner Cleanup.takeCleanupMap)} (async4 coordinator) (W.next {a = (W.cleanup owner Cleanup.selectCleanupEntry)} (async5 coordinator) (W.next {a = (W.cleanup owner Cleanup.closeHandlerSocket)} (async6 coordinator) (W.next {a = (W.cleanup owner Cleanup.publishCleanupMap)} (async7 coordinator) (W.next {a = (W.cleanup owner Cleanup.readCleanupCounters)} (async8 coordinator) (W.next {a = (W.finishCleanup owner)} (async9 coordinator) (W.done)))))))))

    abstract
     asyncPath : ∀ coordinator → W.Executes (hold coordinator EF.async0) EF.asyncActions (hold coordinator EF.async10)
     asyncPath coordinator = W.next {a = (W.beginExit owner)} (async1 coordinator) (W.next {a = (W.observeBufferReturn owner)} (async2 coordinator) (W.next {a = (W.enterFinalizer owner)} (async3 coordinator) (W.next {a = (W.cleanup owner Cleanup.takeCleanupMap)} (async4 coordinator) (W.next {a = (W.cleanup owner Cleanup.selectCleanupEntry)} (async5 coordinator) (W.next {a = (W.cleanup owner Cleanup.closeHandlerSocket)} (async6 coordinator) (W.next {a = (W.cleanup owner Cleanup.publishCleanupMap)} (async7 coordinator) (W.next {a = (W.cleanup owner Cleanup.readCleanupCounters)} (async8 coordinator) (W.next {a = (W.finishCleanup owner)} (async9 coordinator) (W.next {a = (W.publishAsyncResult owner)} (async10 coordinator) (W.done))))))))))

    append : ∀ {s as t bs u} → W.Executes s as t → W.Executes t bs u → W.Executes s (as ++ bs) u
    append W.done rest = rest
    append (W.next actual path) rest = W.next actual (append path rest)

    throughCleanupActions : List W.Action
    throughCleanupActions = abortTailActions ++ cleanupActions
    throughPublicationActions : List W.Action
    throughPublicationActions = abortTailActions ++ EF.asyncActions
    abstract
     throughCleanup : W.Executes receiptCM throughCleanupActions (hold acknowledged EF.async9)
     throughCleanup = append (abortTail acknowledged) (cleanupPath acknowledged)
     throughPublication : W.Executes receiptCM throughPublicationActions (hold acknowledged EF.async10)
     throughPublication = append (abortTail acknowledged) (asyncPath acknowledged)

    traverse : W.step (W.shutdownStep Close.finishTraversal) (hold acknowledged EF.async10) ≡ just (hold awaiting EF.async10)
    traverse = refl
    wait : W.step (W.shutdownStep Close.finishClose) (hold awaiting EF.async10) ≡ just (hold closed EF.async10)
    wait = refl

    -- The real receipt remains distinct from pool/cleanup/result availability.
    receiptNoResult : W.resultReady owner receiptCM ≡ false
    receiptNoResult = refl
    cleanupNoResult : W.resultReady owner (hold acknowledged EF.async9) ≡ false
    cleanupNoResult = refl
    publishedResult : W.resultReady owner (hold acknowledged EF.async10) ≡ true
    publishedResult = refl
    physicalOutcome : W.resultOf owner (hold acknowledged EF.async10) ≡ just (W.asyncException err)
    physicalOutcome = refl
    collectedAtReceipt : owner ∈ Close.collected (W.shutdown receiptCM)
    collectedAtReceipt = here refl
    collectedAtWait : owner ∈ Close.collected (W.shutdown (hold closed EF.async10))
    collectedAtWait = here refl

    prematureReceipt : W.step (W.deliverShutdownMux err) beforeCM ≡ nothing
    prematureReceipt = refl
    duplicateReceipt : W.step (W.deliverShutdownMux err) receiptCM ≡ nothing
    duplicateReceipt = refl
    poolCloseNoResult : W.resultReady owner (hold acknowledged (wrap GF.abortGroup20)) ≡ false
    poolCloseNoResult = refl
    prematurePublication : W.step (W.publishAsyncResult owner) (hold acknowledged EF.async8) ≡ nothing
    prematurePublication = refl
    duplicatePublication : W.step (W.publishAsyncResult owner) (hold acknowledged EF.async10) ≡ nothing
    duplicatePublication = refl
    noWaitAtReceipt : W.step (W.shutdownStep Close.finishClose) receiptCM ≡ nothing
    noWaitAtReceipt = refl
    noWaitAtCleanup : W.step (W.shutdownStep Close.finishClose) (hold awaiting EF.async9) ≡ nothing
    noWaitAtCleanup = refl
    duplicateWait : W.step (W.shutdownStep Close.finishClose) (hold closed EF.async10) ≡ nothing
    duplicateWait = refl
    rawAckBypass : W.step (W.shutdownStep Close.acknowledgeDelivery) requestedCM ≡ nothing
    rawAckBypass = refl
    finishedAckNoResult : W.step W.acknowledgeFinished requestedCM ≡ nothing
    finishedAckNoResult = refl
    standaloneAbort : W.step (W.run (G.abortOwner owner err)) requestedCM ≡ just (hold requested (wrap GF.abortGroup1))
    standaloneAbort = refl
    standaloneLeavesUncollected : Close.collected (W.shutdown (hold requested (wrap GF.abortGroup1))) ≡ []
    standaloneLeavesUncollected = refl

  module ScopeClose where
    open import Data.Bool using (Bool; true; false)
    open import Data.List using (List; []; _∷_; _++_)
    open import Data.Maybe using (just; nothing)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    import ConnectionManagement.OutboundMachine as O
    import ConnectionManagement.Machine as Machine
    import ConnectionManagement.Rules.IGRegistration as IG
    import ConnectionManagement.Rules.AsyncScope as Scope
    import ConnectionManagement.PeerContext as Context
    import ConnectionManagement.PeerSupervision as Supervision
    import ConnectionManagement.GovernorPool as Governor
    import ConnectionManagement.Properties.ServerPeersMonitorJoins as Joins
    import ConnectionManagement.ServerPeers as Combined
    import ConnectionManagement.ServerAdmission as Server
    import ConnectionManagement.ServerIGExit as IGExit
    import ConnectionManagement.MuxHandlerExit as Exit
    import ConnectionManagement.Properties.ServerPeersMuxEmbedding as Embedding
    import ConnectionManagement.Negative.MuxProtocolJobs as Old
    import ConnectionManagement.Negative.MuxResultMonitor as RF
    import ConnectionManagement.Negative.GovernorPool as Prior
    import ConnectionManagement.Negative.ServerPeers as PriorServer
    import ConnectionManagement.CSP.GovernorLifecycle as L
    module Prefix = ServingPrefix
    module Physical = PhysicalPrefix
    module Suffix = PhysicalSuffix
    import ConnectionManagement.HandlerSupervision as H
    import ConnectionManagement.OutboundHandlerSupervision as B
    import ConnectionManagement.MuxProtocolJobs as P

    private
     module C = Context Prior.classify
     module PS = Supervision Prior.classify
     module GP = Governor Prior.classify
     module S = Server RF.bearerClosed
     module E = IGExit RF.bearerClosed
     module W = Exit RF.bearerClosed
     module K = Combined RF.bearerClosed Prior.classify
     module T = Combined.Protocols RF.bearerClosed Prior.classify PriorServer.Protocols.capability
     module Embed = Embedding.Frontend RF.bearerClosed Prior.classify PriorServer.Protocols.capability
     module J = Joins.Frontend RF.bearerClosed Prior.classify PriorServer.Protocols.capability using (ServerRuns; serverNext; serverDone)
     module Fixtures = PriorServer.Fixtures
     module U = P.U

    -- The IG loop can receive its exit exception only at its genuine loop boundary.
    readySource : O.Configuration
    readySource = record source { core = record core
     { inboundGovernor = record (Machine.inboundGovernor core) { continuation = IG.sampleTime } } }
     where
     source = W.source (Physical.clean Physical.beforeAbort)
     core = O.core source
    readyPhysical : W.State
    readyPhysical = W.setSource readySource (Physical.clean Physical.beforeAbort)
    finishBatchAction : W.Action
    finishBatchAction = Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep IG.finishBatch)))))
    ordinaryContext : C.Context
    ordinaryContext = record Prefix.context0 { regions = Prefix.ordinary }
    ready : T.Runtime
    ready = Embed.embed readyPhysical ordinaryContext Prefix.preparedFront S.serving true E.emptyExit
    finishBatch : T.advance (Embed.event finishBatchAction) Prefix.beforeAbort ≡ just ready
    finishBatch = refl

    -- Reuse the original empty pool/scopes snapshots with the current CM-free
    -- context. The current mux/source is never copied from an older fixture.
    peerContext : Scope.State → GP.Pool.ClosePC → PS.Pool.ClosePC → C.Context
    peerContext scopes governorPhase monitorPhase = record ordinaryContext
     { scopes = scopes
     ; governorPool = record (C.governorPool ordinaryContext) { phase = governorPhase }
     ; monitorPool = record (C.monitorPool ordinaryContext) { phase = monitorPhase } }
    peerAt : Scope.State → GP.Pool.ClosePC → PS.Pool.ClosePC → T.Runtime
    peerAt scopes governorPhase monitorPhase = Embed.embed readyPhysical
     (peerContext scopes governorPhase monitorPhase) Prefix.preparedFront S.serving true E.emptyExit
    peerEvent : PS.Action → T.Event
    peerEvent action = T.dispatch (K.peerStep action)

    peer1 : T.Runtime
    peer1 = peerAt Fixtures.q1 GP.Pool.openPool PS.Pool.openPool
    peerStep1 : T.advance (peerEvent (PS.scope Scope.beginUnwind)) ready ≡ just peer1
    peerStep1 = refl

    peer2 : T.Runtime
    peer2 = peerAt Fixtures.q2 GP.Pool.openPool PS.Pool.openPool
    peerStep2 : T.advance (peerEvent (PS.scope Scope.requestCancel)) peer1 ≡ just peer2
    peerStep2 = refl

    peer3 : T.Runtime
    peer3 = peerAt Fixtures.q3 GP.Pool.openPool PS.Pool.openPool
    peerStep3 : T.advance (peerEvent (PS.scope Scope.deliverCancel)) peer2 ≡ just peer3
    peerStep3 = refl

    peer4 : T.Runtime
    peer4 = peerAt Fixtures.q4 GP.Pool.openPool PS.Pool.openPool
    peerStep4 : T.advance (peerEvent (PS.scope (Scope.bodyExit Scope.churn))) peer3 ≡ just peer4
    peerStep4 = refl

    peer5 : T.Runtime
    peer5 = peerAt Fixtures.q5 GP.Pool.openPool PS.Pool.openPool
    peerStep5 : T.advance (peerEvent (PS.scope (Scope.publishResult Scope.churn))) peer4 ≡ just peer5
    peerStep5 = refl

    peer6 : T.Runtime
    peer6 = peerAt Fixtures.q6 GP.Pool.openPool PS.Pool.openPool
    peerStep6 : T.advance (peerEvent (PS.scope Scope.join)) peer5 ≡ just peer6
    peerStep6 = refl

    peer7 : T.Runtime
    peer7 = peerAt Fixtures.q7 GP.Pool.openPool PS.Pool.openPool
    peerStep7 : T.advance (peerEvent (PS.scope Scope.requestCancel)) peer6 ≡ just peer7
    peerStep7 = refl

    peer8 : T.Runtime
    peer8 = peerAt Fixtures.q8 GP.Pool.openPool PS.Pool.openPool
    peerStep8 : T.advance (peerEvent (PS.scope Scope.deliverCancel)) peer7 ≡ just peer8
    peerStep8 = refl

    peer9 : T.Runtime
    peer9 = peerAt Fixtures.q8 GP.Pool.closing PS.Pool.openPool
    peerStep9 : T.advance (peerEvent (PS.run (GP.beginClose []))) peer8 ≡ just peer9
    peerStep9 = refl

    peer10 : T.Runtime
    peer10 = peerAt Fixtures.q8 GP.Pool.closedPool PS.Pool.openPool
    peerStep10 : T.advance (peerEvent (PS.run GP.finishClose)) peer9 ≡ just peer10
    peerStep10 = refl

    peer11 : T.Runtime
    peer11 = peerAt Fixtures.q9 GP.Pool.closedPool PS.Pool.openPool
    peerStep11 : T.advance (peerEvent (PS.scope (Scope.bodyExit Scope.governor))) peer10 ≡ just peer11
    peerStep11 = refl

    peer12 : T.Runtime
    peer12 = peerAt Fixtures.q10 GP.Pool.closedPool PS.Pool.openPool
    peerStep12 : T.advance (peerEvent (PS.scope (Scope.publishResult Scope.governor))) peer11 ≡ just peer12
    peerStep12 = refl

    peer13 : T.Runtime
    peer13 = peerAt Fixtures.q11 GP.Pool.closedPool PS.Pool.openPool
    peerStep13 : T.advance (peerEvent (PS.scope Scope.join)) peer12 ≡ just peer13
    peerStep13 = refl

    peer14 : T.Runtime
    peer14 = peerAt Fixtures.q12 GP.Pool.closedPool PS.Pool.openPool
    peerStep14 : T.advance (peerEvent (PS.scope Scope.requestCancel)) peer13 ≡ just peer14
    peerStep14 = refl

    peer15 : T.Runtime
    peer15 = peerAt Fixtures.q13 GP.Pool.closedPool PS.Pool.openPool
    peerStep15 : T.advance (peerEvent (PS.scope Scope.deliverCancel)) peer14 ≡ just peer15
    peerStep15 = refl

    peer16 : T.Runtime
    peer16 = peerAt Fixtures.q14 GP.Pool.closedPool PS.Pool.openPool
    peerStep16 : T.advance (peerEvent (PS.scope (Scope.bodyExit Scope.localRoot))) peer15 ≡ just peer16
    peerStep16 = refl

    peer17 : T.Runtime
    peer17 = peerAt Fixtures.q15 GP.Pool.closedPool PS.Pool.openPool
    peerStep17 : T.advance (peerEvent (PS.scope (Scope.publishResult Scope.localRoot))) peer16 ≡ just peer17
    peerStep17 = refl

    peer18 : T.Runtime
    peer18 = peerAt Fixtures.q16 GP.Pool.closedPool PS.Pool.openPool
    peerStep18 : T.advance (peerEvent (PS.scope Scope.join)) peer17 ≡ just peer18
    peerStep18 = refl

    peer19 : T.Runtime
    peer19 = peerAt Fixtures.q17 GP.Pool.closedPool PS.Pool.openPool
    peerStep19 : T.advance (peerEvent (PS.scope Scope.requestCancel)) peer18 ≡ just peer19
    peerStep19 = refl

    peer20 : T.Runtime
    peer20 = peerAt Fixtures.q18 GP.Pool.closedPool PS.Pool.openPool
    peerStep20 : T.advance (peerEvent (PS.scope Scope.deliverCancel)) peer19 ≡ just peer20
    peerStep20 = refl

    peer21 : T.Runtime
    peer21 = peerAt Fixtures.q19 GP.Pool.closedPool PS.Pool.openPool
    peerStep21 : T.advance (peerEvent (PS.scope (Scope.bodyExit Scope.ledger))) peer20 ≡ just peer21
    peerStep21 = refl

    peer22 : T.Runtime
    peer22 = peerAt Fixtures.q20 GP.Pool.closedPool PS.Pool.openPool
    peerStep22 : T.advance (peerEvent (PS.scope (Scope.publishResult Scope.ledger))) peer21 ≡ just peer22
    peerStep22 = refl

    peer23 : T.Runtime
    peer23 = peerAt Fixtures.q21 GP.Pool.closedPool PS.Pool.openPool
    peerStep23 : T.advance (peerEvent (PS.scope Scope.join)) peer22 ≡ just peer23
    peerStep23 = refl

    peer24 : T.Runtime
    peer24 = peerAt Fixtures.q22 GP.Pool.closedPool PS.Pool.openPool
    peerStep24 : T.advance (peerEvent (PS.scope Scope.finishClose)) peer23 ≡ just peer24
    peerStep24 = refl

    peer25 : T.Runtime
    peer25 = peerAt Fixtures.q22 GP.Pool.closedPool PS.Pool.closing
    peerStep25 : T.advance (peerEvent (PS.beginMonitorClose [])) peer24 ≡ just peer25
    peerStep25 = refl

    peer26 : T.Runtime
    peer26 = peerAt Fixtures.q22 GP.Pool.closedPool PS.Pool.closedPool
    peerStep26 : T.advance (peerEvent (PS.finishMonitorClose)) peer25 ≡ just peer26
    peerStep26 = refl

    peerEvents : List T.Event
    peerEvents =
      peerEvent (PS.scope Scope.beginUnwind) ∷
      peerEvent (PS.scope Scope.requestCancel) ∷
      peerEvent (PS.scope Scope.deliverCancel) ∷
      peerEvent (PS.scope (Scope.bodyExit Scope.churn)) ∷
      peerEvent (PS.scope (Scope.publishResult Scope.churn)) ∷
      peerEvent (PS.scope Scope.join) ∷
      peerEvent (PS.scope Scope.requestCancel) ∷
      peerEvent (PS.scope Scope.deliverCancel) ∷
      peerEvent (PS.run (GP.beginClose [])) ∷
      peerEvent (PS.run GP.finishClose) ∷
      peerEvent (PS.scope (Scope.bodyExit Scope.governor)) ∷
      peerEvent (PS.scope (Scope.publishResult Scope.governor)) ∷
      peerEvent (PS.scope Scope.join) ∷
      peerEvent (PS.scope Scope.requestCancel) ∷
      peerEvent (PS.scope Scope.deliverCancel) ∷
      peerEvent (PS.scope (Scope.bodyExit Scope.localRoot)) ∷
      peerEvent (PS.scope (Scope.publishResult Scope.localRoot)) ∷
      peerEvent (PS.scope Scope.join) ∷
      peerEvent (PS.scope Scope.requestCancel) ∷
      peerEvent (PS.scope Scope.deliverCancel) ∷
      peerEvent (PS.scope (Scope.bodyExit Scope.ledger)) ∷
      peerEvent (PS.scope (Scope.publishResult Scope.ledger)) ∷
      peerEvent (PS.scope Scope.join) ∷
      peerEvent (PS.scope Scope.finishClose) ∷
      peerEvent (PS.beginMonitorClose []) ∷
      peerEvent (PS.finishMonitorClose) ∷ []

    abstract
      peerPath : T.Runs ready peerEvents peer26
      peerPath = T.more {a = peerEvent (PS.scope Scope.beginUnwind)} peerStep1 (T.more {a = peerEvent (PS.scope Scope.requestCancel)} peerStep2 (T.more {a = peerEvent (PS.scope Scope.deliverCancel)} peerStep3 (T.more {a = peerEvent (PS.scope (Scope.bodyExit Scope.churn))} peerStep4 (T.more {a = peerEvent (PS.scope (Scope.publishResult Scope.churn))} peerStep5 (T.more {a = peerEvent (PS.scope Scope.join)} peerStep6 (T.more {a = peerEvent (PS.scope Scope.requestCancel)} peerStep7 (T.more {a = peerEvent (PS.scope Scope.deliverCancel)} peerStep8 (T.more {a = peerEvent (PS.run (GP.beginClose []))} peerStep9 (T.more {a = peerEvent (PS.run GP.finishClose)} peerStep10 (T.more {a = peerEvent (PS.scope (Scope.bodyExit Scope.governor))} peerStep11 (T.more {a = peerEvent (PS.scope (Scope.publishResult Scope.governor))} peerStep12 (T.more {a = peerEvent (PS.scope Scope.join)} peerStep13 (T.more {a = peerEvent (PS.scope Scope.requestCancel)} peerStep14 (T.more {a = peerEvent (PS.scope Scope.deliverCancel)} peerStep15 (T.more {a = peerEvent (PS.scope (Scope.bodyExit Scope.localRoot))} peerStep16 (T.more {a = peerEvent (PS.scope (Scope.publishResult Scope.localRoot))} peerStep17 (T.more {a = peerEvent (PS.scope Scope.join)} peerStep18 (T.more {a = peerEvent (PS.scope Scope.requestCancel)} peerStep19 (T.more {a = peerEvent (PS.scope Scope.deliverCancel)} peerStep20 (T.more {a = peerEvent (PS.scope (Scope.bodyExit Scope.ledger))} peerStep21 (T.more {a = peerEvent (PS.scope (Scope.publishResult Scope.ledger))} peerStep22 (T.more {a = peerEvent (PS.scope Scope.join)} peerStep23 (T.more {a = peerEvent (PS.scope Scope.finishClose)} peerStep24 (T.more {a = peerEvent (PS.beginMonitorClose [])} peerStep25 (T.more {a = peerEvent (PS.finishMonitorClose)} peerStep26 (T.stop))))))))))))))))))))))))))

    closedContext : C.Context
    closedContext = peerContext Fixtures.q22 GP.Pool.closedPool PS.Pool.closedPool
    scopeAt : W.State → S.Stage → Bool → E.Exit → T.Runtime
    scopeAt physical stage listener exit = Embed.embed physical closedContext Prefix.preparedFront stage listener exit
    -- The IG catch advances while the Server waits at igCancelRequested.
    scopeAtIG : W.State → S.IGPhase → Bool → E.Exit → T.Runtime
    scopeAtIG physical ph listener exit = Embed.embedIG physical closedContext Prefix.preparedFront ph listener exit
    scopeEvent : S.ScopeAction → T.Event
    scopeEvent action = T.dispatch (K.serverStep (E.run (S.scope action)))
    exitEvent : E.Action → T.Event
    exitEvent action = T.dispatch (K.serverStep action)

    -- Deactivation and flush preserve the nonempty published registration while
    -- changing the real active flag, continuation and pending information channel.
    inactiveSource : O.Configuration
    inactiveSource = record readySource { core = record core
     { inboundGovernor = record governor
      { continuation = IG.exitFlush
      ; execution = record (IG.execution governor) { active = false } } } }
     where
     core = O.core readySource
     governor = Machine.inboundGovernor core
    inactivePhysical : W.State
    inactivePhysical = W.setSource inactiveSource readyPhysical
    exitedPhysical : W.State
    exitedPhysical = Suffix.exited Physical.beforeAbort
    caught : E.Exit
    caught = E.caughtExit (E.receipt E.loopBoundary Old.err nothing)
    rows : List E.Row
    rows = E.snapshotRows (IG.connections (IG.publishedState (Machine.inboundGovernor (O.core (W.source exitedPhysical)))))
    snapshotExit : E.Exit
    snapshotExit = record caught { phase = E.traversing; snapshot = rows; remaining = rows; returned = [] }
    invokedExit : E.Exit
    invokedExit = record snapshotExit { phase = E.invoked }
    returnedExit : E.Exit
    returnedExit = record snapshotExit { remaining = []; returned = rows }
    doneExit : E.Exit
    doneExit = record returnedExit { phase = E.bodyDone }
    publishedExit : E.Exit
    publishedExit = record doneExit { result = just (S.async Old.err) }

    scope1 : T.Runtime
    scope1 = scopeAt readyPhysical S.actionBodyExited true E.emptyExit
    scopeStep1 : T.advance (scopeEvent S.returnAction) peer26 ≡ just scope1
    scopeStep1 = refl

    scope2 : T.Runtime
    scope2 = scopeAt readyPhysical S.actionResultAvailable true E.emptyExit
    scopeStep2 : T.advance (scopeEvent S.publishActionResult) scope1 ≡ just scope2
    scopeStep2 = refl

    scope3 : T.Runtime
    scope3 = scopeAt readyPhysical S.closingAccept true E.emptyExit
    scopeStep3 : T.advance (scopeEvent S.selectActionWinner) scope2 ≡ just scope3
    scopeStep3 = refl

    scope4 : T.Runtime
    scope4 = scopeAt readyPhysical S.acceptCancelRequested true E.emptyExit
    scopeStep4 : T.advance (scopeEvent S.requestAcceptCancel) scope3 ≡ just scope4
    scopeStep4 = refl

    scope5 : T.Runtime
    scope5 = scopeAt readyPhysical S.acceptCancelDelivered true E.emptyExit
    scopeStep5 : T.advance (scopeEvent S.deliverAcceptAtWait) scope4 ≡ just scope5
    scopeStep5 = refl

    scope6 : T.Runtime
    scope6 = scopeAt readyPhysical S.acceptBodyExited false E.emptyExit
    scopeStep6 : T.advance (scopeEvent S.closeListener) scope5 ≡ just scope6
    scopeStep6 = refl

    scope7 : T.Runtime
    scope7 = scopeAt readyPhysical S.acceptResultAvailable false E.emptyExit
    scopeStep7 : T.advance (scopeEvent S.publishAcceptResult) scope6 ≡ just scope7
    scopeStep7 = refl

    scope8 : T.Runtime
    scope8 = scopeAt readyPhysical S.acceptJoined false E.emptyExit
    scopeStep8 : T.advance (scopeEvent S.joinAccept) scope7 ≡ just scope8
    scopeStep8 = refl

    scope9 : T.Runtime
    scope9 = scopeAt readyPhysical S.serverStopped false E.emptyExit
    scopeStep9 : T.advance (scopeEvent S.traceStopped) scope8 ≡ just scope9
    scopeStep9 = refl

    scope10 : T.Runtime
    scope10 = scopeAt readyPhysical S.actionJoined false E.emptyExit
    scopeStep10 : T.advance (scopeEvent S.cancelJoinReturnedAction) scope9 ≡ just scope10
    scopeStep10 = refl

    scope11 : T.Runtime
    scope11 = scopeAt readyPhysical S.igCancelRequested false E.emptyExit
    scopeStep11 : T.advance (scopeEvent S.requestIGCancel) scope10 ≡ just scope11
    scopeStep11 = refl

    scope12 : T.Runtime
    scope12 = scopeAtIG readyPhysical S.igCaught false caught
    scopeStep12 : T.advance (exitEvent (E.receive E.loopBoundary Old.err)) scope11 ≡ just scope12
    scopeStep12 = refl

    scope13 : T.Runtime
    scope13 = scopeAtIG inactivePhysical S.igInactive false caught
    scopeStep13 : T.advance (scopeEvent S.deactivateIG) scope12 ≡ just scope13
    scopeStep13 = refl

    scope14 : T.Runtime
    scope14 = scopeAtIG exitedPhysical S.igFlushed false caught
    scopeStep14 : T.advance (scopeEvent S.flushIG) scope13 ≡ just scope14
    scopeStep14 = refl

    scope15 : T.Runtime
    scope15 = scopeAtIG exitedPhysical S.igFlushed false snapshotExit
    scopeStep15 : T.advance (exitEvent (E.captureSnapshot)) scope14 ≡ just scope15
    scopeStep15 = refl

    scope16 : T.Runtime
    scope16 = scopeAtIG exitedPhysical S.igFlushed false invokedExit
    scopeStep16 : T.advance (exitEvent (E.invokeFinal)) scope15 ≡ just scope16
    scopeStep16 = refl

    scope17 : T.Runtime
    scope17 = scopeAtIG exitedPhysical S.igFlushed false returnedExit
    scopeStep17 : T.advance (exitEvent (E.returnFinal)) scope16 ≡ just scope17
    scopeStep17 = refl

    scope18 : T.Runtime
    scope18 = scopeAtIG exitedPhysical S.igBodyExited false doneExit
    scopeStep18 : T.advance (exitEvent (E.finishFinal)) scope17 ≡ just scope18
    scopeStep18 = refl

    scope19 : T.Runtime
    scope19 = scopeAtIG exitedPhysical S.igResultAvailable false publishedExit
    scopeStep19 : T.advance (scopeEvent S.publishIGResult) scope18 ≡ just scope19
    scopeStep19 = refl

    scope20 : T.Runtime
    scope20 = scopeAt exitedPhysical S.igJoined false publishedExit
    scopeStep20 : T.advance (scopeEvent S.joinIG) scope19 ≡ just scope20
    scopeStep20 = refl

    scope21 : T.Runtime
    scope21 = scopeAt exitedPhysical S.closingCM false publishedExit
    scopeStep21 : T.advance (scopeEvent S.beginCM) scope20 ≡ just scope21
    scopeStep21 = refl

    scopeEvents : List T.Event
    scopeEvents =
      scopeEvent S.returnAction ∷
      scopeEvent S.publishActionResult ∷
      scopeEvent S.selectActionWinner ∷
      scopeEvent S.requestAcceptCancel ∷
      scopeEvent S.deliverAcceptAtWait ∷
      scopeEvent S.closeListener ∷
      scopeEvent S.publishAcceptResult ∷
      scopeEvent S.joinAccept ∷
      scopeEvent S.traceStopped ∷
      scopeEvent S.cancelJoinReturnedAction ∷
      scopeEvent S.requestIGCancel ∷
      exitEvent (E.receive E.loopBoundary Old.err) ∷
      scopeEvent S.deactivateIG ∷
      scopeEvent S.flushIG ∷
      exitEvent (E.captureSnapshot) ∷
      exitEvent (E.invokeFinal) ∷
      exitEvent (E.returnFinal) ∷
      exitEvent (E.finishFinal) ∷
      scopeEvent S.publishIGResult ∷
      scopeEvent S.joinIG ∷
      scopeEvent S.beginCM ∷ []

    abstract
      scopePath : T.Runs peer26 scopeEvents scope21
      scopePath = T.more {a = scopeEvent S.returnAction} scopeStep1 (T.more {a = scopeEvent S.publishActionResult} scopeStep2 (T.more {a = scopeEvent S.selectActionWinner} scopeStep3 (T.more {a = scopeEvent S.requestAcceptCancel} scopeStep4 (T.more {a = scopeEvent S.deliverAcceptAtWait} scopeStep5 (T.more {a = scopeEvent S.closeListener} scopeStep6 (T.more {a = scopeEvent S.publishAcceptResult} scopeStep7 (T.more {a = scopeEvent S.joinAccept} scopeStep8 (T.more {a = scopeEvent S.traceStopped} scopeStep9 (T.more {a = scopeEvent S.cancelJoinReturnedAction} scopeStep10 (T.more {a = scopeEvent S.requestIGCancel} scopeStep11 (T.more {a = exitEvent (E.receive E.loopBoundary Old.err)} scopeStep12 (T.more {a = scopeEvent S.deactivateIG} scopeStep13 (T.more {a = scopeEvent S.flushIG} scopeStep14 (T.more {a = exitEvent (E.captureSnapshot)} scopeStep15 (T.more {a = exitEvent (E.invokeFinal)} scopeStep16 (T.more {a = exitEvent (E.returnFinal)} scopeStep17 (T.more {a = exitEvent (E.finishFinal)} scopeStep18 (T.more {a = scopeEvent S.publishIGResult} scopeStep19 (T.more {a = scopeEvent S.joinIG} scopeStep20 (T.more {a = scopeEvent S.beginCM} scopeStep21 (T.stop)))))))))))))))))))))

    append : ∀ {start middle current first last} → T.Runs start first middle → T.Runs middle last current → T.Runs start (first ++ last) current
    append T.stop rest = rest
    append (T.more actual path) rest = T.more actual (append path rest)
    closeEvents : List T.Event
    closeEvents = Embed.event finishBatchAction ∷ (peerEvents ++ scopeEvents)
    closed : T.Runtime
    closed = scope21
    abstract
      actualClose : T.Runs Prefix.beforeAbort closeEvents closed
      actualClose = T.more {a = Embed.event finishBatchAction} finishBatch (append peerPath scopePath)

    -- These are consequences of the actual preceding path, not adopted input PCs.
    closedStage : S.stage (E.base (K.server (T.base closed))) ≡ S.closingCM
    closedStage = refl
    closedPhysical : Suffix.beforeCM ≡ exitedPhysical
    closedPhysical = refl

    -- The callback and following inherited Server actions also inhabit the
    -- existing CM-entry certificate route, retaining its closed peer scopes.
    beforeEntryActions : List E.Action
    beforeEntryActions =
      (E.run (S.scope S.publishActionResult)) ∷
      (E.run (S.scope S.selectActionWinner)) ∷
      (E.run (S.scope S.requestAcceptCancel)) ∷
      (E.run (S.scope S.deliverAcceptAtWait)) ∷
      (E.run (S.scope S.closeListener)) ∷
      (E.run (S.scope S.publishAcceptResult)) ∷
      (E.run (S.scope S.joinAccept)) ∷
      (E.run (S.scope S.traceStopped)) ∷
      (E.run (S.scope S.cancelJoinReturnedAction)) ∷
      (E.run (S.scope S.requestIGCancel)) ∷
      (E.receive E.loopBoundary Old.err) ∷
      (E.run (S.scope S.deactivateIG)) ∷
      (E.run (S.scope S.flushIG)) ∷
      (E.captureSnapshot) ∷
      (E.invokeFinal) ∷
      (E.returnFinal) ∷
      (E.finishFinal) ∷
      (E.run (S.scope S.publishIGResult)) ∷
      (E.run (S.scope S.joinIG)) ∷ []
    afterCallbackActions : List E.Action
    afterCallbackActions = beforeEntryActions ++ (E.run (S.scope S.beginCM) ∷ [])
    abstract
      afterCallbackServerRuns : J.ServerRuns scope1 afterCallbackActions closed
      afterCallbackServerRuns = J.serverNext {a = E.run (S.scope S.publishActionResult)} scopeStep2 (J.serverNext {a = E.run (S.scope S.selectActionWinner)} scopeStep3 (J.serverNext {a = E.run (S.scope S.requestAcceptCancel)} scopeStep4 (J.serverNext {a = E.run (S.scope S.deliverAcceptAtWait)} scopeStep5 (J.serverNext {a = E.run (S.scope S.closeListener)} scopeStep6 (J.serverNext {a = E.run (S.scope S.publishAcceptResult)} scopeStep7 (J.serverNext {a = E.run (S.scope S.joinAccept)} scopeStep8 (J.serverNext {a = E.run (S.scope S.traceStopped)} scopeStep9 (J.serverNext {a = E.run (S.scope S.cancelJoinReturnedAction)} scopeStep10 (J.serverNext {a = E.run (S.scope S.requestIGCancel)} scopeStep11 (J.serverNext {a = E.receive E.loopBoundary Old.err} scopeStep12 (J.serverNext {a = E.run (S.scope S.deactivateIG)} scopeStep13 (J.serverNext {a = E.run (S.scope S.flushIG)} scopeStep14 (J.serverNext {a = E.captureSnapshot} scopeStep15 (J.serverNext {a = E.invokeFinal} scopeStep16 (J.serverNext {a = E.returnFinal} scopeStep17 (J.serverNext {a = E.finishFinal} scopeStep18 (J.serverNext {a = E.run (S.scope S.publishIGResult)} scopeStep19 (J.serverNext {a = E.run (S.scope S.joinIG)} scopeStep20 (J.serverNext {a = E.run (S.scope S.beginCM)} scopeStep21 (J.serverDone))))))))))))))))))))

  module CombinedSuffix where
    open import Data.Bool using (true; false)
    open import Data.List using (List; []; _∷_; _++_; map; drop; take)
    open import Data.Maybe using (just; nothing)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
    import ConnectionManagement.ServerPeers as Combined
    import ConnectionManagement.ServerAdmission as Server
    import ConnectionManagement.Properties.ServerPeersMuxEmbedding as Embedding
    import ConnectionManagement.Negative.MuxProtocolJobs as Old
    import ConnectionManagement.Negative.MuxResultMonitor as RF
    import ConnectionManagement.Negative.MuxGroupShutdown as GF
    import ConnectionManagement.Negative.MuxHandlerExit as EF
    import ConnectionManagement.Negative.GovernorPool as Prior
    import ConnectionManagement.Negative.ServerPeers as PriorServer
    import ConnectionManagement.Rules.CMShutdown as Close
    import ConnectionManagement.Rules.MuxJobTypes as Types
    module Prefix = ServingPrefix
    module Scope = ScopeClose
    module Physical = PhysicalSuffix
    module W = Physical.W
    module G = Physical.G
    module M = Physical.M
    import ConnectionManagement.MuxProtocolJobs as P
    import ConnectionManagement.Rules.Cleanup as Cleanup
    private
     module T = Combined.Protocols RF.bearerClosed Prior.classify PriorServer.Protocols.capability
     module S = Server RF.bearerClosed
     module Emb = Embedding.Frontend RF.bearerClosed Prior.classify PriorServer.Protocols.capability

    owner = Physical.owner
    err = Physical.err
    at : W.State → T.Runtime
    at physical = Emb.embed physical Scope.closedContext Prefix.preparedFront S.closingCM false Scope.publishedExit
    event : W.Action → T.Event
    event = Emb.event

    -- All wrapper and frontend guard equations remain explicit. Copying the Front
    -- uses actual noteLegacy bookkeeping; no runtime component is reset.
    up : ∀ action before {after} →
     Emb.Allowed action before after Scope.closedContext Prefix.preparedFront S.closingCM false Scope.publishedExit →
     Emb.nextFront action Prefix.preparedFront ≡ Prefix.preparedFront →
     W.step action before ≡ just after → T.advance (event action) (at before) ≡ just (at after)
    up action before {after} permitted copied actual = trans
     (Emb.lift-step action before Scope.closedContext Prefix.preparedFront S.closingCM false Scope.publishedExit permitted actual)
     (cong just (cong (λ front → Emb.embed after Scope.closedContext front S.closingCM false Scope.publishedExit) copied))

    beforeCM capturedCM selectedCM beforeAck afterAck published beforeWait final : T.Runtime
    beforeCM = at Physical.beforeCM
    capturedCM = at Physical.capturedCM
    selectedCM = at Physical.selectedCM
    beforeAck = at Physical.requestedCM
    afterAck = at Physical.receiptCM
    published = at (Physical.hold Physical.acknowledged EF.async10)
    beforeWait = at (Physical.hold Physical.awaiting EF.async10)
    final = at (Physical.hold Physical.closed EF.async10)
    fromActualScope : Scope.closed ≡ beforeCM
    fromActualScope = refl

    capture : T.advance (event (W.shutdownStep Close.captureSnapshot)) beforeCM ≡ just capturedCM
    capture = up (W.shutdownStep Close.captureSnapshot) Physical.beforeCM (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl Physical.capture

    read : T.advance (event (W.shutdownStep Close.readEntry)) capturedCM ≡ just selectedCM
    read = up (W.shutdownStep Close.readEntry) Physical.capturedCM (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl Physical.read

    request : T.advance (event (W.shutdownStep Close.requestCancellation)) selectedCM ≡ just beforeAck
    request = up (W.shutdownStep Close.requestCancellation) Physical.selectedCM (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl Physical.request

    receipt : T.advance (event (W.deliverShutdownMux err)) beforeAck ≡ just afterAck
    receipt = up (W.deliverShutdownMux err) Physical.requestedCM (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl Physical.receipt

    group2 : T.advance (event (W.run (G.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ [])))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup1))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup2)))
    group2 = up (W.run (G.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []))) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup1)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group2 Physical.acknowledged)

    group3 : T.advance (event (W.run (G.requestWholeCancel owner))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup2))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup3)))
    group3 = up (W.run (G.requestWholeCancel owner)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup2)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group3 Physical.acknowledged)

    group4 : T.advance (event (W.run (G.finishChildUnwind Old.j₁₀))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup3))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup4)))
    group4 = up (W.run (G.finishChildUnwind Old.j₁₀)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup3)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group4 Physical.acknowledged)

    group5 : T.advance (event (W.run (G.run (M.run (P.deregisterProtocol Old.j₁₀))))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup4))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup5)))
    group5 = up (W.run (G.run (M.run (P.deregisterProtocol Old.j₁₀)))) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup4)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group5 Physical.acknowledged)

    group6 : T.advance (event (W.run (G.run (M.run (P.asyncProtocolResult Old.j₁₀))))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup5))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup6)))
    group6 = up (W.run (G.run (M.run (P.asyncProtocolResult Old.j₁₀)))) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup5)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group6 Physical.acknowledged)

    group7 : T.advance (event (W.run (G.joinWhole owner))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup6))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup7)))
    group7 = up (W.run (G.joinWhole owner)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup6)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group7 Physical.acknowledged)

    group8 : T.advance (event (W.run (G.requestWholeCancel owner))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup7))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup8)))
    group8 = up (W.run (G.requestWholeCancel owner)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup7)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group8 Physical.acknowledged)

    group9 : T.advance (event (W.run (G.deliverWhole owner))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup8))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup9)))
    group9 = up (W.run (G.deliverWhole owner)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup8)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group9 Physical.acknowledged)

    group10 : T.advance (event (W.run (G.finishChildUnwind Old.j₁))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup9))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup10)))
    group10 = up (W.run (G.finishChildUnwind Old.j₁)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup9)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group10 Physical.acknowledged)

    group11 : T.advance (event (W.run (G.run (M.run (P.deregisterInfra owner Types.demuxer))))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup10))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup11)))
    group11 = up (W.run (G.run (M.run (P.deregisterInfra owner Types.demuxer)))) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup10)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group11 Physical.acknowledged)

    group12 : T.advance (event (W.run (G.run (M.run (P.asyncInfraResult owner Types.demuxer))))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup11))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup12)))
    group12 = up (W.run (G.run (M.run (P.asyncInfraResult owner Types.demuxer)))) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup11)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group12 Physical.acknowledged)

    group13 : T.advance (event (W.run (G.joinWhole owner))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup12))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup13)))
    group13 = up (W.run (G.joinWhole owner)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup12)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group13 Physical.acknowledged)

    group14 : T.advance (event (W.run (G.requestWholeCancel owner))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup13))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup14)))
    group14 = up (W.run (G.requestWholeCancel owner)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup13)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group14 Physical.acknowledged)

    group15 : T.advance (event (W.run (G.deliverWhole owner))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup14))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup15)))
    group15 = up (W.run (G.deliverWhole owner)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup14)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group15 Physical.acknowledged)

    group16 : T.advance (event (W.run (G.finishChildUnwind Old.j₀))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup15))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup16)))
    group16 = up (W.run (G.finishChildUnwind Old.j₀)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup15)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group16 Physical.acknowledged)

    group17 : T.advance (event (W.run (G.run (M.run (P.deregisterInfra owner Types.muxer))))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup16))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup17)))
    group17 = up (W.run (G.run (M.run (P.deregisterInfra owner Types.muxer)))) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup16)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group17 Physical.acknowledged)

    group18 : T.advance (event (W.run (G.run (M.run (P.asyncInfraResult owner Types.muxer))))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup17))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup18)))
    group18 = up (W.run (G.run (M.run (P.asyncInfraResult owner Types.muxer)))) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup17)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group18 Physical.acknowledged)

    group19 : T.advance (event (W.run (G.joinWhole owner))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup18))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup19)))
    group19 = up (W.run (G.joinWhole owner)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup18)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group19 Physical.acknowledged)

    group20 : T.advance (event (W.run (G.finishWholeClose owner))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup19))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup20)))
    group20 = up (W.run (G.finishWholeClose owner)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup19)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group20 Physical.acknowledged)

    group21 : T.advance (event (W.run (G.writeAsyncFailure owner))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup20))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup21)))
    group21 = up (W.run (G.writeAsyncFailure owner)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup20)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group21 Physical.acknowledged)

    group22 : T.advance (event (W.run (G.beginAsyncDead owner))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup21))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup22)))
    group22 = up (W.run (G.beginAsyncDead owner)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup21)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group22 Physical.acknowledged)

    group23 : T.advance (event (W.run (G.sampleAsyncTracer owner))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup22))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup23)))
    group23 = up (W.run (G.sampleAsyncTracer owner)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup22)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group23 Physical.acknowledged)

    group24 : T.advance (event (W.run (G.commitAsyncTracer owner))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup23))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup24)))
    group24 = up (W.run (G.commitAsyncTracer owner)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup23)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group24 Physical.acknowledged)

    group25 : T.advance (event (W.run (G.finishAsyncDead owner))) (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup24))) ≡ just (at (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup25)))
    group25 = up (W.run (G.finishAsyncDead owner)) (Physical.hold Physical.acknowledged (Physical.wrap GF.abortGroup24)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.group25 Physical.acknowledged)

    exit1 : T.advance (event (W.beginExit owner)) (at (Physical.hold Physical.acknowledged EF.async0)) ≡ just (at (Physical.hold Physical.acknowledged EF.async1))
    exit1 = up (W.beginExit owner) (Physical.hold Physical.acknowledged EF.async0) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.async1 Physical.acknowledged)

    exit2 : T.advance (event (W.observeBufferReturn owner)) (at (Physical.hold Physical.acknowledged EF.async1)) ≡ just (at (Physical.hold Physical.acknowledged EF.async2))
    exit2 = up (W.observeBufferReturn owner) (Physical.hold Physical.acknowledged EF.async1) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.async2 Physical.acknowledged)

    exit3 : T.advance (event (W.enterFinalizer owner)) (at (Physical.hold Physical.acknowledged EF.async2)) ≡ just (at (Physical.hold Physical.acknowledged EF.async3))
    exit3 = up (W.enterFinalizer owner) (Physical.hold Physical.acknowledged EF.async2) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.async3 Physical.acknowledged)

    exit4 : T.advance (event (W.cleanup owner Cleanup.takeCleanupMap)) (at (Physical.hold Physical.acknowledged EF.async3)) ≡ just (at (Physical.hold Physical.acknowledged EF.async4))
    exit4 = up (W.cleanup owner Cleanup.takeCleanupMap) (Physical.hold Physical.acknowledged EF.async3) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.async4 Physical.acknowledged)

    exit5 : T.advance (event (W.cleanup owner Cleanup.selectCleanupEntry)) (at (Physical.hold Physical.acknowledged EF.async4)) ≡ just (at (Physical.hold Physical.acknowledged EF.async5))
    exit5 = up (W.cleanup owner Cleanup.selectCleanupEntry) (Physical.hold Physical.acknowledged EF.async4) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.async5 Physical.acknowledged)

    exit6 : T.advance (event (W.cleanup owner Cleanup.closeHandlerSocket)) (at (Physical.hold Physical.acknowledged EF.async5)) ≡ just (at (Physical.hold Physical.acknowledged EF.async6))
    exit6 = up (W.cleanup owner Cleanup.closeHandlerSocket) (Physical.hold Physical.acknowledged EF.async5) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.async6 Physical.acknowledged)

    exit7 : T.advance (event (W.cleanup owner Cleanup.publishCleanupMap)) (at (Physical.hold Physical.acknowledged EF.async6)) ≡ just (at (Physical.hold Physical.acknowledged EF.async7))
    exit7 = up (W.cleanup owner Cleanup.publishCleanupMap) (Physical.hold Physical.acknowledged EF.async6) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.async7 Physical.acknowledged)

    exit8 : T.advance (event (W.cleanup owner Cleanup.readCleanupCounters)) (at (Physical.hold Physical.acknowledged EF.async7)) ≡ just (at (Physical.hold Physical.acknowledged EF.async8))
    exit8 = up (W.cleanup owner Cleanup.readCleanupCounters) (Physical.hold Physical.acknowledged EF.async7) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.async8 Physical.acknowledged)

    exit9 : T.advance (event (W.finishCleanup owner)) (at (Physical.hold Physical.acknowledged EF.async8)) ≡ just (at (Physical.hold Physical.acknowledged EF.async9))
    exit9 = up (W.finishCleanup owner) (Physical.hold Physical.acknowledged EF.async8) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.async9 Physical.acknowledged)

    exit10 : T.advance (event (W.publishAsyncResult owner)) (at (Physical.hold Physical.acknowledged EF.async9)) ≡ just (at (Physical.hold Physical.acknowledged EF.async10))
    exit10 = up (W.publishAsyncResult owner) (Physical.hold Physical.acknowledged EF.async9) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (Physical.async10 Physical.acknowledged)

    traverse : T.advance (event (W.shutdownStep Close.finishTraversal)) published ≡ just beforeWait
    traverse = up (W.shutdownStep Close.finishTraversal) (Physical.hold Physical.acknowledged EF.async10) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl Physical.traverse

    wait : T.advance (event (W.shutdownStep Close.finishClose)) beforeWait ≡ just final
    wait = up (W.shutdownStep Close.finishClose) (Physical.hold Physical.awaiting EF.async10) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl Physical.wait


    append : ∀ {start middle current first last} → T.Runs start first middle → T.Runs middle last current → T.Runs start (first ++ last) current
    append T.stop rest = rest
    append (T.more actual path) rest = T.more actual (append path rest)
    requestEvents : List T.Event
    requestEvents = event (W.shutdownStep Close.captureSnapshot) ∷ event (W.shutdownStep Close.readEntry) ∷ event (W.shutdownStep Close.requestCancellation) ∷ []
    abstract
     actualRequest : T.Runs beforeCM requestEvents beforeAck
     actualRequest = T.more {a = event (W.shutdownStep Close.captureSnapshot)} capture (T.more {a = event (W.shutdownStep Close.readEntry)} read (T.more {a = event (W.shutdownStep Close.requestCancellation)} request T.stop))


    receiptEvent : T.Event
    receiptEvent = event (W.deliverShutdownMux err)
    receiptEvents : List T.Event
    receiptEvents = receiptEvent ∷ []
    abstract
     actualReceipt : T.Runs beforeAck receiptEvents afterAck
     actualReceipt = T.more {a = receiptEvent} receipt T.stop


    drainEvents : List T.Event
    drainEvents = map event Physical.abortTailActions
    abstract
     actualDrain : T.Runs afterAck drainEvents (at (Physical.hold Physical.acknowledged EF.async0))
     actualDrain = T.more {a = event (W.run (G.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ [])))} group2 (T.more {a = event (W.run (G.requestWholeCancel owner))} group3 (T.more {a = event (W.run (G.finishChildUnwind Old.j₁₀))} group4 (T.more {a = event (W.run (G.run (M.run (P.deregisterProtocol Old.j₁₀))))} group5 (T.more {a = event (W.run (G.run (M.run (P.asyncProtocolResult Old.j₁₀))))} group6 (T.more {a = event (W.run (G.joinWhole owner))} group7 (T.more {a = event (W.run (G.requestWholeCancel owner))} group8 (T.more {a = event (W.run (G.deliverWhole owner))} group9 (T.more {a = event (W.run (G.finishChildUnwind Old.j₁))} group10 (T.more {a = event (W.run (G.run (M.run (P.deregisterInfra owner Types.demuxer))))} group11 (T.more {a = event (W.run (G.run (M.run (P.asyncInfraResult owner Types.demuxer))))} group12 (T.more {a = event (W.run (G.joinWhole owner))} group13 (T.more {a = event (W.run (G.requestWholeCancel owner))} group14 (T.more {a = event (W.run (G.deliverWhole owner))} group15 (T.more {a = event (W.run (G.finishChildUnwind Old.j₀))} group16 (T.more {a = event (W.run (G.run (M.run (P.deregisterInfra owner Types.muxer))))} group17 (T.more {a = event (W.run (G.run (M.run (P.asyncInfraResult owner Types.muxer))))} group18 (T.more {a = event (W.run (G.joinWhole owner))} group19 (T.more {a = event (W.run (G.finishWholeClose owner))} group20 (T.more {a = event (W.run (G.writeAsyncFailure owner))} group21 (T.more {a = event (W.run (G.beginAsyncDead owner))} group22 (T.more {a = event (W.run (G.sampleAsyncTracer owner))} group23 (T.more {a = event (W.run (G.commitAsyncTracer owner))} group24 (T.more {a = event (W.run (G.finishAsyncDead owner))} group25 (T.stop))))))))))))))))))))))))


    cleanupEvents : List T.Event
    cleanupEvents = map event Physical.cleanupActions
    abstract
     actualCleanup : T.Runs (at (Physical.hold Physical.acknowledged EF.async0)) cleanupEvents (at (Physical.hold Physical.acknowledged EF.async9))
     actualCleanup = T.more {a = event (W.beginExit owner)} exit1 (T.more {a = event (W.observeBufferReturn owner)} exit2 (T.more {a = event (W.enterFinalizer owner)} exit3 (T.more {a = event (W.cleanup owner Cleanup.takeCleanupMap)} exit4 (T.more {a = event (W.cleanup owner Cleanup.selectCleanupEntry)} exit5 (T.more {a = event (W.cleanup owner Cleanup.closeHandlerSocket)} exit6 (T.more {a = event (W.cleanup owner Cleanup.publishCleanupMap)} exit7 (T.more {a = event (W.cleanup owner Cleanup.readCleanupCounters)} exit8 (T.more {a = event (W.finishCleanup owner)} exit9 (T.stop)))))))))


    publicationEvent : T.Event
    publicationEvent = event (W.publishAsyncResult owner)
    publicationEvents : List T.Event
    publicationEvents = publicationEvent ∷ []
    throughPublicationEvents : List T.Event
    throughPublicationEvents = drainEvents ++ (cleanupEvents ++ publicationEvents)
    waitEvents : List T.Event
    waitEvents = event (W.shutdownStep Close.finishTraversal) ∷ event (W.shutdownStep Close.finishClose) ∷ []
    abstract
     actualToPublication : T.Runs afterAck throughPublicationEvents published
     actualToPublication = append actualDrain (append actualCleanup (T.more {a = publicationEvent} exit10 T.stop))
     actualToWait : T.Runs published waitEvents final
     actualToWait = T.more {a = event (W.shutdownStep Close.finishTraversal)} traverse (T.more {a = event (W.shutdownStep Close.finishClose)} wait T.stop)

    prematureReceipt : T.advance (event (W.deliverShutdownMux err)) (at Physical.beforeCM) ≡ nothing
    prematureReceipt = refl

    duplicateReceipt : T.advance (event (W.deliverShutdownMux err)) (at Physical.receiptCM) ≡ nothing
    duplicateReceipt = refl

    prematurePublication : T.advance (event (W.publishAsyncResult owner)) (at (Physical.hold Physical.acknowledged EF.async8)) ≡ nothing
    prematurePublication = refl

    duplicatePublication : T.advance (event (W.publishAsyncResult owner)) (at (Physical.hold Physical.acknowledged EF.async10)) ≡ nothing
    duplicatePublication = refl

    noWaitAtReceipt : T.advance (event (W.shutdownStep Close.finishClose)) (at Physical.receiptCM) ≡ nothing
    noWaitAtReceipt = refl

    noWaitAtCleanup : T.advance (event (W.shutdownStep Close.finishClose)) (at (Physical.hold Physical.awaiting EF.async9)) ≡ nothing
    noWaitAtCleanup = refl

    duplicateWait : T.advance (event (W.shutdownStep Close.finishClose)) (at (Physical.hold Physical.closed EF.async10)) ≡ nothing
    duplicateWait = refl

    rawAckBypass : T.advance (event (W.shutdownStep Close.acknowledgeDelivery)) (at Physical.requestedCM) ≡ nothing
    rawAckBypass = refl

    finishedAckNoResult : T.advance (event W.acknowledgeFinished) (at Physical.requestedCM) ≡ nothing
    finishedAckNoResult = refl

    beforePublication awaitingPublication : T.Runtime
    beforePublication = at (Physical.hold Physical.acknowledged EF.async9)
    awaitingPublication = at (Physical.hold Physical.awaiting EF.async9)
    throughCleanupEvents : List T.Event
    throughCleanupEvents = drainEvents ++ cleanupEvents
    abstract
     actualToCleanup : T.Runs afterAck throughCleanupEvents beforePublication
     actualToCleanup = append actualDrain actualCleanup
    traverseBeforePublication : T.advance (event (W.shutdownStep Close.finishTraversal)) beforePublication ≡ just awaitingPublication
    traverseBeforePublication = up (W.shutdownStep Close.finishTraversal) (Physical.hold Physical.acknowledged EF.async9)
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl refl
    abstract
     actualPrematureWaitState : T.Runs afterAck (throughCleanupEvents ++ (event (W.shutdownStep Close.finishTraversal) ∷ [])) awaitingPublication
     actualPrematureWaitState = append actualToCleanup
      (T.more {a = event (W.shutdownStep Close.finishTraversal)} traverseBeforePublication T.stop)
    publication : T.advance publicationEvent beforePublication ≡ just published
    publication = exit10

    -- Raw handshake entry points cannot replace cancellation of an adopted mux.
    import ConnectionManagement.HandlerSupervision as H
    import ConnectionManagement.OutboundHandlerSupervision as B
    private module U = P.U
    rawHandshake : W.Action
    rawHandshake = W.run (G.run (M.run (P.run (U.run (B.handler (H.deliverShutdownHandshake err))))))
    rawHandshakeBypass : T.advance (event rawHandshake) beforeAck ≡ nothing
    rawHandshakeBypass = refl
    rawIndependentHandshake : W.Action
    rawIndependentHandshake = W.run (G.run (M.run (P.run (U.run (B.handler (H.deliverHandshakeCancellation owner err))))))
    rawHandshakeCancellationBypass : T.advance (event rawIndependentHandshake) beforeAck ≡ nothing
    rawHandshakeCancellationBypass = refl
    poolClosedCannotWait : T.advance (event (W.shutdownStep Close.finishClose))
     (at (Physical.hold Physical.awaiting (Physical.wrap GF.abortGroup20))) ≡ nothing
    poolClosedCannotWait = refl

    -- A standalone owner abort can execute, but it cannot acknowledge CM's send.
    standaloneAbortState : T.Runtime
    standaloneAbortState = at (Physical.hold Physical.requested (Physical.wrap GF.abortGroup1))
    standaloneAbort : T.advance (event (W.run (G.abortOwner owner err))) beforeAck ≡ just standaloneAbortState
    standaloneAbort = up (W.run (G.abortOwner owner err)) Physical.requestedCM
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl Physical.standaloneAbort

    -- Retain the actual physical action list for the existing inherited-Server
    -- cleanup certificate. Its mapped events are exactly the already used labels.
    beforeWaitActions : List W.Action
    beforeWaitActions = W.shutdownStep Close.captureSnapshot ∷ W.shutdownStep Close.readEntry ∷ W.shutdownStep Close.requestCancellation ∷ W.deliverShutdownMux err ∷
     (Physical.abortTailActions ++ (EF.asyncActions ++ (W.shutdownStep Close.finishTraversal ∷ [])))
    abstract
     actualBeforeWait : T.Runs Scope.closed (map event beforeWaitActions) beforeWait
     actualBeforeWait = T.more {a = event (W.shutdownStep Close.captureSnapshot)} capture
      (T.more {a = event (W.shutdownStep Close.readEntry)} read
       (T.more {a = event (W.shutdownStep Close.requestCancellation)} request
        (T.more {a = event (W.deliverShutdownMux err)} receipt
         (append actualDrain
          (append actualCleanup
           (T.more {a = publicationEvent} exit10
            (T.more {a = event (W.shutdownStep Close.finishTraversal)} traverse T.stop)))))))


  open import Data.Bool using (true; false)
  open import Data.List using (List; []; _∷_; _++_; map)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here)
  import Data.List.Relation.Unary.All as All
  open import Data.Maybe using (just; nothing)
  open import Data.Product using (Σ; _×_; _,_)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Unit using (⊤; tt)
  open import Data.Empty using (⊥)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
  open import ConnectionManagement.Domain using (ident)
  open import ConnectionManagement.Store using (lookup)
  import ConnectionManagement.State as Shared
  import ConnectionManagement.OutboundMachine as O
  import ConnectionManagement.OutboundHandlerSupervision as B
  import ConnectionManagement.HandlerSupervision as H
  import ConnectionManagement.Rules.OutboundAcquire as Acquire
  import ConnectionManagement.Rules.CMShutdown as Close
  import ConnectionManagement.ServerPeers as Model
  import ConnectionManagement.ServerAdmission as Server
  import ConnectionManagement.ServerIGExit as IGExit
  import ConnectionManagement.MuxHandlerExit as ExitModel
  import ConnectionManagement.CSP.GovernorLifecycle as L
  import ConnectionManagement.Negative.GovernorPool as Prior
  import ConnectionManagement.Negative.MuxProtocolJobs as Old
  import ConnectionManagement.Negative.MuxResultMonitor as RF
  import ConnectionManagement.Negative.ServerPeers as Parent
  import ConnectionManagement.Properties.ServerPeersMuxEmbedding as Embedding
  import ConnectionManagement.Properties.ServerPeersMuxReceipt as ReceiptModel
  import ConnectionManagement.Properties.ServerPeersMonitorJoins as JoinModel
  import ConnectionManagement.Properties.MuxHandlerExit as WaitModel
  import ConnectionManagement.Properties.CollectedOutboundOrigin as OriginModel
  import ConnectionManagement.Properties.CollectedInboundOrigin as InboundModel
  import ConnectionManagement.Properties.HandlerBirthBacking as Birth
  import ConnectionManagement.Properties.HandlerBirthEffects as BirthEffects
  import ConnectionManagement.Properties.HandlerResourceFacts as ResourceFacts
  private
    module P = ServingPrefix
    module F = CombinedSuffix
    module C = ScopeClose
    module T = Model.Protocols RF.bearerClosed Prior.classify Parent.Protocols.capability using
      (Runtime; Event; Runs; advance; more; stop)
    module W = ExitModel RF.bearerClosed using (State; Action; physical; shutdown; resultReady; resultOf; asyncException; publishAsyncResult; shutdownStep)
    module E = IGExit RF.bearerClosed using (run)
    module S = Server RF.bearerClosed using (scope; beginCM)
    module Emb = Embedding.Frontend RF.bearerClosed Prior.classify Parent.Protocols.capability using (event)
    module Joins = JoinModel.Frontend RF.bearerClosed Prior.classify Parent.Protocols.capability using
      (physical; handler-action; handler-event; ServerRuns; serverDone; serverNext;
       CMEntry; initialized-cm-entry-run; CMResultWait; result-wait; wait-components-after;
       physical-receipt; physical-publication; physical-wait)
    module MuxReceipt = ReceiptModel.Frontend RF.bearerClosed Prior.classify Parent.Protocols.capability using
      (observed-worker; observed-entry)
    module Receipt = JoinModel.Frontend.MuxReceipt using (worker; entry)
    module WaitFacts = WaitModel RF.bearerClosed using (Publication; PhysicalWait)
    module ObservedWait = WaitModel.PhysicalWait using (observed-results)
    module Origin = OriginModel.Frontend RF.bearerClosed Prior.classify Parent.Protocols.capability using
      (Discovery; MuxDiscovery; OutboundOrigin; BirthPacket; from-backing; initialize-origin;
       initialize-mux; extend-outbound; extend-packet; execution; shared)
    module Inbound = InboundModel.Frontend RF.bearerClosed Prior.classify Parent.Protocols.capability using (InboundOrigin)
    module Outbound = OriginModel.Frontend.OutboundOrigin using (packet; retained)
    module Packet = OriginModel.Frontend.BirthPacket using (label; prefix)
    module Found = OriginModel.Frontend.Discovery using (captured; backing)
    module MuxFound = OriginModel.Frontend.MuxDiscovery using (receipt; discovered)
    module Back = Birth.Frontend RF.bearerClosed Prior.classify Parent.Protocols.capability using
      (Backing; ForkStep; Selected; chosen-birth; inherited-birth; actual-fork; execution; view;
       physical-state; follow; follow-operation; capture-of-found; current-thread)

  IsOutbound : ∀ {X Y : Set} → X ⊎ Y → Set
  IsOutbound (inj₁ value) = ⊥
  IsOutbound (inj₂ value) = ⊤
  takeOutbound : ∀ {X Y : Set} (choice : X ⊎ Y) → IsOutbound choice → Y
  takeOutbound (inj₁ value) ()
  takeOutbound (inj₂ value) proof = value

  -- Only the actual selected physical birth is supplied to branch isolation.
  private
    module MuxTag = BirthEffects.MuxLayer using (inherited-birth)
    module JobTag = BirthEffects.ProtocolLayer using (inherited-birth)
    module MonitorTag = BirthEffects.MonitorLayer RF.bearerClosed using (inherited-birth)
    module GroupTag = BirthEffects.GroupLayer RF.bearerClosed using (inherited-birth)
    module ExitTag = BirthEffects.ExitLayer RF.bearerClosed using (chosen-birth; inherited-plan)
    module CancelTag = BirthEffects.CancellationLayer RF.bearerClosed using (inherited-birth)
    module UnwindTag = BirthEffects.UnwindLayer RF.bearerClosed using (chosen-birth; inherited-plan)
    module DeltaTag = BirthEffects.DeltaQLayer RF.bearerClosed using (inherited-birth)
    module CatchTag = BirthEffects.CatchLayer RF.bearerClosed using (inherited-birth)
    module PublicationTag = BirthEffects.PublicationLayer RF.bearerClosed using (inherited-birth)
    module ServerTag = BirthEffects.ServerLayer RF.bearerClosed using (inherited-birth)
    module IGTag = BirthEffects.IGExitLayer RF.bearerClosed using (chosen-birth; delegated-birth)
    module SharedTag = BirthEffects.SharedLayer RF.bearerClosed Prior.classify using (server-birth; core-birth)
  selectedFork : Back.Selected (P.call Acquire.forkOK) P.beforeFork
  selectedFork = Back.chosen-birth refl (Back.inherited-birth (SharedTag.core-birth (IGTag.chosen-birth refl (IGTag.delegated-birth (ServerTag.inherited-birth (PublicationTag.inherited-birth (CatchTag.inherited-birth (DeltaTag.inherited-birth (UnwindTag.chosen-birth refl (UnwindTag.inherited-plan (CancelTag.inherited-birth (ExitTag.chosen-birth refl (ExitTag.inherited-plan (GroupTag.inherited-birth (MonitorTag.inherited-birth (JobTag.inherited-birth (MuxTag.inherited-birth (BirthEffects.outbound-physical Old.Fixture.caller))))))))))))))))))
  module BirthPackets where
    abstract
      backing : Back.Backing P.start P.born P.birthEvents Old.owner Old.Prior.captured
      backing = record
        { location = record
          { before = P.beforeFork; after = P.born; action = P.call Acquire.forkOK
          ; prefix = P.beforeForkEvents; suffix = []; decomposition = refl
          ; prefix-run = Back.execution P.actualBeforeFork; actual = P.core10; selected = selectedFork
          ; absent-before = refl; at-birth = refl; suffix-run = Back.execution T.stop; retained-descriptor = refl }
        ; operation = Back.actual-fork (P.call Acquire.forkOK) P.beforeFork P.core10 selectedFork
        ; selected-operation = refl
        ; at-physical-fork = trans
            (cong (lookup Old.owner) (Back.ForkStep.captures-after
              (Back.actual-fork (P.call Acquire.forkOK) P.beforeFork P.core10 selectedFork))) refl }
      classified : Inbound.InboundOrigin (O.initial PhysicalPrefix.inputCore) L.settings P.start P.born P.birthEvents Old.owner Old.Prior.captured ⊎
        Origin.OutboundOrigin PhysicalPrefix.inputCore L.settings P.start P.born P.birthEvents Old.owner Old.Prior.captured
      classified = Origin.from-backing PhysicalPrefix.inputCore L.settings P.initialized backing
      outboundBranch : IsOutbound classified
      outboundBranch = tt
      origin : Origin.OutboundOrigin PhysicalPrefix.inputCore L.settings P.start P.born P.birthEvents Old.owner Old.Prior.captured
      origin = takeOutbound classified outboundBranch
      originalLabel : Packet.label (Outbound.packet origin) ≡ P.call Acquire.forkOK
      originalLabel = refl
      originalPrefix : Packet.prefix (Outbound.packet origin) ≡ P.beforeForkEvents
      originalPrefix = refl

  append : ∀ {start middle current first last} → T.Runs start first middle → T.Runs middle last current → T.Runs start (first ++ last) current
  append T.stop rest = rest
  append (T.more actual path) rest = T.more actual (append path rest)
  toCMTail toAckTail : List T.Event
  toCMTail = P.afterBirthEvents ++ C.closeEvents
  toAckTail = toCMTail ++ F.requestEvents
  pendingIndex receiptIndex publicationIndex finalIndex : List T.Event
  pendingIndex = P.birthEvents ++ toAckTail
  receiptIndex = pendingIndex ++ F.receiptEvents
  publicationIndex = receiptIndex ++ F.throughPublicationEvents
  finalIndex = publicationIndex ++ F.waitEvents
  abstract
    birthToCM : T.Runs P.born toCMTail C.closed
    birthToCM = append P.actualAfterBirth C.actualClose
    birthToPending : T.Runs P.born toAckTail F.beforeAck
    birthToPending = append birthToCM F.actualRequest
    initializedPending : T.Runs P.start pendingIndex F.beforeAck
    initializedPending = append P.actualBirth birthToPending
    initializedReceipt : T.Runs P.start receiptIndex F.afterAck
    initializedReceipt = append initializedPending F.actualReceipt
    initializedPublication : T.Runs P.start publicationIndex F.published
    initializedPublication = append initializedReceipt F.actualToPublication
    initializedWait : T.Runs P.start finalIndex F.final
    initializedWait = append initializedPublication F.actualToWait

    receiptDiscovery : Origin.MuxDiscovery PhysicalPrefix.inputCore L.settings P.start F.beforeAck F.afterAck pendingIndex Old.err
    receiptDiscovery = Origin.initialize-mux P.initialized initializedPending F.receipt
    receiptWorker : Receipt.worker (MuxFound.receipt receiptDiscovery) ≡ Old.owner
    receiptWorker = MuxReceipt.observed-worker (MuxFound.receipt receiptDiscovery) refl
    receiptEntry : Receipt.entry (MuxFound.receipt receiptDiscovery) ≡ ident 0
    receiptEntry = MuxReceipt.observed-entry (MuxFound.receipt receiptDiscovery) refl
    discoveredAtReceipt : Origin.Discovery PhysicalPrefix.inputCore L.settings P.start F.afterAck receiptIndex Old.owner
    discoveredAtReceipt = subst
      (λ worker → Origin.Discovery PhysicalPrefix.inputCore L.settings P.start F.afterAck receiptIndex worker)
      receiptWorker (MuxFound.discovered receiptDiscovery)
    discoveredAtPublication : Origin.Discovery PhysicalPrefix.inputCore L.settings P.start F.published publicationIndex Old.owner
    discoveredAtPublication = Origin.initialize-origin P.initialized initializedPublication (here refl)
    discoveredAtWait : Origin.Discovery PhysicalPrefix.inputCore L.settings P.start F.final finalIndex Old.owner
    discoveredAtWait = Origin.initialize-origin P.initialized initializedWait (here refl)

  -- Raw capture rows remain historical after negotiation; the mux exit adapter
  -- supplies the actual result observation and masks the old handshake fallback.
  capturedAtReceipt : lookup Old.owner (B.threads (Back.physical-state F.afterAck)) ≡ just (H.handlerThread Old.Prior.captured H.handshaking)
  capturedAtReceipt = refl
  capturedAtPublication : lookup Old.owner (B.threads (Back.physical-state F.published)) ≡ just (H.handlerThread Old.Prior.captured H.handshaking)
  capturedAtPublication = refl
  capturedAtWait : lookup Old.owner (B.threads (Back.physical-state F.final)) ≡ just (H.handlerThread Old.Prior.captured H.handshaking)
  capturedAtWait = refl
  descriptorAtReceipt : Found.captured discoveredAtReceipt ≡ Old.Prior.captured
  descriptorAtReceipt = sym (Back.capture-of-found (Found.backing discoveredAtReceipt) capturedAtReceipt)
  descriptorAtPublication : Found.captured discoveredAtPublication ≡ Old.Prior.captured
  descriptorAtPublication = sym (Back.capture-of-found (Found.backing discoveredAtPublication) capturedAtPublication)
  descriptorAtWait : Found.captured discoveredAtWait ≡ Old.Prior.captured
  descriptorAtWait = sym (Back.capture-of-found (Found.backing discoveredAtWait) capturedAtWait)

  abstract
    originPending : Origin.OutboundOrigin PhysicalPrefix.inputCore L.settings P.start F.beforeAck pendingIndex Old.owner Old.Prior.captured
    originPending = Origin.extend-outbound birthToPending BirthPackets.origin
    originReceipt : Origin.OutboundOrigin PhysicalPrefix.inputCore L.settings P.start F.afterAck receiptIndex Old.owner Old.Prior.captured
    originReceipt = Origin.extend-outbound F.actualReceipt originPending
    originPublication : Origin.OutboundOrigin PhysicalPrefix.inputCore L.settings P.start F.published publicationIndex Old.owner Old.Prior.captured
    originPublication = Origin.extend-outbound F.actualToPublication originReceipt
    originWait : Origin.OutboundOrigin PhysicalPrefix.inputCore L.settings P.start F.final finalIndex Old.owner Old.Prior.captured
    originWait = Origin.extend-outbound F.actualToWait originPublication
    packetPending : Outbound.packet originPending ≡ Outbound.packet BirthPackets.origin
    packetPending = Origin.extend-packet birthToPending BirthPackets.origin
    packetReceipt : Outbound.packet originReceipt ≡ Outbound.packet BirthPackets.origin
    packetReceipt = trans (Origin.extend-packet F.actualReceipt originPending) packetPending
    packetPublication : Outbound.packet originPublication ≡ Outbound.packet BirthPackets.origin
    packetPublication = trans (Origin.extend-packet F.actualToPublication originReceipt) packetReceipt
    packetWait : Outbound.packet originWait ≡ Outbound.packet BirthPackets.origin
    packetWait = trans (Origin.extend-packet F.actualToWait originPublication) packetPublication
    sameBirthLabel : Packet.label (Outbound.packet originWait) ≡ P.call Acquire.forkOK
    sameBirthLabel = trans (cong Packet.label packetWait) BirthPackets.originalLabel
    sameBirthPrefix : Packet.prefix (Outbound.packet originWait) ≡ P.beforeForkEvents
    sameBirthPrefix = trans (cong Packet.prefix packetWait) BirthPackets.originalPrefix

    backingPending : Back.Backing P.start F.beforeAck pendingIndex Old.owner Old.Prior.captured
    backingPending = Back.follow birthToPending BirthPackets.backing
    backingReceipt : Back.Backing P.start F.afterAck receiptIndex Old.owner Old.Prior.captured
    backingReceipt = Back.follow F.actualReceipt backingPending
    backingPublication : Back.Backing P.start F.published publicationIndex Old.owner Old.Prior.captured
    backingPublication = Back.follow F.actualToPublication backingReceipt
    backingWait : Back.Backing P.start F.final finalIndex Old.owner Old.Prior.captured
    backingWait = Back.follow F.actualToWait backingPublication
  birthCommand : ∀ {start current events worker captured} → Back.Backing start current events worker captured → B.Action
  birthCommand history = Back.ForkStep.command (Birth.Frontend.Backing.operation history)
  commandCopy : ∀ {start before after events tail worker captured}
    (path : T.Runs before tail after) (history : Back.Backing start before events worker captured) →
    birthCommand (Back.follow path history) ≡ birthCommand history
  commandCopy path history = cong Back.ForkStep.command (Back.follow-operation path history)
  abstract
    commandPending : birthCommand backingPending ≡ birthCommand BirthPackets.backing
    commandPending = commandCopy birthToPending BirthPackets.backing
    commandReceipt : birthCommand backingReceipt ≡ birthCommand BirthPackets.backing
    commandReceipt = trans (commandCopy F.actualReceipt backingPending) commandPending
    commandPublication : birthCommand backingPublication ≡ birthCommand BirthPackets.backing
    commandPublication = trans (commandCopy F.actualToPublication backingReceipt) commandReceipt
    commandWait : birthCommand backingWait ≡ birthCommand BirthPackets.backing
    commandWait = trans (commandCopy F.actualToWait backingPublication) commandPublication

  resourcesAtReceipt : ResourceFacts.Facts Old.owner Old.Prior.captured (Origin.shared F.afterAck)
  resourcesAtReceipt = Outbound.retained originReceipt
  resourcesAtPublication : ResourceFacts.Facts Old.owner Old.Prior.captured (Origin.shared F.published)
  resourcesAtPublication = Outbound.retained originPublication
  resourcesAtWait : ResourceFacts.Facts Old.owner Old.Prior.captured (Origin.shared F.final)
  resourcesAtWait = Outbound.retained originWait
  exactSameExecution : T.Runs P.start finalIndex F.final
  exactSameExecution = Origin.execution originWait
  physicalPublication : WaitFacts.Publication Old.owner (Joins.physical F.beforePublication) (Joins.physical F.published)
  physicalPublication = Joins.physical-publication Old.owner F.beforePublication F.publication
  physicalFinalWait : WaitFacts.PhysicalWait (Joins.physical F.beforeWait) (Joins.physical F.final)
  physicalFinalWait = Joins.physical-wait F.beforeWait F.wait
  actualFinalResultOracle : W.resultReady Old.owner (Joins.physical F.beforeWait) ≡ true
  actualFinalResultOracle = All.lookup (ObservedWait.observed-results physicalFinalWait) (here refl)
  effectiveAsyncResult : W.resultOf Old.owner (Joins.physical F.final) ≡ just (W.asyncException Old.err)
  effectiveAsyncResult = refl

  -- Convert only canonical physical labels. This reuses the existing complete
  -- Server/component certificate layer without normalizing the full history.
  handlerRuns : ∀ {start current} (actions : List W.Action) →
    T.Runs start (map Emb.event actions) current → Joins.ServerRuns start (map Joins.handler-action actions) current
  handlerRuns [] T.stop = Joins.serverDone
  handlerRuns (action ∷ actions) (T.more actual rest) = Joins.serverNext
    {a = Joins.handler-action action} actual (handlerRuns actions rest)
  callbackPrefix : List T.Event
  callbackPrefix = P.prefixEvents ++ (Emb.event C.finishBatchAction ∷ C.peerEvents)
  abstract
    initializedCallbackPrefix : T.Runs P.start callbackPrefix C.peer26
    initializedCallbackPrefix = append P.actualPrefix (T.more {a = Emb.event C.finishBatchAction} C.finishBatch C.peerPath)
    cmEntry : Joins.CMEntry P.start C.closed
    cmEntry = Joins.initialized-cm-entry-run {actions = C.beforeEntryActions}
      P.initialized initializedCallbackPrefix C.scopeStep1 C.afterCallbackServerRuns
    cmResultWait : Joins.CMResultWait P.start F.beforeWait F.final
    cmResultWait = Joins.result-wait cmEntry (handlerRuns F.beforeWaitActions F.actualBeforeWait) F.wait

  handoffRequired : T.advance (P.call Acquire.commitConnected) P.entered ≡ nothing
  handoffRequired = refl

-- Initialized TIME_WAIT paths retain the accepted opaque outbound birth.
module TimeWaitChecks where

  module TerminatingPrefix where
    open import Data.Bool using (true; false)
    open import Data.List using (List; []; _∷_; _++_)
    open import Data.Maybe using (Maybe; just; nothing)
    open import Data.Product using (_,_)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    open import ConnectionManagement.Domain using (ident; duplex; ticking; expired)
    open import ConnectionManagement.Scenarios.Admission using (key₀)
    open import ConnectionManagement.Store using (lookup; put)
    open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
    import ConnectionManagement.State as Shared
    import ConnectionManagement.Machine as Machine
    import ConnectionManagement.OutboundMachine as O
    import ConnectionManagement.OutboundHandlerSupervision as B
    import ConnectionManagement.HandlerSupervision as H
    import ConnectionManagement.MuxProtocolJobs as P
    import ConnectionManagement.MuxHandlerExit as Exit
    import ConnectionManagement.Rules.InboundRelease as InboundRelease
    import ConnectionManagement.Rules.OutboundRelease as Release
    import ConnectionManagement.Rules.RemoteState as Remote
    import ConnectionManagement.Rules.IGRegistration as IG
    import ConnectionManagement.Rules.MuxRuntime as Mux
    import ConnectionManagement.ServerPeers as Combined
    import ConnectionManagement.ServerAdmission as Server
    import ConnectionManagement.ServerIGExit as IGExit
    import ConnectionManagement.Properties.ServerPeersMuxEmbedding as Embedding
    import ConnectionManagement.Negative.MuxProtocolJobs as Old
    import ConnectionManagement.Negative.MuxResultMonitor as RF
    import ConnectionManagement.Negative.GovernorPool as Prior
    module Physical = OutboundMuxChecks.PhysicalPrefix using (beforeAbort; clean; runP)
    module Prefix = OutboundMuxChecks.ServingPrefix using (beforeAbort; context0; coreEvent; ordinary; preparedFront)
    module T = Combined.Protocols RF.bearerClosed Prior.classify Protocols.capability using (Event; Front; Runs; Runtime; advance; more; stop)
    module W = Exit RF.bearerClosed using (Action; State; setSource; shared; source; step)
    module U = P.U using (run)
    module Emb = Embedding.Frontend RF.bearerClosed Prior.classify Protocols.capability using (embed; event; lift-step)
    module S = Server RF.bearerClosed using (serving)
    module E = IGExit RF.bearerClosed using (emptyExit)
    context = record Prefix.context0 { regions = Prefix.ordinary }
    at : W.State → T.Runtime
    at physical = Emb.embed physical context Prefix.preparedFront S.serving true E.emptyExit
    ig : IG.IGAction → W.Action
    ig action = Physical.runP (P.run (U.run (B.handler (H.run (Machine.igStep action)))))
    inboundRelease : InboundRelease.Action → W.Action
    inboundRelease action = Physical.runP (P.run (U.run (B.handler (H.run (Machine.releaseStep action)))))
    remote : Remote.Action → W.Action
    remote action = Physical.runP (P.run (U.run (B.handler (H.run (Machine.remoteStep action)))))

    s0 : W.State
    s0 = Physical.clean Physical.beforeAbort
    start : T.Runtime
    start = Prefix.beforeAbort
    startShape : start ≡ at s0
    startShape = refl

    -- Flat snapshots retain only the actual primitive edits. Every operation
    -- below still discharges its own guarded equation; these are no reset laws.
    baseSource = W.source s0
    baseCore = O.core baseSource
    baseWorld = Machine.world baseCore
    baseGovernor = Machine.inboundGovernor baseCore
    basePublished = IG.publishedState baseGovernor
    messages : List Shared.IGEvent
    messages = Shared.awakeRemote key₀ ∷ Shared.remotePromotedToHot key₀ ∷ []
    hotMessage : List Shared.IGEvent
    hotMessage = Shared.remotePromotedToHot key₀ ∷ []
    tickEntry = Shared.outboundDup key₀ Old.owner (ident 0) ticking
    expiredEntry = Shared.outboundDup key₀ Old.owner (ident 0) expired
    idleEntry = Shared.outboundIdle key₀ Old.owner (ident 0) duplex
    termEntry = Shared.terminating key₀ Old.owner nothing
    coldPublished = IG.setRemote key₀ IG.remoteCold basePublished
    warmPublished = IG.setRemote key₀ IG.remoteWarm coldPublished
    hotPublished = IG.setRemote key₀ IG.remoteHot warmPublished
    expiredTimers = put (ident 1) expired
     (put (ident 2) ticking (IG.timers (IG.execution baseGovernor)))
    g1 = record baseGovernor { continuation = IG.sampleTime }
    g2 = record baseGovernor { continuation = IG.armInactivity 0 }
    g3 = record baseGovernor
     { nextTimer = 3; continuation = IG.awaitBatch 0 (ident 2)
     ; execution = record (IG.execution baseGovernor)
       { timers = put (ident 2) ticking (IG.timers (IG.execution baseGovernor)) } }
    -- Later governor snapshots share one flat engine and timer table.
    gov : IG.PC → IG.Published → IG.Runtime
    gov pc published = record baseGovernor
     { nextTimer = 3; continuation = pc; publishedState = published
     ; execution = record (IG.execution baseGovernor) { timers = expiredTimers } }
    g4 = gov (IG.awaitBatch 0 (ident 2)) basePublished
    g5 = gov (IG.readNext 0 (Shared.commitRemote key₀ ∷ messages)) basePublished
    g6 = gov (IG.needsCM 0 messages (Shared.commitRemote key₀) basePublished) basePublished
    g7 = gov IG.inCM basePublished
    g12 = gov (IG.publishDecision 0 messages coldPublished) basePublished
    g13 = gov (IG.readNext 0 messages) coldPublished
    g22 = gov (IG.needsCM 0 hotMessage (Shared.awakeRemote key₀) coldPublished) coldPublished
    g23 = gov IG.inCM coldPublished
    g26 = gov (IG.publishDecision 0 hotMessage warmPublished) coldPublished
    g27 = gov (IG.readNext 0 hotMessage) warmPublished
    g28 = gov (IG.publishDecision 0 [] hotPublished) warmPublished
    g29 = gov (IG.readNext 0 []) hotPublished
    g30 = gov IG.sampleTime hotPublished
    inboundFrame : InboundRelease.PC → InboundRelease.Outcome → Maybe InboundRelease.Frame
    inboundFrame pc outcome = just (InboundRelease.frame key₀ 0 messages basePublished pc outcome nothing false)
    releaseFrame : Release.PC → Data.Bool.Bool → Release.Runtime
    releaseFrame pc ready = (Old.Fixture.caller , Release.frame key₀ pc ready) ∷ []
    releaseDone = Release.complete (Release.success (just termEntry))
    remoteFrame : Remote.PC → Remote.Outcome → Maybe Remote.Frame
    remoteFrame pc outcome = just (Remote.frame Remote.promote key₀ 0 hotMessage coldPublished pc outcome false [])
    flat : IG.Runtime → List Shared.IGEvent → Shared.ConnectionState → Release.Runtime →
     Maybe InboundRelease.Frame → Maybe Remote.Frame → W.State
    flat governor queue entry releasing inbound remote = W.setSource
     (record baseSource
      { core = record baseCore
        { world = record baseWorld
          { cm = record (Shared.cm baseWorld)
            { entries = put (ident 0) entry (Shared.entries (Shared.cm baseWorld)) }
          ; inboundInfo = queue }
        ; inboundGovernor = governor; inboundRelease = inbound; remoteCall = remote }
      ; releasing = releasing }) s0

    s1 : W.State
    s1 = flat g1 messages tickEntry [] nothing nothing
    physical1 : W.step (ig IG.finishBatch) s0 ≡ just s1
    physical1 = refl
    edge1 : T.advance (Emb.event (ig IG.finishBatch)) (at s0) ≡ just (at s1)
    edge1 = Emb.lift-step (ig IG.finishBatch) s0 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical1

    s2 : W.State
    s2 = flat g2 messages tickEntry [] nothing nothing
    physical2 : W.step (ig (IG.captureTime 0)) s1 ≡ just s2
    physical2 = refl
    edge2 : T.advance (Emb.event (ig (IG.captureTime 0))) (at s1) ≡ just (at s2)
    edge2 = Emb.lift-step (ig (IG.captureTime 0)) s1 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical2

    s3 : W.State
    s3 = flat g3 messages tickEntry [] nothing nothing
    physical3 : W.step (ig IG.registerInactivity) s2 ≡ just s3
    physical3 = refl
    edge3 : T.advance (Emb.event (ig IG.registerInactivity)) (at s2) ≡ just (at s3)
    edge3 = Emb.lift-step (ig IG.registerInactivity) s2 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical3

    s4 : W.State
    s4 = flat g4 messages tickEntry [] nothing nothing
    physical4 : W.step (ig (IG.expireTimer (ident 1))) s3 ≡ just s4
    physical4 = refl
    edge4 : T.advance (Emb.event (ig (IG.expireTimer (ident 1)))) (at s3) ≡ just (at s4)
    edge4 = Emb.lift-step (ig (IG.expireTimer (ident 1))) s3 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical4

    s5 : W.State
    s5 = flat g5 [] tickEntry [] nothing nothing
    physical5 : W.step (ig IG.selectBatch) s4 ≡ just s5
    physical5 = refl
    edge5 : T.advance (Emb.event (ig IG.selectBatch)) (at s4) ≡ just (at s5)
    edge5 = Emb.lift-step (ig IG.selectBatch) s4 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical5

    s6 : W.State
    s6 = flat g6 [] tickEntry [] nothing nothing
    physical6 : W.step (ig IG.readEvent) s5 ≡ just s6
    physical6 = refl
    edge6 : T.advance (Emb.event (ig IG.readEvent)) (at s5) ≡ just (at s6)
    edge6 = Emb.lift-step (ig IG.readEvent) s5 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical6

    s7 : W.State
    s7 = flat g7 [] tickEntry [] (inboundFrame InboundRelease.transaction InboundRelease.commit) nothing
    physical7 : W.step (inboundRelease InboundRelease.enter) s6 ≡ just s7
    physical7 = refl
    edge7 : T.advance (Emb.event (inboundRelease InboundRelease.enter)) (at s6) ≡ just (at s7)
    edge7 = Emb.lift-step (inboundRelease InboundRelease.enter) s6 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical7

    s8 : W.State
    s8 = flat g7 [] expiredEntry [] (inboundFrame InboundRelease.counters InboundRelease.keep) nothing
    physical8 : W.step (inboundRelease InboundRelease.transact) s7 ≡ just s8
    physical8 = refl
    edge8 : T.advance (Emb.event (inboundRelease InboundRelease.transact)) (at s7) ≡ just (at s8)
    edge8 = Emb.lift-step (inboundRelease InboundRelease.transact) s7 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical8

    s9 : W.State
    s9 = flat g7 [] expiredEntry [] (inboundFrame InboundRelease.cancellation InboundRelease.keep) nothing
    physical9 : W.step (inboundRelease InboundRelease.readCounters) s8 ≡ just s9
    physical9 = refl
    edge9 : T.advance (Emb.event (inboundRelease InboundRelease.readCounters)) (at s8) ≡ just (at s9)
    edge9 = Emb.lift-step (inboundRelease InboundRelease.readCounters) s8 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical9

    s10 : W.State
    s10 = flat g7 [] expiredEntry [] (inboundFrame InboundRelease.assertion InboundRelease.keep) nothing
    physical10 : W.step (inboundRelease InboundRelease.requestCancellation) s9 ≡ just s10
    physical10 = refl
    edge10 : T.advance (Emb.event (inboundRelease InboundRelease.requestCancellation)) (at s9) ≡ just (at s10)
    edge10 = Emb.lift-step (inboundRelease InboundRelease.requestCancellation) s9 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical10

    s11 : W.State
    s11 = flat g7 [] expiredEntry [] (inboundFrame InboundRelease.returning InboundRelease.keep) nothing
    physical11 : W.step (inboundRelease InboundRelease.checkAssertion) s10 ≡ just s11
    physical11 = refl
    edge11 : T.advance (Emb.event (inboundRelease InboundRelease.checkAssertion)) (at s10) ≡ just (at s11)
    edge11 = Emb.lift-step (inboundRelease InboundRelease.checkAssertion) s10 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical11

    s12 : W.State
    s12 = flat g12 [] expiredEntry [] nothing nothing
    physical12 : W.step (inboundRelease InboundRelease.returnToIG) s11 ≡ just s12
    physical12 = refl
    edge12 : T.advance (Emb.event (inboundRelease InboundRelease.returnToIG)) (at s11) ≡ just (at s12)
    edge12 = Emb.lift-step (inboundRelease InboundRelease.returnToIG) s11 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical12

    s13 : W.State
    s13 = flat g13 [] expiredEntry [] nothing nothing
    physical13 : W.step (ig IG.commitDecision) s12 ≡ just s13
    physical13 = refl
    edge13 : T.advance (Emb.event (ig IG.commitDecision)) (at s12) ≡ just (at s13)
    edge13 = Emb.lift-step (ig IG.commitDecision) s12 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical13

    s14 : W.State
    s14 = flat g13 [] expiredEntry (releaseFrame Release.transaction false) nothing nothing
    edge14 : T.advance (Prefix.coreEvent (O.beginRelease Old.Fixture.caller key₀)) (at s13) ≡ just (at s14)
    edge14 = refl

    s15 : W.State
    s15 = flat g13 [] idleEntry (releaseFrame (Release.count (Release.armTimer (ident 0) Old.owner)) false) nothing nothing
    edge15 : T.advance (Prefix.coreEvent (O.release Old.Fixture.caller Release.transactionStep)) (at s14) ≡ just (at s15)
    edge15 = refl

    s16 : W.State
    s16 = flat g13 [] idleEntry (releaseFrame (Release.armTimer (ident 0) Old.owner) false) nothing nothing
    edge16 : T.advance (Prefix.coreEvent (O.release Old.Fixture.caller Release.readCounters)) (at s15) ≡ just (at s16)
    edge16 = refl

    s17 : W.State
    s17 = flat g13 [] idleEntry (releaseFrame (Release.waitIdle (ident 0) Old.owner) false) nothing nothing
    edge17 : T.advance (Prefix.coreEvent (O.release Old.Fixture.caller Release.registerTimer)) (at s16) ≡ just (at s17)
    edge17 = refl

    s18 : W.State
    s18 = flat g13 [] idleEntry (releaseFrame (Release.waitIdle (ident 0) Old.owner) true) nothing nothing
    edge18 : T.advance (Prefix.coreEvent (O.release Old.Fixture.caller Release.expireTimer)) (at s17) ≡ just (at s18)
    edge18 = refl

    s19 : W.State
    s19 = flat g13 [] idleEntry (releaseFrame (Release.timeoutWrite (ident 0) Old.owner) true) nothing nothing
    edge19 : T.advance (Prefix.coreEvent (O.release Old.Fixture.caller Release.selectWakeup)) (at s18) ≡ just (at s19)
    edge19 = refl

    s20 : W.State
    s20 = flat g13 [] termEntry (releaseFrame (Release.count (Release.cancel Old.owner releaseDone)) true) nothing nothing
    edge20 : T.advance (Prefix.coreEvent (O.release Old.Fixture.caller Release.commitTimeout)) (at s19) ≡ just (at s20)
    edge20 = refl

    s21 : W.State
    s21 = flat g13 [] termEntry (releaseFrame (Release.cancel Old.owner releaseDone) true) nothing nothing
    edge21 : T.advance (Prefix.coreEvent (O.release Old.Fixture.caller Release.readCounters)) (at s20) ≡ just (at s21)
    edge21 = refl

    s22 : W.State
    s22 = flat g22 [] termEntry (releaseFrame (Release.cancel Old.owner releaseDone) true) nothing nothing
    physical22 : W.step (ig IG.readEvent) s21 ≡ just s22
    physical22 = refl
    edge22 : T.advance (Emb.event (ig IG.readEvent)) (at s21) ≡ just (at s22)
    edge22 = Emb.lift-step (ig IG.readEvent) s21 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical22

    s23 : W.State
    s23 = flat g23 [] termEntry (releaseFrame (Release.cancel Old.owner releaseDone) true) nothing (remoteFrame Remote.transaction (Remote.unsupported nothing))
    physical23 : W.step (remote Remote.enter) s22 ≡ just s23
    physical23 = refl
    edge23 : T.advance (Emb.event (remote Remote.enter)) (at s22) ≡ just (at s23)
    edge23 = Emb.lift-step (remote Remote.enter) s22 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical23

    s24 : W.State
    s24 = flat g23 [] termEntry (releaseFrame (Release.cancel Old.owner releaseDone) true) nothing (remoteFrame Remote.assertion (Remote.unsupported (just termEntry)))
    physical24 : W.step (remote Remote.transact) s23 ≡ just s24
    physical24 = refl
    edge24 : T.advance (Emb.event (remote Remote.transact)) (at s23) ≡ just (at s24)
    edge24 = Emb.lift-step (remote Remote.transact) s23 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical24

    s25 : W.State
    s25 = flat g23 [] termEntry (releaseFrame (Release.cancel Old.owner releaseDone) true) nothing (remoteFrame Remote.returning (Remote.unsupported (just termEntry)))
    physical25 : W.step (remote Remote.checkAssertion) s24 ≡ just s25
    physical25 = refl
    edge25 : T.advance (Emb.event (remote Remote.checkAssertion)) (at s24) ≡ just (at s25)
    edge25 = Emb.lift-step (remote Remote.checkAssertion) s24 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical25

    s26 : W.State
    s26 = flat g26 [] termEntry (releaseFrame (Release.cancel Old.owner releaseDone) true) nothing nothing
    physical26 : W.step (remote Remote.returnToIG) s25 ≡ just s26
    physical26 = refl
    edge26 : T.advance (Emb.event (remote Remote.returnToIG)) (at s25) ≡ just (at s26)
    edge26 = Emb.lift-step (remote Remote.returnToIG) s25 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical26

    s27 : W.State
    s27 = flat g27 [] termEntry (releaseFrame (Release.cancel Old.owner releaseDone) true) nothing nothing
    physical27 : W.step (ig IG.commitDecision) s26 ≡ just s27
    physical27 = refl
    edge27 : T.advance (Emb.event (ig IG.commitDecision)) (at s26) ≡ just (at s27)
    edge27 = Emb.lift-step (ig IG.commitDecision) s26 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical27

    s28 : W.State
    s28 = flat g28 [] termEntry (releaseFrame (Release.cancel Old.owner releaseDone) true) nothing nothing
    physical28 : W.step (ig IG.readEvent) s27 ≡ just s28
    physical28 = refl
    edge28 : T.advance (Emb.event (ig IG.readEvent)) (at s27) ≡ just (at s28)
    edge28 = Emb.lift-step (ig IG.readEvent) s27 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical28

    s29 : W.State
    s29 = flat g29 [] termEntry (releaseFrame (Release.cancel Old.owner releaseDone) true) nothing nothing
    physical29 : W.step (ig IG.commitDecision) s28 ≡ just s29
    physical29 = refl
    edge29 : T.advance (Emb.event (ig IG.commitDecision)) (at s28) ≡ just (at s29)
    edge29 = Emb.lift-step (ig IG.commitDecision) s28 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical29

    s30 : W.State
    s30 = flat g30 [] termEntry (releaseFrame (Release.cancel Old.owner releaseDone) true) nothing nothing
    physical30 : W.step (ig IG.finishBatch) s29 ≡ just s30
    physical30 = refl
    edge30 : T.advance (Emb.event (ig IG.finishBatch)) (at s29) ≡ just (at s30)
    edge30 = Emb.lift-step (ig IG.finishBatch) s29 context Prefix.preparedFront S.serving true E.emptyExit
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) physical30

    terminatingPhysical : W.State
    terminatingPhysical = s30
    terminatingRuntime : T.Runtime
    terminatingRuntime = at terminatingPhysical

    events : List T.Event
    events = Emb.event (ig IG.finishBatch) ∷
     Emb.event (ig (IG.captureTime 0)) ∷
     Emb.event (ig IG.registerInactivity) ∷
     Emb.event (ig (IG.expireTimer (ident 1))) ∷
     Emb.event (ig IG.selectBatch) ∷
     Emb.event (ig IG.readEvent) ∷
     Emb.event (inboundRelease InboundRelease.enter) ∷
     Emb.event (inboundRelease InboundRelease.transact) ∷
     Emb.event (inboundRelease InboundRelease.readCounters) ∷
     Emb.event (inboundRelease InboundRelease.requestCancellation) ∷
     Emb.event (inboundRelease InboundRelease.checkAssertion) ∷
     Emb.event (inboundRelease InboundRelease.returnToIG) ∷
     Emb.event (ig IG.commitDecision) ∷
     Prefix.coreEvent (O.beginRelease Old.Fixture.caller key₀) ∷
     Prefix.coreEvent (O.release Old.Fixture.caller Release.transactionStep) ∷
     Prefix.coreEvent (O.release Old.Fixture.caller Release.readCounters) ∷
     Prefix.coreEvent (O.release Old.Fixture.caller Release.registerTimer) ∷
     Prefix.coreEvent (O.release Old.Fixture.caller Release.expireTimer) ∷
     Prefix.coreEvent (O.release Old.Fixture.caller Release.selectWakeup) ∷
     Prefix.coreEvent (O.release Old.Fixture.caller Release.commitTimeout) ∷
     Prefix.coreEvent (O.release Old.Fixture.caller Release.readCounters) ∷
     Emb.event (ig IG.readEvent) ∷
     Emb.event (remote Remote.enter) ∷
     Emb.event (remote Remote.transact) ∷
     Emb.event (remote Remote.checkAssertion) ∷
     Emb.event (remote Remote.returnToIG) ∷
     Emb.event (ig IG.commitDecision) ∷
     Emb.event (ig IG.readEvent) ∷
     Emb.event (ig IG.commitDecision) ∷
     Emb.event (ig IG.finishBatch) ∷ []

    abstract
     actualPrefix : T.Runs start events terminatingRuntime
     actualPrefix = T.more {a = Emb.event (ig IG.finishBatch)} edge1 ( T.more {a = Emb.event (ig (IG.captureTime 0))} edge2 ( T.more {a = Emb.event (ig IG.registerInactivity)} edge3 ( T.more {a = Emb.event (ig (IG.expireTimer (ident 1)))} edge4 ( T.more {a = Emb.event (ig IG.selectBatch)} edge5 ( T.more {a = Emb.event (ig IG.readEvent)} edge6 ( T.more {a = Emb.event (inboundRelease InboundRelease.enter)} edge7 ( T.more {a = Emb.event (inboundRelease InboundRelease.transact)} edge8 ( T.more {a = Emb.event (inboundRelease InboundRelease.readCounters)} edge9 ( T.more {a = Emb.event (inboundRelease InboundRelease.requestCancellation)} edge10 ( T.more {a = Emb.event (inboundRelease InboundRelease.checkAssertion)} edge11 ( T.more {a = Emb.event (inboundRelease InboundRelease.returnToIG)} edge12 ( T.more {a = Emb.event (ig IG.commitDecision)} edge13 ( T.more {a = Prefix.coreEvent (O.beginRelease Old.Fixture.caller key₀)} edge14 ( T.more {a = Prefix.coreEvent (O.release Old.Fixture.caller Release.transactionStep)} edge15 ( T.more {a = Prefix.coreEvent (O.release Old.Fixture.caller Release.readCounters)} edge16 ( T.more {a = Prefix.coreEvent (O.release Old.Fixture.caller Release.registerTimer)} edge17 ( T.more {a = Prefix.coreEvent (O.release Old.Fixture.caller Release.expireTimer)} edge18 ( T.more {a = Prefix.coreEvent (O.release Old.Fixture.caller Release.selectWakeup)} edge19 ( T.more {a = Prefix.coreEvent (O.release Old.Fixture.caller Release.commitTimeout)} edge20 ( T.more {a = Prefix.coreEvent (O.release Old.Fixture.caller Release.readCounters)} edge21 ( T.more {a = Emb.event (ig IG.readEvent)} edge22 ( T.more {a = Emb.event (remote Remote.enter)} edge23 ( T.more {a = Emb.event (remote Remote.transact)} edge24 ( T.more {a = Emb.event (remote Remote.checkAssertion)} edge25 ( T.more {a = Emb.event (remote Remote.returnToIG)} edge26 ( T.more {a = Emb.event (ig IG.commitDecision)} edge27 ( T.more {a = Emb.event (ig IG.readEvent)} edge28 ( T.more {a = Emb.event (ig IG.commitDecision)} edge29 ( T.more {a = Emb.event (ig IG.finishBatch)} edge30 (T.stop))))))))))))))))))))))))))))))

    -- The CM writer is the actual selected timeout, after real inbound idle expiry.
    actualExpired : lookup (ident 0) (Shared.entries (Shared.cm (W.shared s8))) ≡
     just (Shared.outboundDup key₀ Old.owner (ident 0) expired)
    actualExpired = refl
    actualIdle : lookup (ident 0) (Shared.entries (Shared.cm (W.shared s19))) ≡
     just (Shared.outboundIdle key₀ Old.owner (ident 0) duplex)
    actualIdle = refl
    actualTerminating : lookup (ident 0) (Shared.entries (Shared.cm (W.shared terminatingPhysical))) ≡
     just (Shared.terminating key₀ Old.owner nothing)
    actualTerminating = refl
    releaseStillPending : lookup Old.Fixture.caller (O.releasing (W.source terminatingPhysical)) ≡
     just (Release.frame key₀ (Release.cancel Old.owner (Release.complete (Release.success (just (Shared.terminating key₀ Old.owner nothing))))) true)
    releaseStillPending = refl
    notYetCleanup : lookup Old.owner (Shared.cleanups (W.shared terminatingPhysical)) ≡ nothing
    notYetCleanup = refl
    prematureTimeout : T.advance (Prefix.coreEvent (O.release Old.Fixture.caller Release.commitTimeout)) (at s17) ≡ nothing
    prematureTimeout = refl

    -- A snapshot transformation carries only this prefix's actual persistent edits.
    -- It preserves the supplied old continuation, active flag and physical groups.
    -- Its users must prove every transformed operation afresh.
    stamp : W.State → W.State
    stamp physical = W.setSource stampedSource physical
     where
     terminal = W.source (flat g30 [] termEntry (releaseFrame (Release.cancel Old.owner releaseDone) true) nothing nothing)
     original = W.source physical
     core = O.core original
     world = Machine.world core
     governor = Machine.inboundGovernor core
     terminalGovernor = Machine.inboundGovernor (O.core terminal)
     stampedGovernor = record governor
      { nextTimer = IG.nextTimer terminalGovernor
      ; publishedState = IG.publishedState terminalGovernor
      ; execution = record (IG.execution governor) { timers = IG.timers (IG.execution terminalGovernor) } }
     stampedWorld = record world
      { cm = record (Shared.cm world)
        { entries = put (ident 0) (Shared.terminating key₀ Old.owner nothing) (Shared.entries (Shared.cm world)) } }
     stampedSource = record original
      { core = record core { world = stampedWorld; inboundGovernor = stampedGovernor }
      ; releasing = O.releasing terminal }

    context0 = Prefix.context0
    ordinary = Prefix.ordinary
    preparedFront : T.Front
    preparedFront = Prefix.preparedFront

  module ScopeClose where
    open import Data.Bool using (Bool; true; false)
    open import Data.List using (List; []; _∷_; _++_)
    open import Data.Maybe using (just; nothing)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    import ConnectionManagement.OutboundMachine as O
    import ConnectionManagement.Machine as Machine
    import ConnectionManagement.Rules.IGRegistration as IG
    import ConnectionManagement.Rules.AsyncScope as Scope
    import ConnectionManagement.PeerContext as Context
    import ConnectionManagement.PeerSupervision as Supervision
    import ConnectionManagement.GovernorPool as Governor
    import ConnectionManagement.Properties.ServerPeersMonitorJoins as Joins
    import ConnectionManagement.ServerPeers as Combined
    import ConnectionManagement.ServerAdmission as Server
    import ConnectionManagement.ServerIGExit as IGExit
    import ConnectionManagement.MuxHandlerExit as Exit
    import ConnectionManagement.Properties.ServerPeersMuxEmbedding as Embedding
    import ConnectionManagement.Negative.MuxProtocolJobs as Old
    import ConnectionManagement.Negative.MuxResultMonitor as RF
    import ConnectionManagement.Negative.GovernorPool as Prior
    import ConnectionManagement.Negative.ServerPeers as PriorServer
    import ConnectionManagement.CSP.GovernorLifecycle as L
    module Prefix = TerminatingPrefix using (context; preparedFront; stamp; terminatingPhysical; terminatingRuntime)
    module Physical = OutboundMuxChecks.PhysicalPrefix using (beforeAbort)
    module Suffix = OutboundMuxChecks.PhysicalSuffix using (beforeCM; exited)
    import ConnectionManagement.HandlerSupervision as H
    import ConnectionManagement.OutboundHandlerSupervision as B
    import ConnectionManagement.MuxProtocolJobs as P

    private
     module C = Context Prior.classify using (Context; governorPool; monitorPool)
     module PS = Supervision Prior.classify using (Action; module Pool; beginMonitorClose; finishMonitorClose; run; scope)
     module GP = Governor Prior.classify using (module Pool; beginClose; finishClose)
     module S = Server RF.bearerClosed using (ScopeAction; Stage; acceptBodyExited; acceptCancelDelivered; acceptCancelRequested; acceptJoined; acceptResultAvailable; actionBodyExited; actionJoined; actionResultAvailable; async; beginCM; cancelJoinReturnedAction; closeListener; closingAccept; closingCM; deactivateIG; deliverAcceptAtWait; flushIG; IGPhase; igBodyExited; igCaught; igCancelRequested; igFlushed; igInactive; igJoined; igResultAvailable; joinAccept; joinIG; publishAcceptResult; publishActionResult; publishIGResult; requestAcceptCancel; requestIGCancel; returnAction; scope; selectActionWinner; serverStopped; serving; stage; traceStopped)
     module E = IGExit RF.bearerClosed using (Action; Exit; Row; base; bodyDone; captureSnapshot; caughtExit; emptyExit; finishFinal; invokeFinal; invoked; loopBoundary; receipt; receive; returnFinal; run; snapshotRows; traversing)
     module W = Exit RF.bearerClosed using (State; setSource; source)
     module K = Combined RF.bearerClosed Prior.classify using (peerStep; server; serverStep)
     module T = Combined.Protocols RF.bearerClosed Prior.classify PriorServer.Protocols.capability using (Event; Runs; Runtime; advance; base; dispatch; more; stop)
     module Embed = Embedding.Frontend RF.bearerClosed Prior.classify PriorServer.Protocols.capability using (embed; embedIG)
     module J = Joins.Frontend RF.bearerClosed Prior.classify PriorServer.Protocols.capability using (ServerRuns; serverDone; serverNext)
     module Fixtures = PriorServer.Fixtures using (q1; q10; q11; q12; q13; q14; q15; q16; q17; q18; q19; q2; q20; q21; q22; q3; q4; q5; q6; q7; q8; q9)


    -- The TIME_WAIT prefix itself returned the completed IG idle batch. The
    -- following context and state are its actual terminal values.
    readySource : O.Configuration
    readySource = W.source Prefix.terminatingPhysical
    readyPhysical : W.State
    readyPhysical = Prefix.terminatingPhysical
    ordinaryContext : C.Context
    ordinaryContext = Prefix.context
    ready : T.Runtime
    ready = Prefix.terminatingRuntime

    -- Reuse the original empty pool/scopes snapshots with the current CM-free
    -- context. The current mux/source is never copied from an older fixture.
    peerContext : Scope.State → GP.Pool.ClosePC → PS.Pool.ClosePC → C.Context
    peerContext scopes governorPhase monitorPhase = record ordinaryContext
     { scopes = scopes
     ; governorPool = record (C.governorPool ordinaryContext) { phase = governorPhase }
     ; monitorPool = record (C.monitorPool ordinaryContext) { phase = monitorPhase } }
    peerAt : Scope.State → GP.Pool.ClosePC → PS.Pool.ClosePC → T.Runtime
    peerAt scopes governorPhase monitorPhase = Embed.embed readyPhysical
     (peerContext scopes governorPhase monitorPhase) Prefix.preparedFront S.serving true E.emptyExit
    peerEvent : PS.Action → T.Event
    peerEvent action = T.dispatch (K.peerStep action)

    peer1 : T.Runtime
    peer1 = peerAt Fixtures.q1 GP.Pool.openPool PS.Pool.openPool
    peerStep1 : T.advance (peerEvent (PS.scope Scope.beginUnwind)) ready ≡ just peer1
    peerStep1 = refl

    peer2 : T.Runtime
    peer2 = peerAt Fixtures.q2 GP.Pool.openPool PS.Pool.openPool
    peerStep2 : T.advance (peerEvent (PS.scope Scope.requestCancel)) peer1 ≡ just peer2
    peerStep2 = refl

    peer3 : T.Runtime
    peer3 = peerAt Fixtures.q3 GP.Pool.openPool PS.Pool.openPool
    peerStep3 : T.advance (peerEvent (PS.scope Scope.deliverCancel)) peer2 ≡ just peer3
    peerStep3 = refl

    peer4 : T.Runtime
    peer4 = peerAt Fixtures.q4 GP.Pool.openPool PS.Pool.openPool
    peerStep4 : T.advance (peerEvent (PS.scope (Scope.bodyExit Scope.churn))) peer3 ≡ just peer4
    peerStep4 = refl

    peer5 : T.Runtime
    peer5 = peerAt Fixtures.q5 GP.Pool.openPool PS.Pool.openPool
    peerStep5 : T.advance (peerEvent (PS.scope (Scope.publishResult Scope.churn))) peer4 ≡ just peer5
    peerStep5 = refl

    peer6 : T.Runtime
    peer6 = peerAt Fixtures.q6 GP.Pool.openPool PS.Pool.openPool
    peerStep6 : T.advance (peerEvent (PS.scope Scope.join)) peer5 ≡ just peer6
    peerStep6 = refl

    peer7 : T.Runtime
    peer7 = peerAt Fixtures.q7 GP.Pool.openPool PS.Pool.openPool
    peerStep7 : T.advance (peerEvent (PS.scope Scope.requestCancel)) peer6 ≡ just peer7
    peerStep7 = refl

    peer8 : T.Runtime
    peer8 = peerAt Fixtures.q8 GP.Pool.openPool PS.Pool.openPool
    peerStep8 : T.advance (peerEvent (PS.scope Scope.deliverCancel)) peer7 ≡ just peer8
    peerStep8 = refl

    peer9 : T.Runtime
    peer9 = peerAt Fixtures.q8 GP.Pool.closing PS.Pool.openPool
    peerStep9 : T.advance (peerEvent (PS.run (GP.beginClose []))) peer8 ≡ just peer9
    peerStep9 = refl

    peer10 : T.Runtime
    peer10 = peerAt Fixtures.q8 GP.Pool.closedPool PS.Pool.openPool
    peerStep10 : T.advance (peerEvent (PS.run GP.finishClose)) peer9 ≡ just peer10
    peerStep10 = refl

    peer11 : T.Runtime
    peer11 = peerAt Fixtures.q9 GP.Pool.closedPool PS.Pool.openPool
    peerStep11 : T.advance (peerEvent (PS.scope (Scope.bodyExit Scope.governor))) peer10 ≡ just peer11
    peerStep11 = refl

    peer12 : T.Runtime
    peer12 = peerAt Fixtures.q10 GP.Pool.closedPool PS.Pool.openPool
    peerStep12 : T.advance (peerEvent (PS.scope (Scope.publishResult Scope.governor))) peer11 ≡ just peer12
    peerStep12 = refl

    peer13 : T.Runtime
    peer13 = peerAt Fixtures.q11 GP.Pool.closedPool PS.Pool.openPool
    peerStep13 : T.advance (peerEvent (PS.scope Scope.join)) peer12 ≡ just peer13
    peerStep13 = refl

    peer14 : T.Runtime
    peer14 = peerAt Fixtures.q12 GP.Pool.closedPool PS.Pool.openPool
    peerStep14 : T.advance (peerEvent (PS.scope Scope.requestCancel)) peer13 ≡ just peer14
    peerStep14 = refl

    peer15 : T.Runtime
    peer15 = peerAt Fixtures.q13 GP.Pool.closedPool PS.Pool.openPool
    peerStep15 : T.advance (peerEvent (PS.scope Scope.deliverCancel)) peer14 ≡ just peer15
    peerStep15 = refl

    peer16 : T.Runtime
    peer16 = peerAt Fixtures.q14 GP.Pool.closedPool PS.Pool.openPool
    peerStep16 : T.advance (peerEvent (PS.scope (Scope.bodyExit Scope.localRoot))) peer15 ≡ just peer16
    peerStep16 = refl

    peer17 : T.Runtime
    peer17 = peerAt Fixtures.q15 GP.Pool.closedPool PS.Pool.openPool
    peerStep17 : T.advance (peerEvent (PS.scope (Scope.publishResult Scope.localRoot))) peer16 ≡ just peer17
    peerStep17 = refl

    peer18 : T.Runtime
    peer18 = peerAt Fixtures.q16 GP.Pool.closedPool PS.Pool.openPool
    peerStep18 : T.advance (peerEvent (PS.scope Scope.join)) peer17 ≡ just peer18
    peerStep18 = refl

    peer19 : T.Runtime
    peer19 = peerAt Fixtures.q17 GP.Pool.closedPool PS.Pool.openPool
    peerStep19 : T.advance (peerEvent (PS.scope Scope.requestCancel)) peer18 ≡ just peer19
    peerStep19 = refl

    peer20 : T.Runtime
    peer20 = peerAt Fixtures.q18 GP.Pool.closedPool PS.Pool.openPool
    peerStep20 : T.advance (peerEvent (PS.scope Scope.deliverCancel)) peer19 ≡ just peer20
    peerStep20 = refl

    peer21 : T.Runtime
    peer21 = peerAt Fixtures.q19 GP.Pool.closedPool PS.Pool.openPool
    peerStep21 : T.advance (peerEvent (PS.scope (Scope.bodyExit Scope.ledger))) peer20 ≡ just peer21
    peerStep21 = refl

    peer22 : T.Runtime
    peer22 = peerAt Fixtures.q20 GP.Pool.closedPool PS.Pool.openPool
    peerStep22 : T.advance (peerEvent (PS.scope (Scope.publishResult Scope.ledger))) peer21 ≡ just peer22
    peerStep22 = refl

    peer23 : T.Runtime
    peer23 = peerAt Fixtures.q21 GP.Pool.closedPool PS.Pool.openPool
    peerStep23 : T.advance (peerEvent (PS.scope Scope.join)) peer22 ≡ just peer23
    peerStep23 = refl

    peer24 : T.Runtime
    peer24 = peerAt Fixtures.q22 GP.Pool.closedPool PS.Pool.openPool
    peerStep24 : T.advance (peerEvent (PS.scope Scope.finishClose)) peer23 ≡ just peer24
    peerStep24 = refl

    peer25 : T.Runtime
    peer25 = peerAt Fixtures.q22 GP.Pool.closedPool PS.Pool.closing
    peerStep25 : T.advance (peerEvent (PS.beginMonitorClose [])) peer24 ≡ just peer25
    peerStep25 = refl

    peer26 : T.Runtime
    peer26 = peerAt Fixtures.q22 GP.Pool.closedPool PS.Pool.closedPool
    peerStep26 : T.advance (peerEvent (PS.finishMonitorClose)) peer25 ≡ just peer26
    peerStep26 = refl

    peerEvents : List T.Event
    peerEvents =
      peerEvent (PS.scope Scope.beginUnwind) ∷
      peerEvent (PS.scope Scope.requestCancel) ∷
      peerEvent (PS.scope Scope.deliverCancel) ∷
      peerEvent (PS.scope (Scope.bodyExit Scope.churn)) ∷
      peerEvent (PS.scope (Scope.publishResult Scope.churn)) ∷
      peerEvent (PS.scope Scope.join) ∷
      peerEvent (PS.scope Scope.requestCancel) ∷
      peerEvent (PS.scope Scope.deliverCancel) ∷
      peerEvent (PS.run (GP.beginClose [])) ∷
      peerEvent (PS.run GP.finishClose) ∷
      peerEvent (PS.scope (Scope.bodyExit Scope.governor)) ∷
      peerEvent (PS.scope (Scope.publishResult Scope.governor)) ∷
      peerEvent (PS.scope Scope.join) ∷
      peerEvent (PS.scope Scope.requestCancel) ∷
      peerEvent (PS.scope Scope.deliverCancel) ∷
      peerEvent (PS.scope (Scope.bodyExit Scope.localRoot)) ∷
      peerEvent (PS.scope (Scope.publishResult Scope.localRoot)) ∷
      peerEvent (PS.scope Scope.join) ∷
      peerEvent (PS.scope Scope.requestCancel) ∷
      peerEvent (PS.scope Scope.deliverCancel) ∷
      peerEvent (PS.scope (Scope.bodyExit Scope.ledger)) ∷
      peerEvent (PS.scope (Scope.publishResult Scope.ledger)) ∷
      peerEvent (PS.scope Scope.join) ∷
      peerEvent (PS.scope Scope.finishClose) ∷
      peerEvent (PS.beginMonitorClose []) ∷
      peerEvent (PS.finishMonitorClose) ∷ []

    abstract
      peerPath : T.Runs ready peerEvents peer26
      peerPath = T.more {a = peerEvent (PS.scope Scope.beginUnwind)} peerStep1 (T.more {a = peerEvent (PS.scope Scope.requestCancel)} peerStep2 (T.more {a = peerEvent (PS.scope Scope.deliverCancel)} peerStep3 (T.more {a = peerEvent (PS.scope (Scope.bodyExit Scope.churn))} peerStep4 (T.more {a = peerEvent (PS.scope (Scope.publishResult Scope.churn))} peerStep5 (T.more {a = peerEvent (PS.scope Scope.join)} peerStep6 (T.more {a = peerEvent (PS.scope Scope.requestCancel)} peerStep7 (T.more {a = peerEvent (PS.scope Scope.deliverCancel)} peerStep8 (T.more {a = peerEvent (PS.run (GP.beginClose []))} peerStep9 (T.more {a = peerEvent (PS.run GP.finishClose)} peerStep10 (T.more {a = peerEvent (PS.scope (Scope.bodyExit Scope.governor))} peerStep11 (T.more {a = peerEvent (PS.scope (Scope.publishResult Scope.governor))} peerStep12 (T.more {a = peerEvent (PS.scope Scope.join)} peerStep13 (T.more {a = peerEvent (PS.scope Scope.requestCancel)} peerStep14 (T.more {a = peerEvent (PS.scope Scope.deliverCancel)} peerStep15 (T.more {a = peerEvent (PS.scope (Scope.bodyExit Scope.localRoot))} peerStep16 (T.more {a = peerEvent (PS.scope (Scope.publishResult Scope.localRoot))} peerStep17 (T.more {a = peerEvent (PS.scope Scope.join)} peerStep18 (T.more {a = peerEvent (PS.scope Scope.requestCancel)} peerStep19 (T.more {a = peerEvent (PS.scope Scope.deliverCancel)} peerStep20 (T.more {a = peerEvent (PS.scope (Scope.bodyExit Scope.ledger))} peerStep21 (T.more {a = peerEvent (PS.scope (Scope.publishResult Scope.ledger))} peerStep22 (T.more {a = peerEvent (PS.scope Scope.join)} peerStep23 (T.more {a = peerEvent (PS.scope Scope.finishClose)} peerStep24 (T.more {a = peerEvent (PS.beginMonitorClose [])} peerStep25 (T.more {a = peerEvent (PS.finishMonitorClose)} peerStep26 (T.stop))))))))))))))))))))))))))

    closedContext : C.Context
    closedContext = peerContext Fixtures.q22 GP.Pool.closedPool PS.Pool.closedPool
    scopeAt : W.State → S.Stage → Bool → E.Exit → T.Runtime
    scopeAt physical stage listener exit = Embed.embed physical closedContext Prefix.preparedFront stage listener exit
    -- The IG catch advances while the Server waits at igCancelRequested.
    scopeAtIG : W.State → S.IGPhase → Bool → E.Exit → T.Runtime
    scopeAtIG physical ph listener exit = Embed.embedIG physical closedContext Prefix.preparedFront ph listener exit
    scopeEvent : S.ScopeAction → T.Event
    scopeEvent action = T.dispatch (K.serverStep (E.run (S.scope action)))
    exitEvent : E.Action → T.Event
    exitEvent action = T.dispatch (K.serverStep action)

    -- Deactivation and flush preserve the nonempty published registration while
    -- changing the real active flag, continuation and pending information channel.
    inactiveSource : O.Configuration
    inactiveSource = record readySource { core = record core
     { inboundGovernor = record governor
      { continuation = IG.exitFlush
      ; execution = record (IG.execution governor) { active = false } } } }
     where
     core = O.core readySource
     governor = Machine.inboundGovernor core
    inactivePhysical : W.State
    inactivePhysical = W.setSource inactiveSource readyPhysical
    exitedPhysical : W.State
    exitedPhysical = Prefix.stamp (Suffix.exited Physical.beforeAbort)
    caught : E.Exit
    caught = E.caughtExit (E.receipt E.loopBoundary Old.err nothing)
    rows : List E.Row
    rows = E.snapshotRows (IG.connections (IG.publishedState (Machine.inboundGovernor (O.core (W.source exitedPhysical)))))
    snapshotExit : E.Exit
    snapshotExit = record caught { phase = E.traversing; snapshot = rows; remaining = rows; returned = [] }
    invokedExit : E.Exit
    invokedExit = record snapshotExit { phase = E.invoked }
    returnedExit : E.Exit
    returnedExit = record snapshotExit { remaining = []; returned = rows }
    doneExit : E.Exit
    doneExit = record returnedExit { phase = E.bodyDone }
    publishedExit : E.Exit
    publishedExit = record doneExit { result = just (S.async Old.err) }

    scope1 : T.Runtime
    scope1 = scopeAt readyPhysical S.actionBodyExited true E.emptyExit
    scopeStep1 : T.advance (scopeEvent S.returnAction) peer26 ≡ just scope1
    scopeStep1 = refl

    scope2 : T.Runtime
    scope2 = scopeAt readyPhysical S.actionResultAvailable true E.emptyExit
    scopeStep2 : T.advance (scopeEvent S.publishActionResult) scope1 ≡ just scope2
    scopeStep2 = refl

    scope3 : T.Runtime
    scope3 = scopeAt readyPhysical S.closingAccept true E.emptyExit
    scopeStep3 : T.advance (scopeEvent S.selectActionWinner) scope2 ≡ just scope3
    scopeStep3 = refl

    scope4 : T.Runtime
    scope4 = scopeAt readyPhysical S.acceptCancelRequested true E.emptyExit
    scopeStep4 : T.advance (scopeEvent S.requestAcceptCancel) scope3 ≡ just scope4
    scopeStep4 = refl

    scope5 : T.Runtime
    scope5 = scopeAt readyPhysical S.acceptCancelDelivered true E.emptyExit
    scopeStep5 : T.advance (scopeEvent S.deliverAcceptAtWait) scope4 ≡ just scope5
    scopeStep5 = refl

    scope6 : T.Runtime
    scope6 = scopeAt readyPhysical S.acceptBodyExited false E.emptyExit
    scopeStep6 : T.advance (scopeEvent S.closeListener) scope5 ≡ just scope6
    scopeStep6 = refl

    scope7 : T.Runtime
    scope7 = scopeAt readyPhysical S.acceptResultAvailable false E.emptyExit
    scopeStep7 : T.advance (scopeEvent S.publishAcceptResult) scope6 ≡ just scope7
    scopeStep7 = refl

    scope8 : T.Runtime
    scope8 = scopeAt readyPhysical S.acceptJoined false E.emptyExit
    scopeStep8 : T.advance (scopeEvent S.joinAccept) scope7 ≡ just scope8
    scopeStep8 = refl

    scope9 : T.Runtime
    scope9 = scopeAt readyPhysical S.serverStopped false E.emptyExit
    scopeStep9 : T.advance (scopeEvent S.traceStopped) scope8 ≡ just scope9
    scopeStep9 = refl

    scope10 : T.Runtime
    scope10 = scopeAt readyPhysical S.actionJoined false E.emptyExit
    scopeStep10 : T.advance (scopeEvent S.cancelJoinReturnedAction) scope9 ≡ just scope10
    scopeStep10 = refl

    scope11 : T.Runtime
    scope11 = scopeAt readyPhysical S.igCancelRequested false E.emptyExit
    scopeStep11 : T.advance (scopeEvent S.requestIGCancel) scope10 ≡ just scope11
    scopeStep11 = refl

    scope12 : T.Runtime
    scope12 = scopeAtIG readyPhysical S.igCaught false caught
    scopeStep12 : T.advance (exitEvent (E.receive E.loopBoundary Old.err)) scope11 ≡ just scope12
    scopeStep12 = refl

    scope13 : T.Runtime
    scope13 = scopeAtIG inactivePhysical S.igInactive false caught
    scopeStep13 : T.advance (scopeEvent S.deactivateIG) scope12 ≡ just scope13
    scopeStep13 = refl

    scope14 : T.Runtime
    scope14 = scopeAtIG exitedPhysical S.igFlushed false caught
    scopeStep14 : T.advance (scopeEvent S.flushIG) scope13 ≡ just scope14
    scopeStep14 = refl

    scope15 : T.Runtime
    scope15 = scopeAtIG exitedPhysical S.igFlushed false snapshotExit
    scopeStep15 : T.advance (exitEvent (E.captureSnapshot)) scope14 ≡ just scope15
    scopeStep15 = refl

    scope16 : T.Runtime
    scope16 = scopeAtIG exitedPhysical S.igFlushed false invokedExit
    scopeStep16 : T.advance (exitEvent (E.invokeFinal)) scope15 ≡ just scope16
    scopeStep16 = refl

    scope17 : T.Runtime
    scope17 = scopeAtIG exitedPhysical S.igFlushed false returnedExit
    scopeStep17 : T.advance (exitEvent (E.returnFinal)) scope16 ≡ just scope17
    scopeStep17 = refl

    scope18 : T.Runtime
    scope18 = scopeAtIG exitedPhysical S.igBodyExited false doneExit
    scopeStep18 : T.advance (exitEvent (E.finishFinal)) scope17 ≡ just scope18
    scopeStep18 = refl

    scope19 : T.Runtime
    scope19 = scopeAtIG exitedPhysical S.igResultAvailable false publishedExit
    scopeStep19 : T.advance (scopeEvent S.publishIGResult) scope18 ≡ just scope19
    scopeStep19 = refl

    scope20 : T.Runtime
    scope20 = scopeAt exitedPhysical S.igJoined false publishedExit
    scopeStep20 : T.advance (scopeEvent S.joinIG) scope19 ≡ just scope20
    scopeStep20 = refl

    scope21 : T.Runtime
    scope21 = scopeAt exitedPhysical S.closingCM false publishedExit
    scopeStep21 : T.advance (scopeEvent S.beginCM) scope20 ≡ just scope21
    scopeStep21 = refl

    scopeEvents : List T.Event
    scopeEvents =
      scopeEvent S.returnAction ∷
      scopeEvent S.publishActionResult ∷
      scopeEvent S.selectActionWinner ∷
      scopeEvent S.requestAcceptCancel ∷
      scopeEvent S.deliverAcceptAtWait ∷
      scopeEvent S.closeListener ∷
      scopeEvent S.publishAcceptResult ∷
      scopeEvent S.joinAccept ∷
      scopeEvent S.traceStopped ∷
      scopeEvent S.cancelJoinReturnedAction ∷
      scopeEvent S.requestIGCancel ∷
      exitEvent (E.receive E.loopBoundary Old.err) ∷
      scopeEvent S.deactivateIG ∷
      scopeEvent S.flushIG ∷
      exitEvent (E.captureSnapshot) ∷
      exitEvent (E.invokeFinal) ∷
      exitEvent (E.returnFinal) ∷
      exitEvent (E.finishFinal) ∷
      scopeEvent S.publishIGResult ∷
      scopeEvent S.joinIG ∷
      scopeEvent S.beginCM ∷ []

    abstract
      scopePath : T.Runs peer26 scopeEvents scope21
      scopePath = T.more {a = scopeEvent S.returnAction} scopeStep1 (T.more {a = scopeEvent S.publishActionResult} scopeStep2 (T.more {a = scopeEvent S.selectActionWinner} scopeStep3 (T.more {a = scopeEvent S.requestAcceptCancel} scopeStep4 (T.more {a = scopeEvent S.deliverAcceptAtWait} scopeStep5 (T.more {a = scopeEvent S.closeListener} scopeStep6 (T.more {a = scopeEvent S.publishAcceptResult} scopeStep7 (T.more {a = scopeEvent S.joinAccept} scopeStep8 (T.more {a = scopeEvent S.traceStopped} scopeStep9 (T.more {a = scopeEvent S.cancelJoinReturnedAction} scopeStep10 (T.more {a = scopeEvent S.requestIGCancel} scopeStep11 (T.more {a = exitEvent (E.receive E.loopBoundary Old.err)} scopeStep12 (T.more {a = scopeEvent S.deactivateIG} scopeStep13 (T.more {a = scopeEvent S.flushIG} scopeStep14 (T.more {a = exitEvent (E.captureSnapshot)} scopeStep15 (T.more {a = exitEvent (E.invokeFinal)} scopeStep16 (T.more {a = exitEvent (E.returnFinal)} scopeStep17 (T.more {a = exitEvent (E.finishFinal)} scopeStep18 (T.more {a = scopeEvent S.publishIGResult} scopeStep19 (T.more {a = scopeEvent S.joinIG} scopeStep20 (T.more {a = scopeEvent S.beginCM} scopeStep21 (T.stop)))))))))))))))))))))

    append : ∀ {start middle current first last} → T.Runs start first middle → T.Runs middle last current → T.Runs start (first ++ last) current
    append T.stop rest = rest
    append (T.more actual path) rest = T.more actual (append path rest)
    closeEvents : List T.Event
    closeEvents = peerEvents ++ scopeEvents
    closed : T.Runtime
    closed = scope21
    abstract
      actualClose : T.Runs Prefix.terminatingRuntime closeEvents closed
      actualClose = append peerPath scopePath

    -- These are consequences of the actual preceding path, not adopted input PCs.
    closedStage : S.stage (E.base (K.server (T.base closed))) ≡ S.closingCM
    closedStage = refl
    closedPhysical : Prefix.stamp Suffix.beforeCM ≡ exitedPhysical
    closedPhysical = refl

    -- The callback and following inherited Server actions also inhabit the
    -- existing CM-entry certificate route, retaining its closed peer scopes.
    beforeEntryActions : List E.Action
    beforeEntryActions =
      (E.run (S.scope S.publishActionResult)) ∷
      (E.run (S.scope S.selectActionWinner)) ∷
      (E.run (S.scope S.requestAcceptCancel)) ∷
      (E.run (S.scope S.deliverAcceptAtWait)) ∷
      (E.run (S.scope S.closeListener)) ∷
      (E.run (S.scope S.publishAcceptResult)) ∷
      (E.run (S.scope S.joinAccept)) ∷
      (E.run (S.scope S.traceStopped)) ∷
      (E.run (S.scope S.cancelJoinReturnedAction)) ∷
      (E.run (S.scope S.requestIGCancel)) ∷
      (E.receive E.loopBoundary Old.err) ∷
      (E.run (S.scope S.deactivateIG)) ∷
      (E.run (S.scope S.flushIG)) ∷
      (E.captureSnapshot) ∷
      (E.invokeFinal) ∷
      (E.returnFinal) ∷
      (E.finishFinal) ∷
      (E.run (S.scope S.publishIGResult)) ∷
      (E.run (S.scope S.joinIG)) ∷ []
    afterCallbackActions : List E.Action
    afterCallbackActions = beforeEntryActions ++ (E.run (S.scope S.beginCM) ∷ [])
    abstract
      afterCallbackServerRuns : J.ServerRuns scope1 afterCallbackActions closed
      afterCallbackServerRuns = J.serverNext {a = E.run (S.scope S.publishActionResult)} scopeStep2 (J.serverNext {a = E.run (S.scope S.selectActionWinner)} scopeStep3 (J.serverNext {a = E.run (S.scope S.requestAcceptCancel)} scopeStep4 (J.serverNext {a = E.run (S.scope S.deliverAcceptAtWait)} scopeStep5 (J.serverNext {a = E.run (S.scope S.closeListener)} scopeStep6 (J.serverNext {a = E.run (S.scope S.publishAcceptResult)} scopeStep7 (J.serverNext {a = E.run (S.scope S.joinAccept)} scopeStep8 (J.serverNext {a = E.run (S.scope S.traceStopped)} scopeStep9 (J.serverNext {a = E.run (S.scope S.cancelJoinReturnedAction)} scopeStep10 (J.serverNext {a = E.run (S.scope S.requestIGCancel)} scopeStep11 (J.serverNext {a = E.receive E.loopBoundary Old.err} scopeStep12 (J.serverNext {a = E.run (S.scope S.deactivateIG)} scopeStep13 (J.serverNext {a = E.run (S.scope S.flushIG)} scopeStep14 (J.serverNext {a = E.captureSnapshot} scopeStep15 (J.serverNext {a = E.invokeFinal} scopeStep16 (J.serverNext {a = E.returnFinal} scopeStep17 (J.serverNext {a = E.finishFinal} scopeStep18 (J.serverNext {a = E.run (S.scope S.publishIGResult)} scopeStep19 (J.serverNext {a = E.run (S.scope S.joinIG)} scopeStep20 (J.serverNext {a = E.run (S.scope S.beginCM)} scopeStep21 (J.serverDone))))))))))))))))))))

  module WaitingPrefix where
    open import Data.Bool using (true; false)
    open import Data.List using (List; []; _∷_; _++_; map; drop)
    open import Data.Maybe using (just; nothing)
    open import Data.Product using (_,_)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
    open import ConnectionManagement.Domain using (ident)
    open import ConnectionManagement.Store using (put; lookup)
    import ConnectionManagement.State as Shared
    import ConnectionManagement.Machine as Machine
    import ConnectionManagement.OutboundMachine as O
    import ConnectionManagement.Rules.Cleanup as Cleanup
    import ConnectionManagement.Rules.CMShutdown as Close
    import ConnectionManagement.Rules.MuxJobTypes as Types
    import ConnectionManagement.MuxProtocolJobs as P
    import ConnectionManagement.Negative.MuxProtocolJobs as Old
    import ConnectionManagement.Negative.MuxGroupShutdown as GF
    import ConnectionManagement.Negative.MuxHandlerExit as EF
    import ConnectionManagement.Negative.MuxResultMonitor as RF
    import ConnectionManagement.Negative.GovernorPool as Prior
    import ConnectionManagement.Negative.ServerPeers as PriorServer
    import ConnectionManagement.ServerPeers as Combined
    import ConnectionManagement.ServerAdmission as Server
    import ConnectionManagement.Properties.ServerPeersMuxEmbedding as Embedding
    module Prefix = TerminatingPrefix using (preparedFront; stamp)
    module Scope = ScopeClose using (closed; closedContext; publishedExit)

    module W = OutboundMuxChecks.PhysicalSuffix.W using (Action; Executes; Phase; State; acknowledgeFinished; asyncException; beginExit; cleanup; cleanupComplete; deliverShutdownTimeWait; done; enterFinalizer; exitFrame; finalizing; finishCleanup; next; observeBufferReturn; publishAsyncResult; resultAvailable; resultOf; resultReady; run; setShutdown; setSource; shared; shutdown; shutdownStep; source; step)
    module G = OutboundMuxChecks.PhysicalSuffix.G using (Outcome; abortOwner; asyncExit; beginAsyncDead; beginWholeClose; commitAsyncTracer; deliverWhole; finishAsyncDead; finishChildUnwind; finishWholeClose; joinWhole; requestWholeCancel; run; sampleAsyncTracer; writeAsyncFailure)
    module M = OutboundMuxChecks.PhysicalSuffix.M using (run)
    private
     module T = Combined.Protocols RF.bearerClosed Prior.classify PriorServer.Protocols.capability using (Event; Runs; Runtime; advance; more; stop)
     module S = Server RF.bearerClosed using (closingCM)
     module Emb = Embedding.Frontend RF.bearerClosed Prior.classify PriorServer.Protocols.capability using (Allowed; embed; event; lift-step; nextFront)

    owner = Old.owner
    err = Old.err
    captured = Old.Prior.captured
    term = Shared.terminating (Shared.handlerKey captured) owner nothing
    wrap = OutboundMuxChecks.PhysicalSuffix.wrap
    post : W.State → W.State
    post original = Prefix.stamp (OutboundMuxChecks.PhysicalSuffix.exited original)
    hold : Close.State → W.State → W.State
    hold coordinator original = W.setShutdown coordinator (post original)
    at : W.State → T.Runtime
    at physical = Emb.embed physical Scope.closedContext Prefix.preparedFront S.closingCM false Scope.publishedExit
    event : W.Action → T.Event
    event = Emb.event
    up : ∀ action before {after} →
     Emb.Allowed action before after Scope.closedContext Prefix.preparedFront S.closingCM false Scope.publishedExit →
     Emb.nextFront action Prefix.preparedFront ≡ Prefix.preparedFront →
     W.step action before ≡ just after → T.advance (event action) (at before) ≡ just (at after)
    up action before {after} permitted copied actual = trans
     (Emb.lift-step action before Scope.closedContext Prefix.preparedFront S.closingCM false Scope.publishedExit permitted actual)
     (cong just (cong (λ front → Emb.embed after Scope.closedContext front S.closingCM false Scope.publishedExit) copied))

    startPhysical = hold Close.initialState (wrap GF.abortGroup0)
    start = at startPhysical
    closedMatches : Scope.closed ≡ start
    closedMatches = refl

    -- This owner interruption is independent; CM has not captured or acknowledged it.
    abort : ∀ coordinator → W.step (W.run (G.abortOwner owner err))
     (hold coordinator (wrap GF.abortGroup0)) ≡ just (hold coordinator (wrap GF.abortGroup1))
    abort coordinator = refl
    group2 : ∀ coordinator → W.step (W.run (G.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []))) (hold coordinator (wrap GF.abortGroup1)) ≡ just (hold coordinator (wrap GF.abortGroup2))
    group2 coordinator = refl

    group3 : ∀ coordinator → W.step (W.run (G.requestWholeCancel owner)) (hold coordinator (wrap GF.abortGroup2)) ≡ just (hold coordinator (wrap GF.abortGroup3))
    group3 coordinator = refl

    group4 : ∀ coordinator → W.step (W.run (G.finishChildUnwind Old.j₁₀)) (hold coordinator (wrap GF.abortGroup3)) ≡ just (hold coordinator (wrap GF.abortGroup4))
    group4 coordinator = refl

    group5 : ∀ coordinator → W.step (W.run (G.run (M.run (P.deregisterProtocol Old.j₁₀)))) (hold coordinator (wrap GF.abortGroup4)) ≡ just (hold coordinator (wrap GF.abortGroup5))
    group5 coordinator = refl

    group6 : ∀ coordinator → W.step (W.run (G.run (M.run (P.asyncProtocolResult Old.j₁₀)))) (hold coordinator (wrap GF.abortGroup5)) ≡ just (hold coordinator (wrap GF.abortGroup6))
    group6 coordinator = refl

    group7 : ∀ coordinator → W.step (W.run (G.joinWhole owner)) (hold coordinator (wrap GF.abortGroup6)) ≡ just (hold coordinator (wrap GF.abortGroup7))
    group7 coordinator = refl

    group8 : ∀ coordinator → W.step (W.run (G.requestWholeCancel owner)) (hold coordinator (wrap GF.abortGroup7)) ≡ just (hold coordinator (wrap GF.abortGroup8))
    group8 coordinator = refl

    group9 : ∀ coordinator → W.step (W.run (G.deliverWhole owner)) (hold coordinator (wrap GF.abortGroup8)) ≡ just (hold coordinator (wrap GF.abortGroup9))
    group9 coordinator = refl

    group10 : ∀ coordinator → W.step (W.run (G.finishChildUnwind Old.j₁)) (hold coordinator (wrap GF.abortGroup9)) ≡ just (hold coordinator (wrap GF.abortGroup10))
    group10 coordinator = refl

    group11 : ∀ coordinator → W.step (W.run (G.run (M.run (P.deregisterInfra owner Types.demuxer)))) (hold coordinator (wrap GF.abortGroup10)) ≡ just (hold coordinator (wrap GF.abortGroup11))
    group11 coordinator = refl

    group12 : ∀ coordinator → W.step (W.run (G.run (M.run (P.asyncInfraResult owner Types.demuxer)))) (hold coordinator (wrap GF.abortGroup11)) ≡ just (hold coordinator (wrap GF.abortGroup12))
    group12 coordinator = refl

    group13 : ∀ coordinator → W.step (W.run (G.joinWhole owner)) (hold coordinator (wrap GF.abortGroup12)) ≡ just (hold coordinator (wrap GF.abortGroup13))
    group13 coordinator = refl

    group14 : ∀ coordinator → W.step (W.run (G.requestWholeCancel owner)) (hold coordinator (wrap GF.abortGroup13)) ≡ just (hold coordinator (wrap GF.abortGroup14))
    group14 coordinator = refl

    group15 : ∀ coordinator → W.step (W.run (G.deliverWhole owner)) (hold coordinator (wrap GF.abortGroup14)) ≡ just (hold coordinator (wrap GF.abortGroup15))
    group15 coordinator = refl

    group16 : ∀ coordinator → W.step (W.run (G.finishChildUnwind Old.j₀)) (hold coordinator (wrap GF.abortGroup15)) ≡ just (hold coordinator (wrap GF.abortGroup16))
    group16 coordinator = refl

    group17 : ∀ coordinator → W.step (W.run (G.run (M.run (P.deregisterInfra owner Types.muxer)))) (hold coordinator (wrap GF.abortGroup16)) ≡ just (hold coordinator (wrap GF.abortGroup17))
    group17 coordinator = refl

    group18 : ∀ coordinator → W.step (W.run (G.run (M.run (P.asyncInfraResult owner Types.muxer)))) (hold coordinator (wrap GF.abortGroup17)) ≡ just (hold coordinator (wrap GF.abortGroup18))
    group18 coordinator = refl

    group19 : ∀ coordinator → W.step (W.run (G.joinWhole owner)) (hold coordinator (wrap GF.abortGroup18)) ≡ just (hold coordinator (wrap GF.abortGroup19))
    group19 coordinator = refl

    group20 : ∀ coordinator → W.step (W.run (G.finishWholeClose owner)) (hold coordinator (wrap GF.abortGroup19)) ≡ just (hold coordinator (wrap GF.abortGroup20))
    group20 coordinator = refl

    group21 : ∀ coordinator → W.step (W.run (G.writeAsyncFailure owner)) (hold coordinator (wrap GF.abortGroup20)) ≡ just (hold coordinator (wrap GF.abortGroup21))
    group21 coordinator = refl

    group22 : ∀ coordinator → W.step (W.run (G.beginAsyncDead owner)) (hold coordinator (wrap GF.abortGroup21)) ≡ just (hold coordinator (wrap GF.abortGroup22))
    group22 coordinator = refl

    group23 : ∀ coordinator → W.step (W.run (G.sampleAsyncTracer owner)) (hold coordinator (wrap GF.abortGroup22)) ≡ just (hold coordinator (wrap GF.abortGroup23))
    group23 coordinator = refl

    group24 : ∀ coordinator → W.step (W.run (G.commitAsyncTracer owner)) (hold coordinator (wrap GF.abortGroup23)) ≡ just (hold coordinator (wrap GF.abortGroup24))
    group24 coordinator = refl

    group25 : ∀ coordinator → W.step (W.run (G.finishAsyncDead owner)) (hold coordinator (wrap GF.abortGroup24)) ≡ just (hold coordinator (wrap GF.abortGroup25))
    group25 coordinator = refl


    abortTailActions : List W.Action
    abortTailActions = map W.run (drop 1 GF.abortGroupActions)

    abstract
     abortTail : ∀ coordinator → W.Executes (hold coordinator (wrap GF.abortGroup1)) abortTailActions (hold coordinator EF.async0)
     abortTail coordinator = W.next {a = W.run (G.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []))} (group2 coordinator) (W.next {a = W.run (G.requestWholeCancel owner)} (group3 coordinator) (W.next {a = W.run (G.finishChildUnwind Old.j₁₀)} (group4 coordinator) (W.next {a = W.run (G.run (M.run (P.deregisterProtocol Old.j₁₀)))} (group5 coordinator) (W.next {a = W.run (G.run (M.run (P.asyncProtocolResult Old.j₁₀)))} (group6 coordinator) (W.next {a = W.run (G.joinWhole owner)} (group7 coordinator) (W.next {a = W.run (G.requestWholeCancel owner)} (group8 coordinator) (W.next {a = W.run (G.deliverWhole owner)} (group9 coordinator) (W.next {a = W.run (G.finishChildUnwind Old.j₁)} (group10 coordinator) (W.next {a = W.run (G.run (M.run (P.deregisterInfra owner Types.demuxer)))} (group11 coordinator) (W.next {a = W.run (G.run (M.run (P.asyncInfraResult owner Types.demuxer)))} (group12 coordinator) (W.next {a = W.run (G.joinWhole owner)} (group13 coordinator) (W.next {a = W.run (G.requestWholeCancel owner)} (group14 coordinator) (W.next {a = W.run (G.deliverWhole owner)} (group15 coordinator) (W.next {a = W.run (G.finishChildUnwind Old.j₀)} (group16 coordinator) (W.next {a = W.run (G.run (M.run (P.deregisterInfra owner Types.muxer)))} (group17 coordinator) (W.next {a = W.run (G.run (M.run (P.asyncInfraResult owner Types.muxer)))} (group18 coordinator) (W.next {a = W.run (G.joinWhole owner)} (group19 coordinator) (W.next {a = W.run (G.finishWholeClose owner)} (group20 coordinator) (W.next {a = W.run (G.writeAsyncFailure owner)} (group21 coordinator) (W.next {a = W.run (G.beginAsyncDead owner)} (group22 coordinator) (W.next {a = W.run (G.sampleAsyncTracer owner)} (group23 coordinator) (W.next {a = W.run (G.commitAsyncTracer owner)} (group24 coordinator) (W.next {a = W.run (G.finishAsyncDead owner)} (group25 coordinator) (W.done))))))))))))))))))))))))

    -- Expected cleanup states retain the committed Terminating entry and binding
    -- until readiness is observed and the separate finally transaction executes.
    setWorld : Shared.State → W.State → W.State
    setWorld world physical = W.setSource (record source { core = Machine.replaceWorld (O.core source) world }) physical
     where source = W.source physical
    world0 : Shared.State
    world0 = W.shared (post EF.async2)
    world1 world2 world3 world4 world5 : Shared.State
    world1 = record world0 { cleanups = (owner , Shared.cleanupAcquire) ∷ [] }
    world2 = record world1
     { cm = record (Shared.cm world1) { mapCell = Shared.taken owner }
     ; cleanups = (owner , Shared.cleanupSelect EF.lease) ∷ [] }
    world3 = record world2
     { cleanups = (owner , Shared.cleanupClose EF.lease EF.table (Shared.timeWait term)) ∷ [] }
    world4 = record world3
     { sockets = put (Shared.handlerSocket captured) Shared.closed (Shared.sockets world3)
     ; cleanups = (owner , Shared.cleanupPublish EF.lease EF.table (Shared.timeWait term)) ∷ [] }
    world5 = record world4
     { cm = record (Shared.cm world4) { mapCell = Shared.full EF.table }
     ; cleanups = (owner , Shared.cleanupWaiting term) ∷ [] }

    finalizer : Close.State → Shared.State → W.State
    finalizer coordinator world = W.setShutdown coordinator
     (record (setWorld world (post EF.async2))
      { exits = (owner , W.exitFrame captured (W.finalizing (W.asyncException err)) nothing) ∷ [] })
    waitingPhysical : Close.State → W.State
    waitingPhysical coordinator = finalizer coordinator world5
    waiting : T.Runtime
    waiting = at (waitingPhysical Close.initialState)

    beginExit : ∀ coordinator → W.step (W.beginExit owner) (hold coordinator EF.async0) ≡ just (hold coordinator EF.async1)
    beginExit coordinator = refl

    bufferReturn : ∀ coordinator → W.step (W.observeBufferReturn owner) (hold coordinator EF.async1) ≡ just (hold coordinator EF.async2)
    bufferReturn coordinator = refl

    enterFinally : ∀ coordinator → W.step (W.enterFinalizer owner) (hold coordinator EF.async2) ≡ just (finalizer coordinator world1)
    enterFinally coordinator = refl

    takeMap : ∀ coordinator → W.step (W.cleanup owner Cleanup.takeCleanupMap) (finalizer coordinator world1) ≡ just (finalizer coordinator world2)
    takeMap coordinator = refl

    selectEntry : ∀ coordinator → W.step (W.cleanup owner Cleanup.selectCleanupEntry) (finalizer coordinator world2) ≡ just (finalizer coordinator world3)
    selectEntry coordinator = refl

    closeSocket : ∀ coordinator → W.step (W.cleanup owner Cleanup.closeHandlerSocket) (finalizer coordinator world3) ≡ just (finalizer coordinator world4)
    closeSocket coordinator = refl

    publishMap : ∀ coordinator → W.step (W.cleanup owner Cleanup.publishCleanupMap) (finalizer coordinator world4) ≡ just (waitingPhysical coordinator)
    publishMap coordinator = refl

    bodyActions : List W.Action
    bodyActions = W.beginExit owner ∷ W.observeBufferReturn owner ∷ W.enterFinalizer owner ∷
     W.cleanup owner Cleanup.takeCleanupMap ∷ W.cleanup owner Cleanup.selectCleanupEntry ∷
     W.cleanup owner Cleanup.closeHandlerSocket ∷ W.cleanup owner Cleanup.publishCleanupMap ∷ []
    abstract
     bodyPath : ∀ coordinator → W.Executes (hold coordinator EF.async0) bodyActions (waitingPhysical coordinator)
     bodyPath coordinator = W.next {a = W.beginExit owner} (beginExit coordinator) (W.next {a = W.observeBufferReturn owner} (bufferReturn coordinator) (W.next {a = W.enterFinalizer owner} (enterFinally coordinator) (W.next {a = W.cleanup owner Cleanup.takeCleanupMap} (takeMap coordinator) (W.next {a = W.cleanup owner Cleanup.selectCleanupEntry} (selectEntry coordinator) (W.next {a = W.cleanup owner Cleanup.closeHandlerSocket} (closeSocket coordinator) (W.next {a = W.cleanup owner Cleanup.publishCleanupMap} (publishMap coordinator) (W.done)))))))

    independentAbort : ∀ coordinator → T.advance (event (W.run (G.abortOwner owner err))) (at (hold coordinator (wrap GF.abortGroup0))) ≡ just (at (hold coordinator (wrap GF.abortGroup1)))
    independentAbort coordinator = up (W.run (G.abortOwner owner err)) (hold coordinator (wrap GF.abortGroup0)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (abort coordinator)

    liftGroup2 : ∀ coordinator → T.advance (event (W.run (G.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ [])))) (at (hold coordinator (wrap GF.abortGroup1))) ≡ just (at (hold coordinator (wrap GF.abortGroup2)))
    liftGroup2 coordinator = up (W.run (G.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []))) (hold coordinator (wrap GF.abortGroup1)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group2 coordinator)

    liftGroup3 : ∀ coordinator → T.advance (event (W.run (G.requestWholeCancel owner))) (at (hold coordinator (wrap GF.abortGroup2))) ≡ just (at (hold coordinator (wrap GF.abortGroup3)))
    liftGroup3 coordinator = up (W.run (G.requestWholeCancel owner)) (hold coordinator (wrap GF.abortGroup2)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group3 coordinator)

    liftGroup4 : ∀ coordinator → T.advance (event (W.run (G.finishChildUnwind Old.j₁₀))) (at (hold coordinator (wrap GF.abortGroup3))) ≡ just (at (hold coordinator (wrap GF.abortGroup4)))
    liftGroup4 coordinator = up (W.run (G.finishChildUnwind Old.j₁₀)) (hold coordinator (wrap GF.abortGroup3)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group4 coordinator)

    liftGroup5 : ∀ coordinator → T.advance (event (W.run (G.run (M.run (P.deregisterProtocol Old.j₁₀))))) (at (hold coordinator (wrap GF.abortGroup4))) ≡ just (at (hold coordinator (wrap GF.abortGroup5)))
    liftGroup5 coordinator = up (W.run (G.run (M.run (P.deregisterProtocol Old.j₁₀)))) (hold coordinator (wrap GF.abortGroup4)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group5 coordinator)

    liftGroup6 : ∀ coordinator → T.advance (event (W.run (G.run (M.run (P.asyncProtocolResult Old.j₁₀))))) (at (hold coordinator (wrap GF.abortGroup5))) ≡ just (at (hold coordinator (wrap GF.abortGroup6)))
    liftGroup6 coordinator = up (W.run (G.run (M.run (P.asyncProtocolResult Old.j₁₀)))) (hold coordinator (wrap GF.abortGroup5)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group6 coordinator)

    liftGroup7 : ∀ coordinator → T.advance (event (W.run (G.joinWhole owner))) (at (hold coordinator (wrap GF.abortGroup6))) ≡ just (at (hold coordinator (wrap GF.abortGroup7)))
    liftGroup7 coordinator = up (W.run (G.joinWhole owner)) (hold coordinator (wrap GF.abortGroup6)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group7 coordinator)

    liftGroup8 : ∀ coordinator → T.advance (event (W.run (G.requestWholeCancel owner))) (at (hold coordinator (wrap GF.abortGroup7))) ≡ just (at (hold coordinator (wrap GF.abortGroup8)))
    liftGroup8 coordinator = up (W.run (G.requestWholeCancel owner)) (hold coordinator (wrap GF.abortGroup7)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group8 coordinator)

    liftGroup9 : ∀ coordinator → T.advance (event (W.run (G.deliverWhole owner))) (at (hold coordinator (wrap GF.abortGroup8))) ≡ just (at (hold coordinator (wrap GF.abortGroup9)))
    liftGroup9 coordinator = up (W.run (G.deliverWhole owner)) (hold coordinator (wrap GF.abortGroup8)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group9 coordinator)

    liftGroup10 : ∀ coordinator → T.advance (event (W.run (G.finishChildUnwind Old.j₁))) (at (hold coordinator (wrap GF.abortGroup9))) ≡ just (at (hold coordinator (wrap GF.abortGroup10)))
    liftGroup10 coordinator = up (W.run (G.finishChildUnwind Old.j₁)) (hold coordinator (wrap GF.abortGroup9)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group10 coordinator)

    liftGroup11 : ∀ coordinator → T.advance (event (W.run (G.run (M.run (P.deregisterInfra owner Types.demuxer))))) (at (hold coordinator (wrap GF.abortGroup10))) ≡ just (at (hold coordinator (wrap GF.abortGroup11)))
    liftGroup11 coordinator = up (W.run (G.run (M.run (P.deregisterInfra owner Types.demuxer)))) (hold coordinator (wrap GF.abortGroup10)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group11 coordinator)

    liftGroup12 : ∀ coordinator → T.advance (event (W.run (G.run (M.run (P.asyncInfraResult owner Types.demuxer))))) (at (hold coordinator (wrap GF.abortGroup11))) ≡ just (at (hold coordinator (wrap GF.abortGroup12)))
    liftGroup12 coordinator = up (W.run (G.run (M.run (P.asyncInfraResult owner Types.demuxer)))) (hold coordinator (wrap GF.abortGroup11)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group12 coordinator)

    liftGroup13 : ∀ coordinator → T.advance (event (W.run (G.joinWhole owner))) (at (hold coordinator (wrap GF.abortGroup12))) ≡ just (at (hold coordinator (wrap GF.abortGroup13)))
    liftGroup13 coordinator = up (W.run (G.joinWhole owner)) (hold coordinator (wrap GF.abortGroup12)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group13 coordinator)

    liftGroup14 : ∀ coordinator → T.advance (event (W.run (G.requestWholeCancel owner))) (at (hold coordinator (wrap GF.abortGroup13))) ≡ just (at (hold coordinator (wrap GF.abortGroup14)))
    liftGroup14 coordinator = up (W.run (G.requestWholeCancel owner)) (hold coordinator (wrap GF.abortGroup13)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group14 coordinator)

    liftGroup15 : ∀ coordinator → T.advance (event (W.run (G.deliverWhole owner))) (at (hold coordinator (wrap GF.abortGroup14))) ≡ just (at (hold coordinator (wrap GF.abortGroup15)))
    liftGroup15 coordinator = up (W.run (G.deliverWhole owner)) (hold coordinator (wrap GF.abortGroup14)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group15 coordinator)

    liftGroup16 : ∀ coordinator → T.advance (event (W.run (G.finishChildUnwind Old.j₀))) (at (hold coordinator (wrap GF.abortGroup15))) ≡ just (at (hold coordinator (wrap GF.abortGroup16)))
    liftGroup16 coordinator = up (W.run (G.finishChildUnwind Old.j₀)) (hold coordinator (wrap GF.abortGroup15)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group16 coordinator)

    liftGroup17 : ∀ coordinator → T.advance (event (W.run (G.run (M.run (P.deregisterInfra owner Types.muxer))))) (at (hold coordinator (wrap GF.abortGroup16))) ≡ just (at (hold coordinator (wrap GF.abortGroup17)))
    liftGroup17 coordinator = up (W.run (G.run (M.run (P.deregisterInfra owner Types.muxer)))) (hold coordinator (wrap GF.abortGroup16)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group17 coordinator)

    liftGroup18 : ∀ coordinator → T.advance (event (W.run (G.run (M.run (P.asyncInfraResult owner Types.muxer))))) (at (hold coordinator (wrap GF.abortGroup17))) ≡ just (at (hold coordinator (wrap GF.abortGroup18)))
    liftGroup18 coordinator = up (W.run (G.run (M.run (P.asyncInfraResult owner Types.muxer)))) (hold coordinator (wrap GF.abortGroup17)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group18 coordinator)

    liftGroup19 : ∀ coordinator → T.advance (event (W.run (G.joinWhole owner))) (at (hold coordinator (wrap GF.abortGroup18))) ≡ just (at (hold coordinator (wrap GF.abortGroup19)))
    liftGroup19 coordinator = up (W.run (G.joinWhole owner)) (hold coordinator (wrap GF.abortGroup18)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group19 coordinator)

    liftGroup20 : ∀ coordinator → T.advance (event (W.run (G.finishWholeClose owner))) (at (hold coordinator (wrap GF.abortGroup19))) ≡ just (at (hold coordinator (wrap GF.abortGroup20)))
    liftGroup20 coordinator = up (W.run (G.finishWholeClose owner)) (hold coordinator (wrap GF.abortGroup19)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group20 coordinator)

    liftGroup21 : ∀ coordinator → T.advance (event (W.run (G.writeAsyncFailure owner))) (at (hold coordinator (wrap GF.abortGroup20))) ≡ just (at (hold coordinator (wrap GF.abortGroup21)))
    liftGroup21 coordinator = up (W.run (G.writeAsyncFailure owner)) (hold coordinator (wrap GF.abortGroup20)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group21 coordinator)

    liftGroup22 : ∀ coordinator → T.advance (event (W.run (G.beginAsyncDead owner))) (at (hold coordinator (wrap GF.abortGroup21))) ≡ just (at (hold coordinator (wrap GF.abortGroup22)))
    liftGroup22 coordinator = up (W.run (G.beginAsyncDead owner)) (hold coordinator (wrap GF.abortGroup21)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group22 coordinator)

    liftGroup23 : ∀ coordinator → T.advance (event (W.run (G.sampleAsyncTracer owner))) (at (hold coordinator (wrap GF.abortGroup22))) ≡ just (at (hold coordinator (wrap GF.abortGroup23)))
    liftGroup23 coordinator = up (W.run (G.sampleAsyncTracer owner)) (hold coordinator (wrap GF.abortGroup22)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group23 coordinator)

    liftGroup24 : ∀ coordinator → T.advance (event (W.run (G.commitAsyncTracer owner))) (at (hold coordinator (wrap GF.abortGroup23))) ≡ just (at (hold coordinator (wrap GF.abortGroup24)))
    liftGroup24 coordinator = up (W.run (G.commitAsyncTracer owner)) (hold coordinator (wrap GF.abortGroup23)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group24 coordinator)

    liftGroup25 : ∀ coordinator → T.advance (event (W.run (G.finishAsyncDead owner))) (at (hold coordinator (wrap GF.abortGroup24))) ≡ just (at (hold coordinator (wrap GF.abortGroup25)))
    liftGroup25 coordinator = up (W.run (G.finishAsyncDead owner)) (hold coordinator (wrap GF.abortGroup24)) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (group25 coordinator)

    liftbeginExit : ∀ coordinator → T.advance (event (W.beginExit owner)) (at (hold coordinator EF.async0)) ≡ just (at (hold coordinator EF.async1))
    liftbeginExit coordinator = up (W.beginExit owner) (hold coordinator EF.async0) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (beginExit coordinator)

    liftbufferReturn : ∀ coordinator → T.advance (event (W.observeBufferReturn owner)) (at (hold coordinator EF.async1)) ≡ just (at (hold coordinator EF.async2))
    liftbufferReturn coordinator = up (W.observeBufferReturn owner) (hold coordinator EF.async1) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (bufferReturn coordinator)

    liftenterFinally : ∀ coordinator → T.advance (event (W.enterFinalizer owner)) (at (hold coordinator EF.async2)) ≡ just (at (finalizer coordinator world1))
    liftenterFinally coordinator = up (W.enterFinalizer owner) (hold coordinator EF.async2) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (enterFinally coordinator)

    lifttakeMap : ∀ coordinator → T.advance (event (W.cleanup owner Cleanup.takeCleanupMap)) (at (finalizer coordinator world1)) ≡ just (at (finalizer coordinator world2))
    lifttakeMap coordinator = up (W.cleanup owner Cleanup.takeCleanupMap) (finalizer coordinator world1) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (takeMap coordinator)

    liftselectEntry : ∀ coordinator → T.advance (event (W.cleanup owner Cleanup.selectCleanupEntry)) (at (finalizer coordinator world2)) ≡ just (at (finalizer coordinator world3))
    liftselectEntry coordinator = up (W.cleanup owner Cleanup.selectCleanupEntry) (finalizer coordinator world2) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (selectEntry coordinator)

    liftcloseSocket : ∀ coordinator → T.advance (event (W.cleanup owner Cleanup.closeHandlerSocket)) (at (finalizer coordinator world3)) ≡ just (at (finalizer coordinator world4))
    liftcloseSocket coordinator = up (W.cleanup owner Cleanup.closeHandlerSocket) (finalizer coordinator world3) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (closeSocket coordinator)

    liftpublishMap : ∀ coordinator → T.advance (event (W.cleanup owner Cleanup.publishCleanupMap)) (at (finalizer coordinator world4)) ≡ just (at (waitingPhysical coordinator))
    liftpublishMap coordinator = up (W.cleanup owner Cleanup.publishCleanupMap) (finalizer coordinator world4) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl (publishMap coordinator)

    waitingActions : List W.Action
    waitingActions = W.run (G.abortOwner owner err) ∷ (abortTailActions ++ bodyActions)
    waitingEvents : List T.Event
    waitingEvents = map event waitingActions
    abstract
     actualWaiting : T.Runs start waitingEvents waiting
     actualWaiting = T.more {a = event (W.run (G.abortOwner owner err))} (independentAbort Close.initialState) (T.more {a = event (W.run (G.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ [])))} (liftGroup2 Close.initialState) (T.more {a = event (W.run (G.requestWholeCancel owner))} (liftGroup3 Close.initialState) (T.more {a = event (W.run (G.finishChildUnwind Old.j₁₀))} (liftGroup4 Close.initialState) (T.more {a = event (W.run (G.run (M.run (P.deregisterProtocol Old.j₁₀))))} (liftGroup5 Close.initialState) (T.more {a = event (W.run (G.run (M.run (P.asyncProtocolResult Old.j₁₀))))} (liftGroup6 Close.initialState) (T.more {a = event (W.run (G.joinWhole owner))} (liftGroup7 Close.initialState) (T.more {a = event (W.run (G.requestWholeCancel owner))} (liftGroup8 Close.initialState) (T.more {a = event (W.run (G.deliverWhole owner))} (liftGroup9 Close.initialState) (T.more {a = event (W.run (G.finishChildUnwind Old.j₁))} (liftGroup10 Close.initialState) (T.more {a = event (W.run (G.run (M.run (P.deregisterInfra owner Types.demuxer))))} (liftGroup11 Close.initialState) (T.more {a = event (W.run (G.run (M.run (P.asyncInfraResult owner Types.demuxer))))} (liftGroup12 Close.initialState) (T.more {a = event (W.run (G.joinWhole owner))} (liftGroup13 Close.initialState) (T.more {a = event (W.run (G.requestWholeCancel owner))} (liftGroup14 Close.initialState) (T.more {a = event (W.run (G.deliverWhole owner))} (liftGroup15 Close.initialState) (T.more {a = event (W.run (G.finishChildUnwind Old.j₀))} (liftGroup16 Close.initialState) (T.more {a = event (W.run (G.run (M.run (P.deregisterInfra owner Types.muxer))))} (liftGroup17 Close.initialState) (T.more {a = event (W.run (G.run (M.run (P.asyncInfraResult owner Types.muxer))))} (liftGroup18 Close.initialState) (T.more {a = event (W.run (G.joinWhole owner))} (liftGroup19 Close.initialState) (T.more {a = event (W.run (G.finishWholeClose owner))} (liftGroup20 Close.initialState) (T.more {a = event (W.run (G.writeAsyncFailure owner))} (liftGroup21 Close.initialState) (T.more {a = event (W.run (G.beginAsyncDead owner))} (liftGroup22 Close.initialState) (T.more {a = event (W.run (G.sampleAsyncTracer owner))} (liftGroup23 Close.initialState) (T.more {a = event (W.run (G.commitAsyncTracer owner))} (liftGroup24 Close.initialState) (T.more {a = event (W.run (G.finishAsyncDead owner))} (liftGroup25 Close.initialState) (T.more {a = event (W.beginExit owner)} (liftbeginExit Close.initialState) (T.more {a = event (W.observeBufferReturn owner)} (liftbufferReturn Close.initialState) (T.more {a = event (W.enterFinalizer owner)} (liftenterFinally Close.initialState) (T.more {a = event (W.cleanup owner Cleanup.takeCleanupMap)} (lifttakeMap Close.initialState) (T.more {a = event (W.cleanup owner Cleanup.selectCleanupEntry)} (liftselectEntry Close.initialState) (T.more {a = event (W.cleanup owner Cleanup.closeHandlerSocket)} (liftcloseSocket Close.initialState) (T.more {a = event (W.cleanup owner Cleanup.publishCleanupMap)} (liftpublishMap Close.initialState) (T.stop))))))))))))))))))))))))))))))))

    waitingEntry : lookup (ident 0) (Shared.entries (Shared.cm (W.shared (waitingPhysical Close.initialState)))) ≡ just term
    waitingEntry = refl
    waitingBinding : Shared.mapCell (Shared.cm (W.shared (waitingPhysical Close.initialState))) ≡ Shared.full EF.table
    waitingBinding = refl
    waitingSocketClosed : lookup (Shared.handlerSocket captured) (Shared.sockets (W.shared (waitingPhysical Close.initialState))) ≡ just Shared.closed
    waitingSocketClosed = refl
    waitingNoResult : W.resultReady owner (waitingPhysical Close.initialState) ≡ false
    waitingNoResult = refl
    independentStillUncollected : Close.collected (W.shutdown (waitingPhysical Close.initialState)) ≡ []
    independentStillUncollected = refl

  module Suffix where
    open import Data.Bool using (true; false)
    open import Data.List using (List; []; _∷_; _++_; map)
    open import Data.List.Membership.Propositional using (_∈_)
    open import Data.List.Relation.Unary.Any using (here)
    open import Data.Maybe using (Maybe; just; nothing)
    open import Data.Product using (_,_)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
    open import ConnectionManagement.Domain using (ident; errorId)
    open import ConnectionManagement.Store using (lookup)
    import ConnectionManagement.State as Shared
    import ConnectionManagement.Negative.MuxHandlerExit as EF
    import ConnectionManagement.Negative.MuxResultMonitor as RF
    import ConnectionManagement.Negative.GovernorPool as Prior
    import ConnectionManagement.Negative.ServerPeers as PriorServer
    import ConnectionManagement.ServerPeers as Combined
    import ConnectionManagement.Rules.Cleanup as Cleanup
    import ConnectionManagement.Rules.CMShutdown as Close
    module Waiting = WaitingPrefix using (module G; module W; actualWaiting; at; captured; err; event; owner; post; setWorld; start; term; up; waiting; waitingActions; waitingPhysical; world5)

    module W = Waiting.W using (Action; Phase; State; acknowledgeFinished; asyncException; cleanup; cleanupComplete; deliverShutdownTimeWait; exitFrame; finalizing; finishCleanup; publishAsyncResult; resultAvailable; resultOf; setShutdown; shared; shutdown; shutdownStep; step)
    module G = Waiting.G using (Outcome; asyncExit)
    private module T = Combined.Protocols RF.bearerClosed Prior.classify PriorServer.Protocols.capability using (Event; Runs; advance; more; stop)
    owner = Waiting.owner
    bodyError = Waiting.err
    receiptError = errorId 99
    term = Waiting.term
    captured = Waiting.captured
    module OldCM = OutboundMuxChecks.PhysicalSuffix using (acknowledged; awaiting; captured; closed; requested; selected)
    at = Waiting.at
    event = Waiting.event
    up = Waiting.up

    beforeCapture = Waiting.waiting
    capturedState = at (Waiting.waitingPhysical OldCM.captured)
    branchpoint = at (Waiting.waitingPhysical OldCM.selected)
    requested = at (Waiting.waitingPhysical OldCM.requested)

    -- Expected successors preserve the real original source and captured handler.
    worldFinalize : Shared.CleanupOutcome → Shared.State
    worldFinalize outcome = record Waiting.world5
     { cleanups = (owner , Shared.cleanupFinalize term outcome) ∷ [] }
    worldCount : Shared.CleanupOutcome → Shared.State
    worldCount outcome = record (worldFinalize outcome)
     { cm = record (Shared.cm Waiting.world5)
       { mapCell = Shared.full []; entries = (ident 0 , Shared.terminated nothing) ∷ [] }
     ; cleanups = (owner , Shared.cleanupCount outcome) ∷ [] }
    worldDone : Shared.CleanupOutcome → Shared.State
    worldDone outcome = record (worldCount outcome)
     { cleanups = (owner , Shared.cleanupDone outcome) ∷ [] }

    -- Body and finally outcomes are retained independently until publication.
    state : Close.State → W.Phase → Maybe G.Outcome → Shared.State → W.State
    state coordinator phase fault world = W.setShutdown coordinator
     (record (Waiting.setWorld world (Waiting.post EF.async2))
      { exits = (owner , W.exitFrame captured phase fault) ∷ [] })
    finalizing = W.finalizing (W.asyncException bodyError)
    interruptedPhysical = state OldCM.acknowledged finalizing (just (G.asyncExit receiptError)) (worldFinalize (Shared.cleanupError receiptError))
    interruptedCountPhysical = state OldCM.acknowledged finalizing (just (G.asyncExit receiptError)) (worldCount (Shared.cleanupError receiptError))
    interruptedDonePhysical = state OldCM.acknowledged finalizing (just (G.asyncExit receiptError)) (worldDone (Shared.cleanupError receiptError))
    interruptedCleanedPhysical = state OldCM.acknowledged
     (W.cleanupComplete (W.asyncException bodyError) (Shared.cleanupError receiptError))
     (just (G.asyncExit receiptError)) (worldDone (Shared.cleanupError receiptError))
    interruptedPublishedPhysical = state OldCM.acknowledged
     (W.resultAvailable (W.asyncException bodyError) (Shared.cleanupError receiptError))
     (just (G.asyncExit receiptError)) (worldDone (Shared.cleanupError receiptError))
    interruptedBeforeWaitPhysical = W.setShutdown OldCM.awaiting interruptedPublishedPhysical
    interruptedFinalPhysical = W.setShutdown OldCM.closed interruptedPublishedPhysical
    interrupted = at interruptedPhysical
    interruptedCount = at interruptedCountPhysical
    interruptedDone = at interruptedDonePhysical
    interruptedCleaned = at interruptedCleanedPhysical
    interruptedPublished = at interruptedPublishedPhysical
    interruptedBeforeWait = at interruptedBeforeWaitPhysical
    interruptedFinal = at interruptedFinalPhysical

    elapsedPhysical = state OldCM.selected finalizing nothing (worldFinalize Shared.cleanupNormal)
    elapsedCountPhysical = state OldCM.selected finalizing nothing (worldCount Shared.cleanupNormal)
    elapsedDonePhysical = state OldCM.selected finalizing nothing (worldDone Shared.cleanupNormal)
    elapsedCleanedPhysical = state OldCM.selected
     (W.cleanupComplete (W.asyncException bodyError) Shared.cleanupNormal) nothing (worldDone Shared.cleanupNormal)
    elapsedPublishedPhysical = state OldCM.selected
     (W.resultAvailable (W.asyncException bodyError) Shared.cleanupNormal) nothing (worldDone Shared.cleanupNormal)
    elapsedRequestedPhysical = W.setShutdown OldCM.requested elapsedPublishedPhysical
    elapsedAcknowledgedPhysical = W.setShutdown OldCM.acknowledged elapsedPublishedPhysical
    elapsedBeforeWaitPhysical = W.setShutdown OldCM.awaiting elapsedPublishedPhysical
    elapsedFinalPhysical = W.setShutdown OldCM.closed elapsedPublishedPhysical
    elapsed = at elapsedPhysical
    elapsedCount = at elapsedCountPhysical
    elapsedDone = at elapsedDonePhysical
    elapsedCleaned = at elapsedCleanedPhysical
    elapsedPublished = at elapsedPublishedPhysical
    elapsedRequested = at elapsedRequestedPhysical
    elapsedAcknowledged = at elapsedAcknowledgedPhysical
    elapsedBeforeWait = at elapsedBeforeWaitPhysical
    elapsedFinal = at elapsedFinalPhysical

    -- Generated actual edge equations. Each has its own physical and guard proof.

    physicalcapture : W.step (W.shutdownStep Close.captureSnapshot) (Waiting.waitingPhysical Close.initialState) ≡ just (Waiting.waitingPhysical OldCM.captured)
    physicalcapture = refl
    capture : T.advance (event (W.shutdownStep Close.captureSnapshot)) (at (Waiting.waitingPhysical Close.initialState)) ≡ just (at (Waiting.waitingPhysical OldCM.captured))
    capture = up (W.shutdownStep Close.captureSnapshot) (Waiting.waitingPhysical Close.initialState) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalcapture

    physicalread : W.step (W.shutdownStep Close.readEntry) (Waiting.waitingPhysical OldCM.captured) ≡ just (Waiting.waitingPhysical OldCM.selected)
    physicalread = refl
    read : T.advance (event (W.shutdownStep Close.readEntry)) (at (Waiting.waitingPhysical OldCM.captured)) ≡ just (at (Waiting.waitingPhysical OldCM.selected))
    read = up (W.shutdownStep Close.readEntry) (Waiting.waitingPhysical OldCM.captured) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalread

    physicalrequest : W.step (W.shutdownStep Close.requestCancellation) (Waiting.waitingPhysical OldCM.selected) ≡ just (Waiting.waitingPhysical OldCM.requested)
    physicalrequest = refl
    request : T.advance (event (W.shutdownStep Close.requestCancellation)) (at (Waiting.waitingPhysical OldCM.selected)) ≡ just (at (Waiting.waitingPhysical OldCM.requested))
    request = up (W.shutdownStep Close.requestCancellation) (Waiting.waitingPhysical OldCM.selected) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalrequest

    physicalreceipt : W.step (W.deliverShutdownTimeWait receiptError) (Waiting.waitingPhysical OldCM.requested) ≡ just (interruptedPhysical)
    physicalreceipt = refl
    receipt : T.advance (event (W.deliverShutdownTimeWait receiptError)) (at (Waiting.waitingPhysical OldCM.requested)) ≡ just (at (interruptedPhysical))
    receipt = up (W.deliverShutdownTimeWait receiptError) (Waiting.waitingPhysical OldCM.requested) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalreceipt

    physicalinterruptedFinally : W.step (W.cleanup owner Cleanup.finishTimeWait) (interruptedPhysical) ≡ just (interruptedCountPhysical)
    physicalinterruptedFinally = refl
    interruptedFinally : T.advance (event (W.cleanup owner Cleanup.finishTimeWait)) (at (interruptedPhysical)) ≡ just (at (interruptedCountPhysical))
    interruptedFinally = up (W.cleanup owner Cleanup.finishTimeWait) (interruptedPhysical) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalinterruptedFinally

    physicalinterruptedCounters : W.step (W.cleanup owner Cleanup.readCleanupCounters) (interruptedCountPhysical) ≡ just (interruptedDonePhysical)
    physicalinterruptedCounters = refl
    interruptedCounters : T.advance (event (W.cleanup owner Cleanup.readCleanupCounters)) (at (interruptedCountPhysical)) ≡ just (at (interruptedDonePhysical))
    interruptedCounters = up (W.cleanup owner Cleanup.readCleanupCounters) (interruptedCountPhysical) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalinterruptedCounters

    physicalinterruptedFinish : W.step (W.finishCleanup owner) (interruptedDonePhysical) ≡ just (interruptedCleanedPhysical)
    physicalinterruptedFinish = refl
    interruptedFinish : T.advance (event (W.finishCleanup owner)) (at (interruptedDonePhysical)) ≡ just (at (interruptedCleanedPhysical))
    interruptedFinish = up (W.finishCleanup owner) (interruptedDonePhysical) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalinterruptedFinish

    physicalinterruptedPublication : W.step (W.publishAsyncResult owner) (interruptedCleanedPhysical) ≡ just (interruptedPublishedPhysical)
    physicalinterruptedPublication = refl
    interruptedPublication : T.advance (event (W.publishAsyncResult owner)) (at (interruptedCleanedPhysical)) ≡ just (at (interruptedPublishedPhysical))
    interruptedPublication = up (W.publishAsyncResult owner) (interruptedCleanedPhysical) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalinterruptedPublication

    physicalinterruptedTraverse : W.step (W.shutdownStep Close.finishTraversal) (interruptedPublishedPhysical) ≡ just (interruptedBeforeWaitPhysical)
    physicalinterruptedTraverse = refl
    interruptedTraverse : T.advance (event (W.shutdownStep Close.finishTraversal)) (at (interruptedPublishedPhysical)) ≡ just (at (interruptedBeforeWaitPhysical))
    interruptedTraverse = up (W.shutdownStep Close.finishTraversal) (interruptedPublishedPhysical) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalinterruptedTraverse

    physicalinterruptedWait : W.step (W.shutdownStep Close.finishClose) (interruptedBeforeWaitPhysical) ≡ just (interruptedFinalPhysical)
    physicalinterruptedWait = refl
    interruptedWait : T.advance (event (W.shutdownStep Close.finishClose)) (at (interruptedBeforeWaitPhysical)) ≡ just (at (interruptedFinalPhysical))
    interruptedWait = up (W.shutdownStep Close.finishClose) (interruptedBeforeWaitPhysical) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalinterruptedWait

    physicalexpiry : W.step (W.cleanup owner Cleanup.timeWaitElapsed) (Waiting.waitingPhysical OldCM.selected) ≡ just (elapsedPhysical)
    physicalexpiry = refl
    expiry : T.advance (event (W.cleanup owner Cleanup.timeWaitElapsed)) (at (Waiting.waitingPhysical OldCM.selected)) ≡ just (at (elapsedPhysical))
    expiry = up (W.cleanup owner Cleanup.timeWaitElapsed) (Waiting.waitingPhysical OldCM.selected) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalexpiry

    physicalelapsedFinally : W.step (W.cleanup owner Cleanup.finishTimeWait) (elapsedPhysical) ≡ just (elapsedCountPhysical)
    physicalelapsedFinally = refl
    elapsedFinally : T.advance (event (W.cleanup owner Cleanup.finishTimeWait)) (at (elapsedPhysical)) ≡ just (at (elapsedCountPhysical))
    elapsedFinally = up (W.cleanup owner Cleanup.finishTimeWait) (elapsedPhysical) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalelapsedFinally

    physicalelapsedCounters : W.step (W.cleanup owner Cleanup.readCleanupCounters) (elapsedCountPhysical) ≡ just (elapsedDonePhysical)
    physicalelapsedCounters = refl
    elapsedCounters : T.advance (event (W.cleanup owner Cleanup.readCleanupCounters)) (at (elapsedCountPhysical)) ≡ just (at (elapsedDonePhysical))
    elapsedCounters = up (W.cleanup owner Cleanup.readCleanupCounters) (elapsedCountPhysical) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalelapsedCounters

    physicalelapsedFinish : W.step (W.finishCleanup owner) (elapsedDonePhysical) ≡ just (elapsedCleanedPhysical)
    physicalelapsedFinish = refl
    elapsedFinish : T.advance (event (W.finishCleanup owner)) (at (elapsedDonePhysical)) ≡ just (at (elapsedCleanedPhysical))
    elapsedFinish = up (W.finishCleanup owner) (elapsedDonePhysical) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalelapsedFinish

    physicalelapsedPublication : W.step (W.publishAsyncResult owner) (elapsedCleanedPhysical) ≡ just (elapsedPublishedPhysical)
    physicalelapsedPublication = refl
    elapsedPublication : T.advance (event (W.publishAsyncResult owner)) (at (elapsedCleanedPhysical)) ≡ just (at (elapsedPublishedPhysical))
    elapsedPublication = up (W.publishAsyncResult owner) (elapsedCleanedPhysical) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalelapsedPublication

    physicalelapsedRequest : W.step (W.shutdownStep Close.requestCancellation) (elapsedPublishedPhysical) ≡ just (elapsedRequestedPhysical)
    physicalelapsedRequest = refl
    elapsedRequest : T.advance (event (W.shutdownStep Close.requestCancellation)) (at (elapsedPublishedPhysical)) ≡ just (at (elapsedRequestedPhysical))
    elapsedRequest = up (W.shutdownStep Close.requestCancellation) (elapsedPublishedPhysical) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalelapsedRequest

    physicalelapsedReceipt : W.step (W.acknowledgeFinished) (elapsedRequestedPhysical) ≡ just (elapsedAcknowledgedPhysical)
    physicalelapsedReceipt = refl
    elapsedReceipt : T.advance (event (W.acknowledgeFinished)) (at (elapsedRequestedPhysical)) ≡ just (at (elapsedAcknowledgedPhysical))
    elapsedReceipt = up (W.acknowledgeFinished) (elapsedRequestedPhysical) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalelapsedReceipt

    physicalelapsedTraverse : W.step (W.shutdownStep Close.finishTraversal) (elapsedAcknowledgedPhysical) ≡ just (elapsedBeforeWaitPhysical)
    physicalelapsedTraverse = refl
    elapsedTraverse : T.advance (event (W.shutdownStep Close.finishTraversal)) (at (elapsedAcknowledgedPhysical)) ≡ just (at (elapsedBeforeWaitPhysical))
    elapsedTraverse = up (W.shutdownStep Close.finishTraversal) (elapsedAcknowledgedPhysical) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalelapsedTraverse

    physicalelapsedWait : W.step (W.shutdownStep Close.finishClose) (elapsedBeforeWaitPhysical) ≡ just (elapsedFinalPhysical)
    physicalelapsedWait = refl
    elapsedWait : T.advance (event (W.shutdownStep Close.finishClose)) (at (elapsedBeforeWaitPhysical)) ≡ just (at (elapsedFinalPhysical))
    elapsedWait = up (W.shutdownStep Close.finishClose) (elapsedBeforeWaitPhysical) (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl physicalelapsedWait

    actualSelectedActions : List W.Action
    actualSelectedActions = (W.shutdownStep Close.captureSnapshot) ∷ (W.shutdownStep Close.readEntry) ∷ []
    actualSelectedEvents : List T.Event
    actualSelectedEvents = map event actualSelectedActions
    abstract
     actualSelected : T.Runs beforeCapture actualSelectedEvents branchpoint
     actualSelected = T.more {a = event (W.shutdownStep Close.captureSnapshot)} capture (T.more {a = event (W.shutdownStep Close.readEntry)} read (T.stop))

    actualInterruptReceiptActions : List W.Action
    actualInterruptReceiptActions = (W.shutdownStep Close.requestCancellation) ∷ (W.deliverShutdownTimeWait receiptError) ∷ []
    actualInterruptReceiptEvents : List T.Event
    actualInterruptReceiptEvents = map event actualInterruptReceiptActions
    abstract
     actualInterruptReceipt : T.Runs branchpoint actualInterruptReceiptEvents interrupted
     actualInterruptReceipt = T.more {a = event (W.shutdownStep Close.requestCancellation)} request (T.more {a = event (W.deliverShutdownTimeWait receiptError)} receipt (T.stop))

    actualInterruptPublicationActions : List W.Action
    actualInterruptPublicationActions = (W.cleanup owner Cleanup.finishTimeWait) ∷ (W.cleanup owner Cleanup.readCleanupCounters) ∷ (W.finishCleanup owner) ∷ (W.publishAsyncResult owner) ∷ []
    actualInterruptPublicationEvents : List T.Event
    actualInterruptPublicationEvents = map event actualInterruptPublicationActions
    abstract
     actualInterruptPublication : T.Runs interrupted actualInterruptPublicationEvents interruptedPublished
     actualInterruptPublication = T.more {a = event (W.cleanup owner Cleanup.finishTimeWait)} interruptedFinally (T.more {a = event (W.cleanup owner Cleanup.readCleanupCounters)} interruptedCounters (T.more {a = event (W.finishCleanup owner)} interruptedFinish (T.more {a = event (W.publishAsyncResult owner)} interruptedPublication (T.stop))))

    actualInterruptWaitActions : List W.Action
    actualInterruptWaitActions = (W.shutdownStep Close.finishTraversal) ∷ (W.shutdownStep Close.finishClose) ∷ []
    actualInterruptWaitEvents : List T.Event
    actualInterruptWaitEvents = map event actualInterruptWaitActions
    abstract
     actualInterruptWait : T.Runs interruptedPublished actualInterruptWaitEvents interruptedFinal
     actualInterruptWait = T.more {a = event (W.shutdownStep Close.finishTraversal)} interruptedTraverse (T.more {a = event (W.shutdownStep Close.finishClose)} interruptedWait (T.stop))

    actualExpiryPublicationActions : List W.Action
    actualExpiryPublicationActions = (W.cleanup owner Cleanup.timeWaitElapsed) ∷ (W.cleanup owner Cleanup.finishTimeWait) ∷ (W.cleanup owner Cleanup.readCleanupCounters) ∷ (W.finishCleanup owner) ∷ (W.publishAsyncResult owner) ∷ []
    actualExpiryPublicationEvents : List T.Event
    actualExpiryPublicationEvents = map event actualExpiryPublicationActions
    abstract
     actualExpiryPublication : T.Runs branchpoint actualExpiryPublicationEvents elapsedPublished
     actualExpiryPublication = T.more {a = event (W.cleanup owner Cleanup.timeWaitElapsed)} expiry (T.more {a = event (W.cleanup owner Cleanup.finishTimeWait)} elapsedFinally (T.more {a = event (W.cleanup owner Cleanup.readCleanupCounters)} elapsedCounters (T.more {a = event (W.finishCleanup owner)} elapsedFinish (T.more {a = event (W.publishAsyncResult owner)} elapsedPublication (T.stop)))))

    actualElapsedReceiptActions : List W.Action
    actualElapsedReceiptActions = (W.shutdownStep Close.requestCancellation) ∷ (W.acknowledgeFinished) ∷ []
    actualElapsedReceiptEvents : List T.Event
    actualElapsedReceiptEvents = map event actualElapsedReceiptActions
    abstract
     actualElapsedReceipt : T.Runs elapsedPublished actualElapsedReceiptEvents elapsedAcknowledged
     actualElapsedReceipt = T.more {a = event (W.shutdownStep Close.requestCancellation)} elapsedRequest (T.more {a = event (W.acknowledgeFinished)} elapsedReceipt (T.stop))

    actualElapsedWaitActions : List W.Action
    actualElapsedWaitActions = (W.shutdownStep Close.finishTraversal) ∷ (W.shutdownStep Close.finishClose) ∷ []
    actualElapsedWaitEvents : List T.Event
    actualElapsedWaitEvents = map event actualElapsedWaitActions
    abstract
     actualElapsedWait : T.Runs elapsedAcknowledged actualElapsedWaitEvents elapsedFinal
     actualElapsedWait = T.more {a = event (W.shutdownStep Close.finishTraversal)} elapsedTraverse (T.more {a = event (W.shutdownStep Close.finishClose)} elapsedWait (T.stop))

    append : ∀ {start middle current first last} → T.Runs start first middle → T.Runs middle last current → T.Runs start (first ++ last) current
    append T.stop rest = rest
    append (T.more actual path) rest = T.more actual (append path rest)

    interruptBeforeWaitActions : List W.Action
    interruptBeforeWaitActions = Waiting.waitingActions ++ (actualSelectedActions ++ (actualInterruptReceiptActions ++ (actualInterruptPublicationActions ++ (W.shutdownStep Close.finishTraversal ∷ []))))
    elapsedBeforeWaitActions : List W.Action
    elapsedBeforeWaitActions = Waiting.waitingActions ++ (actualSelectedActions ++ (actualExpiryPublicationActions ++ (actualElapsedReceiptActions ++ (W.shutdownStep Close.finishTraversal ∷ []))))
    abstract
     actualInterruptBeforeWait : T.Runs Waiting.start (map event interruptBeforeWaitActions) interruptedBeforeWait
     actualInterruptBeforeWait = append Waiting.actualWaiting (append actualSelected
      (append actualInterruptReceipt (append actualInterruptPublication
       (T.more {a = event (W.shutdownStep Close.finishTraversal)} interruptedTraverse T.stop))))
     actualElapsedBeforeWait : T.Runs Waiting.start (map event elapsedBeforeWaitActions) elapsedBeforeWait
     actualElapsedBeforeWait = append Waiting.actualWaiting (append actualSelected
      (append actualExpiryPublication (append actualElapsedReceipt
       (T.more {a = event (W.shutdownStep Close.finishTraversal)} elapsedTraverse T.stop))))

    -- Primitive consequences at the actual receipt and finally boundaries.
    receiptRetainsTerminating : lookup (ident 0) (Shared.entries (Shared.cm (W.shared interruptedPhysical))) ≡ just term
    receiptRetainsTerminating = refl
    receiptRetainsBinding : Shared.mapCell (Shared.cm (W.shared interruptedPhysical)) ≡ Shared.full EF.table
    receiptRetainsBinding = refl
    interruptedFinallyTerminates : lookup (ident 0) (Shared.entries (Shared.cm (W.shared interruptedCountPhysical))) ≡ just (Shared.terminated nothing)
    interruptedFinallyTerminates = refl
    interruptedFinallyPurges : Shared.mapCell (Shared.cm (W.shared interruptedCountPhysical)) ≡ Shared.full []
    interruptedFinallyPurges = refl
    elapsedFinallyTerminates : lookup (ident 0) (Shared.entries (Shared.cm (W.shared elapsedCountPhysical))) ≡ just (Shared.terminated nothing)
    elapsedFinallyTerminates = refl
    elapsedFinallyPurges : Shared.mapCell (Shared.cm (W.shared elapsedCountPhysical)) ≡ Shared.full []
    elapsedFinallyPurges = refl
    interruptedEffectiveResult : W.resultOf owner interruptedFinalPhysical ≡ just (W.asyncException receiptError)
    interruptedEffectiveResult = refl
    elapsedEffectiveResult : W.resultOf owner elapsedFinalPhysical ≡ just (W.asyncException bodyError)
    elapsedEffectiveResult = refl
    interruptedMember : owner ∈ Close.collected (W.shutdown interruptedFinalPhysical)
    interruptedMember = here refl
    elapsedMember : owner ∈ Close.collected (W.shutdown elapsedFinalPhysical)
    elapsedMember = here refl

    -- Actual refusal controls.

    waitingCannotFinalize : T.advance (event (W.cleanup owner Cleanup.finishTimeWait)) (at (Waiting.waitingPhysical OldCM.selected)) ≡ nothing
    waitingCannotFinalize = refl

    waitingCannotCount : T.advance (event (W.cleanup owner Cleanup.readCleanupCounters)) (at (Waiting.waitingPhysical OldCM.selected)) ≡ nothing
    waitingCannotCount = refl

    waitingCannotFinish : T.advance (event (W.finishCleanup owner)) (at (Waiting.waitingPhysical OldCM.selected)) ≡ nothing
    waitingCannotFinish = refl

    waitingCannotPublish : T.advance (event (W.publishAsyncResult owner)) (at (Waiting.waitingPhysical OldCM.selected)) ≡ nothing
    waitingCannotPublish = refl

    prematureReceipt : T.advance (event (W.deliverShutdownTimeWait receiptError)) (at (Waiting.waitingPhysical OldCM.selected)) ≡ nothing
    prematureReceipt = refl

    rawAckBypass : T.advance (event (W.shutdownStep Close.acknowledgeDelivery)) (at (Waiting.waitingPhysical OldCM.requested)) ≡ nothing
    rawAckBypass = refl

    finishedAckNeedsResult : T.advance (event (W.acknowledgeFinished)) (at (Waiting.waitingPhysical OldCM.requested)) ≡ nothing
    finishedAckNeedsResult = refl

    receiptCannotPublish : T.advance (event (W.publishAsyncResult owner)) (at (interruptedPhysical)) ≡ nothing
    receiptCannotPublish = refl

    receiptCannotCount : T.advance (event (W.cleanup owner Cleanup.readCleanupCounters)) (at (interruptedPhysical)) ≡ nothing
    receiptCannotCount = refl

    expiryCannotPublish : T.advance (event (W.publishAsyncResult owner)) (at (elapsedPhysical)) ≡ nothing
    expiryCannotPublish = refl

    expiryCannotCount : T.advance (event (W.cleanup owner Cleanup.readCleanupCounters)) (at (elapsedPhysical)) ≡ nothing
    expiryCannotCount = refl

    duplicateReceipt : T.advance (event (W.deliverShutdownTimeWait receiptError)) (at (interruptedPhysical)) ≡ nothing
    duplicateReceipt = refl

    duplicateExpiry : T.advance (event (W.cleanup owner Cleanup.timeWaitElapsed)) (at (elapsedPhysical)) ≡ nothing
    duplicateExpiry = refl

    duplicateInterruption : T.advance (event (W.cleanup owner (Cleanup.interruptTimeWait receiptError))) (at (interruptedPhysical)) ≡ nothing
    duplicateInterruption = refl

    duplicateInterruptedFinally : T.advance (event (W.cleanup owner Cleanup.finishTimeWait)) (at (interruptedCountPhysical)) ≡ nothing
    duplicateInterruptedFinally = refl

    duplicateElapsedFinally : T.advance (event (W.cleanup owner Cleanup.finishTimeWait)) (at (elapsedCountPhysical)) ≡ nothing
    duplicateElapsedFinally = refl

    duplicateInterruptedPublication : T.advance (event (W.publishAsyncResult owner)) (at (interruptedPublishedPhysical)) ≡ nothing
    duplicateInterruptedPublication = refl

    duplicateElapsedPublication : T.advance (event (W.publishAsyncResult owner)) (at (elapsedPublishedPhysical)) ≡ nothing
    duplicateElapsedPublication = refl

    duplicateInterruptedWait : T.advance (event (W.shutdownStep Close.finishClose)) (at (interruptedFinalPhysical)) ≡ nothing
    duplicateInterruptedWait = refl

    duplicateElapsedWait : T.advance (event (W.shutdownStep Close.finishClose)) (at (elapsedFinalPhysical)) ≡ nothing
    duplicateElapsedWait = refl

    -- Early traversal is itself enabled after receipt. Its actual successor still
    -- refuses collective waiting until Async publication, even after cleanupDone.
    interruptedEarlyWaitingPhysical = W.setShutdown OldCM.awaiting interruptedCleanedPhysical
    interruptedEarlyTraversal : T.advance (event (W.shutdownStep Close.finishTraversal)) interruptedCleaned ≡ just (at interruptedEarlyWaitingPhysical)
    interruptedEarlyTraversal = up (W.shutdownStep Close.finishTraversal) interruptedCleanedPhysical
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl refl
    interruptedEarlyWaitRefused : T.advance (event (W.shutdownStep Close.finishClose)) (at interruptedEarlyWaitingPhysical) ≡ nothing
    interruptedEarlyWaitRefused = refl

    -- An early expiry-branch CM request is real, but cannot acknowledgeFinished
    -- before physical publication even when cleanup has completed.
    elapsedEarlyRequestedPhysical = W.setShutdown OldCM.requested elapsedCleanedPhysical
    elapsedEarlyRequest : T.advance (event (W.shutdownStep Close.requestCancellation)) elapsedCleaned ≡ just (at elapsedEarlyRequestedPhysical)
    elapsedEarlyRequest = up (W.shutdownStep Close.requestCancellation) elapsedCleanedPhysical
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl refl
    elapsedEarlyAckRefused : T.advance (event W.acknowledgeFinished) (at elapsedEarlyRequestedPhysical) ≡ nothing
    elapsedEarlyAckRefused = refl

    -- Independent cleanup cancellation may be enabled but is not CM receipt.
    rawInterruptedPhysical = state OldCM.requested finalizing (just (G.asyncExit receiptError)) (worldFinalize (Shared.cleanupError receiptError))
    standaloneInterrupt : T.advance (event (W.cleanup owner (Cleanup.interruptTimeWait receiptError))) requested ≡ just (at rawInterruptedPhysical)
    standaloneInterrupt = up (W.cleanup owner (Cleanup.interruptTimeWait receiptError)) (Waiting.waitingPhysical OldCM.requested)
     (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl refl
    standaloneUnacknowledged : Close.phase (W.shutdown rawInterruptedPhysical) ≡ Close.awaitDelivery (ident 0) owner
    standaloneUnacknowledged = refl
    standaloneUncollected : Close.collected (W.shutdown rawInterruptedPhysical) ≡ []
    standaloneUncollected = refl

  open import Data.Bool using (true; false)
  open import Data.List using (List; []; _∷_; _++_; map)
  open import Data.List.Relation.Unary.Any using (here)
  import Data.List.Relation.Unary.All as All
  open import Data.Maybe using (just; nothing)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
  open import ConnectionManagement.Domain using (ident)
  open import ConnectionManagement.Store using (lookup)
  import ConnectionManagement.OutboundMachine as O
  import ConnectionManagement.State as Shared
  import ConnectionManagement.OutboundHandlerSupervision as B
  import ConnectionManagement.HandlerSupervision as H
  import ConnectionManagement.ServerPeers as Model
  import ConnectionManagement.MuxHandlerExit as ExitModel
  import ConnectionManagement.Rules.OutboundAcquire as Acquire
  import ConnectionManagement.Rules.CMShutdown as Close
  import ConnectionManagement.CSP.GovernorLifecycle as L
  import ConnectionManagement.Negative.GovernorPool as Prior
  import ConnectionManagement.Negative.MuxProtocolJobs as Old
  import ConnectionManagement.Negative.MuxResultMonitor as RF
  import ConnectionManagement.Negative.ServerPeers as Parent
  import ConnectionManagement.Properties.ServerPeersMuxEmbedding as Embedding
  import ConnectionManagement.Properties.ServerPeersMonitorJoins as JoinModel
  import ConnectionManagement.Properties.ServerPeersTimeWaitReceipt as TimeWaitModel
  import ConnectionManagement.Properties.ServerPeersFinishedReceipt as FinishedModel
  import ConnectionManagement.Properties.CollectedOutboundOrigin as OriginModel
  import ConnectionManagement.Properties.HandlerBirthBacking as BirthModel
  import ConnectionManagement.Properties.HandlerResourceFacts as ResourceFacts
  import ConnectionManagement.Properties.MuxHandlerExit as WaitModel
  private
    module P = OutboundMuxChecks.ServingPrefix using (actualAfterBirth; actualPrefix; afterBirthEvents; beforeForkEvents; birthEvents; born; call; initialized; prefixEvents; start)
    module Birth = OutboundMuxChecks.BirthPackets using (backing; origin; originalLabel; originalPrefix)
    module Input = OutboundMuxChecks.PhysicalPrefix using (inputCore)
    module A = TerminatingPrefix using (actualPrefix; events)
    module C = ScopeClose using (actualClose; afterCallbackServerRuns; beforeEntryActions; closeEvents; closed; peer26; peerEvents; peerPath; scopeStep1)
    module F = Suffix using (actualElapsedBeforeWait; actualElapsedWait; actualElapsedWaitEvents; actualExpiryPublication; actualExpiryPublicationEvents; actualInterruptBeforeWait; actualInterruptPublication; actualInterruptPublicationEvents; actualInterruptWait; actualInterruptWaitEvents; actualSelected; actualSelectedEvents; branchpoint; elapsedAcknowledged; elapsedBeforeWait; elapsedBeforeWaitActions; elapsedCleaned; elapsedFinal; elapsedPublication; elapsedPublished; elapsedReceipt; elapsedRequest; elapsedRequested; elapsedWait; interruptBeforeWaitActions; interrupted; interruptedBeforeWait; interruptedCleaned; interruptedFinal; interruptedPublication; interruptedPublished; interruptedWait; receipt; receiptError; request; requested)
    module T = Model.Protocols RF.bearerClosed Prior.classify Parent.Protocols.capability using
      (Runtime; Event; Runs; advance; more; stop)
    module W = ExitModel RF.bearerClosed using
      (State; Action; shutdown; resultReady; resultOf; asyncException; publishAsyncResult; shutdownStep)
    module Emb = Embedding.Frontend RF.bearerClosed Prior.classify Parent.Protocols.capability using (event)
    module Joins = JoinModel.Frontend RF.bearerClosed Prior.classify Parent.Protocols.capability using
      (physical; CMEntry; initialized-cm-entry-run; CMResultWait; result-wait; physical-publication; physical-wait)
    module TW = TimeWaitModel RF.bearerClosed Prior.classify using (Receipt; observed-worker; observed-entry)
    module TWFront = TimeWaitModel.Frontend RF.bearerClosed Prior.classify Parent.Protocols.capability using (event)
    module TWFields = TimeWaitModel.Receipt using (worker; entry)
    module Finished = FinishedModel RF.bearerClosed Prior.classify using (observed-worker)
    module FinishedFields = FinishedModel.Receipt using (worker)
    module FinishedFront = FinishedModel.Frontend RF.bearerClosed Prior.classify Parent.Protocols.capability using (event)
    module Origin = OriginModel.Frontend RF.bearerClosed Prior.classify Parent.Protocols.capability using
      (Discovery; TimeWaitDiscovery; FinishedDiscovery; OutboundOrigin; BirthPacket;
       initialize-origin; initialize-timewait; initialize-finished; extend-outbound; extend-packet; execution; shared)
    module Outbound = OriginModel.Frontend.OutboundOrigin using (packet; retained)
    module Packet = OriginModel.Frontend.BirthPacket using (label; prefix)
    module Found = OriginModel.Frontend.Discovery using (captured; backing)
    module TWFound = OriginModel.Frontend.TimeWaitDiscovery using (receipt; discovered)
    module FinishedFound = OriginModel.Frontend.FinishedDiscovery using (receipt; discovered)
    module Back = BirthModel.Frontend RF.bearerClosed Prior.classify Parent.Protocols.capability using
      (Backing; ForkStep; physical-state; follow; follow-operation; capture-of-found)
    module WaitFacts = WaitModel RF.bearerClosed using (Publication; PhysicalWait)
    module ObservedWait = WaitModel.PhysicalWait using (observed-results)

  append : ∀ {start middle current first last} → T.Runs start first middle → T.Runs middle last current → T.Runs start (first ++ last) current
  append T.stop rest = rest
  append (T.more actual path) rest = T.more actual (append path rest)

  -- Reuse the accepted opaque physical birth instead of reconstructing it.
  -- Both branches copy its exact packet and enabled physical fork command.
  module Retention where
    birthCommand : ∀ {start current events worker captured} → Back.Backing start current events worker captured → B.Action
    birthCommand history = Back.ForkStep.command (BirthModel.Frontend.Backing.operation history)
    record Retained (current : T.Runtime) (events : List T.Event) : Set where
      field
        origin : Origin.OutboundOrigin Input.inputCore L.settings P.start current events Old.owner Old.Prior.captured
        same-packet : Outbound.packet origin ≡ Outbound.packet Birth.origin
        backing : Back.Backing P.start current events Old.owner Old.Prior.captured
        same-command : birthCommand backing ≡ birthCommand Birth.backing
    original : Retained P.born P.birthEvents
    original = record { origin = Birth.origin; same-packet = refl; backing = Birth.backing; same-command = refl }
    abstract
      retain : ∀ {before after events tail} → T.Runs before tail after → Retained before events → Retained after (events ++ tail)
      retain path history = record
        { origin = Origin.extend-outbound path (Retained.origin history)
        ; same-packet = trans (Origin.extend-packet path (Retained.origin history)) (Retained.same-packet history)
        ; backing = Back.follow path (Retained.backing history)
        ; same-command = trans (cong Back.ForkStep.command (Back.follow-operation path (Retained.backing history))) (Retained.same-command history) }
    resources : ∀ {current events} → Retained current events → ResourceFacts.Facts Old.owner Old.Prior.captured (Origin.shared current)
    resources history = Outbound.retained (Retained.origin history)
  open Retention public using (birthCommand; Retained; original; retain; resources)

  toBranchTail : List T.Event
  toBranchTail = P.afterBirthEvents ++ (A.events ++ (C.closeEvents ++ (WaitingPrefix.waitingEvents ++ F.actualSelectedEvents)))
  branchIndex : List T.Event
  branchIndex = P.birthEvents ++ toBranchTail
  requestedEvents : List T.Event
  requestedEvents = Emb.event (W.shutdownStep Close.requestCancellation) ∷ []
  requestedIndex : List T.Event
  requestedIndex = branchIndex ++ requestedEvents
  receiptEvents : List T.Event
  receiptEvents = TWFront.event F.receiptError ∷ []
  receiptIndex : List T.Event
  receiptIndex = requestedIndex ++ receiptEvents
  interruptPublicationIndex : List T.Event
  interruptPublicationIndex = receiptIndex ++ F.actualInterruptPublicationEvents
  interruptFinalIndex : List T.Event
  interruptFinalIndex = interruptPublicationIndex ++ F.actualInterruptWaitEvents
  elapsedPublicationIndex : List T.Event
  elapsedPublicationIndex = branchIndex ++ F.actualExpiryPublicationEvents
  elapsedRequestedIndex : List T.Event
  elapsedRequestedIndex = elapsedPublicationIndex ++ requestedEvents
  finishedEvents : List T.Event
  finishedEvents = FinishedFront.event ∷ []
  elapsedReceiptIndex : List T.Event
  elapsedReceiptIndex = elapsedRequestedIndex ++ finishedEvents
  elapsedFinalIndex : List T.Event
  elapsedFinalIndex = elapsedReceiptIndex ++ F.actualElapsedWaitEvents

  -- Reuse the checked closing-state equality at each composition boundary.
  -- No guarded transition is reconstructed by normalizing the whole runtime.
  module Glue where
    abstract
      waitingFromScope : T.Runs C.closed WaitingPrefix.waitingEvents WaitingPrefix.waiting
      waitingFromScope = subst (λ start → T.Runs start WaitingPrefix.waitingEvents WaitingPrefix.waiting)
        (sym WaitingPrefix.closedMatches) WaitingPrefix.actualWaiting
      interruptFromScope : T.Runs C.closed (map Emb.event F.interruptBeforeWaitActions) F.interruptedBeforeWait
      interruptFromScope = subst (λ start → T.Runs start (map Emb.event F.interruptBeforeWaitActions) F.interruptedBeforeWait)
        (sym WaitingPrefix.closedMatches) F.actualInterruptBeforeWait
      elapsedFromScope : T.Runs C.closed (map Emb.event F.elapsedBeforeWaitActions) F.elapsedBeforeWait
      elapsedFromScope = subst (λ start → T.Runs start (map Emb.event F.elapsedBeforeWaitActions) F.elapsedBeforeWait)
        (sym WaitingPrefix.closedMatches) F.actualElapsedBeforeWait

  module Histories where
    abstract
      birthToBranch : T.Runs P.born toBranchTail F.branchpoint
      birthToBranch = append P.actualAfterBirth (append A.actualPrefix (append C.actualClose (append Glue.waitingFromScope F.actualSelected)))
      branch : Retained F.branchpoint branchIndex
      branch = retain birthToBranch original
      initializedBranch : T.Runs P.start branchIndex F.branchpoint
      initializedBranch = Origin.execution (Retained.origin branch)
      beforeReceipt : Retained F.requested requestedIndex
      beforeReceipt = retain (T.more {a = Emb.event (W.shutdownStep Close.requestCancellation)} F.request T.stop) branch
      atReceipt : Retained F.interrupted receiptIndex
      atReceipt = retain (T.more {a = TWFront.event F.receiptError} F.receipt T.stop) beforeReceipt
      interruptPublication : Retained F.interruptedPublished interruptPublicationIndex
      interruptPublication = retain F.actualInterruptPublication atReceipt
      interruptFinal : Retained F.interruptedFinal interruptFinalIndex
      interruptFinal = retain F.actualInterruptWait interruptPublication
      elapsedPublication : Retained F.elapsedPublished elapsedPublicationIndex
      elapsedPublication = retain F.actualExpiryPublication branch
      elapsedRequested : Retained F.elapsedRequested elapsedRequestedIndex
      elapsedRequested = retain (T.more {a = Emb.event (W.shutdownStep Close.requestCancellation)} F.elapsedRequest T.stop) elapsedPublication
      elapsedReceipt : Retained F.elapsedAcknowledged elapsedReceiptIndex
      elapsedReceipt = retain (T.more {a = FinishedFront.event} F.elapsedReceipt T.stop) elapsedRequested
      elapsedFinal : Retained F.elapsedFinal elapsedFinalIndex
      elapsedFinal = retain F.actualElapsedWait elapsedReceipt
  open Histories public using (birthToBranch; branch; initializedBranch; beforeReceipt; atReceipt; interruptPublication; interruptFinal; elapsedPublication; elapsedRequested; elapsedReceipt; elapsedFinal)

  abstract
    -- The closed constructors derive both receipt identity and membership.
    interruption : Origin.TimeWaitDiscovery Input.inputCore L.settings P.start F.requested F.interrupted requestedIndex F.receiptError
    interruption = Origin.initialize-timewait P.initialized (Origin.execution (Retained.origin beforeReceipt)) F.receipt
    receiptWorker : TWFields.worker (TWFound.receipt interruption) ≡ Old.owner
    receiptWorker = TW.observed-worker (TWFound.receipt interruption) refl
    receiptEntry : TWFields.entry (TWFound.receipt interruption) ≡ ident 0
    receiptEntry = TW.observed-entry (TWFound.receipt interruption) refl
    discoveredInterruption : Origin.Discovery Input.inputCore L.settings P.start F.interrupted receiptIndex Old.owner
    discoveredInterruption = subst (Origin.Discovery Input.inputCore L.settings P.start F.interrupted receiptIndex)
      receiptWorker (TWFound.discovered interruption)
    finished : Origin.FinishedDiscovery Input.inputCore L.settings P.start F.elapsedRequested F.elapsedAcknowledged elapsedRequestedIndex
    finished = Origin.initialize-finished P.initialized (Origin.execution (Retained.origin elapsedRequested)) F.elapsedReceipt
    discoveredExpiry : Origin.Discovery Input.inputCore L.settings P.start F.elapsedAcknowledged elapsedReceiptIndex Old.owner
    discoveredExpiry = subst (Origin.Discovery Input.inputCore L.settings P.start F.elapsedAcknowledged elapsedReceiptIndex)
      (Finished.observed-worker (FinishedFound.receipt finished) refl) (FinishedFound.discovered finished)
    discoveredInterruptFinal : Origin.Discovery Input.inputCore L.settings P.start F.interruptedFinal interruptFinalIndex Old.owner
    discoveredInterruptFinal = Origin.initialize-origin P.initialized (Origin.execution (Retained.origin interruptFinal)) (here refl)
    discoveredElapsedFinal : Origin.Discovery Input.inputCore L.settings P.start F.elapsedFinal elapsedFinalIndex Old.owner
    discoveredElapsedFinal = Origin.initialize-origin P.initialized (Origin.execution (Retained.origin elapsedFinal)) (here refl)

  -- Raw registry phases are historical beneath the effective mux exit frame.
  capturedAfterInterrupt : lookup Old.owner (B.threads (Back.physical-state F.interruptedFinal)) ≡ just (H.handlerThread Old.Prior.captured H.handshaking)
  capturedAfterInterrupt = refl
  capturedAfterExpiry : lookup Old.owner (B.threads (Back.physical-state F.elapsedFinal)) ≡ just (H.handlerThread Old.Prior.captured H.handshaking)
  capturedAfterExpiry = refl
  descriptorInterrupt : Found.captured discoveredInterruptFinal ≡ Old.Prior.captured
  descriptorInterrupt = sym (Back.capture-of-found (Found.backing discoveredInterruptFinal) capturedAfterInterrupt)
  descriptorExpiry : Found.captured discoveredElapsedFinal ≡ Old.Prior.captured
  descriptorExpiry = sym (Back.capture-of-found (Found.backing discoveredElapsedFinal) capturedAfterExpiry)
  resourcesInterrupt : ResourceFacts.Facts Old.owner Old.Prior.captured (Origin.shared F.interruptedFinal)
  resourcesInterrupt = resources interruptFinal
  resourcesExpiry : ResourceFacts.Facts Old.owner Old.Prior.captured (Origin.shared F.elapsedFinal)
  resourcesExpiry = resources elapsedFinal
  sameBirthLabelInterrupt : Packet.label (Outbound.packet (Retained.origin interruptFinal)) ≡ P.call Acquire.forkOK
  sameBirthLabelInterrupt = trans (cong Packet.label (Retained.same-packet interruptFinal)) Birth.originalLabel
  sameBirthLabelExpiry : Packet.label (Outbound.packet (Retained.origin elapsedFinal)) ≡ P.call Acquire.forkOK
  sameBirthLabelExpiry = trans (cong Packet.label (Retained.same-packet elapsedFinal)) Birth.originalLabel
  sameBirthPrefixInterrupt : Packet.prefix (Outbound.packet (Retained.origin interruptFinal)) ≡ P.beforeForkEvents
  sameBirthPrefixInterrupt = trans (cong Packet.prefix (Retained.same-packet interruptFinal)) Birth.originalPrefix
  sameBirthPrefixExpiry : Packet.prefix (Outbound.packet (Retained.origin elapsedFinal)) ≡ P.beforeForkEvents
  sameBirthPrefixExpiry = trans (cong Packet.prefix (Retained.same-packet elapsedFinal)) Birth.originalPrefix

  interruptPhysicalPublication : WaitFacts.Publication Old.owner (Joins.physical F.interruptedCleaned) (Joins.physical F.interruptedPublished)
  interruptPhysicalPublication = Joins.physical-publication Old.owner F.interruptedCleaned F.interruptedPublication
  elapsedPhysicalPublication : WaitFacts.Publication Old.owner (Joins.physical F.elapsedCleaned) (Joins.physical F.elapsedPublished)
  elapsedPhysicalPublication = Joins.physical-publication Old.owner F.elapsedCleaned F.elapsedPublication
  interruptPhysicalWait : WaitFacts.PhysicalWait (Joins.physical F.interruptedBeforeWait) (Joins.physical F.interruptedFinal)
  interruptPhysicalWait = Joins.physical-wait F.interruptedBeforeWait F.interruptedWait
  elapsedPhysicalWait : WaitFacts.PhysicalWait (Joins.physical F.elapsedBeforeWait) (Joins.physical F.elapsedFinal)
  elapsedPhysicalWait = Joins.physical-wait F.elapsedBeforeWait F.elapsedWait
  interruptResultOracle : W.resultReady Old.owner (Joins.physical F.interruptedBeforeWait) ≡ true
  interruptResultOracle = All.lookup (ObservedWait.observed-results interruptPhysicalWait) (here refl)
  elapsedResultOracle : W.resultReady Old.owner (Joins.physical F.elapsedBeforeWait) ≡ true
  elapsedResultOracle = All.lookup (ObservedWait.observed-results elapsedPhysicalWait) (here refl)

  -- Scope certificates use actual returnAction/beginCM and the same later
  -- handler events. There is no invented CM entry or supplied result oracle.
  callbackEvents : List T.Event
  callbackEvents = P.prefixEvents ++ (A.events ++ C.peerEvents)
  abstract
    initializedCallbackPrefix : T.Runs P.start callbackEvents C.peer26
    initializedCallbackPrefix = append P.actualPrefix (append A.actualPrefix C.peerPath)
    cmEntry : Joins.CMEntry P.start C.closed
    cmEntry = Joins.initialized-cm-entry-run {actions = C.beforeEntryActions}
      P.initialized initializedCallbackPrefix C.scopeStep1 C.afterCallbackServerRuns
    interruptedCMWait : Joins.CMResultWait P.start F.interruptedBeforeWait F.interruptedFinal
    interruptedCMWait = Joins.result-wait {start = P.start} {entry = C.closed}
      {before = F.interruptedBeforeWait} {after = F.interruptedFinal} cmEntry
      (OutboundMuxChecks.handlerRuns {start = C.closed} {current = F.interruptedBeforeWait}
        F.interruptBeforeWaitActions Glue.interruptFromScope) F.interruptedWait
    elapsedCMWait : Joins.CMResultWait P.start F.elapsedBeforeWait F.elapsedFinal
    elapsedCMWait = Joins.result-wait {start = P.start} {entry = C.closed}
      {before = F.elapsedBeforeWait} {after = F.elapsedFinal} cmEntry
      (OutboundMuxChecks.handlerRuns {start = C.closed} {current = F.elapsedBeforeWait}
        F.elapsedBeforeWaitActions Glue.elapsedFromScope) F.elapsedWait

-- Source release caller receipt and return retain the initialized outbound birth.
module ReleaseMuxChecks where
  open import Data.Bool using (true; false)
  open import Data.List using (List; []; _∷_; _++_; map)
  open import Data.Maybe using (just; nothing)
  open import Data.Product using (_,_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
  open import ConnectionManagement.Domain using (ident)
  open import ConnectionManagement.Store using (lookup)
  import ConnectionManagement.State as Shared
  import ConnectionManagement.OutboundMachine as O
  import ConnectionManagement.Rules.OutboundRelease as Release
  import ConnectionManagement.Rules.Cleanup as Cleanup
  import ConnectionManagement.Rules.CMShutdown as Close
  import ConnectionManagement.Rules.MuxJobTypes as Types
  import ConnectionManagement.MuxProtocolJobs as P
  import ConnectionManagement.MuxHandlerExit as Exit
  import ConnectionManagement.ServerPeers as Combined
  import ConnectionManagement.Negative.MuxProtocolJobs as Old
  import ConnectionManagement.Negative.MuxGroupShutdown as GF
  import ConnectionManagement.Negative.MuxHandlerExit as EF
  import ConnectionManagement.Negative.MuxResultMonitor as RF
  import ConnectionManagement.Negative.GovernorPool as Prior
  import ConnectionManagement.Negative.ServerPeers as PriorServer

  module W = Exit RF.bearerClosed using
   (State; Action; step; source; setSource; shared; shutdown; resultReady; resultOf;
    run; shutdownStep; acknowledgeFinished; deliverReleaseMux; acknowledgeReleaseFinished;
    releaseTarget; beginExit; observeBufferReturn; enterFinalizer; cleanup; finishCleanup; publishAsyncResult)
  private
   module K = Combined RF.bearerClosed Prior.classify using (coreStep; context; releaseCallerAllowed)
   module T = Combined.Protocols RF.bearerClosed Prior.classify PriorServer.Protocols.capability using
    (Runtime; Event; Runs; advance; more; stop; dispatch; base)

  owner = Old.owner
  caller = Old.Fixture.caller
  err = Old.err
  term = Shared.terminating (Shared.handlerKey Old.Prior.captured) owner nothing
  result = Release.success (just term)
  continuation = Release.complete result
  at = TimeWaitChecks.WaitingPrefix.at
  event = TimeWaitChecks.WaitingPrefix.event
  import ConnectionManagement.Properties.ServerPeersMuxEmbedding as Embedding
  import ConnectionManagement.ServerAdmission as AdmissionModel
  private
   module Emb = Embedding.Frontend RF.bearerClosed Prior.classify PriorServer.Protocols.capability
    using (Allowed; nextFront)
   module Admission = AdmissionModel RF.bearerClosed using (closingCM)

  -- The result is stated directly in this module's T.advance/at/event vocabulary.
  -- Fixed context/front/stage/exit are exactly those used by the original Waiting.up.
  abstract
   up : ∀ (action : W.Action) (before : W.State) {after : W.State} →
    Emb.Allowed action before after
     TimeWaitChecks.ScopeClose.closedContext
     TimeWaitChecks.TerminatingPrefix.preparedFront
     Admission.closingCM false TimeWaitChecks.ScopeClose.publishedExit →
    Emb.nextFront action TimeWaitChecks.TerminatingPrefix.preparedFront ≡
     TimeWaitChecks.TerminatingPrefix.preparedFront →
    W.step action before ≡ just after →
    T.advance (event action) (at before) ≡ just (at after)
   up action before {after} permitted copied actual =
    TimeWaitChecks.WaitingPrefix.up action before {after = after} permitted copied actual

   endpoint-up : ∀ (action : W.Action) (before : W.State) {after : W.State}
    (beforeRuntime afterRuntime : T.Runtime) →
    beforeRuntime ≡ at before → afterRuntime ≡ at after →
    Emb.Allowed action before after
     TimeWaitChecks.ScopeClose.closedContext
     TimeWaitChecks.TerminatingPrefix.preparedFront
     Admission.closingCM false TimeWaitChecks.ScopeClose.publishedExit →
    Emb.nextFront action TimeWaitChecks.TerminatingPrefix.preparedFront ≡
     TimeWaitChecks.TerminatingPrefix.preparedFront →
    W.step action before ≡ just after →
    T.advance (event action) beforeRuntime ≡ just afterRuntime
   endpoint-up action before {after} .(at before) .(at after)
    refl refl permitted copied actual =
    up action before {after = after} permitted copied actual

  abstract
   trace-edge : ∀ (event : T.Event)
    (stepBefore stepAfter traceBefore traceAfter : T.Runtime) {end : T.Runtime} {events} →
    traceBefore ≡ stepBefore → traceAfter ≡ stepAfter →
    T.advance event stepBefore ≡ just stepAfter →
    T.Runs traceAfter events end →
    T.Runs traceBefore (event ∷ events) end
   trace-edge event stepBefore stepAfter .stepBefore .stepAfter
    refl refl actual path = T.more {a = event} actual path

  coreEvent : O.Action → T.Event
  coreEvent action = T.dispatch (K.coreStep action)
  call : Release.Action → T.Event
  call action = coreEvent (O.release caller action)

  -- Expected snapshots change only source-call bookkeeping. Every use below has
  -- its own real guarded step equation; no general commuting lemma is assumed.
  reframe : Release.PC → W.State → W.State
  reframe pc physical = W.setSource (record source
   { releasing = (caller , Release.frame (Shared.handlerKey Old.Prior.captured) pc true) ∷ [] }) physical
   where source = W.source physical
  returned : W.State → W.State
  returned physical = W.setSource (record source
   { releasing = []; released = (caller , result) ∷ [] }) physical
   where source = W.source physical

  append : ∀ {start middle current first last} → T.Runs start first middle → T.Runs middle last current → T.Runs start (first ++ last) current
  append T.stop rest = rest
  append (T.more actual path) rest = T.more actual (append path rest)

  module Live where
   startPhysical = TimeWaitChecks.WaitingPrefix.startPhysical
   start = TimeWaitChecks.WaitingPrefix.start
   requestedPhysical = reframe (Release.delivering owner continuation) TimeWaitChecks.WaitingPrefix.startPhysical
   receiptPhysical = reframe continuation (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup1))
   returnedPhysical = returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup1))
   requested = at requestedPhysical
   received = at receiptPhysical
   returnedState = at returnedPhysical
   closedMatches : TimeWaitChecks.ScopeClose.closed ≡ start
   closedMatches = TimeWaitChecks.WaitingPrefix.closedMatches
   request : T.advance (call Release.requestCancellation) start ≡ just requested
   request = refl
   receipt : T.advance (event (W.deliverReleaseMux caller err)) requested ≡ just received
   receipt = endpoint-up (W.deliverReleaseMux caller err) requestedPhysical
    {after = receiptPhysical} requested received refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl refl
   returnCall : T.advance (call Release.returnResult) received ≡ just returnedState
   returnCall = refl

   group2Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []))) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup1))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup2)))
   group2Physical = refl
   group2 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ [])))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup1)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup2))))
   group2 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []))) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup1))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup2)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup1)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup2)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group2Physical

   group3Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup2))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup3)))
   group3Physical = refl
   group3 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup2)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup3))))
   group3 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup2))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup3)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup2)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup3)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group3Physical

   group4Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁₀)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup3))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup4)))
   group4Physical = refl
   group4 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁₀))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup3)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup4))))
   group4 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁₀)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup3))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup4)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup3)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup4)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group4Physical

   group5Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterProtocol Old.j₁₀)))) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup4))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup5)))
   group5Physical = refl
   group5 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterProtocol Old.j₁₀))))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup4)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup5))))
   group5 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterProtocol Old.j₁₀)))) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup4))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup5)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup4)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup5)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group5Physical

   group6Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncProtocolResult Old.j₁₀)))) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup5))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup6)))
   group6Physical = refl
   group6 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncProtocolResult Old.j₁₀))))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup5)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup6))))
   group6 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncProtocolResult Old.j₁₀)))) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup5))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup6)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup5)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup6)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group6Physical

   group7Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup6))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup7)))
   group7Physical = refl
   group7 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup6)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup7))))
   group7 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup6))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup7)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup6)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup7)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group7Physical

   group8Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup7))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup8)))
   group8Physical = refl
   group8 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup7)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup8))))
   group8 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup7))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup8)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup7)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup8)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group8Physical

   group9Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup8))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup9)))
   group9Physical = refl
   group9 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup8)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup9))))
   group9 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup8))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup9)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup8)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup9)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group9Physical

   group10Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup9))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup10)))
   group10Physical = refl
   group10 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup9)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup10))))
   group10 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup9))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup10)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup9)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup10)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group10Physical

   group11Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.demuxer)))) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup10))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup11)))
   group11Physical = refl
   group11 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.demuxer))))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup10)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup11))))
   group11 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.demuxer)))) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup10))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup11)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup10)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup11)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group11Physical

   group12Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.demuxer)))) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup11))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup12)))
   group12Physical = refl
   group12 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.demuxer))))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup11)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup12))))
   group12 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.demuxer)))) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup11))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup12)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup11)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup12)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group12Physical

   group13Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup12))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup13)))
   group13Physical = refl
   group13 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup12)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup13))))
   group13 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup12))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup13)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup12)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup13)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group13Physical

   group14Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup13))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup14)))
   group14Physical = refl
   group14 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup13)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup14))))
   group14 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup13))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup14)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup13)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup14)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group14Physical

   group15Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup14))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup15)))
   group15Physical = refl
   group15 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup14)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup15))))
   group15 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup14))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup15)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup14)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup15)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group15Physical

   group16Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup15))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup16)))
   group16Physical = refl
   group16 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup15)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup16))))
   group16 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup15))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup16)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup15)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup16)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group16Physical

   group17Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer)))) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup16))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup17)))
   group17Physical = refl
   group17 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup16)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup17))))
   group17 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer)))) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup16))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup17)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup16)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup17)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group17Physical

   group18Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer)))) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup17))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup18)))
   group18Physical = refl
   group18 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup17)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup18))))
   group18 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer)))) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup17))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup18)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup17)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup18)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group18Physical

   group19Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup18))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup19)))
   group19Physical = refl
   group19 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup18)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup19))))
   group19 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup18))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup19)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup18)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup19)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group19Physical

   group20Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup19))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup20)))
   group20Physical = refl
   group20 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup19)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup20))))
   group20 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup19))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup20)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup19)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup20)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group20Physical

   group21Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup20))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup21)))
   group21Physical = refl
   group21 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup20)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup21))))
   group21 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup20))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup21)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup20)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup21)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group21Physical

   group22Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup21))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup22)))
   group22Physical = refl
   group22 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup21)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup22))))
   group22 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup21))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup22)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup21)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup22)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group22Physical

   group23Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup22))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup23)))
   group23Physical = refl
   group23 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup22)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup23))))
   group23 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup22))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup23)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup22)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup23)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group23Physical

   group24Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup23))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup24)))
   group24Physical = refl
   group24 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup23)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup24))))
   group24 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup23))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup24)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup23)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup24)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group24Physical

   group25Physical : W.step (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup24))) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup25)))
   group25Physical = refl
   group25 : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup24)))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup25))))
   group25 = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner)) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup24))) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup25)))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup24)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup25)))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl group25Physical

   beginExitPhysical : W.step (W.beginExit owner) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async0)) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async1))
   beginExitPhysical = refl
   beginExit : T.advance (event (W.beginExit owner)) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async0))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async1)))
   beginExit = endpoint-up (W.beginExit owner) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async0)) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async1))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async0))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async1))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl beginExitPhysical

   bufferReturnPhysical : W.step (W.observeBufferReturn owner) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async1)) ≡ just (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async2))
   bufferReturnPhysical = refl
   bufferReturn : T.advance (event (W.observeBufferReturn owner)) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async1))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async2)))
   bufferReturn = endpoint-up (W.observeBufferReturn owner) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async1)) {after = (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async2))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async1))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async2))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl bufferReturnPhysical

   enterFinallyPhysical : W.step (W.enterFinalizer owner) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async2)) ≡ just (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world1))
   enterFinallyPhysical = refl
   enterFinally : T.advance (event (W.enterFinalizer owner)) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async2))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world1)))
   enterFinally = endpoint-up (W.enterFinalizer owner) (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async2)) {after = (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world1))}
    (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async2))) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world1))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl enterFinallyPhysical

   takeMapPhysical : W.step (W.cleanup owner Cleanup.takeCleanupMap) (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world1)) ≡ just (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world2))
   takeMapPhysical = refl
   takeMap : T.advance (event (W.cleanup owner Cleanup.takeCleanupMap)) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world1))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world2)))
   takeMap = endpoint-up (W.cleanup owner Cleanup.takeCleanupMap) (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world1)) {after = (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world2))}
    (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world1))) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world2))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl takeMapPhysical

   selectEntryPhysical : W.step (W.cleanup owner Cleanup.selectCleanupEntry) (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world2)) ≡ just (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world3))
   selectEntryPhysical = refl
   selectEntry : T.advance (event (W.cleanup owner Cleanup.selectCleanupEntry)) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world2))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world3)))
   selectEntry = endpoint-up (W.cleanup owner Cleanup.selectCleanupEntry) (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world2)) {after = (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world3))}
    (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world2))) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world3))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl selectEntryPhysical

   closeSocketPhysical : W.step (W.cleanup owner Cleanup.closeHandlerSocket) (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world3)) ≡ just (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world4))
   closeSocketPhysical = refl
   closeSocket : T.advance (event (W.cleanup owner Cleanup.closeHandlerSocket)) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world3))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world4)))
   closeSocket = endpoint-up (W.cleanup owner Cleanup.closeHandlerSocket) (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world3)) {after = (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world4))}
    (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world3))) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world4))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl closeSocketPhysical

   publishMapPhysical : W.step (W.cleanup owner Cleanup.publishCleanupMap) (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world4)) ≡ just (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical Close.initialState))
   publishMapPhysical = refl
   publishMap : T.advance (event (W.cleanup owner Cleanup.publishCleanupMap)) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world4))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical Close.initialState)))
   publishMap = endpoint-up (W.cleanup owner Cleanup.publishCleanupMap) (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world4)) {after = (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical Close.initialState))}
    (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world4))) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical Close.initialState))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl publishMapPhysical

   capturePhysical : W.step (W.shutdownStep Close.captureSnapshot) (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical Close.initialState)) ≡ just (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.captured))
   capturePhysical = refl
   capture : T.advance (event (W.shutdownStep Close.captureSnapshot)) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical Close.initialState))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.captured)))
   capture = endpoint-up (W.shutdownStep Close.captureSnapshot) (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical Close.initialState)) {after = (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.captured))}
    (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical Close.initialState))) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.captured))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl capturePhysical

   readPhysical : W.step (W.shutdownStep Close.readEntry) (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.captured)) ≡ just (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.selected))
   readPhysical = refl
   read : T.advance (event (W.shutdownStep Close.readEntry)) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.captured))) ≡ just (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.selected)))
   read = endpoint-up (W.shutdownStep Close.readEntry) (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.captured)) {after = (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.selected))}
    (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.captured))) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.selected))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl readPhysical

   expiryPhysical : W.step (W.cleanup owner Cleanup.timeWaitElapsed) (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.selected)) ≡ just (returned (TimeWaitChecks.Suffix.elapsedPhysical))
   expiryPhysical = refl
   expiry : T.advance (event (W.cleanup owner Cleanup.timeWaitElapsed)) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.selected))) ≡ just (at (returned (TimeWaitChecks.Suffix.elapsedPhysical)))
   expiry = endpoint-up (W.cleanup owner Cleanup.timeWaitElapsed) (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.selected)) {after = (returned (TimeWaitChecks.Suffix.elapsedPhysical))}
    (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.selected))) (at (returned (TimeWaitChecks.Suffix.elapsedPhysical))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl expiryPhysical

   elapsedFinallyPhysical : W.step (W.cleanup owner Cleanup.finishTimeWait) (returned (TimeWaitChecks.Suffix.elapsedPhysical)) ≡ just (returned (TimeWaitChecks.Suffix.elapsedCountPhysical))
   elapsedFinallyPhysical = refl
   elapsedFinally : T.advance (event (W.cleanup owner Cleanup.finishTimeWait)) (at (returned (TimeWaitChecks.Suffix.elapsedPhysical))) ≡ just (at (returned (TimeWaitChecks.Suffix.elapsedCountPhysical)))
   elapsedFinally = endpoint-up (W.cleanup owner Cleanup.finishTimeWait) (returned (TimeWaitChecks.Suffix.elapsedPhysical)) {after = (returned (TimeWaitChecks.Suffix.elapsedCountPhysical))}
    (at (returned (TimeWaitChecks.Suffix.elapsedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedCountPhysical))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl elapsedFinallyPhysical

   elapsedCountersPhysical : W.step (W.cleanup owner Cleanup.readCleanupCounters) (returned (TimeWaitChecks.Suffix.elapsedCountPhysical)) ≡ just (returned (TimeWaitChecks.Suffix.elapsedDonePhysical))
   elapsedCountersPhysical = refl
   elapsedCounters : T.advance (event (W.cleanup owner Cleanup.readCleanupCounters)) (at (returned (TimeWaitChecks.Suffix.elapsedCountPhysical))) ≡ just (at (returned (TimeWaitChecks.Suffix.elapsedDonePhysical)))
   elapsedCounters = endpoint-up (W.cleanup owner Cleanup.readCleanupCounters) (returned (TimeWaitChecks.Suffix.elapsedCountPhysical)) {after = (returned (TimeWaitChecks.Suffix.elapsedDonePhysical))}
    (at (returned (TimeWaitChecks.Suffix.elapsedCountPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedDonePhysical))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl elapsedCountersPhysical

   elapsedFinishPhysical : W.step (W.finishCleanup owner) (returned (TimeWaitChecks.Suffix.elapsedDonePhysical)) ≡ just (returned (TimeWaitChecks.Suffix.elapsedCleanedPhysical))
   elapsedFinishPhysical = refl
   elapsedFinish : T.advance (event (W.finishCleanup owner)) (at (returned (TimeWaitChecks.Suffix.elapsedDonePhysical))) ≡ just (at (returned (TimeWaitChecks.Suffix.elapsedCleanedPhysical)))
   elapsedFinish = endpoint-up (W.finishCleanup owner) (returned (TimeWaitChecks.Suffix.elapsedDonePhysical)) {after = (returned (TimeWaitChecks.Suffix.elapsedCleanedPhysical))}
    (at (returned (TimeWaitChecks.Suffix.elapsedDonePhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedCleanedPhysical))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl elapsedFinishPhysical

   elapsedPublicationPhysical : W.step (W.publishAsyncResult owner) (returned (TimeWaitChecks.Suffix.elapsedCleanedPhysical)) ≡ just (returned (TimeWaitChecks.Suffix.elapsedPublishedPhysical))
   elapsedPublicationPhysical = refl
   elapsedPublication : T.advance (event (W.publishAsyncResult owner)) (at (returned (TimeWaitChecks.Suffix.elapsedCleanedPhysical))) ≡ just (at (returned (TimeWaitChecks.Suffix.elapsedPublishedPhysical)))
   elapsedPublication = endpoint-up (W.publishAsyncResult owner) (returned (TimeWaitChecks.Suffix.elapsedCleanedPhysical)) {after = (returned (TimeWaitChecks.Suffix.elapsedPublishedPhysical))}
    (at (returned (TimeWaitChecks.Suffix.elapsedCleanedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedPublishedPhysical))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl elapsedPublicationPhysical

   elapsedRequestPhysical : W.step (W.shutdownStep Close.requestCancellation) (returned (TimeWaitChecks.Suffix.elapsedPublishedPhysical)) ≡ just (returned (TimeWaitChecks.Suffix.elapsedRequestedPhysical))
   elapsedRequestPhysical = refl
   elapsedRequest : T.advance (event (W.shutdownStep Close.requestCancellation)) (at (returned (TimeWaitChecks.Suffix.elapsedPublishedPhysical))) ≡ just (at (returned (TimeWaitChecks.Suffix.elapsedRequestedPhysical)))
   elapsedRequest = endpoint-up (W.shutdownStep Close.requestCancellation) (returned (TimeWaitChecks.Suffix.elapsedPublishedPhysical)) {after = (returned (TimeWaitChecks.Suffix.elapsedRequestedPhysical))}
    (at (returned (TimeWaitChecks.Suffix.elapsedPublishedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedRequestedPhysical))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl elapsedRequestPhysical

   elapsedReceiptPhysical : W.step (W.acknowledgeFinished) (returned (TimeWaitChecks.Suffix.elapsedRequestedPhysical)) ≡ just (returned (TimeWaitChecks.Suffix.elapsedAcknowledgedPhysical))
   elapsedReceiptPhysical = refl
   elapsedReceipt : T.advance (event (W.acknowledgeFinished)) (at (returned (TimeWaitChecks.Suffix.elapsedRequestedPhysical))) ≡ just (at (returned (TimeWaitChecks.Suffix.elapsedAcknowledgedPhysical)))
   elapsedReceipt = endpoint-up (W.acknowledgeFinished) (returned (TimeWaitChecks.Suffix.elapsedRequestedPhysical)) {after = (returned (TimeWaitChecks.Suffix.elapsedAcknowledgedPhysical))}
    (at (returned (TimeWaitChecks.Suffix.elapsedRequestedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedAcknowledgedPhysical))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl elapsedReceiptPhysical

   elapsedTraversePhysical : W.step (W.shutdownStep Close.finishTraversal) (returned (TimeWaitChecks.Suffix.elapsedAcknowledgedPhysical)) ≡ just (returned (TimeWaitChecks.Suffix.elapsedBeforeWaitPhysical))
   elapsedTraversePhysical = refl
   elapsedTraverse : T.advance (event (W.shutdownStep Close.finishTraversal)) (at (returned (TimeWaitChecks.Suffix.elapsedAcknowledgedPhysical))) ≡ just (at (returned (TimeWaitChecks.Suffix.elapsedBeforeWaitPhysical)))
   elapsedTraverse = endpoint-up (W.shutdownStep Close.finishTraversal) (returned (TimeWaitChecks.Suffix.elapsedAcknowledgedPhysical)) {after = (returned (TimeWaitChecks.Suffix.elapsedBeforeWaitPhysical))}
    (at (returned (TimeWaitChecks.Suffix.elapsedAcknowledgedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedBeforeWaitPhysical))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl elapsedTraversePhysical

   elapsedWaitPhysical : W.step (W.shutdownStep Close.finishClose) (returned (TimeWaitChecks.Suffix.elapsedBeforeWaitPhysical)) ≡ just (returned (TimeWaitChecks.Suffix.elapsedFinalPhysical))
   elapsedWaitPhysical = refl
   elapsedWait : T.advance (event (W.shutdownStep Close.finishClose)) (at (returned (TimeWaitChecks.Suffix.elapsedBeforeWaitPhysical))) ≡ just (at (returned (TimeWaitChecks.Suffix.elapsedFinalPhysical)))
   elapsedWait = endpoint-up (W.shutdownStep Close.finishClose) (returned (TimeWaitChecks.Suffix.elapsedBeforeWaitPhysical)) {after = (returned (TimeWaitChecks.Suffix.elapsedFinalPhysical))}
    (at (returned (TimeWaitChecks.Suffix.elapsedBeforeWaitPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedFinalPhysical))) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl elapsedWaitPhysical

   finalPhysical = returned TimeWaitChecks.Suffix.elapsedFinalPhysical
   final = at finalPhysical
   beforeWait = at (returned TimeWaitChecks.Suffix.elapsedBeforeWaitPhysical)
   beforePublication = at (returned TimeWaitChecks.Suffix.elapsedCleanedPhysical)
   published = at (returned TimeWaitChecks.Suffix.elapsedPublishedPhysical)
   requestEvents : List T.Event
   requestEvents = call Release.requestCancellation ∷ []
   receiptEvents : List T.Event
   receiptEvents = event (W.deliverReleaseMux caller err) ∷ []
   returnEvents : List T.Event
   returnEvents = call Release.returnResult ∷ []
   tailBeforeWaitActions : List W.Action
   tailBeforeWaitActions = TimeWaitChecks.WaitingPrefix.abortTailActions ++ (TimeWaitChecks.WaitingPrefix.bodyActions ++
    (W.shutdownStep Close.captureSnapshot ∷ W.shutdownStep Close.readEntry ∷
     W.cleanup owner Cleanup.timeWaitElapsed ∷ W.cleanup owner Cleanup.finishTimeWait ∷
     W.cleanup owner Cleanup.readCleanupCounters ∷ W.finishCleanup owner ∷ W.publishAsyncResult owner ∷
     W.shutdownStep Close.requestCancellation ∷ W.acknowledgeFinished ∷
     W.shutdownStep Close.finishTraversal ∷ []))
   tailBeforeWaitEvents : List T.Event
   tailBeforeWaitEvents = map event tailBeforeWaitActions
   tailActions : List W.Action
   tailActions = tailBeforeWaitActions ++ (W.shutdownStep Close.finishClose ∷ [])
   tailEvents : List T.Event
   tailEvents = tailBeforeWaitEvents ++ (event (W.shutdownStep Close.finishClose) ∷ [])
   beforeWaitEvents : List T.Event
   beforeWaitEvents = requestEvents ++ (receiptEvents ++ (returnEvents ++ tailBeforeWaitEvents))
   events = requestEvents ++ (receiptEvents ++ (returnEvents ++ tailEvents))
   abstract
    actualRequest : T.Runs start requestEvents requested
    actualRequest = trace-edge (call Release.requestCancellation) start requested start requested {end = requested} {events = []} refl refl request (T.stop)
    actualReceipt : T.Runs requested receiptEvents received
    actualReceipt = trace-edge (event (W.deliverReleaseMux caller err)) requested received requested received {end = received} {events = []} refl refl receipt (T.stop)
    actualReturn : T.Runs received returnEvents returnedState
    actualReturn = trace-edge (call Release.returnResult) received returnedState received returnedState {end = returnedState} {events = []} refl refl returnCall (T.stop)
    actualTailBeforeWait : T.Runs returnedState tailBeforeWaitEvents beforeWait
    actualTailBeforeWait = trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ [])))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup1)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup2)))) returnedState (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup2)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁₀))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterProtocol Old.j₁₀))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncProtocolResult Old.j₁₀))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group2 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup2)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup3)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup2)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup3)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁₀))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterProtocol Old.j₁₀))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncProtocolResult Old.j₁₀))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group3 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁₀))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup3)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup4)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup3)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup4)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterProtocol Old.j₁₀))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncProtocolResult Old.j₁₀))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group4 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterProtocol Old.j₁₀))))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup4)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup5)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup4)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup5)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncProtocolResult Old.j₁₀))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group5 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncProtocolResult Old.j₁₀))))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup5)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup6)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup5)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup6)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group6 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup6)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup7)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup6)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup7)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group7 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup7)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup8)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup7)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup8)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group8 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup8)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup9)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup8)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup9)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group9 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₁))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup9)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup10)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup9)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup10)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group10 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.demuxer))))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup10)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup11)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup10)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup11)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.demuxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group11 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.demuxer))))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup11)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup12)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup11)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup12)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group12 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup12)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup13)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup12)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup13)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group13 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.requestWholeCancel owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup13)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup14)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup13)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup14)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group14 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.deliverWhole owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup14)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup15)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup14)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup15)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group15 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishChildUnwind Old.j₀))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup15)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup16)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup15)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup16)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group16 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.deregisterInfra owner Types.muxer))))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup16)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup17)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup16)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup17)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group17 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.run (TimeWaitChecks.WaitingPrefix.M.run (P.asyncInfraResult owner Types.muxer))))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup17)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup18)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup17)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup18)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group18 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.joinWhole owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup18)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup19)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup18)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup19)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group19 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishWholeClose owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup19)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup20)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup19)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup20)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group20 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.writeAsyncFailure owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup20)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup21)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup20)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup21)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group21 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.beginAsyncDead owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup21)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup22)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup21)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup22)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group22 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.sampleAsyncTracer owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup22)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup23)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup22)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup23)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) ∷ (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group23 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.commitAsyncTracer owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup23)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup24)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup23)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup24)))) {end = beforeWait} {events = (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) ∷ (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group24 (trace-edge (event (W.run (TimeWaitChecks.WaitingPrefix.G.finishAsyncDead owner))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup24)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup25)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup24)))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async0))) {end = beforeWait} {events = (event (W.beginExit owner)) ∷ (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl group25 (trace-edge (event (W.beginExit owner)) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async0))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async1))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async0))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async1))) {end = beforeWait} {events = (event (W.observeBufferReturn owner)) ∷ (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl beginExit (trace-edge (event (W.observeBufferReturn owner)) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async1))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async2))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async1))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async2))) {end = beforeWait} {events = (event (W.enterFinalizer owner)) ∷ (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl bufferReturn (trace-edge (event (W.enterFinalizer owner)) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async2))) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world1))) (at (returned (TimeWaitChecks.WaitingPrefix.hold Close.initialState EF.async2))) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world1))) {end = beforeWait} {events = (event (W.cleanup owner Cleanup.takeCleanupMap)) ∷ (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl enterFinally (trace-edge (event (W.cleanup owner Cleanup.takeCleanupMap)) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world1))) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world2))) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world1))) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world2))) {end = beforeWait} {events = (event (W.cleanup owner Cleanup.selectCleanupEntry)) ∷ (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl takeMap (trace-edge (event (W.cleanup owner Cleanup.selectCleanupEntry)) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world2))) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world3))) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world2))) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world3))) {end = beforeWait} {events = (event (W.cleanup owner Cleanup.closeHandlerSocket)) ∷ (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl selectEntry (trace-edge (event (W.cleanup owner Cleanup.closeHandlerSocket)) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world3))) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world4))) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world3))) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world4))) {end = beforeWait} {events = (event (W.cleanup owner Cleanup.publishCleanupMap)) ∷ (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl closeSocket (trace-edge (event (W.cleanup owner Cleanup.publishCleanupMap)) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world4))) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical Close.initialState))) (at (returned (TimeWaitChecks.WaitingPrefix.finalizer Close.initialState TimeWaitChecks.WaitingPrefix.world4))) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical Close.initialState))) {end = beforeWait} {events = (event (W.shutdownStep Close.captureSnapshot)) ∷ (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl publishMap (trace-edge (event (W.shutdownStep Close.captureSnapshot)) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical Close.initialState))) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.captured))) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical Close.initialState))) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.captured))) {end = beforeWait} {events = (event (W.shutdownStep Close.readEntry)) ∷ (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl capture (trace-edge (event (W.shutdownStep Close.readEntry)) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.captured))) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.selected))) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.captured))) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.selected))) {end = beforeWait} {events = (event (W.cleanup owner Cleanup.timeWaitElapsed)) ∷ (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl read (trace-edge (event (W.cleanup owner Cleanup.timeWaitElapsed)) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.selected))) (at (returned (TimeWaitChecks.Suffix.elapsedPhysical))) (at (returned (TimeWaitChecks.WaitingPrefix.waitingPhysical OutboundMuxChecks.PhysicalSuffix.selected))) (at (returned (TimeWaitChecks.Suffix.elapsedPhysical))) {end = beforeWait} {events = (event (W.cleanup owner Cleanup.finishTimeWait)) ∷ (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl expiry (trace-edge (event (W.cleanup owner Cleanup.finishTimeWait)) (at (returned (TimeWaitChecks.Suffix.elapsedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedCountPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedCountPhysical))) {end = beforeWait} {events = (event (W.cleanup owner Cleanup.readCleanupCounters)) ∷ (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl elapsedFinally (trace-edge (event (W.cleanup owner Cleanup.readCleanupCounters)) (at (returned (TimeWaitChecks.Suffix.elapsedCountPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedDonePhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedCountPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedDonePhysical))) {end = beforeWait} {events = (event (W.finishCleanup owner)) ∷ (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl elapsedCounters (trace-edge (event (W.finishCleanup owner)) (at (returned (TimeWaitChecks.Suffix.elapsedDonePhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedCleanedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedDonePhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedCleanedPhysical))) {end = beforeWait} {events = (event (W.publishAsyncResult owner)) ∷ (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl elapsedFinish (trace-edge (event (W.publishAsyncResult owner)) (at (returned (TimeWaitChecks.Suffix.elapsedCleanedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedPublishedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedCleanedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedPublishedPhysical))) {end = beforeWait} {events = (event (W.shutdownStep Close.requestCancellation)) ∷ (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl elapsedPublication (trace-edge (event (W.shutdownStep Close.requestCancellation)) (at (returned (TimeWaitChecks.Suffix.elapsedPublishedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedRequestedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedPublishedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedRequestedPhysical))) {end = beforeWait} {events = (event (W.acknowledgeFinished)) ∷ (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl elapsedRequest (trace-edge (event (W.acknowledgeFinished)) (at (returned (TimeWaitChecks.Suffix.elapsedRequestedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedAcknowledgedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedRequestedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedAcknowledgedPhysical))) {end = beforeWait} {events = (event (W.shutdownStep Close.finishTraversal)) ∷ []} refl refl elapsedReceipt (trace-edge (event (W.shutdownStep Close.finishTraversal)) (at (returned (TimeWaitChecks.Suffix.elapsedAcknowledgedPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedBeforeWaitPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedAcknowledgedPhysical))) beforeWait {end = beforeWait} {events = []} refl refl elapsedTraverse (T.stop)))))))))))))))))))))))))))))))))))))))))
    actualTail : T.Runs returnedState tailEvents final
    actualTail = append actualTailBeforeWait (trace-edge (event (W.shutdownStep Close.finishClose)) (at (returned (TimeWaitChecks.Suffix.elapsedBeforeWaitPhysical))) (at (returned (TimeWaitChecks.Suffix.elapsedFinalPhysical))) beforeWait final {end = final} {events = []} refl refl elapsedWait (T.stop))
    actualBeforeWait : T.Runs start beforeWaitEvents beforeWait
    actualBeforeWait = append actualRequest (append actualReceipt (append actualReturn actualTailBeforeWait))

    actual : T.Runs start events final
    actual = append actualRequest (append actualReceipt (append actualReturn actualTail))

   -- Receipt completes the source throwTo continuation before physical cleanup.
   receiptHasNoResult : W.resultReady owner receiptPhysical ≡ false
   receiptHasNoResult = refl
   receiptHasNotCollected : Close.collected (W.shutdown receiptPhysical) ≡ []
   receiptHasNotCollected = refl
   returnBeforeResult : W.resultReady owner returnedPhysical ≡ false
   returnBeforeResult = refl
   resultReturned : lookup caller (O.released (W.source returnedPhysical)) ≡ just result
   resultReturned = refl
   finalResultReturned : lookup caller (O.released (W.source finalPhysical)) ≡ just result
   finalResultReturned = refl
   finalLiveEntry : lookup (ident 0) (Shared.entries (Shared.cm (W.shared finalPhysical))) ≡ just (Shared.terminated nothing)
   finalLiveEntry = refl
   prematureReceipt : T.advance (event (W.deliverReleaseMux caller err)) start ≡ nothing
   prematureReceipt = refl
   prematureReturn : T.advance (call Release.returnResult) requested ≡ nothing
   prematureReturn = refl
   duplicateReceipt : T.advance (event (W.deliverReleaseMux caller err)) received ≡ nothing
   duplicateReceipt = refl
   duplicateRequest : T.advance (call Release.requestCancellation) requested ≡ nothing
   duplicateRequest = refl
   duplicateReturn : T.advance (call Release.returnResult) returnedState ≡ nothing
   duplicateReturn = refl
   missingCaller : T.advance (event (W.deliverReleaseMux (ident 999) err)) requested ≡ nothing
   missingCaller = refl
   finishedNeedsResult : T.advance (event (W.acknowledgeReleaseFinished caller)) requested ≡ nothing
   finishedNeedsResult = refl
   rawDeliveryBypass : T.advance (call (Release.cancellationDelivered owner)) requested ≡ nothing
   rawDeliveryBypass = refl
   noPublicationAtReceipt : T.advance (event (W.publishAsyncResult owner)) received ≡ nothing
   noPublicationAtReceipt = refl

   -- An independent owner exception leaves this caller awaiting its own send.
   independentPhysical = reframe (Release.delivering owner continuation) (TimeWaitChecks.WaitingPrefix.hold Close.initialState (TimeWaitChecks.WaitingPrefix.wrap GF.abortGroup1))
   independentAbort : T.advance (event (W.run (TimeWaitChecks.WaitingPrefix.G.abortOwner owner err))) requested ≡ just (at independentPhysical)
   independentAbort = endpoint-up (W.run (TimeWaitChecks.WaitingPrefix.G.abortOwner owner err)) requestedPhysical
    {after = independentPhysical} requested (at independentPhysical) refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl refl
   independentReturnRefused : T.advance (call Release.returnResult) (at independentPhysical) ≡ nothing
   independentReturnRefused = refl
   failedReceipt : T.advance (event (W.deliverReleaseMux caller err)) (at independentPhysical) ≡ nothing
   failedReceipt = refl
   failedReceiptStillPending : lookup caller (O.releasing (W.source independentPhysical)) ≡
    just (Release.frame (Shared.handlerKey Old.Prior.captured) (Release.delivering owner continuation) true)
   failedReceiptStillPending = refl
   wrongTargetPhysical = reframe (Release.delivering (ident 999) continuation) TimeWaitChecks.WaitingPrefix.startPhysical
   wrongTargetRefused : T.advance (event (W.deliverReleaseMux caller err)) (at wrongTargetPhysical) ≡ nothing
   wrongTargetRefused = refl
   targetFromFrame : W.releaseTarget caller requestedPhysical ≡ just owner
   targetFromFrame = refl
   receiptSameCM : W.shutdown receiptPhysical ≡ W.shutdown requestedPhysical
   receiptSameCM = refl

  module Finished where
   start = TimeWaitChecks.Suffix.elapsedFinal
   startPhysical = TimeWaitChecks.Suffix.elapsedFinalPhysical
   requestedPhysical = reframe (Release.delivering owner continuation) startPhysical
   receiptPhysical = reframe continuation startPhysical
   returnedPhysical = returned startPhysical
   requested = at requestedPhysical
   received = at receiptPhysical
   final = at returnedPhysical
   request : T.advance (call Release.requestCancellation) start ≡ just requested
   request = refl
   receipt : T.advance (event (W.acknowledgeReleaseFinished caller)) requested ≡ just received
   receipt = endpoint-up (W.acknowledgeReleaseFinished caller) requestedPhysical
    {after = receiptPhysical} requested received refl refl
    (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl refl
   returnCall : T.advance (call Release.returnResult) received ≡ just final
   returnCall = refl
   requestEvents : List T.Event
   requestEvents = call Release.requestCancellation ∷ []
   receiptEvents : List T.Event
   receiptEvents = event (W.acknowledgeReleaseFinished caller) ∷ []
   returnEvents : List T.Event
   returnEvents = call Release.returnResult ∷ []
   events = requestEvents ++ (receiptEvents ++ returnEvents)
   abstract
    actualRequest : T.Runs start requestEvents requested
    actualRequest = trace-edge (call Release.requestCancellation) start requested start requested {end = requested} {events = []} refl refl request (T.stop)
    actualReceipt : T.Runs requested receiptEvents received
    actualReceipt = trace-edge (event (W.acknowledgeReleaseFinished caller)) requested received requested received {end = received} {events = []} refl refl receipt (T.stop)
    actualReturn : T.Runs received returnEvents final
    actualReturn = trace-edge (call Release.returnResult) received final received final {end = final} {events = []} refl refl returnCall (T.stop)
    actual : T.Runs start events final
    actual = append actualRequest (append actualReceipt actualReturn)
   genuineResult : W.resultReady owner startPhysical ≡ true
   genuineResult = refl
   retainedCMCollection : Close.collected (W.shutdown receiptPhysical) ≡ Close.collected (W.shutdown startPhysical)
   retainedCMCollection = refl
   resultReturned : lookup caller (O.released (W.source returnedPhysical)) ≡ just result
   resultReturned = refl
   prematureReceipt : T.advance (event (W.acknowledgeReleaseFinished caller)) start ≡ nothing
   prematureReceipt = refl
   prematureReturn : T.advance (call Release.returnResult) requested ≡ nothing
   prematureReturn = refl
   duplicateReceipt : T.advance (event (W.acknowledgeReleaseFinished caller)) received ≡ nothing
   duplicateReceipt = refl
   duplicateReturn : T.advance (call Release.returnResult) final ≡ nothing
   duplicateReturn = refl
   missingCaller : T.advance (event (W.acknowledgeReleaseFinished (ident 999))) requested ≡ nothing
   missingCaller = refl
   rawDeliveryBypass : T.advance (call (Release.cancellationDelivered owner)) requested ≡ nothing
   rawDeliveryBypass = refl
   liveDeliveryCannotReplaceFinished : T.advance (event (W.deliverReleaseMux caller err)) requested ≡ nothing
   liveDeliveryCannotReplaceFinished = refl

   wrongTargetPhysical = reframe (Release.delivering (ident 999) continuation) startPhysical
   wrongTargetRefused : T.advance (event (W.acknowledgeReleaseFinished caller)) (at wrongTargetPhysical) ≡ nothing
   wrongTargetRefused = refl
   targetAfterMapPurged : W.releaseTarget caller requestedPhysical ≡ just owner
   targetAfterMapPurged = refl
   receiptSameCM : W.shutdown receiptPhysical ≡ W.shutdown requestedPhysical
   receiptSameCM = refl

  -- Reuse the accepted, opaque packet/backing retention API. The live branch
  -- extends only actual newly enabled edges; the finished branch extends the
  -- accepted final CM wait without attributing its earlier abort to release.

  module Retention where
   open TimeWaitChecks.Retention public using (Retained; retain; resources)
   liveStartTail = OutboundMuxChecks.ServingPrefix.afterBirthEvents ++ (TimeWaitChecks.TerminatingPrefix.events ++ TimeWaitChecks.ScopeClose.closeEvents)
   liveStartIndex = OutboundMuxChecks.ServingPrefix.birthEvents ++ liveStartTail
   liveRequestIndex = liveStartIndex ++ Live.requestEvents
   liveReceiptIndex = liveRequestIndex ++ Live.receiptEvents
   liveReturnIndex = liveReceiptIndex ++ Live.returnEvents
   liveFinalIndex = liveReturnIndex ++ Live.tailEvents
   finishedRequestIndex = TimeWaitChecks.elapsedFinalIndex ++ Finished.requestEvents
   finishedReceiptIndex = finishedRequestIndex ++ Finished.receiptEvents
   finishedFinalIndex = finishedReceiptIndex ++ Finished.returnEvents

  module Histories where
   open Retention
   abstract
    toLiveStart : T.Runs OutboundMuxChecks.ServingPrefix.born Retention.liveStartTail Live.start
    toLiveStart = subst (λ end → T.Runs OutboundMuxChecks.ServingPrefix.born Retention.liveStartTail end)
     Live.closedMatches (append OutboundMuxChecks.ServingPrefix.actualAfterBirth (append TimeWaitChecks.TerminatingPrefix.actualPrefix TimeWaitChecks.ScopeClose.actualClose))
    liveStart : Retained Live.start liveStartIndex
    liveStart = retain toLiveStart TimeWaitChecks.Retention.original
    liveRequested : Retained Live.requested liveRequestIndex
    liveRequested = retain Live.actualRequest liveStart
    liveReceipt : Retained Live.received liveReceiptIndex
    liveReceipt = retain Live.actualReceipt liveRequested
    liveReturned : Retained Live.returnedState liveReturnIndex
    liveReturned = retain Live.actualReturn liveReceipt
    liveFinal : Retained Live.final liveFinalIndex
    liveFinal = retain Live.actualTail liveReturned
    finishedRequested : Retained Finished.requested finishedRequestIndex
    finishedRequested = retain Finished.actualRequest TimeWaitChecks.Histories.elapsedFinal
    finishedReceipt : Retained Finished.received finishedReceiptIndex
    finishedReceipt = retain Finished.actualReceipt finishedRequested
    finishedFinal : Retained Finished.final finishedFinalIndex
    finishedFinal = retain Finished.actualReturn finishedReceipt

  resourcesLiveReceipt = Retention.resources Histories.liveReceipt
  resourcesLiveReturn = Retention.resources Histories.liveReturned
  resourcesLiveFinal = Retention.resources Histories.liveFinal
  resourcesFinishedReceipt = Retention.resources Histories.finishedReceipt
  resourcesFinishedFinal = Retention.resources Histories.finishedFinal

  import ConnectionManagement.Properties.ServerPeersMonitorJoins as JoinModel
  private
   module Joins = JoinModel.Frontend RF.bearerClosed Prior.classify PriorServer.Protocols.capability using
    (CMEntry; physical; FramedRuns; frameRelease; frameNext; frameDone; framed-server; framed-view;
     handler-action; server-framed; FramedCMResultWait; framed-result-wait;
     framed-wait-components; wait-components-after; transport-frame-components)

  -- Keep the core release labels canonical while reusing closed peer scopes.
  -- The inherited physical tail is lifted from its actual existing action labels.
  -- Convert the imported frontend instance at variable runtime endpoints once.
  abstract
   release-frame : ∀ caller action (before after end : T.Runtime) {events} →
    T.advance (T.dispatch (K.coreStep (O.release caller action))) before ≡ just after →
    Joins.FramedRuns after events end →
    Joins.FramedRuns before (T.dispatch (K.coreStep (O.release caller action)) ∷ events) end
   release-frame caller action before after end actual path =
    Joins.frameRelease {s = before} {t = after} {u = end} {caller = caller} {action = action} actual path

   handler-frame : ∀ action (before after end : T.Runtime) {events} →
    T.advance (event action) before ≡ just after →
    Joins.FramedRuns after events end →
    Joins.FramedRuns before (event action ∷ events) end
   handler-frame action before after end actual path =
    Joins.frameNext {s = before} {t = after} {u = end} {event = event action}
     (Joins.server-framed (Joins.handler-action action) before actual) actual path

   local-result-wait : ∀ (start entry before after : T.Runtime) {events} →
    Joins.CMEntry start entry → Joins.FramedRuns entry events before →
    T.advance (event (W.shutdownStep Close.finishClose)) before ≡ just after →
    Joins.FramedCMResultWait start before after
   local-result-wait start entry before after certificate path actual =
    Joins.framed-result-wait {start = start} {entry = entry} {before = before} {after = after}
     certificate path actual

  module ScopeCertificates where
   abstract
    liveFramed : Joins.FramedRuns Live.start Live.beforeWaitEvents Live.beforeWait
    liveFramed = release-frame caller Release.requestCancellation Live.start Live.requested Live.beforeWait Live.request
     (handler-frame (W.deliverReleaseMux caller err) Live.requested Live.received Live.beforeWait Live.receipt
      (release-frame caller Release.returnResult Live.received Live.returnedState Live.beforeWait Live.returnCall
       (Joins.framed-server (OutboundMuxChecks.handlerRuns {start = Live.returnedState} {current = Live.beforeWait} Live.tailBeforeWaitActions Live.actualTailBeforeWait))))
    liveFromCM : Joins.FramedRuns TimeWaitChecks.ScopeClose.closed Live.beforeWaitEvents Live.beforeWait
    liveFromCM = subst (λ start → Joins.FramedRuns start Live.beforeWaitEvents Live.beforeWait)
     (sym Live.closedMatches) liveFramed
    liveCMWait : Joins.FramedCMResultWait OutboundMuxChecks.ServingPrefix.start Live.beforeWait Live.final
    liveCMWait = local-result-wait OutboundMuxChecks.ServingPrefix.start TimeWaitChecks.ScopeClose.closed Live.beforeWait Live.final TimeWaitChecks.cmEntry liveFromCM Live.elapsedWait
    finishedFramed : Joins.FramedRuns Finished.start Finished.events Finished.final
    finishedFramed = release-frame caller Release.requestCancellation Finished.start Finished.requested Finished.final Finished.request
     (handler-frame (W.acknowledgeReleaseFinished caller) Finished.requested Finished.received Finished.final Finished.receipt
      (release-frame caller Release.returnResult Finished.received Finished.final Finished.final Finished.returnCall Joins.frameDone))
   liveComponents = Joins.framed-wait-components liveCMWait
   finishedComponents = Joins.transport-frame-components {s = Finished.start} {t = Finished.final} (Joins.framed-view finishedFramed)
    (Joins.wait-components-after TimeWaitChecks.elapsedCMWait)

  import ConnectionManagement.PeerContext as ContextModel
  import ConnectionManagement.Subsystem as Sub
  import ConnectionManagement.Rules.PeerJobs as Jobs
  private
   module Context = ContextModel Prior.classify using (subsystem; governorPool)

  -- Local permission controls preserve the real release/handler state, but replace
  -- its peer context by an owned unwinding caller. They assert guard behavior,
  -- not reachability of that combined context from the positive witness.
  module CallerPermissionControls where
   blocked : T.Runtime → T.Runtime
   blocked current = record current { base = record shared { context = record saved
    { subsystem = record (Context.subsystem saved)
      { jobs = (ident 999 , Sub.jobFrame
        (Jobs.frame Prior.work caller owner (Shared.handlerSocket Old.Prior.captured) (ident 999) Jobs.awaitRelease)
        false false) ∷ [] }
    ; governorPool = record (Context.governorPool saved)
      { handles = (ident 999 , Prior.Pool.bodyUnwinding) ∷ [] } } } }
    where
    shared = T.base current
    saved = K.context shared
   liveOwnedUnwind : T.advance (event (W.deliverReleaseMux caller err)) (blocked Live.requested) ≡ nothing
   liveOwnedUnwind = refl
   finishedOwnedUnwind : T.advance (event (W.acknowledgeReleaseFinished caller)) (blocked Finished.requested) ≡ nothing
   finishedOwnedUnwind = refl
   coreReturnOwnedUnwind : T.advance (call Release.returnResult) (blocked Live.received) ≡ nothing
   coreReturnOwnedUnwind = refl

  import ConnectionManagement.Properties.ServerPeersReleaseReceipt as ReleaseReceiptModel
  private
   module ReleaseReceipt = ReleaseReceiptModel RF.bearerClosed Prior.classify using
    (LiveReceipt; FinishedReceipt; live-shutdown; finished-shutdown)
   module ReleaseFrontend = ReleaseReceiptModel.Frontend RF.bearerClosed Prior.classify PriorServer.Protocols.capability using
    (physical-live; physical-finished; live-permission; finished-permission)

  abstract
   local-physical-live : ∀ caller err (before after : T.Runtime) →
    T.advance (event (W.deliverReleaseMux caller err)) before ≡ just after →
    ReleaseReceipt.LiveReceipt caller err (Joins.physical before) (Joins.physical after)
   local-physical-live caller err before after actual =
    ReleaseFrontend.physical-live caller err before {after = after} actual

   local-physical-finished : ∀ caller (before after : T.Runtime) →
    T.advance (event (W.acknowledgeReleaseFinished caller)) before ≡ just after →
    ReleaseReceipt.FinishedReceipt caller (Joins.physical before) (Joins.physical after)
   local-physical-finished caller before after actual =
    ReleaseFrontend.physical-finished caller before {after = after} actual

   local-live-permission : ∀ caller err (before after : T.Runtime) →
    T.advance (event (W.deliverReleaseMux caller err)) before ≡ just after →
    K.releaseCallerAllowed caller (T.base before) ≡ true
   local-live-permission caller err before after actual =
    ReleaseFrontend.live-permission caller err before {after = after} actual

   local-finished-permission : ∀ caller (before after : T.Runtime) →
    T.advance (event (W.acknowledgeReleaseFinished caller)) before ≡ just after →
    K.releaseCallerAllowed caller (T.base before) ≡ true
   local-finished-permission caller before after actual =
    ReleaseFrontend.finished-permission caller before {after = after} actual

  -- Invert the actual accepted frontend labels; neither target nor source
  -- acknowledgement evidence is supplied by the caller of these observations.
  module ReceiptObservations where
   abstract
    live : ReleaseReceipt.LiveReceipt caller err (Joins.physical Live.requested) (Joins.physical Live.received)
    live = local-physical-live caller err Live.requested Live.received Live.receipt
    finished : ReleaseReceipt.FinishedReceipt caller (Joins.physical Finished.requested) (Joins.physical Finished.received)
    finished = local-physical-finished caller Finished.requested Finished.received Finished.receipt
    livePermission : K.releaseCallerAllowed caller (T.base Live.requested) ≡ true
    livePermission = local-live-permission caller err Live.requested Live.received Live.receipt
    finishedPermission : K.releaseCallerAllowed caller (T.base Finished.requested) ≡ true
    finishedPermission = local-finished-permission caller Finished.requested Finished.received Finished.receipt
    liveCoordinatorUnchanged : W.shutdown (Joins.physical Live.received) ≡ W.shutdown (Joins.physical Live.requested)
    liveCoordinatorUnchanged = ReleaseReceipt.live-shutdown live
    finishedCoordinatorUnchanged : W.shutdown (Joins.physical Finished.received) ≡ W.shutdown (Joins.physical Finished.requested)
    finishedCoordinatorUnchanged = ReleaseReceipt.finished-shutdown finished
