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
