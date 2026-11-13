{-# OPTIONS --guardedness #-}

-- SI5b: the CM shutdown coordinator at the finished outer scope. Every
-- initialized run of the outer composition that reaches the finished relays
-- state has, besides the SI5a certificate, a closed coordinator with no
-- unread snapshot entries, closed by an actual wrapper wait whose oracle was
-- that wrapper's physical handler-result table. The Server may return only
-- after the coordinator closed, and closed admits no further coordinator step.
-- This is a finite-trace safety certificate; it asserts no eventuality.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerShutdownCoordinator
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import ConnectionManagement.Domain using (HandleId)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.PoolRelays as RR
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.MuxResultMonitor as MonitorModel
import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.MuxDeltaQ as DeltaQModel
import ConnectionManagement.MuxCatchUnwind as CatchModel
import ConnectionManagement.MuxPublicationUnwind as PublicationModel
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerPeersRelays as Relays
import ConnectionManagement.Properties.CMShutdown as CloseProof
import ConnectionManagement.Properties.HandlerSupervision as Handler
import ConnectionManagement.Properties.OutboundHandlerSupervision as Physical
import ConnectionManagement.Properties.CoordinatorFrames as Frames
import ConnectionManagement.Properties.CoordinatorFrontend as Frontend
import ConnectionManagement.Properties.ServerShutdownComplete as SI5aModel
import ConnectionManagement.Properties.ServerStageEntry as Entry
import ConnectionManagement.Properties.PoolRelays as RelaysFacts
private
  module Low = Frames isBearerClosed
  module Up = Frontend isBearerClosed isIOManagerError
  module SI5a = SI5aModel isBearerClosed isIOManagerError
  module Stage = Entry isBearerClosed
  module U = MuxModel Types.TypedResult
  module P = ProtocolModel
  module M = MonitorModel isBearerClosed
  module G = GroupModel isBearerClosed
  module W = ExitModel isBearerClosed
  module R = UnwindModel isBearerClosed
  module D = DeltaQModel isBearerClosed
  module C = CatchModel isBearerClosed
  module N = PublicationModel isBearerClosed
  module S = Server isBearerClosed
  module E = Exit isBearerClosed
  module K = Combined isBearerClosed isIOManagerError
  module SR = Relays isBearerClosed isIOManagerError

-- A scope plan into serverReturned starts there, or is finishServer reading
-- a closed coordinator.
returned-entry : ∀ x s {p} → S.chooseScope x s ≡ just p → S.nextStage p ≡ S.serverReturned →
  S.stage s ≡ S.serverReturned ⊎ x ≡ S.finishServer
returned-entry (S.forkFailure sock err) s chosen with S.accepting (S.stage s) | S.listenerOpen s | lookup sock (Shared.sockets (S.shared s))
... | true | true | nothing = case just-injective chosen of λ { refl → λ () }
... | false | _ | _ = case chosen of λ ()
... | true | false | _ = case chosen of λ ()
... | true | true | just _ = case chosen of λ ()
returned-entry S.finishForkFailure s chosen with S.failedForkSocket s
... | nothing = case chosen of λ ()
... | just sock with lookup sock (Shared.sockets (S.shared s))
...   | just Shared.closed = case just-injective chosen of λ { refl → λ () }
...   | just (Shared.closeUncertain _) = case just-injective chosen of λ { refl → λ () }
...   | nothing = case chosen of λ ()
...   | just Shared.acceptPending = case chosen of λ ()
...   | just (Shared.admitting _) = case chosen of λ ()
...   | just (Shared.handling _) = case chosen of λ ()
returned-entry S.returnAction s chosen with S.stage s
... | S.serving = case just-injective chosen of λ { refl → λ () }
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | (S.acceptForkClosing _ _) = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
returned-entry S.publishActionResult s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case just-injective chosen of λ { refl → λ () }
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | (S.acceptForkClosing _ _) = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
returned-entry S.interruptServer s chosen with S.stage s
... | S.serving = case just-injective chosen of λ { refl → λ () }
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | (S.acceptForkClosing _ _) = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
returned-entry S.selectActionWinner s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case just-injective chosen of λ { refl → λ () }
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | (S.acceptForkClosing _ _) = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
returned-entry S.requestAcceptCancel s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case just-injective chosen of λ { refl → λ () }
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | (S.acceptForkClosing _ _) = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
returned-entry S.deliverAcceptAtWait s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case just-injective chosen of λ { refl → λ () }
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | (S.acceptForkClosing _ _) = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
returned-entry S.closeListener s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case just-injective chosen of λ { refl → λ () }
... | S.acceptFailed = case just-injective chosen of λ { refl → λ () }
... | (S.acceptForkClosing _ _) = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
returned-entry S.publishAcceptResult s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | (S.acceptForkClosing _ _) = case chosen of λ ()
... | S.acceptBodyExited = case just-injective chosen of λ { refl → λ () }
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
returned-entry S.joinAccept s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | (S.acceptForkClosing _ _) = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case just-injective chosen of λ { refl → λ () }
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
returned-entry S.traceStopped s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | (S.acceptForkClosing _ _) = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case just-injective chosen of λ { refl → λ () }
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
returned-entry S.cancelJoinReturnedAction s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | (S.acceptForkClosing _ _) = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case just-injective chosen of λ { refl → λ () }
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
returned-entry S.requestIGCancel s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | (S.acceptForkClosing _ _) = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case just-injective chosen of λ { refl → λ () }
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
returned-entry S.acceptFails s chosen with S.stage s
... | S.serving = case just-injective chosen of λ { refl → λ () }
... | S.actionBodyExited = case just-injective chosen of λ { refl → λ () }
... | S.actionResultAvailable = case just-injective chosen of λ { refl → λ () }
... | S.closingAccept = case just-injective chosen of λ { refl → λ () }
... | S.acceptCancelRequested = case just-injective chosen of λ { refl → λ () }
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | (S.acceptForkClosing _ _) = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
returned-entry S.beginCM s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | (S.acceptForkClosing _ _) = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case just-injective chosen of λ { refl → λ () }
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
returned-entry S.deliverIGBody s chosen with S.stage s in st | S.ig s | Machine.inboundRelease (O.core (S.source s)) | Machine.remoteCall (O.core (S.source s))
... | S.serving | _ | _ | _ = case chosen of λ ()
... | S.actionBodyExited | _ | _ | _ = case chosen of λ ()
... | S.actionResultAvailable | _ | _ | _ = case chosen of λ ()
... | S.closingAccept | _ | _ | _ = case chosen of λ ()
... | S.acceptCancelRequested | _ | _ | _ = case chosen of λ ()
... | S.acceptCancelDelivered | _ | _ | _ = case chosen of λ ()
... | S.acceptFailed | _ | _ | _ = case chosen of λ ()
... | (S.acceptForkClosing _ _) | _ | _ | _ = case chosen of λ ()
... | S.acceptBodyExited | _ | _ | _ = case chosen of λ ()
... | S.acceptResultAvailable | _ | _ | _ = case chosen of λ ()
... | S.acceptJoined | _ | _ | _ = case chosen of λ ()
... | S.serverStopped | _ | _ | _ = case chosen of λ ()
... | S.actionJoined | _ | _ | _ = case chosen of λ ()
... | S.igCancelRequested | S.igLive | nothing | nothing = case just-injective chosen of λ { refl → λ returned →
  case trans (sym st) returned of λ () }
... | S.igCancelRequested | S.igLive | nothing | just _ = case chosen of λ ()
... | S.igCancelRequested | S.igLive | just _ | _ = case chosen of λ ()
... | S.igCancelRequested | S.igCaught | _ | _ = case chosen of λ ()
... | S.igCancelRequested | S.igInactive | _ | _ = case chosen of λ ()
... | S.igCancelRequested | S.igFlushed | _ | _ = case chosen of λ ()
... | S.igCancelRequested | S.igBodyExited | _ | _ = case chosen of λ ()
... | S.igCancelRequested | S.igResultAvailable | _ | _ = case chosen of λ ()
... | S.igJoined | _ | _ | _ = case chosen of λ ()
... | S.closingCM | _ | _ | _ = case chosen of λ ()
... | S.serverReturned | _ | _ | _ = case chosen of λ ()
returned-entry S.joinIG s chosen with S.stage s | S.ig s
... | S.serving | _ = case chosen of λ ()
... | S.actionBodyExited | _ = case chosen of λ ()
... | S.actionResultAvailable | _ = case chosen of λ ()
... | S.closingAccept | _ = case chosen of λ ()
... | S.acceptCancelRequested | _ = case chosen of λ ()
... | S.acceptCancelDelivered | _ = case chosen of λ ()
... | S.acceptFailed | _ = case chosen of λ ()
... | (S.acceptForkClosing _ _) | _ = case chosen of λ ()
... | S.acceptBodyExited | _ = case chosen of λ ()
... | S.acceptResultAvailable | _ = case chosen of λ ()
... | S.acceptJoined | _ = case chosen of λ ()
... | S.serverStopped | _ = case chosen of λ ()
... | S.actionJoined | _ = case chosen of λ ()
... | S.igCancelRequested | S.igLive = case chosen of λ ()
... | S.igCancelRequested | S.igCaught = case chosen of λ ()
... | S.igCancelRequested | S.igInactive = case chosen of λ ()
... | S.igCancelRequested | S.igFlushed = case chosen of λ ()
... | S.igCancelRequested | S.igBodyExited = case chosen of λ ()
... | S.igCancelRequested | S.igResultAvailable = case just-injective chosen of λ { refl → λ () }
... | S.igJoined | _ = case chosen of λ ()
... | S.closingCM | _ = case chosen of λ ()
... | S.serverReturned | _ = case chosen of λ ()
returned-entry S.igWins s chosen with S.stage s | S.ig s
... | S.serving | S.igLive = case chosen of λ ()
... | S.serving | S.igCaught = case chosen of λ ()
... | S.serving | S.igInactive = case chosen of λ ()
... | S.serving | S.igFlushed = case chosen of λ ()
... | S.serving | S.igBodyExited = case chosen of λ ()
... | S.serving | S.igResultAvailable = case just-injective chosen of λ { refl → λ () }
... | S.actionBodyExited | S.igLive = case chosen of λ ()
... | S.actionBodyExited | S.igCaught = case chosen of λ ()
... | S.actionBodyExited | S.igInactive = case chosen of λ ()
... | S.actionBodyExited | S.igFlushed = case chosen of λ ()
... | S.actionBodyExited | S.igBodyExited = case chosen of λ ()
... | S.actionBodyExited | S.igResultAvailable = case just-injective chosen of λ { refl → λ () }
... | S.actionResultAvailable | S.igLive = case chosen of λ ()
... | S.actionResultAvailable | S.igCaught = case chosen of λ ()
... | S.actionResultAvailable | S.igInactive = case chosen of λ ()
... | S.actionResultAvailable | S.igFlushed = case chosen of λ ()
... | S.actionResultAvailable | S.igBodyExited = case chosen of λ ()
... | S.actionResultAvailable | S.igResultAvailable = case just-injective chosen of λ { refl → λ () }
... | S.closingAccept | _ = case chosen of λ ()
... | S.acceptCancelRequested | _ = case chosen of λ ()
... | S.acceptCancelDelivered | _ = case chosen of λ ()
... | S.acceptFailed | _ = case chosen of λ ()
... | (S.acceptForkClosing _ _) | _ = case chosen of λ ()
... | S.acceptBodyExited | _ = case chosen of λ ()
... | S.acceptResultAvailable | _ = case chosen of λ ()
... | S.acceptJoined | _ = case chosen of λ ()
... | S.serverStopped | _ = case chosen of λ ()
... | S.actionJoined | _ = case chosen of λ ()
... | S.igCancelRequested | _ = case chosen of λ ()
... | S.igJoined | _ = case chosen of λ ()
... | S.closingCM | _ = case chosen of λ ()
... | S.serverReturned | _ = case chosen of λ ()
returned-entry S.finishServer s chosen with S.stage s | Close.phase (W.shutdown (R.base (N.raw (S.base s))))
... | S.serving | _ = case chosen of λ ()
... | S.actionBodyExited | _ = case chosen of λ ()
... | S.actionResultAvailable | _ = case chosen of λ ()
... | S.closingAccept | _ = case chosen of λ ()
... | S.acceptCancelRequested | _ = case chosen of λ ()
... | S.acceptCancelDelivered | _ = case chosen of λ ()
... | S.acceptFailed | _ = case chosen of λ ()
... | (S.acceptForkClosing _ _) | _ = case chosen of λ ()
... | S.acceptBodyExited | _ = case chosen of λ ()
... | S.acceptResultAvailable | _ = case chosen of λ ()
... | S.acceptJoined | _ = case chosen of λ ()
... | S.serverStopped | _ = case chosen of λ ()
... | S.actionJoined | _ = case chosen of λ ()
... | S.igCancelRequested | _ = case chosen of λ ()
... | S.igJoined | _ = case chosen of λ ()
... | S.closingCM | Close.initial = case chosen of λ ()
... | S.closingCM | Close.reading = case chosen of λ ()
... | S.closingCM | Close.awaitResults = case chosen of λ ()
... | S.closingCM | Close.closed = case just-injective chosen of λ { refl → λ _ → inj₂ refl }
... | S.closingCM | (Close.sendReady _ _) = case chosen of λ ()
... | S.closingCM | (Close.awaitDelivery _ _) = case chosen of λ ()
... | S.serverReturned | _ = case chosen of λ ()
returned-entry S.deactivateIG s chosen with S.ig s
... | S.igLive = case chosen of λ ()
... | S.igCaught = case just-injective chosen of λ { refl → λ returned → inj₁ returned }
... | S.igInactive = case chosen of λ ()
... | S.igFlushed = case chosen of λ ()
... | S.igBodyExited = case chosen of λ ()
... | S.igResultAvailable = case chosen of λ ()
returned-entry S.flushIG s chosen with S.ig s
... | S.igLive = case chosen of λ ()
... | S.igCaught = case chosen of λ ()
... | S.igInactive = case just-injective chosen of λ { refl → λ returned → inj₁ returned }
... | S.igFlushed = case chosen of λ ()
... | S.igBodyExited = case chosen of λ ()
... | S.igResultAvailable = case chosen of λ ()
returned-entry S.publishIGResult s chosen with S.ig s
... | S.igLive = case chosen of λ ()
... | S.igCaught = case chosen of λ ()
... | S.igInactive = case chosen of λ ()
... | S.igFlushed = case chosen of λ ()
... | S.igBodyExited = case just-injective chosen of λ { refl → λ returned → inj₁ returned }
... | S.igResultAvailable = case chosen of λ ()
returned-entry S.failIGBody s chosen with S.ig s | Machine.inboundRelease (O.core (S.source s)) | Machine.remoteCall (O.core (S.source s))
... | S.igLive | nothing | nothing = case just-injective chosen of λ { refl → λ returned → inj₁ returned }
... | S.igLive | nothing | just _ = case chosen of λ ()
... | S.igLive | just _ | _ = case chosen of λ ()
... | S.igCaught | _ | _ = case chosen of λ ()
... | S.igInactive | _ | _ = case chosen of λ ()
... | S.igFlushed | _ | _ = case chosen of λ ()
... | S.igBodyExited | _ | _ = case chosen of λ ()
... | S.igResultAvailable | _ | _ = case chosen of λ ()
returned-entry S.finishIGBody s chosen with S.ig s | IG.connections (IG.publishedState (Machine.inboundGovernor (O.core (S.source s)))) |
  IG.continuation (Machine.inboundGovernor (O.core (S.source s))) | IG.active (IG.execution (Machine.inboundGovernor (O.core (S.source s))))
... | S.igFlushed | [] | IG.exited | false = case just-injective chosen of λ { refl → λ returned → inj₁ returned }
... | S.igFlushed | [] | IG.exited | true = case chosen of λ ()
... | S.igFlushed | [] | IG.sampleTime | _ = case chosen of λ ()
... | S.igFlushed | [] | IG.exitFlush | _ = case chosen of λ ()
... | S.igFlushed | [] | IG.inCM | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.armInactivity _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.awaitBatch _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.readNext _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.prepareNew _ _ _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.startResponders _ _ _ _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.publishDecision _ _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.stopAfterFailure _ _ _ _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.waitStopped _ _ _ _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.restartResponder _ _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.awaitRemoteIdle _ _ _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.needsCM _ _ _ _) | _ = case chosen of λ ()
... | S.igFlushed | _ ∷ _ | _ | _ = case chosen of λ ()
... | S.igLive | _ | _ | _ = case chosen of λ ()
... | S.igCaught | _ | _ | _ = case chosen of λ ()
... | S.igInactive | _ | _ | _ = case chosen of λ ()
... | S.igBodyExited | _ | _ | _ = case chosen of λ ()
... | S.igResultAvailable | _ | _ | _ = case chosen of λ ()
-- finishServer is chosen only on a closed coordinator.
finish-closed : ∀ s {p} → S.chooseScope S.finishServer s ≡ just p → Close.phase (Up.coordS s) ≡ Close.closed
finish-closed s chosen with S.stage s | Close.phase (W.shutdown (R.base (N.raw (S.base s))))
... | S.closingCM | Close.closed = refl
... | S.closingCM | Close.initial = case chosen of λ ()
... | S.closingCM | Close.reading = case chosen of λ ()
... | S.closingCM | Close.awaitResults = case chosen of λ ()
... | S.closingCM | Close.sendReady _ _ = case chosen of λ ()
... | S.closingCM | Close.awaitDelivery _ _ = case chosen of λ ()
... | S.serving | _ = case chosen of λ ()
... | S.actionBodyExited | _ = case chosen of λ ()
... | S.actionResultAvailable | _ = case chosen of λ ()
... | S.closingAccept | _ = case chosen of λ ()
... | S.acceptCancelRequested | _ = case chosen of λ ()
... | S.acceptCancelDelivered | _ = case chosen of λ ()
... | S.acceptFailed | _ = case chosen of λ ()
... | (S.acceptForkClosing _ _) | _ = case chosen of λ ()
... | S.acceptBodyExited | _ = case chosen of λ ()
... | S.acceptResultAvailable | _ = case chosen of λ ()
... | S.acceptJoined | _ = case chosen of λ ()
... | S.serverStopped | _ = case chosen of λ ()
... | S.actionJoined | _ = case chosen of λ ()
... | S.igCancelRequested | _ = case chosen of λ ()
... | S.igJoined | _ = case chosen of λ ()
... | S.serverReturned | _ = case chosen of λ ()
scope-returned : ∀ x s {t} → S.scopeAdvance x s ≡ just t → S.stage t ≡ S.serverReturned →
  S.stage s ≡ S.serverReturned ⊎ Close.phase (Up.coordS s) ≡ Close.closed
scope-returned x s eq returned with S.chooseScope x s in chosen
... | nothing = case eq of λ ()
... | just p with returned-entry x s chosen (trans (sym (Stage.enact-scope-stage p s eq)) returned)
...   | inj₁ before = inj₁ before
...   | inj₂ refl = inj₂ (finish-closed s chosen)

-- Initialization starts the coordinator at its initial state.
init-U : ∀ c {s} → U.initial c ≡ just s → B.shutdown (U.base s) ≡ Close.initialState
init-U c eq with IG.handles (IG.execution (Machine.inboundGovernor (O.core c))) |
  IG.muxes (IG.execution (Machine.inboundGovernor (O.core c))) | B.initial c in actual
... | [] | [] | just b = case just-injective eq of λ { refl → Physical.initial-coordinator c actual }
... | _ ∷ _ | _ | _ = case eq of λ ()
... | [] | _ ∷ _ | _ = case eq of λ ()
... | [] | [] | nothing = case eq of λ ()
init-P : ∀ c {s} → P.initial c ≡ just s → Low.coordP s ≡ Close.initialState
init-P c eq with U.initial c in actual
... | nothing = case eq of λ ()
... | just u = case just-injective eq of λ { refl → init-U c actual }
init-M : ∀ c {s} → M.initial c ≡ just s → Low.coordM s ≡ Close.initialState
init-M c eq with P.initial c in actual
... | nothing = case eq of λ ()
... | just p = case just-injective eq of λ { refl → init-P c actual }
init-G : ∀ c {s} → G.initial c ≡ just s → Low.coordG s ≡ Close.initialState
init-G c eq with M.initial c in actual
... | nothing = case eq of λ ()
... | just m = case just-injective eq of λ { refl → init-M c actual }
init-W : ∀ c {s} → W.initial c ≡ just s → W.shutdown s ≡ Close.initialState
init-W c eq with G.initial c in actual
... | nothing = case eq of λ ()
... | just g = case just-injective eq of λ { refl → init-G c actual }
init-R : ∀ c {s} → R.initial c ≡ just s → Low.coordR s ≡ Close.initialState
init-R c eq with W.initial c in actual
... | nothing = case eq of λ ()
... | just x = case just-injective eq of λ { refl → init-W c actual }
init-D : ∀ c {s} → D.initial c ≡ just s → Low.coordD s ≡ Close.initialState
init-D c eq with R.initial c in actual
... | nothing = case eq of λ ()
... | just r = case just-injective eq of λ { refl → init-R c actual }
init-C : ∀ c {s} → C.initial c ≡ just s → Low.coordC s ≡ Close.initialState
init-C c eq with D.initial c in actual
... | nothing = case eq of λ ()
... | just d = case just-injective eq of λ { refl → init-D c actual }
init-N : ∀ c {s} → N.initial c ≡ just s → Low.coordN s ≡ Close.initialState
init-N c eq with C.initial c in actual
... | nothing = case eq of λ ()
... | just current = case just-injective eq of λ { refl → init-C c actual }
init-S : ∀ c {s} → S.initial c ≡ just s → Up.coordS s ≡ Close.initialState
init-S c eq with Shared.admissions (Machine.world (O.core c)) | Shared.sockets (Machine.world (O.core c)) | N.initial c in actual
... | [] | [] | just n = case just-injective eq of λ { refl → init-N c actual }
... | [] | [] | nothing = case eq of λ ()
... | [] | _ ∷ _ | _ = case eq of λ ()
... | _ ∷ _ | _ | _ = case eq of λ ()
init-E : ∀ c {s} → E.initial c ≡ just s → Up.coordE s ≡ Close.initialState
init-E c eq with Machine.inboundRelease (O.core c) | Machine.remoteCall (O.core c) | S.initial c in actual
... | nothing | nothing | just server = case just-injective eq of λ { refl → init-S c actual }
... | nothing | nothing | nothing = case eq of λ ()
... | nothing | just _ | _ = case eq of λ ()
... | just _ | _ | _ = case eq of λ ()
init-K : ∀ c g {s} → K.initial c g ≡ just s → Up.coordK s ≡ Close.initialState
init-K c g eq with E.initial c in actual
... | nothing = case eq of λ ()
... | just e = case just-injective eq of λ { refl → init-E c actual }

-- The initial coordinator is not closed.
initial-last : Low.Last Close.initialState
initial-last ()

module Protocols (canInitiate : HandleId → ℕ → Bool) where
  private
    module T = K.Protocols canInitiate
    module Outer = SR.Protocols canInitiate
    module Certified = RelaysFacts.Certified T.advance Outer.runtimeReturned
    module Done = SI5a.Protocols canInitiate
    module Lift = Up.Protocols canInitiate
  coordT : T.Runtime → Close.State
  coordT = Lift.coordT

  init-T : ∀ c g {s} → T.initialize c g ≡ just s → coordT s ≡ Close.initialState
  init-T c g eq with K.initial c g in actual
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → init-K c g actual }

  -- Invariant: a returned Server has a closed coordinator.
  Inv : T.Runtime → Set
  Inv s = Done.stageT s ≡ S.serverReturned → Close.phase (coordT s) ≡ Close.closed
  closed-before : ∀ a s {t} → T.advance a s ≡ just t → Inv s → Done.stageT t ≡ S.serverReturned →
    Close.phase (coordT s) ≡ Close.closed
  closed-before a s eq inv returned with Done.advance-stage a s eq
  ... | inj₁ same = inv (trans (sym same) returned)
  ... | inj₂ (x , b , stepped , same) with SI5a.scope-gate x (T.base s) stepped
  ...   | allowed , scoped with scope-returned x (E.base (K.server (T.base s))) scoped (trans (sym same) returned)
  ...     | inj₁ before = inv before
  ...     | inj₂ closed = closed
  advance-preserves : ∀ a s {t} → T.advance a s ≡ just t → Inv s → Inv t
  advance-preserves a s {t} eq inv returned = subst (λ c → Close.phase c ≡ Close.closed)
    (sym (Low.closed-frame (Lift.advance-frame a s eq) closed)) closed
    where closed = closed-before a s eq inv returned
  runs-preserve : ∀ {s as t} → T.Runs s as t → Inv s → Inv t
  runs-preserve T.stop inv = inv
  runs-preserve (T.more {s = s} {a = a} eq rest) inv = runs-preserve rest (advance-preserves a s eq inv)
  initial-inv : ∀ c g {s} → T.initialize c g ≡ just s → Inv s
  initial-inv c g eq with K.initial c g in actual
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → λ returned →
    case trans (sym (SI5a.shared-initial c g actual)) returned of λ () }

  -- The coordinator part of the SI5 certificate.
  record CMClosed (final : T.Runtime) : Set where
    field
      closed : Close.phase (coordT final) ≡ Close.closed
      drained : Close.remaining (coordT final) ≡ []
      physicalWait : Handler.PhysicalWait (coordT final) ⊎ Low.ExitWait (coordT final)

  -- The full SI5 certificate: SI5a plus the closed CM coordinator.
  record Complete (scheduled : Bool) (final : T.Runtime) (t : Maybe RR.ThreadPhase) : Set where
    field
      shutdown : Done.Complete scheduled final t
      cm : CMClosed final

  complete : ∀ {c g start scheduled as final t} → T.initialize c g ≡ just start →
    Outer.Executes (Outer.outer start (RR.initial scheduled)) as (Outer.outer final (RR.relaysState t RR.finished)) →
    Complete scheduled final t
  complete {c} {g} {start} {final = final} initialized path with Done.outer-runs path | Done.complete initialized path
  ... | events , run | certificate with runs-preserve run (initial-inv c g initialized) (Done.Complete.serverReturned certificate)
  ...   | closed with subst (λ p → Low.Frame p (coordT final)) (init-T c g initialized) (Lift.runs-frame run)
  ...     | Low.frame (actions , trace) last = record
    { shutdown = certificate
    ; cm = record
      { closed = closed
      ; drained = proj₁ (CloseProof.closed-from-initial trace closed)
      ; physicalWait = last initial-last closed } }
