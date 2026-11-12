{-# OPTIONS --guardedness #-}

-- Invert each real higher initializer to the newly empty protocol/PC tables.
module ConnectionManagement.Properties.LiveTrackerAuxInitial where
open import Data.Bool using (Bool)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (ErrorId)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.State as Shared
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.MuxResultMonitor as Monitor
import ConnectionManagement.MuxGroupShutdown as Group
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.MuxStartupUnwind as Unwind
import ConnectionManagement.MuxDeltaQ as Delta
import ConnectionManagement.MuxCatchUnwind as Catch
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.ServerAdmission as Admission
import ConnectionManagement.ServerIGExit as IGExit
import ConnectionManagement.ServerPeers as Model
import ConnectionManagement.Properties.LiveTrackerAuxCoreInitialized as Core

module For (b io : ErrorId → Bool) where
 private module M = Monitor b using (State; pcs; base; initial)
 private module G = Group b using (base; initial)
 private module W = Exit b using (base; initial)
 private module R = Unwind b using (base; initial)
 private module D = Delta b using (monitor; initial)
 private module C = Catch b using (base; initial)
 private module N = Publication b using (base; initial)
 private module S = Admission b using (base; initial)
 private module E = IGExit b using (base; initial)
 private module K = Model b io using (server; initial)
 open Core.MonitorEndpoint b using (Valid; monitor-initialized-valid)
 group : ∀ c {s} → G.initial c ≡ just s → Valid (G.base s)
 group c eq with M.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just m = case just-injective eq of λ { refl → monitor-initialized-valid c actual }
 exit : ∀ c {s} → W.initial c ≡ just s → Valid (G.base (W.base s))
 exit c eq with G.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just g = case just-injective eq of λ { refl → group c actual }
 unwind : ∀ c {s} → R.initial c ≡ just s → Valid (G.base (W.base (R.base s)))
 unwind c eq with W.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just w = case just-injective eq of λ { refl → exit c actual }
 delta : ∀ c {s} → D.initial c ≡ just s → Valid (D.monitor s)
 delta c eq with R.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just r = case just-injective eq of λ { refl → unwind c actual }
 caught : ∀ c {s} → C.initial c ≡ just s → Valid (D.monitor (C.base s))
 caught c eq with D.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just d = case just-injective eq of λ { refl → delta c actual }
 publication : ∀ c {s} → N.initial c ≡ just s → Valid (D.monitor (C.base (N.base s)))
 publication c eq with C.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → caught c actual }
 server : ∀ c {s} → S.initial c ≡ just s → Valid (D.monitor (C.base (N.base (S.base s))))
 server c eq with Shared.admissions (Machine.world (O.core c)) | Shared.sockets (Machine.world (O.core c)) | N.initial c in actual
 ... | [] | [] | just n = case just-injective eq of λ { refl → publication c actual }
 ... | _ ∷ _ | _ | _ = case eq of λ ()
 ... | [] | _ ∷ _ | _ = case eq of λ ()
 ... | [] | [] | nothing = case eq of λ ()
 igExit : ∀ c {s} → E.initial c ≡ just s → Valid (D.monitor (C.base (N.base (S.base (E.base s)))))
 igExit c eq with Machine.inboundRelease (O.core c) | Machine.remoteCall (O.core c) | S.initial c in actual
 ... | nothing | nothing | just s = case just-injective eq of λ { refl → server c actual }
 ... | just _ | _ | _ = case eq of λ ()
 ... | nothing | just _ | _ = case eq of λ ()
 ... | nothing | nothing | nothing = case eq of λ ()
 combined : ∀ c g {s} → K.initial c g ≡ just s →
   Valid (D.monitor (C.base (N.base (S.base (E.base (K.server s))))))
 combined c g eq with E.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just e = case just-injective eq of λ { refl → igExit c actual }
