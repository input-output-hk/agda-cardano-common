{-# OPTIONS --guardedness #-}

-- Initialized finite prefix exits, with real births and successful-step proofs.
-- Duplicate-key input is abstract; unresolved mfix references are not evaluated.
module ConnectionManagement.Negative.ServerAdmissionPrefixSupport where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.Store using (Store; lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.ServerAdmissionPrefixFixtures as Fixtures
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.Handshake as Handshake
private
  module S = Server I.bearerClosed
  module N = Publication I.bearerClosed
  module C = N.C
  module D = N.D
  module R = N.R
  module W = N.W
  module G = N.G
  module M = N.M
  module P = N.P
  module U = N.U

-- Observe the single physical registry below the handler/mux adapters.
physicalThreads : S.State → Store WorkerId H.Thread
physicalThreads s = B.threads (U.base (P.base (M.base (G.base (W.base (R.base (N.raw (S.base s))))))))

-- All scenario lists compose checked steps; no refused action gets a default.
append : ∀ {s as t bs u} → S.Executes s as t → S.Executes t bs u → S.Executes s (as ++ bs) u
append S.done tail = tail
append (S.next eq rest) tail = S.next eq (append rest tail)
admit : WorkerId → Admission.AdmissionAction → S.Action
admit w a = S.run (S.runMachine (Machine.admissionStep w a))
consume : Handshake.HandshakeAction → S.Action
consume a = S.run (S.runMachine (Machine.handshakeStep A.w₀ a))
mux : U.Action → S.Action
mux a = S.run (N.run (C.run (D.run (D.wrapMonitor (M.run (P.run a))))))
handler : H.Action → S.Action
handler a = mux (U.run (B.handler a))
