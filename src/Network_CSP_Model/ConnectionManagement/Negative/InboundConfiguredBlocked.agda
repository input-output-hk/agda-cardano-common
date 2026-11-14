{-# OPTIONS --guardedness #-}

-- Reuse diagnostic, not configured inbound coverage. The existing outbound
-- contract wrapper refuses the real reduced initialized responder capture.
module ConnectionManagement.Negative.InboundConfiguredBlocked where

open import ConnectionManagement.Negative.InboundCleanLifecycleSupport
open import Data.Maybe using (map)
import ConnectionManagement.ConfiguredProtocols as Contracts
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.InboundCleanLifecycleAdmission as Admission
import ConnectionManagement.Negative.InboundCleanLifecycleProtocol as Protocol
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as Runtime
module B = Contracts I.bearerClosed classify capability

-- Keep the checked admission prefix and exactly the first eight real edges.
body-actions : List V.Event
body-actions = Protocol.a1 ∷ Protocol.a2 ∷ Protocol.a3 ∷ Protocol.a4 ∷
  Protocol.a5 ∷ Protocol.a6 ∷ Protocol.a7 ∷ Protocol.a8 ∷ []
abstract
  to-body : V.Runs Admission.s38 body-actions Protocol.s8
  to-body = V.more Protocol.e1 (V.more Protocol.e2 (V.more Protocol.e3
    (V.more Protocol.e4 (V.more Protocol.e5 (V.more Protocol.e6
    (V.more Protocol.e7 (V.more Protocol.e8 V.stop)))))))

-- Composition retains the ordinary initializer and checks no new raw edge.
append : ∀ {s as t bs u} → V.Runs s as t → V.Runs t bs u → V.Runs s (as ++ bs) u
append V.stop tail = tail
append (V.more eq rest) tail = V.more eq (append rest tail)
abstract
  initialized-to-body : V.Runs initial (Admission.actions ++ body-actions) Protocol.s8
  initialized-to-body = append Admission.path to-body

prefix-length : length (Admission.actions ++ body-actions) ≡ 46
prefix-length = refl

-- The caller, mux and protocol number match; direction is the obstruction.
wrapped : B.State
wrapped = B.initial Protocol.s8 A.child₀ (ident 0) (ident 0)

captured-owner : map Types.owner (P.collector (ident 10) (B.physical wrapped)) ≡ just A.child₀
captured-owner = refl
captured-mux : map Types.mux (P.collector (ident 10) (B.physical wrapped)) ≡ just (ident 0)
captured-mux = refl
captured-number : map Types.protocolNumber (P.collector (ident 10) (B.physical wrapped)) ≡ just 1
captured-number = refl
captured-direction : map Types.direction (P.collector (ident 10) (B.physical wrapped)) ≡ just Runtime.responderJob
captured-direction = refl

responder-capture-refused : B.attach 1 (ident 10) wrapped ≡ nothing
responder-capture-refused = refl

-- The raw return is really enabled, while contract-coupled return/publication
-- cannot pass through this outbound wrapper at the same responder boundary.
raw-return-enabled : V.advance Protocol.a9 Protocol.s8 ≡ just Protocol.s9
raw-return-enabled = refl
contract-return-refused : B.frontend Protocol.a9 wrapped ≡ nothing
contract-return-refused = refl
premature-clean-refused : B.frontend (protocol (P.commitClean (ident 10))) wrapped ≡ nothing
premature-clean-refused = refl
