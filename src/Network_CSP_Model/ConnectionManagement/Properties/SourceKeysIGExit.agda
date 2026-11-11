{-# OPTIONS --guardedness #-}

-- Caller bookkeeping through the inbound-governor exit wrapper: only a
-- delegated Server action can have a root; receipts clear only IG calls.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.SourceKeysIGExit (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
open import ConnectionManagement.Properties.OutboundKeys
import ConnectionManagement.Properties.SourceKeysServer as ServerKeys
private
  module E = Exit isBearerClosed
  module S = Server isBearerClosed
  module Lower = ServerKeys isBearerClosed

rootE : E.Action → Maybe O.Action
rootE (E.run a) = Lower.rootS a
rootE _ = nothing
planRoot : E.Plan → Maybe O.Action
planRoot (E.delegate a e) = Lower.rootS a
planRoot _ = nothing

enact-keys : ∀ p s {s′} → E.enact p s ≡ just s′ → Effect (planRoot p) (E.source s) (E.source s′)
enact-keys (E.delegate a e) s eq with S.step a (E.base s) in stepped
... | nothing = case eq of λ ()
... | just server = case just-injective eq of λ { refl → Lower.step-keysS a (E.base s) stepped }
enact-keys (E.local e) s eq = case just-injective eq of λ { refl → same-refl _ }
enact-keys (E.abandon r) s eq = case just-injective eq of λ { refl → fields-same _ _ refl refl refl refl }
enact-keys (E.ownFailure r f) s eq = case just-injective eq of λ { refl → fields-same _ _ refl refl refl refl }
enact-keys (E.finish e) s eq = case just-injective eq of λ { refl → same-refl _ }

choose-root : ∀ a s {p} → E.choose a s ≡ just p → planRoot p ≡ rootE a
choose-root (E.run a) s eq with E.runAllowed a s
... | false = case eq of λ ()
... | true with E.delegateExit a (E.exit s)
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → refl }
choose-root (E.receive at err) s eq with E.selectReceipt at err s
... | nothing = case eq of λ ()
... | just r = case just-injective eq of λ { refl → refl }
choose-root (E.fail at f) s eq with E.selectFailure at (S.error f) s
... | nothing = case eq of λ ()
... | just r = case just-injective eq of λ { refl → refl }
choose-root E.captureSnapshot s eq with E.phase (E.exit s) | S.ig (E.base s) | IG.active (IG.execution (E.governor s)) |
  IG.continuation (E.governor s) | Machine.inboundRelease (O.core (E.source s)) | Machine.remoteCall (O.core (E.source s)) |
  E.unique (IG.connections (IG.publishedState (E.governor s)))
... | E.caught | S.igFlushed | false | IG.exited | nothing | nothing | true = case just-injective eq of λ { refl → refl }
choose-root E.captureSnapshot s eq | E.live | _ | _ | _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igLive | _ | _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igCaught | _ | _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igInactive | _ | _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | true | _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.sampleTime | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.exitFlush | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.inCM | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.exited | nothing | nothing | false = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.exited | nothing | just _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.exited | just _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.armInactivity _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.awaitBatch _ _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.readNext _ _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.prepareNew _ _ _ _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.startResponders _ _ _ _ _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.publishDecision _ _ _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.stopAfterFailure _ _ _ _ _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.waitStopped _ _ _ _ _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.restartResponder _ _ _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.awaitRemoteIdle _ _ _ _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igFlushed | false | IG.needsCM _ _ _ _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igBodyExited | _ | _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.caught | S.igResultAvailable | _ | _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.traversing | _ | _ | _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.invoked | _ | _ | _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.failed | _ | _ | _ | _ | _ | _ = case eq of λ ()
choose-root E.captureSnapshot s eq | E.bodyDone | _ | _ | _ | _ | _ | _ = case eq of λ ()
choose-root E.invokeFinal s eq with E.phase (E.exit s) | E.remaining (E.exit s)
... | E.traversing | r ∷ rs = case just-injective eq of λ { refl → refl }
choose-root E.invokeFinal s eq | E.live | _ = case eq of λ ()
choose-root E.invokeFinal s eq | E.caught | _ = case eq of λ ()
choose-root E.invokeFinal s eq | E.traversing | [] = case eq of λ ()
choose-root E.invokeFinal s eq | E.invoked | _ = case eq of λ ()
choose-root E.invokeFinal s eq | E.failed | _ = case eq of λ ()
choose-root E.invokeFinal s eq | E.bodyDone | _ = case eq of λ ()
choose-root E.returnFinal s eq with E.phase (E.exit s) | E.remaining (E.exit s)
... | E.invoked | r ∷ rs = case just-injective eq of λ { refl → refl }
choose-root E.returnFinal s eq | E.live | _ = case eq of λ ()
choose-root E.returnFinal s eq | E.caught | _ = case eq of λ ()
choose-root E.returnFinal s eq | E.traversing | _ = case eq of λ ()
choose-root E.returnFinal s eq | E.invoked | [] = case eq of λ ()
choose-root E.returnFinal s eq | E.failed | _ = case eq of λ ()
choose-root E.returnFinal s eq | E.bodyDone | _ = case eq of λ ()
choose-root (E.failFinal err) s eq with E.phase (E.exit s) | E.remaining (E.exit s)
... | E.invoked | r ∷ rs = case just-injective eq of λ { refl → refl }
choose-root (E.failFinal err) s eq | E.live | _ = case eq of λ ()
choose-root (E.failFinal err) s eq | E.caught | _ = case eq of λ ()
choose-root (E.failFinal err) s eq | E.traversing | _ = case eq of λ ()
choose-root (E.failFinal err) s eq | E.invoked | [] = case eq of λ ()
choose-root (E.failFinal err) s eq | E.failed | _ = case eq of λ ()
choose-root (E.failFinal err) s eq | E.bodyDone | _ = case eq of λ ()
choose-root E.finishFinal s eq with E.phase (E.exit s) | E.remaining (E.exit s) | E.outcome (E.exit s) | S.ig (E.base s)
... | E.traversing | [] | just err | S.igFlushed = case just-injective eq of λ { refl → refl }
... | E.failed | _ | just err | S.igFlushed = case just-injective eq of λ { refl → refl }
choose-root E.finishFinal s eq | E.live | _ | _ | _ = case eq of λ ()
choose-root E.finishFinal s eq | E.caught | _ | _ | _ = case eq of λ ()
choose-root E.finishFinal s eq | E.traversing | [] | nothing | _ = case eq of λ ()
choose-root E.finishFinal s eq | E.traversing | [] | just _ | S.igLive = case eq of λ ()
choose-root E.finishFinal s eq | E.traversing | [] | just _ | S.igCaught = case eq of λ ()
choose-root E.finishFinal s eq | E.traversing | [] | just _ | S.igInactive = case eq of λ ()
choose-root E.finishFinal s eq | E.traversing | [] | just _ | S.igBodyExited = case eq of λ ()
choose-root E.finishFinal s eq | E.traversing | [] | just _ | S.igResultAvailable = case eq of λ ()
choose-root E.finishFinal s eq | E.traversing | _ ∷ _ | _ | _ = case eq of λ ()
choose-root E.finishFinal s eq | E.invoked | _ | _ | _ = case eq of λ ()
choose-root E.finishFinal s eq | E.failed | _ | nothing | _ = case eq of λ ()
choose-root E.finishFinal s eq | E.failed | _ | just _ | S.igLive = case eq of λ ()
choose-root E.finishFinal s eq | E.failed | _ | just _ | S.igCaught = case eq of λ ()
choose-root E.finishFinal s eq | E.failed | _ | just _ | S.igInactive = case eq of λ ()
choose-root E.finishFinal s eq | E.failed | _ | just _ | S.igBodyExited = case eq of λ ()
choose-root E.finishFinal s eq | E.failed | _ | just _ | S.igResultAvailable = case eq of λ ()
choose-root E.finishFinal s eq | E.bodyDone | _ | _ | _ = case eq of λ ()

step-keysE : ∀ a s {s′} → E.step a s ≡ just s′ → Effect (rootE a) (E.source s) (E.source s′)
step-keysE a s {s′} eq with E.choose a s in chosen
... | nothing = case eq of λ ()
... | just p = subst (λ r → Effect r (E.source s) (E.source s′)) (choose-root a s chosen) (enact-keys p s eq)
