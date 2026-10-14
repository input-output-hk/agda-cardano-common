{-# OPTIONS --guardedness #-}

-- Admission prefix after Server.acceptLoop's successful handoff, through the
-- handshake-wait boundary. Not a model of accept, IG, OG, or handler execution.
module ConnectionManagement.Rules.Server where

open import Data.Nat using (suc; _≤?_)
open import Data.List using (_∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.State
open import ConnectionManagement.Rules.CM

-- Labels are diagnostic attempts, not extra source rendezvous.
data AdmissionAction : Set where
  take countLimit allocatePromise chooseEntry fork putMapBack readCounters
    restore close failFork : AdmissionAction

-- Update only the caller's continuation, retaining other admission workers.
setPC : WorkerId → AdmissionWorker → AdmissionPC → State → State
setPC w a p s = record s { admissions = put w (record a { pc = p }) (admissions s) }

-- A map count is its own STM step. The admitted decision is not rechecked later.
stepWorker : WorkerId → AdmissionWorker → AdmissionAction → State → Maybe State
stepWorker w a take s with pc a
... | acquireMap with takeMap w (cm s)
...   | nothing = nothing
...   | just (l , c) = just (setPC w a (count l) (record s { cm = c }))
stepWorker w a take s | _ = nothing

stepWorker w a countLimit s with pc a
... | count l with countIncoming (entries (cm s)) (savedMap l)
...   | nothing = nothing
...   | just n with suc n ≤? hardLimit (request a)
...     | yes _ = just (setPC w a (prepare l) s)
...     | no _ = just (setPC w a (reject l hardLimitReached) s)
stepWorker w a countLimit s | _ = nothing

stepWorker w a allocatePromise s with pc a
... | prepare l = just (setPC w a (selectEntry l (ident (nextPromise s)))
      (record s { promises = ident (nextPromise s) ∷ promises s
                ; nextPromise = suc (nextPromise s) }))
... | _ = nothing

stepWorker w a chooseEntry s with pc a
... | selectEntry l p with selectInbound l (request a) (cm s)
...   | nothing = nothing
...   | just denied = just (setPC w a (reject l forbidden) s)
...   | just (selected e c) = just (setPC w a (forkHandler l p e) (record s { cm = c }))
stepWorker w a chooseEntry s | _ = nothing

stepWorker w a fork s with pc a
... | forkHandler l p e with lookup (child (request a)) (handlers s)
                          | lookup (child (request a)) (admissions s)
...   | nothing | nothing = just (setPC w a (publish l p e)
        (record s
          { handlers = put (child (request a)) (handlerStart e (socketRef (request a)) p) (handlers s)
          ; sockets = put (socketRef (request a)) (handling (child (request a))) (sockets s) }))
...   | _ | _ = nothing -- a reused child token is a malformed fixture
stepWorker w a fork s | _ = nothing

stepWorker w a failFork s with pc a
... | forkHandler l p e = just (setPC w a (reject l forkFailed) s)
... | _ = nothing

stepWorker w a putMapBack s with pc a
... | publish l p e with putMap l (insertConnection (key (request a)) e (savedMap l)) (cm s)
...   | nothing = nothing
...   | just c = just (setPC w a (countPublished p e) (record s { cm = c }))
stepWorker w a putMapBack s | reject l hardLimitReached with restoreMap l (cm s)
... | nothing = nothing
... | just c = just (setPC w a (closeSocket hardLimitReached) (record s { cm = c }))
stepWorker w a putMapBack s | _ = nothing

-- traceCounters reads the map after publication and can wait for another owner.
stepWorker w a readCounters s with pc a | mapCell (cm s)
... | countPublished p e | full m with countIncoming (entries (cm s)) m
...   | just _ = just (setPC w a (awaitHandshake p e) s)
...   | nothing = nothing
stepWorker w a readCounters s | _ | _ = nothing

-- Synchronous failure unwinds the IO helper before the server closes the socket.
stepWorker w a restore s with pc a
... | reject l hardLimitReached = nothing
... | reject l f with restoreMap l (cm s)
...   | nothing = nothing
...   | just c = just (setPC w a (closeSocket f) (record s { cm = c }))
stepWorker w a restore s | _ = nothing

stepWorker w a close s with pc a
... | closeSocket f = just (setPC w a (finished f)
    (record s { sockets = put (socketRef (request a)) closed (sockets s) }))
... | _ = nothing

-- Undefined continuations (including handshake execution) are outside this
-- prefix's alphabet. Absence here must not be used as a whole-source deadlock.
stepPrefix : WorkerId → AdmissionAction → State → Maybe State
stepPrefix w act s with lookup w (admissions s)
... | nothing = nothing
... | just a = stepWorker w a act s
