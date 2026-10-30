{-# OPTIONS --guardedness #-}

-- A refusal counts as promise blocking only at the actual promise-reading PC.
-- This lemma concerns one source step, not permanent blocking or deadlock.
module ConnectionManagement.Properties.PromiseWait where

open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (DecEq-Id)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as M
import ConnectionManagement.State as S
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.Handshake as H

-- Counter reads and other earlier phases are deliberately excluded by the
-- continuation premise. This is the real dispatcher, without adapter guards.
outbound-read-retries : ∀ c caller req entry promise key →
  lookup caller (O.acquiring c) ≡ just (A.frame req (A.awaitResult entry promise key)) →
  lookup promise (S.handshakeResults (M.world (O.core c))) ≡ nothing →
  O.advance (O.acquire caller A.readResult) c ≡ nothing
outbound-read-retries c caller req entry promise key at empty rewrite at | empty = refl


-- The inbound counter read must already have reached awaitHandshake. This is
-- the raw dispatcher action, without any physical-handler adapter guard.
inbound-read-retries : ∀ c caller req entry promise →
  lookup caller (S.admissions (M.world c)) ≡
    just (S.admissionWorker req (S.awaitHandshake promise entry)) →
  lookup promise (S.handshakeResults (M.world c)) ≡ nothing →
  M.advance (M.handshakeStep caller H.readResult) c ≡ nothing
inbound-read-retries c caller req entry promise at empty rewrite at | empty = refl
