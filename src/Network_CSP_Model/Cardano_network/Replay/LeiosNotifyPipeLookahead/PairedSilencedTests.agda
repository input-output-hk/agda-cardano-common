{-# OPTIONS --safe #-}

-- Concrete paired silenced verdicts: certified acceptance, certified local rejection and an
-- undetermined FIFO swap that both local silenced languages accept.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.PairedSilencedTests where

open import Data.Bool using (Bool; false; true)
import Data.Bool.Properties as Bool
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊤ as Rows
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PairedSilenced Bool Bool._≟_ false (λ b → b) as P

-- Verdict category only; the evidence itself is checked by the Outcome constructors' types.
data Kind : Set where
  accepted rejected undetermined : Kind

-- Read off the verdict constructor of a concrete paired check.
kind : ∀ {contract c s} → P.Outcome contract c s → Kind
kind (P.accepted _) = accepted
kind (P.rejected _) = rejected
kind (P.undetermined _ _ _) = undetermined

-- Client record of a visible normal reply (`false` is not hidden).
recvNormal : Rows.ClientRow
recvNormal = Rows.receiveResponse (D.reply (S.normal false))

-- Server record of the same visible normal reply.
sendNormal : Rows.ServerRow
sendNormal = Rows.sendResponse (D.reply (S.normal false))

-- Graceful client shutdown with every Request row silenced.
gracefulClient : List Rows.ClientRow
gracefulClient = recvNormal ∷ Rows.sendCommand D.quit ∷
  Rows.receiveResponse (D.reply S.canceled) ∷ Rows.receiveResponse D.done ∷ []

-- The matching node-next server shutdown, also with every Request row silenced.
gracefulServer : List Rows.ServerRow
gracefulServer = sendNormal ∷ Rows.receiveCommand D.quit ∷
  Rows.sendResponse (D.reply S.canceled) ∷ Rows.sendResponse D.done ∷ []

-- Both silenced logs of a graceful shutdown are certified as the erasure of one paired source run.
paired-graceful-accepted : kind (P.check S.nodeNext gracefulClient gracefulServer) ≡ accepted
paired-graceful-accepted = refl

-- The client file ends after one reply while the server has already sent a second.
eofClient : List Rows.ClientRow
eofClient = recvNormal ∷ []

-- Two server replies, so the reconstruction must pad the client with one more Request.
eofServer : List Rows.ServerRow
eofServer = sendNormal ∷ sendNormal ∷ []

-- The server's extra Request is appended to the quit-free client reconstruction.
client-eof-reconstruction : P.reconstruct eofClient eofServer ≡
  (Rows.sendCommand D.request ∷ recvNormal ∷ Rows.sendCommand D.request ∷ [] ,
   Rows.receiveCommand D.request ∷ sendNormal ∷ Rows.receiveCommand D.request ∷ sendNormal ∷ [])
client-eof-reconstruction = refl

-- A client EOF prefix is accepted once the missing client Request is padded in.
client-eof-padded : kind (P.check S.nodeNext eofClient eofServer) ≡ accepted
client-eof-padded = refl

-- Done before Quit fails the client's local silenced language, which refutes every paired source.
local-reject-certified : kind (P.check S.nodeNext (Rows.receiveResponse D.done ∷ []) []) ≡ rejected
local-reject-certified = refl

-- The client receives the normal reply first, the server sends Canceled first.
swapClient : List Rows.ClientRow
swapClient = recvNormal ∷ Rows.receiveResponse (D.reply S.canceled) ∷ []

-- Reversed server send order; each endpoint alone is a valid generic-next silenced log.
swapServer : List Rows.ServerRow
swapServer = Rows.sendResponse (D.reply S.canceled) ∷ sendNormal ∷ []

-- Both locals accept but the exact decider refutes the canonical reconstruction: no verdict is claimed.
fifo-swap-undetermined : kind (P.check S.genericNext swapClient swapServer) ≡ undetermined
fifo-swap-undetermined = refl
