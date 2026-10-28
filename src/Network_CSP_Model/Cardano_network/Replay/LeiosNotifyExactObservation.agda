{-# OPTIONS --guardedness #-}

-- One depth/endpoint-independent observation retains every Notify logger field.
module Cardano_network.Replay.LeiosNotifyExactObservation where

open import Cardano_network.Replay.LeiosNotifyExactParams renaming (exactParams to p)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees using (ExtI)
open import Cardano_network.Data p
open import Cardano_network.LeiosNotifyP p using (LNPEv; sendLNP; receiveLNP)
import Cardano_network.Replay.LeiosNotifyPipeline as N
import Cardano_network.Replay.LeiosNotifySession as Log
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as LTS

-- Preserve the native constructor shape used by protocol credit control.
kind : MessageLeiosNotifyP → N.Kind
kind MsgLNPRequestNext = N.request
kind (MsgLNPBlockAnnouncement _) = N.announcement
kind (MsgLNPBlockOffer _ _) = N.offer
kind (MsgLNPBlockTxsOffer _) = N.txsOffer
kind (MsgLNPVotes _) = N.votes
kind MsgLNPDone = N.doneK

-- Recover exactly the optional metadata stored in a native header representative.
headerSummary : Header → Log.Announcement
headerSummary (header a) = a

-- All logger fields are retained; vote order and repeated entries are unchanged.
canonical : MessageLeiosNotifyP → N.Msg
canonical MsgLNPRequestNext = Log.RequestNext
canonical (MsgLNPBlockAnnouncement h) = Log.BlockAnnouncement (headerSummary h)
canonical (MsgLNPBlockOffer (h , s) z) = Log.BlockOffer h s z
canonical (MsgLNPBlockTxsOffer (h , s)) = Log.BlockTxsOffer h s
canonical (MsgLNPVotes vs) = Log.Votes vs
canonical MsgLNPDone = Log.Done

-- Canonical log values retain precisely the native message kind.
canonical-kind : ∀ m → Log.kind (canonical m) ≡ kind m
canonical-kind MsgLNPRequestNext = refl
canonical-kind (MsgLNPBlockAnnouncement _) = refl
canonical-kind (MsgLNPBlockOffer (_ , _) _) = refl
canonical-kind (MsgLNPBlockTxsOffer (_ , _)) = refl
canonical-kind (MsgLNPVotes _) = refl
canonical-kind MsgLNPDone = refl

-- Wire directions are observed; native API delivery and local done are erased.
classify : LTS.Event → Maybe N.E
classify (LTS.evLabel _ (sendLNP _ _) (_ , _ , _ , leiosNotifyP m)) = just (N.Send , canonical m)
classify (LTS.evLabel _ (receiveLNP _ _) (_ , _ , _ , leiosNotifyP m)) = just (N.Recv , canonical m)
classify _ = nothing
