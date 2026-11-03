{-# OPTIONS --guardedness #-}

-- Canonical native realization of every exact server action at every endpoint.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerEventsBridge (p : Params) where

open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Maybe.Properties using (just-injective)
open import Class.DecEq using (_≟_)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Data p
open import Cardano_network.Net p using (Link)
import Cardano_network.LeiosNotifyPipe p as Payloads
import Cardano_network.LeiosNotifyPipeLookahead p as Native
import Cardano_network.LeiosNotifyPipeLookahead.ServerEvents p as Events
open Native.Reference

-- The decoder's callback contract does not restrict which events can be represented.
module For (contract : Contract) (l : Link) (d : Dir) where
  open Native.Machine contract l d

  -- Decidable endpoint equality accepts the fixed endpoint for every supplied action.
  endpoint-self : (a : Maybe Action) → endpoint l d a ≡ a
  endpoint-self a with l ≟ l | d ≟ d
  ... | yes _ | yes _ = refl
  ... | no neq | _ = ⊥-elim (neq refl)
  ... | _ | no neq = ⊥-elim (neq refl)

  -- Native outgoing decoding distinguishes Done from replies and invalid commands.
  response-action : MessageLeiosNotifyP → Maybe Action
  response-action MsgLNPDone = just sendDone
  response-action msg = map sendReply (replyOf msg)

  -- Canonical metadata always passes the native sender's exact-packet guard.
  outgoing-exact : (msg : MessageLeiosNotifyP) → outgoing (packet msg) ≡ response-action msg
  outgoing-exact msg with packet msg ≟ packet msg
  ... | yes _ with msg
  ...   | MsgLNPRequestNext = refl
  ...   | MsgLNPQuit = refl
  ...   | MsgLNPDone = refl
  ...   | MsgLNPCanceled = refl
  ...   | MsgLNPBlockAnnouncement h = refl
  ...   | MsgLNPBlockOffer pt size = refl
  ...   | MsgLNPBlockTxsOffer pt = refl
  ...   | MsgLNPVotes votes = refl
  outgoing-exact msg | no neq = ⊥-elim (neq refl)

  -- Reply realization retains the entire selected notification or cancellation.
  reply-action : (r : Reply) → response-action (Events.replyMessage r) ≡ just (sendReply r)
  reply-action (normal (Payloads.announcement h)) = refl
  reply-action (normal (Payloads.offer pt size)) = refl
  reply-action (normal (Payloads.txsOffer pt)) = refl
  reply-action (normal (Payloads.votes votes)) = refl
  reply-action canceled = refl

  -- Every exact source action has a canonical native event whose decode is that action.
  decode-encode : (a : Action) → decode (Events.encode l d a) ≡ just a
  decode-encode recvRequest = endpoint-self (just recvRequest)
  decode-encode recvQuit = endpoint-self (just recvQuit)
  decode-encode sendDone rewrite outgoing-exact MsgLNPDone = endpoint-self (just sendDone)
  decode-encode (sendReply r)
    rewrite outgoing-exact (Events.replyMessage r) | reply-action r = endpoint-self (just (sendReply r))
  decode-encode (nextReply (normal (Payloads.announcement h))) =
    endpoint-self (just (nextReply (normal (Payloads.announcement h))))
  decode-encode (nextReply (normal (Payloads.offer pt size))) =
    endpoint-self (just (nextReply (normal (Payloads.offer pt size))))
  decode-encode (nextReply (normal (Payloads.txsOffer pt))) =
    endpoint-self (just (nextReply (normal (Payloads.txsOffer pt))))
  decode-encode (nextReply (normal (Payloads.votes votes))) =
    endpoint-self (just (nextReply (normal (Payloads.votes votes))))
  decode-encode (nextReply canceled) = endpoint-self (just (nextReply canceled))

  -- Native realization cannot collapse two distinct exact source actions or payloads.
  encode-injective : ∀ {a b} → Events.encode l d a ≡ Events.encode l d b → a ≡ b
  encode-injective {a} {b} eq = just-injective
    (trans (sym (decode-encode a)) (trans (cong decode eq) (decode-encode b)))
