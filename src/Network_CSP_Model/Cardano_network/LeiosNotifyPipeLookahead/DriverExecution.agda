{-# OPTIONS --safe #-}

-- Certified executable selectors for the unchanged driver-record product.
-- Callback selectors range over source data; no finite-search bound is claimed.
open import Relation.Binary.Definitions using (DecidableEquality)
module Cardano_network.LeiosNotifyPipeLookahead.DriverExecution
  (Notification Return : Set) (notificationEq : DecidableEquality Notification) where

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_; _∷ʳ_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.ClientExecution Notification Return notificationEq as CE
open import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return
open import Cardano_network.LeiosNotifyPipeLookahead.Selection using (select; select-complete)
import Cardano_network.LeiosNotifyPipeLookahead.Enumeration Notification as SE
module SX = S.Executable notificationEq

-- Initiator message equality distinguishes Request and Quit.
clientMessageEq : DecidableEquality ClientMessage
clientMessageEq request request = yes refl
clientMessageEq quit quit = yes refl
clientMessageEq request quit = no λ ()
clientMessageEq quit request = no λ ()

-- Responder equality compares exact notification payloads, cancellation and Done.
serverMessageEq : DecidableEquality ServerMessage
serverMessageEq done done = yes refl
serverMessageEq done (reply _) = no λ ()
serverMessageEq (reply _) done = no λ ()
serverMessageEq (reply m) (reply n) with SX.replyEq m n
... | yes refl = yes refl
... | no neq = no λ { refl → neq refl }

-- Visible records require a matching pending packet and the endpoint's own rule.
lookup : (contract : S.Contract) (e : Event) (s : State) →
  Maybe (Σ[ t ∈ State ] Step contract s e t)
lookup p (clientSend m) (pair c s cs sc (just pending) ps rc rs)
  with clientMessageEq pending m | CE.lookup (clientSendAction m) c
... | yes refl | just (c′ , pr) = just (_ , clientSent pr)
... | _ | _ = nothing
lookup p (serverSend m) (pair c s cs sc pc (just pending) rc rs)
  with serverMessageEq pending m | SX.lookup p s (serverSendAction m)
... | yes refl | just (s′ , pr) = just (_ , serverSent pr)
... | _ | _ = nothing
lookup p (clientRecv m) (pair c s cs sc pc ps (just pending) rs)
  with serverMessageEq pending m | CE.lookup (clientRecvAction m) c
... | yes refl | just (c′ , pr) = just (_ , clientReceived pr)
... | _ | _ = nothing
lookup p (serverRecv m) (pair c s cs sc pc ps rc (just pending))
  with clientMessageEq pending m | SX.lookup p s (serverRecvAction m)
... | yes refl | just (s′ , pr) = just (_ , serverReceived pr)
... | _ | _ = nothing
lookup _ _ _ = nothing

-- Only record completion changes the endpoint continuation, never transport again.
next : S.Contract → State → Event → Maybe State
next p s e = map proj₁ (lookup p e s)

-- Every independently specified driver-record rule is implemented by lookup.
next-complete : ∀ {p s e t} → Step p s e t → next p s e ≡ just t
next-complete (clientSent {c = c} {m = m} pr)
  with clientMessageEq m m | CE.lookup (clientSendAction m) c | CE.next-complete pr
... | yes refl | just (_ , _) | refl = refl
... | no neq | _ | _ = ⊥-elim (neq refl)
next-complete {p = p} (serverSent {s = s} {m = m} pr)
  with serverMessageEq m m | SX.lookup p s (serverSendAction m) | SX.next-complete pr
... | yes refl | just (_ , _) | refl = refl
... | no neq | _ | _ = ⊥-elim (neq refl)
next-complete (clientReceived {c = c} {m = m} pr)
  with serverMessageEq m m | CE.lookup (clientRecvAction m) c | CE.next-complete pr
... | yes refl | just (_ , _) | refl = refl
... | no neq | _ | _ = ⊥-elim (neq refl)
next-complete {p = p} (serverReceived {s = s} {m = m} pr)
  with clientMessageEq m m | SX.lookup p s (serverRecvAction m) | SX.next-complete pr
... | yes refl | just (_ , _) | refl = refl
... | no neq | _ | _ = ⊥-elim (neq refl)

-- Scheduler inputs name operations and data, without supplying transition evidence.
data Choice : Set where
  clientSchedule serverSchedule : ℕ → Choice
  decide : C.Action → Choice
  ready : S.Reply → Choice
  writeClient : ClientMessage → Choice
  writeServer : ServerMessage → Choice
  readClient readServer : Choice

-- A callback classifier excludes wire events from the hidden decision channel.
callback : (a : C.Action) → Maybe (ClientCallback a)
callback (C.continue _) = just continue
callback (C.terminate _) = just terminate
callback (C.handled _) = just handled
callback _ = nothing

-- Hidden execution preserves commits, decode, callbacks and endpoint scheduling.
hidden : (p : S.Contract) (s : State) (choice : Choice) →
  Maybe (Σ[ t ∈ State ] Tau p s t)
hidden p (pair c s cs sc pc ps rc rs) (clientSchedule n) with select (CE.internalMoves c) n
... | just (c′ , pr) = just (_ , clientInternal pr)
... | nothing = nothing
hidden p (pair c s cs sc pc ps rc rs) (serverSchedule n) with select (S.internalMoves s) n
... | just (s′ , pr) = just (_ , serverInternal pr)
... | nothing = nothing
hidden p (pair c s cs sc pc ps rc rs) (decide a) with callback a | CE.lookup a c
... | just ca | just (c′ , pr) = just (_ , clientCallback ca pr)
... | _ | _ = nothing
hidden p (pair c s cs sc pc ps rc rs) (ready m) with SX.lookup p s (S.nextReply m)
... | just (s′ , pr) = just (_ , serverCallback pr)
... | nothing = nothing
hidden p (pair c s cs sc nothing ps rc rs) (writeClient m) with CE.lookup (clientSendAction m) c
... | just (c′ , pr) = just (_ , commitClient pr)
... | nothing = nothing
hidden p (pair c s cs sc pc nothing rc rs) (writeServer m) with SX.lookup p s (serverSendAction m)
... | just (s′ , pr) = just (_ , commitServer pr)
... | nothing = nothing
hidden p (pair c s cs (m ∷ sc) pc ps nothing rs) readClient with CE.lookup (clientRecvAction m) c
... | just (c′ , pr) = just (_ , decodeClient pr)
... | nothing = nothing
hidden p (pair c s (m ∷ cs) sc pc ps rc nothing) readServer with SX.lookup p s (serverRecvAction m)
... | just (s′ , pr) = just (_ , decodeServer pr)
... | nothing = nothing
hidden _ _ _ = nothing

-- Selector target lemmas unfold the interpreter after a particular operation is chosen.
client-schedule-target : ∀ {p c c′ s cs sc pc ps rc rs n} {pr : C.Tau c c′} →
  select (CE.internalMoves c) n ≡ just (c′ , pr) →
  map proj₁ (hidden p (pair c s cs sc pc ps rc rs) (clientSchedule n)) ≡
    just (pair c′ s cs sc pc ps rc rs)
client-schedule-target eq rewrite eq = refl

-- The server scheduling menu is interpreted independently of the client's menu.
server-schedule-target : ∀ {p c s s′ cs sc pc ps rc rs n} {pr : S.Tau s s′} →
  select (S.internalMoves s) n ≡ just (s′ , pr) →
  map proj₁ (hidden p (pair c s cs sc pc ps rc rs) (serverSchedule n)) ≡
    just (pair c s′ cs sc pc ps rc rs)
server-schedule-target eq rewrite eq = refl

-- Only a classified successful client callback advances the callback selector.
callback-target : ∀ {p c c′ s cs sc pc ps rc rs a} {ca : ClientCallback a} {pr : C.Step c a c′} →
  callback a ≡ just ca → CE.lookup a c ≡ just (c′ , pr) →
  map proj₁ (hidden p (pair c s cs sc pc ps rc rs) (decide a)) ≡
    just (pair c′ s cs sc pc ps rc rs)
callback-target caEq eq rewrite caEq | eq = refl

-- Readiness retains the source callback's selected exact payload.
ready-target : ∀ {p c s s′ cs sc pc ps rc rs m} {pr : S.Step p s (S.nextReply m) s′} →
  SX.lookup p s (S.nextReply m) ≡ just (s′ , pr) →
  map proj₁ (hidden p (pair c s cs sc pc ps rc rs) (ready m)) ≡
    just (pair c s′ cs sc pc ps rc rs)
ready-target eq rewrite eq = refl

-- Client channel commit records a pending Send without advancing the sending call.
write-client-target : ∀ {p c c′ s cs sc ps rc rs m} {pr : C.Step c (clientSendAction m) c′} →
  CE.lookup (clientSendAction m) c ≡ just (c′ , pr) →
  map proj₁ (hidden p (pair c s cs sc nothing ps rc rs) (writeClient m)) ≡
    just (pair c s (cs ∷ʳ m) sc (just m) ps rc rs)
write-client-target eq rewrite eq = refl

-- Server channel commit retains the selected reply until its Send record completes.
write-server-target : ∀ {p c s s′ cs sc pc rc rs m} {pr : S.Step p s (serverSendAction m) s′} →
  SX.lookup p s (serverSendAction m) ≡ just (s′ , pr) →
  map proj₁ (hidden p (pair c s cs sc pc nothing rc rs) (writeServer m)) ≡
    just (pair c s cs (sc ∷ʳ m) pc (just m) rc rs)
write-server-target eq rewrite eq = refl

-- Client decode removes precisely the existing transport head.
read-client-target : ∀ {p c c′ s cs sc pc ps rs m} {pr : C.Step c (clientRecvAction m) c′} →
  CE.lookup (clientRecvAction m) c ≡ just (c′ , pr) →
  map proj₁ (hidden p (pair c s cs (m ∷ sc) pc ps nothing rs) readClient) ≡
    just (pair c s cs sc pc ps (just m) rs)
read-client-target eq rewrite eq = refl

-- Server decode preserves that same FIFO discipline for client commands.
read-server-target : ∀ {p c s s′ cs sc pc ps rc m} {pr : S.Step p s (serverRecvAction m) s′} →
  SX.lookup p s (serverRecvAction m) ≡ just (s′ , pr) →
  map proj₁ (hidden p (pair c s (m ∷ cs) sc pc ps rc nothing) readServer) ≡
    just (pair c s cs sc pc ps rc (just m))
read-server-target eq rewrite eq = refl

-- Every hidden source rule has a concrete executable selector with the same target.
hidden-complete : ∀ {p s t} → Tau p s t →
  Σ[ choice ∈ Choice ] map proj₁ (hidden p s choice) ≡ just t
hidden-complete (clientInternal {c = c} pr) with select-complete (CE.target-complete pr)
... | n , eq with select (CE.internalMoves c) n in chosen | eq
...   | just (_ , _) | refl = clientSchedule n , client-schedule-target chosen
hidden-complete (serverInternal {s = s} pr) with select-complete (SE.target-complete pr)
... | n , eq with select (S.internalMoves s) n in chosen | eq
...   | just (_ , _) | refl = serverSchedule n , server-schedule-target chosen
hidden-complete (clientCallback {c = c} {a = a} continue pr) with CE.lookup a c in chosen | CE.next-complete pr
... | just (_ , _) | refl = decide a , callback-target refl chosen
hidden-complete (clientCallback {c = c} {a = a} terminate pr) with CE.lookup a c in chosen | CE.next-complete pr
... | just (_ , _) | refl = decide a , callback-target refl chosen
hidden-complete (clientCallback {c = c} {a = a} handled pr) with CE.lookup a c in chosen | CE.next-complete pr
... | just (_ , _) | refl = decide a , callback-target refl chosen
hidden-complete {p = p} (serverCallback {s = s} {m = m} pr)
  with SX.lookup p s (S.nextReply m) in chosen | SX.next-complete pr
... | just (_ , _) | refl = ready m , ready-target chosen
hidden-complete (commitClient {c = c} {m = m} pr) with CE.lookup (clientSendAction m) c in chosen | CE.next-complete pr
... | just (_ , _) | refl = writeClient m , write-client-target chosen
hidden-complete {p = p} (commitServer {s = s} {m = m} pr)
  with SX.lookup p s (serverSendAction m) in chosen | SX.next-complete pr
... | just (_ , _) | refl = writeServer m , write-server-target chosen
hidden-complete (decodeClient {c = c} {m = m} pr) with CE.lookup (clientRecvAction m) c in chosen | CE.next-complete pr
... | just (_ , _) | refl = readClient , read-client-target chosen
hidden-complete {p = p} (decodeServer {s = s} {m = m} pr)
  with SX.lookup p s (serverRecvAction m) in chosen | SX.next-complete pr
... | just (_ , _) | refl = readServer , read-server-target chosen
