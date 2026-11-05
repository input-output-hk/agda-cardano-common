{-# OPTIONS --guardedness #-}

-- A typed post-lexical logger schema, not JSON/Python or deployed logger refinement.
-- Independent namespace/data/message tags are checked before exact adapter transport.
-- Source boundary: consensus 2416493bfdbe93b761b3a4bb1ccf2b4a913e5e4b,
-- LeiosDemoTypes.messageLeiosNotifyToObject and LeiosDemoOnlyTestNotify's messages;
-- tools/raw-input/lookahead_raw.py canonical_notify is the separate executable check.
-- Lists below contain supplied selected Notify hooks, not every JSON/file line.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.LoggerObservation where

open import Level using (Level; _⊔_)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Properties using (∷-injectiveˡ; ∷-injectiveʳ; map-∘)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
import Cardano_network.Replay.LeiosNotifySession as Log
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Data exactParams using (header)
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Payloads.Notification as CW
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Payloads.Notification as SW
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapter as Client
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapter as Server
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.PairedAdapter as Paired

-- Logger namespace suffixes retain both accepted spellings of RequestNext.
data NamespaceTag : Set where
  requestTag notificationRequestTag announcementTag offerTag txsOfferTag votesTag : NamespaceTag
  quitTag canceledTag doneTag unsupportedTag : NamespaceTag

-- Namespace direction is independent of data.kind, including an unsupported case.
data HookDirection : Set where
  sendHook receiveHook unsupportedHook : HookDirection

-- Data.kind uses Recv rather than the namespace's Receive spelling.
data DataDirection : Set where
  sendData recvData unsupportedData : DataDirection

-- Each retained vote names its independent logger fields, after lexical validation.
record VoteFields : Set where
  constructor voteFields
  field
    rbHash voterId : ℕ
open VoteFields public

-- Typed message fields model the supported logger object, including partial announcements.
-- Naturals/hash values here assume prior valid lexical decoding; signatures are unmodeled.
data MessageFields : Set where
  requestMessage : MessageFields
  announcementMessage : (ebHash ebSlot ebBodySize : Maybe ℕ) → MessageFields
  offerMessage : (ebHash ebSlot ebBytesSize : ℕ) → MessageFields
  txsOfferMessage : (ebHash ebSlot : ℕ) → MessageFields
  votesMessage : List VoteFields → MessageFields
  quitMessage canceledMessage doneMessage unsupportedMessage : MessageFields

-- A logger hook can contain contradictory independent tags; it is not already a Log.E.
record Hook : Set where
  constructor hook
  field
    namespaceDirection : HookDirection
    namespaceTag : NamespaceTag
    dataDirection : DataDirection
    message : MessageFields
open Hook public

-- Vote observation retains both fields and every ordered occurrence.
voteSummary : VoteFields → ℕ × ℕ
voteSummary (voteFields hash voter) = hash , voter

-- Canonical reconstruction does not supply omitted signatures or other native data.
voteRepresentative : ℕ × ℕ → VoteFields
voteRepresentative (hash , voter) = voteFields hash voter

-- This universe-polymorphic mapping fact reuses any pointwise reconstruction proof.
map-retraction : ∀ {a b : Level} {A : Set a} {B : Set b}
  (f : A → B) (g : B → A) → (∀ x → g (f x) ≡ x) →
  ∀ xs → map g (map f xs) ≡ xs
map-retraction f g exact [] = refl
map-retraction f g exact (x ∷ xs) = cong₂ _∷_ (exact x) (map-retraction f g exact xs)

-- Independent vote records reconstruct exactly, preserving duplicate positions.
votes-exact : ∀ votes → map voteRepresentative (map voteSummary votes) ≡ votes
votes-exact = map-retraction voteSummary voteRepresentative (λ { (voteFields _ _) → refl })

-- Reconstructed summary votes return the original ordered value list.
vote-summaries-exact : ∀ votes → map voteSummary (map voteRepresentative votes) ≡ votes
vote-summaries-exact = map-retraction voteRepresentative voteSummary (λ { (_ , _) → refl })

-- All-absent or all-present announcement metadata is supported; partial fields fail.
messageSummary : MessageFields → Maybe Log.Msg
messageSummary requestMessage = just Log.RequestNext
messageSummary (announcementMessage nothing nothing nothing) = just (Log.BlockAnnouncement nothing)
messageSummary (announcementMessage (just h) (just s) (just z)) = just (Log.BlockAnnouncement (just (h , s , z)))
messageSummary (announcementMessage _ _ _) = nothing
messageSummary (offerMessage h s z) = just (Log.BlockOffer h s z)
messageSummary (txsOfferMessage h s) = just (Log.BlockTxsOffer h s)
messageSummary (votesMessage votes) = just (Log.Votes (map voteSummary votes))
messageSummary quitMessage = just Log.Quit
messageSummary canceledMessage = just Log.Canceled
messageSummary doneMessage = just Log.Done
messageSummary unsupportedMessage = nothing

-- Every normalized summary has a canonical logger-field representative.
messageRepresentative : Log.Msg → MessageFields
messageRepresentative Log.RequestNext = requestMessage
messageRepresentative (Log.BlockAnnouncement nothing) = announcementMessage nothing nothing nothing
messageRepresentative (Log.BlockAnnouncement (just (h , s , z))) = announcementMessage (just h) (just s) (just z)
messageRepresentative (Log.BlockOffer h s z) = offerMessage h s z
messageRepresentative (Log.BlockTxsOffer h s) = txsOfferMessage h s
messageRepresentative (Log.Votes votes) = votesMessage (map voteRepresentative votes)
messageRepresentative Log.Quit = quitMessage
messageRepresentative Log.Canceled = canceledMessage
messageRepresentative Log.Done = doneMessage

-- This retraction retains optional metadata and every exact ordered vote field.
message-roundtrip : ∀ msg → messageSummary (messageRepresentative msg) ≡ just msg
message-roundtrip Log.RequestNext = refl
message-roundtrip (Log.BlockAnnouncement nothing) = refl
message-roundtrip (Log.BlockAnnouncement (just (_ , _ , _))) = refl
message-roundtrip (Log.BlockOffer _ _ _) = refl
message-roundtrip (Log.BlockTxsOffer _ _) = refl
message-roundtrip (Log.Votes votes) rewrite vote-summaries-exact votes = refl
message-roundtrip Log.Quit = refl
message-roundtrip Log.Canceled = refl
message-roundtrip Log.Done = refl

-- Successful observation reconstructs every represented field; partial cases have no witness.
message-exact : ∀ {fields summary} → messageSummary fields ≡ just summary →
  messageRepresentative summary ≡ fields
message-exact {requestMessage} refl = refl
message-exact {announcementMessage nothing nothing nothing} refl = refl
message-exact {announcementMessage (just _) (just _) (just _)} refl = refl
message-exact {announcementMessage nothing nothing (just _)} ()
message-exact {announcementMessage nothing (just _) nothing} ()
message-exact {announcementMessage nothing (just _) (just _)} ()
message-exact {announcementMessage (just _) nothing nothing} ()
message-exact {announcementMessage (just _) nothing (just _)} ()
message-exact {announcementMessage (just _) (just _) nothing} ()
message-exact {offerMessage _ _ _} refl = refl
message-exact {txsOfferMessage _ _} refl = refl
message-exact {votesMessage votes} refl = cong votesMessage (votes-exact votes)
message-exact {quitMessage} refl = refl
message-exact {canceledMessage} refl = refl
message-exact {doneMessage} refl = refl
message-exact {unsupportedMessage} ()

-- Namespace and message constructors must agree, independently of their payload fields.
namespaceMatches : NamespaceTag → MessageFields → Bool
namespaceMatches requestTag requestMessage = true
namespaceMatches notificationRequestTag requestMessage = true
namespaceMatches announcementTag (announcementMessage _ _ _) = true
namespaceMatches offerTag (offerMessage _ _ _) = true
namespaceMatches txsOfferTag (txsOfferMessage _ _) = true
namespaceMatches votesTag (votesMessage _) = true
namespaceMatches quitTag quitMessage = true
namespaceMatches canceledTag canceledMessage = true
namespaceMatches doneTag doneMessage = true
namespaceMatches _ _ = false

-- The two independent direction tags must denote the same hook observation.
agreeDirection : HookDirection → DataDirection → Maybe Log.Direction
agreeDirection sendHook sendData = just Log.Send
agreeDirection receiveHook recvData = just Log.Recv
agreeDirection _ _ = nothing

-- Canonical data.kind for an observed normalized direction.
dataOf : Log.Direction → DataDirection
dataOf Log.Send = sendData
dataOf Log.Recv = recvData

-- A successful direction check recovers the data.kind without changing agency.
direction-exact : ∀ {ns value direction} → agreeDirection ns value ≡ just direction →
  value ≡ dataOf direction
direction-exact {sendHook} {sendData} refl = refl
direction-exact {receiveHook} {recvData} refl = refl
direction-exact {sendHook} {recvData} ()
direction-exact {sendHook} {unsupportedData} ()
direction-exact {receiveHook} {sendData} ()
direction-exact {receiveHook} {unsupportedData} ()
direction-exact {unsupportedHook} {sendData} ()
direction-exact {unsupportedHook} {recvData} ()
direction-exact {unsupportedHook} {unsupportedData} ()

-- Total typed-schema normalization preserves invalid hooks as Nothing rather than deleting rows.
normalize : Hook → Maybe Log.E
normalize (hook ns tag value fields) with agreeDirection ns value | namespaceMatches tag fields
... | nothing | _ = nothing
... | just direction | false = nothing
... | just direction | true = Maybe.map (direction ,_) (messageSummary fields)

-- The actual namespace table derives endpoint role from command/reply agency and direction.
-- There is no explicit Client/Server field in the raw namespace modeled here.
summaryRole : Log.E → Log.Role
summaryRole (Log.Send , Log.RequestNext) = Log.client
summaryRole (Log.Send , Log.Quit) = Log.client
summaryRole (Log.Recv , Log.RequestNext) = Log.server
summaryRole (Log.Recv , Log.Quit) = Log.server
summaryRole (Log.Send , _) = Log.server
summaryRole (Log.Recv , _) = Log.client

-- Derive namespace agency only after all independent namespace/data/message checks succeed.
-- File/session selection, actual peer entry points and provenance remain external.
observedRole : Hook → Maybe Log.Role
observedRole event = Maybe.map summaryRole (normalize event)

-- Every client wire encoding has exactly the initiating-side namespace agency.
client-encode-role : ∀ row → summaryRole (Client.encode row) ≡ Log.client
client-encode-role CW.request = refl
client-encode-role CW.quit = refl
client-encode-role CW.done = refl
client-encode-role (CW.reply S.canceled) = refl
client-encode-role (CW.reply (S.normal (Payloads.announcement (header _)))) = refl
client-encode-role (CW.reply (S.normal (Payloads.offer _ _))) = refl
client-encode-role (CW.reply (S.normal (Payloads.txsOffer _))) = refl
client-encode-role (CW.reply (S.normal (Payloads.votes _))) = refl

-- Every server wire encoding has the responder-side namespace agency.
server-encode-role : ∀ row → summaryRole (Server.encode row) ≡ Log.server
server-encode-role SW.request = refl
server-encode-role SW.quit = refl
server-encode-role SW.done = refl
server-encode-role (SW.reply S.canceled) = refl
server-encode-role (SW.reply (S.normal (Payloads.announcement (header _)))) = refl
server-encode-role (SW.reply (S.normal (Payloads.offer _ _))) = refl
server-encode-role (SW.reply (S.normal (Payloads.txsOffer _))) = refl
server-encode-role (SW.reply (S.normal (Payloads.votes _))) = refl

-- Independent evidence identifies the checked namespace, direction and complete retained fields.
record Faithful (event : Hook) (summary : Log.E) : Set where
  constructor faithful
  field
    namespace-match : namespaceMatches (namespaceTag event) (message event) ≡ true
    direction-match : agreeDirection (namespaceDirection event) (dataDirection event) ≡ just (proj₁ summary)
    data-match : dataDirection event ≡ dataOf (proj₁ summary)
    fields-exact : messageRepresentative (proj₂ summary) ≡ message event
open Faithful public

-- Inverting a successful Maybe post-map retains the actual pre-map value and its image.
map-present : ∀ {a b : Level} {A : Set a} {B : Set b} {f : A → B} {value summary} →
  Maybe.map f value ≡ just summary → Σ[ x ∈ A ] (value ≡ just x × f x ≡ summary)
map-present {value = nothing} ()
map-present {value = just x} refl = x , refl , refl

-- Every successful typed normalization retains all fields and validates the independent tags.
normalize-faithful : ∀ {event summary} → normalize event ≡ just summary → Faithful event summary
normalize-faithful {hook ns tag value fields} same
  with agreeDirection ns value in direction | namespaceMatches tag fields in namespace | same
... | nothing | _ | ()
... | just d | false | ()
... | just d | true | valid with map-present {f = (d ,_)} {value = messageSummary fields} valid
...   | msg , payload , refl = faithful namespace direction (direction-exact direction) (message-exact payload)

-- Conversely, explicit agreement and exact retained fields justify the same computed normalization.
faithful-normalize : ∀ {event summary} → Faithful event summary → normalize event ≡ just summary
faithful-normalize {hook ns tag value fields} {direction , msg}
  (faithful namespace directionSame dataSame exact)
  rewrite directionSame | namespace | sym exact | message-roundtrip msg = refl

-- The full hook is not injective: accepted namespace aliases deliberately have the same observation.
faithful-unique : ∀ {event first second} → Faithful event first → Faithful event second → first ≡ second
faithful-unique first second = just-injective (trans (sym (faithful-normalize first)) (faithful-normalize second))

-- Canonical namespace tags choose RequestNext while normalization also accepts its alias.
tagOf : Log.Msg → NamespaceTag
tagOf Log.RequestNext = requestTag
tagOf (Log.BlockAnnouncement _) = announcementTag
tagOf (Log.BlockOffer _ _ _) = offerTag
tagOf (Log.BlockTxsOffer _ _) = txsOfferTag
tagOf (Log.Votes _) = votesTag
tagOf Log.Quit = quitTag
tagOf Log.Canceled = canceledTag
tagOf Log.Done = doneTag

-- Canonical namespace direction spelling for a normalized event.
hookOf : Log.Direction → HookDirection
hookOf Log.Send = sendHook
hookOf Log.Recv = receiveHook

-- Canonical typed hooks realize all normalized summary fields without adding native data.
representative : Log.E → Hook
representative (direction , msg) = hook (hookOf direction) (tagOf msg) (dataOf direction) (messageRepresentative msg)

-- Canonical representatives retain matching namespace/message tags for all exact payloads.
canonical-namespace : ∀ msg → namespaceMatches (tagOf msg) (messageRepresentative msg) ≡ true
canonical-namespace Log.RequestNext = refl
canonical-namespace (Log.BlockAnnouncement nothing) = refl
canonical-namespace (Log.BlockAnnouncement (just (_ , _ , _))) = refl
canonical-namespace (Log.BlockOffer _ _ _) = refl
canonical-namespace (Log.BlockTxsOffer _ _) = refl
canonical-namespace (Log.Votes _) = refl
canonical-namespace Log.Quit = refl
canonical-namespace Log.Canceled = refl
canonical-namespace Log.Done = refl

-- Canonical direction spellings agree without identifying independent logger tags by fiat.
canonical-direction : ∀ direction → agreeDirection (hookOf direction) (dataOf direction) ≡ just direction
canonical-direction Log.Send = refl
canonical-direction Log.Recv = refl

-- Every normalized event has a genuine successful typed-schema representative.
normalize-representative : ∀ event → normalize (representative event) ≡ just event
normalize-representative (direction , msg) = faithful-normalize
  (faithful (canonical-namespace msg) (canonical-direction direction) refl refl)

-- A reusable row relation preserves failed mapping outcomes instead of implementing mapMaybe.
data Mapped {a b : Level} {A : Set a} {B : Set b} (f : A → Maybe B) : List A → List B → Set (a ⊔ b) where
  empty : Mapped f [] []
  linked : ∀ {x xs y ys} → f x ≡ just y → Mapped f xs ys → Mapped f (x ∷ xs) (y ∷ ys)

-- Generic mapping evidence gives an exact ordered re-encoding equation, including duplicate positions.
mapped-equation : ∀ {a b : Level} {A : Set a} {B : Set b} {f : A → Maybe B} {xs ys} →
  Mapped f xs ys → map f xs ≡ map just ys
mapped-equation empty = refl
mapped-equation (linked same rest) = cong₂ _∷_ same (mapped-equation rest)

-- Exact successful output equations reconstruct complete pointwise witnesses.
equation-mapped : ∀ {a b : Level} {A : Set a} {B : Set b} {f : A → Maybe B} {xs ys} →
  map f xs ≡ map just ys → Mapped f xs ys
equation-mapped {xs = []} {[]} refl = empty
equation-mapped {xs = []} {_ ∷ _} ()
equation-mapped {xs = _ ∷ _} {[]} ()
equation-mapped {xs = _ ∷ _} {_ ∷ _} same = linked (∷-injectiveˡ same) (equation-mapped (∷-injectiveʳ same))

-- The generic relation always retains one output position for each original input.
mapped-length : ∀ {a b : Level} {A : Set a} {B : Set b} {f : A → Maybe B} {xs ys} →
  Mapped f xs ys → length ys ≡ length xs
mapped-length empty = refl
mapped-length (linked _ rest) = cong suc (mapped-length rest)

-- Deterministic pointwise mapping makes the entire ordered output list unique.
mapped-unique : ∀ {a b : Level} {A : Set a} {B : Set b} {f : A → Maybe B} {xs first second} →
  Mapped f xs first → Mapped f xs second → first ≡ second
mapped-unique empty empty = refl
mapped-unique (linked first rest) (linked second later) =
  cong₂ _∷_ (just-injective (trans (sym first) second)) (mapped-unique rest later)

-- A reusable post-map preserves all successful row witnesses without deleting failed inputs.
mapped-postmap : ∀ {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
  {f : A → Maybe B} {xs ys} (g : B → C) → Mapped f xs ys →
  Mapped (λ x → Maybe.map g (f x)) xs (map g ys)
mapped-postmap g empty = empty
mapped-postmap g (linked same rest) = linked (cong (Maybe.map g) same) (mapped-postmap g rest)

-- The parser-outcome input contains every original hook, including invalid outcomes.
input : List Hook → Client.Input
input = map normalize

-- Successful typed logger observation is the generic ordered row relation specialized to this schema.
Observation : List Hook → List Log.E → Set
Observation = Mapped normalize

-- Existing adapter input is recovered exactly; this is the explicit transport premise.
observation-input : ∀ {hooks events} → Observation hooks events → input hooks ≡ Client.present events
observation-input = mapped-equation

-- Canonical lists provide inhabited observation premises at every normalized summary list.
representative-list : ∀ events → Observation (map representative events) events
representative-list [] = empty
representative-list (event ∷ events) = linked (normalize-representative event) (representative-list events)

-- A successful client adaptation cannot silently have omitted an invalid typed hook.
client-observation : ∀ {hooks rows} → Client.Rows (input hooks) rows →
  Observation hooks (map Client.encode rows)
client-observation {rows = rows} valid = equation-mapped (trans (sym (Client.roundtrip valid)) (map-∘ rows))

-- The corresponding server result reconstructs all original ordered summary observations.
server-observation : ∀ {hooks rows} → Server.Rows (input hooks) rows →
  Observation hooks (map Server.encode rows)
server-observation {rows = rows} valid = equation-mapped (trans (sym (Server.roundtrip valid)) (map-∘ rows))

-- Client summaries all carry client agency, including arbitrary exact notification fields.
client-summary-roles : ∀ rows → map summaryRole (map Client.encode rows) ≡ map (λ _ → Log.client) rows
client-summary-roles [] = refl
client-summary-roles (row ∷ rows) = cong₂ _∷_ (client-encode-role row) (client-summary-roles rows)

-- Server summaries carry server agency at each original ordered position.
server-summary-roles : ∀ rows → map summaryRole (map Server.encode rows) ≡ map (λ _ → Log.server) rows
server-summary-roles [] = refl
server-summary-roles (row ∷ rows) = cong₂ _∷_ (server-encode-role row) (server-summary-roles rows)

-- Successful client adaptation proves every supplied selected hook has client namespace agency.
client-roles-preserved : ∀ {hooks rows} → Client.Rows (input hooks) rows →
  Mapped observedRole hooks (map (λ _ → Log.client) rows)
client-roles-preserved {hooks} {rows} valid =
  subst (Mapped observedRole hooks) (client-summary-roles rows)
    (mapped-postmap summaryRole (client-observation valid))

-- Successful server adaptation likewise cannot accept a hook with client namespace agency.
server-roles-preserved : ∀ {hooks rows} → Server.Rows (input hooks) rows →
  Mapped observedRole hooks (map (λ _ → Log.server) rows)
server-roles-preserved {hooks} {rows} valid =
  subst (Mapped observedRole hooks) (server-summary-roles rows)
    (mapped-postmap summaryRole (server-observation valid))

-- Client source-language acceptance transports through exact typed-hook observation in either direction.
client-transport : ∀ {role hooks events} → Observation hooks events →
  (Client.Accepted role (input hooks) → Client.Accepted role (Client.present events)) ×
  (Client.Accepted role (Client.present events) → Client.Accepted role (input hooks))
client-transport {role} observed =
  subst (Client.Accepted role) (observation-input observed) ,
  subst (Client.Accepted role) (sym (observation-input observed))

-- Server callback contract remains explicit when transporting the exact source acceptance language.
server-transport : ∀ contract {role hooks events} → Observation hooks events →
  (Server.Accepted contract role (input hooks) → Server.Accepted contract role (Server.present events)) ×
  (Server.Accepted contract role (Server.present events) → Server.Accepted contract role (input hooks))
server-transport contract {role} observed =
  subst (Server.Accepted contract role) (observation-input observed) ,
  subst (Server.Accepted contract role) (sym (observation-input observed))

-- Two local observations preserve the paired language without guessing any cross-endpoint timestamp merge.
paired-transport : ∀ contract {cr sr clientHooks serverHooks clientEvents serverEvents} →
  Observation clientHooks clientEvents → Observation serverHooks serverEvents →
  (Paired.Accepted contract cr (input clientHooks) sr (input serverHooks) →
   Paired.Accepted contract cr (Paired.present clientEvents) sr (Paired.present serverEvents)) ×
  (Paired.Accepted contract cr (Paired.present clientEvents) sr (Paired.present serverEvents) →
   Paired.Accepted contract cr (input clientHooks) sr (input serverHooks))
paired-transport contract {cr} {sr} clientObserved serverObserved
  rewrite observation-input clientObserved | observation-input serverObserved = (λ witness → witness) , (λ witness → witness)
