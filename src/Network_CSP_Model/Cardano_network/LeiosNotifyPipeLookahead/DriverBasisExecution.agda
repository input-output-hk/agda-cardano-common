{-# OPTIONS --safe #-}

-- Finite hidden successors for basis-restricted generic callbacks at unit return.
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.List using (List)
module Cardano_network.LeiosNotifyPipeLookahead.DriverBasisExecution
  (Notification : Set) (notificationEq : DecidableEquality Notification)
  (basis : List Notification) where

open import Data.Unit using (⊤)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_; map; concat)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-concat⁺′)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.ClientExecution Notification ⊤ notificationEq as CE
import Cardano_network.LeiosNotifyPipeLookahead.ClientCallbackBasis Notification as CB
import Cardano_network.LeiosNotifyPipeLookahead.Enumeration Notification as SE
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasis Notification ⊤ basis as B
module SX = S.Executable notificationEq

-- Every finite candidate retains evidence for the restricted, rather than raw, relation.
Move : S.Contract → D.State → Set
Move p s = Σ[ t ∈ D.State ] B.Tau p s t

-- Lifting client scheduling changes only the current client continuation.
liftClient : ∀ p (s : D.State) → CE.Internal (D.clientState s) → Move p s
liftClient p (D.pair c server cs sc pc ps rc rs) (next , pr) =
  D.pair next server cs sc pc ps rc rs , B.clientInternal pr

-- Lifting server scheduling leaves both channel FIFOs and all pending hooks intact.
liftServer : ∀ p (s : D.State) → S.Internal (D.serverState s) → Move p s
liftServer p (D.pair c server cs sc pc ps rc rs) (next , pr) =
  D.pair c next cs sc pc ps rc rs , B.serverInternal pr

-- The proven finite callback target basis preserves all signed-depth choices exactly.
liftCallback : ∀ p (s : D.State) → CB.Move (D.clientState s) → Move p s
liftCallback p (D.pair c server cs sc pc ps rc rs) (next , action , classification , pr) =
  D.pair next server cs sc pc ps rc rs , B.clientCallback classification pr

-- Internal client successors are already certified independently of this driver menu.
clientMoves : ∀ p (s : D.State) → List (Move p s)
clientMoves p s = map (liftClient p s) (CE.internalMoves (D.clientState s))

-- Internal server choices retain admission, excess-request fault and cancellation alternatives.
serverMoves : ∀ p (s : D.State) → List (Move p s)
serverMoves p s = map (liftServer p s) (S.internalMoves (D.serverState s))

-- Main callback and handler choices stay available concurrently.
callbackMoves : ∀ p (s : D.State) → List (Move p s)
callbackMoves p s = map (liftCallback p s) (CB.moves (D.clientState s))

-- Normal choices carry membership in the supplied list, which may contain duplicates.
normalChoices : (xs : List Notification) →
  (∀ {m} → m ∈ xs → m ∈ basis) → List (Σ[ m ∈ S.Reply ] B.AllowedReply m)
normalChoices [] include = []
normalChoices (m ∷ xs) include =
  (S.normal m , B.allowNormal (include (here refl))) ∷
  normalChoices xs (λ member → include (there member))

-- Cancellation is a finite generic result and is still checked against the source contract.
replyChoices : List (Σ[ m ∈ S.Reply ] B.AllowedReply m)
replyChoices = normalChoices basis (λ member → member) ++ ((S.canceled , B.allowCanceled) ∷ [])

-- Readiness enumerates only supplied normal values and cancellation, with actual source guards.
readyOne : ∀ p (s : D.State) → (Σ[ m ∈ S.Reply ] B.AllowedReply m) → List (Move p s)
readyOne p (D.pair c server cs sc pc ps rc rs) (m , allowed)
  with SX.lookup p server (S.nextReply m)
... | just (next , pr) = (D.pair c next cs sc pc ps rc rs , B.serverCallback allowed pr) ∷ []
... | nothing = []

-- Every candidate callback result is independently enabled or absent at the current source state.
readyMoves : ∀ p (s : D.State) → List (Move p s)
readyMoves p s = concat (map (readyOne p s) replyChoices)

-- Commit tests Request and Quit only when the pending client Send slot is empty.
clientCommitOne : ∀ p (s : D.State) → D.ClientMessage → List (Move p s)
clientCommitOne p (D.pair c server cs sc nothing ps rc rs) m
  with CE.lookup (D.clientSendAction m) c
... | just (next , pr) = (D.pair c server (cs ∷ʳ m) sc (just m) ps rc rs , B.commitClient pr) ∷ []
... | nothing = []
clientCommitOne _ _ _ = []

-- The entire initiator wire-message type is this fixed two-element candidate list.
clientCommitMoves : ∀ p (s : D.State) → List (Move p s)
clientCommitMoves p s = clientCommitOne p s D.request ++ clientCommitOne p s D.quit

-- A server commit uses its actual current selected value, without inventing payloads.
serverCommitOne : ∀ p (s : D.State) → D.ServerMessage → List (Move p s)
serverCommitOne p (D.pair c server cs sc pc nothing rc rs) m
  with SX.lookup p server (D.serverSendAction m)
... | just (next , pr) = (D.pair c server cs (sc ∷ʳ m) pc (just m) rc rs , B.commitServer pr) ∷ []
... | nothing = []
serverCommitOne _ _ _ = []

-- Only a selected reply can commit a reply packet; Done is tested separately.
selectedCommitMoves : ∀ p (s : D.State) → List (Move p s)
selectedCommitMoves p s with S.sender (D.serverState s)
... | S.selected m = serverCommitOne p s (D.reply m)
... | _ = []

-- The server message menu is finite even for an infinite notification carrier.
serverCommitMoves : ∀ p (s : D.State) → List (Move p s)
serverCommitMoves p s = serverCommitOne p s D.done ++ selectedCommitMoves p s

-- Client decoding can consume only the actual transport head into an empty Receive slot.
clientDecodeMoves : ∀ p (s : D.State) → List (Move p s)
clientDecodeMoves p (D.pair c server cs (m ∷ sc) pc ps nothing rs)
  with CE.lookup (D.clientRecvAction m) c
... | just (next , pr) = (D.pair c server cs sc pc ps (just m) rs , B.decodeClient pr) ∷ []
... | nothing = []
clientDecodeMoves _ _ = []

-- Server decoding uses the analogous command FIFO head, preserving physical packet order.
serverDecodeMoves : ∀ p (s : D.State) → List (Move p s)
serverDecodeMoves p (D.pair c server (m ∷ cs) sc pc ps rc nothing)
  with SX.lookup p server (D.serverRecvAction m)
... | just (next , pr) = (D.pair c server cs sc pc ps rc (just m) , B.decodeServer pr) ∷ []
... | nothing = []
serverDecodeMoves _ _ = []

-- Eight independent operation families preserve all source interleavings.
menus : ∀ p (s : D.State) → List (List (Move p s))
menus p s = clientMoves p s ∷ serverMoves p s ∷ callbackMoves p s ∷ readyMoves p s ∷
  clientCommitMoves p s ∷ serverCommitMoves p s ∷ clientDecodeMoves p s ∷ serverDecodeMoves p s ∷ []

-- The finite menu contains evidence before erasing any target certificates.
moves : ∀ p (s : D.State) → List (Move p s)
moves p s = concat (menus p s)

-- Replay consumes only these state targets and reconstructs evidence by membership.
targets : S.Contract → D.State → List D.State
targets p s = map proj₁ (moves p s)

-- Every listed state is a basis-restricted hidden successor, including all packet movements.
target-sound : ∀ {p s t} → t ∈ targets p s → B.Tau p s t
target-sound member with ∈-map⁻ proj₁ member
... | (_ , pr) , _ , refl = pr

-- Membership in one independent operation menu embeds in the complete target list.
listed : ∀ {p s t menu} → menu ∈ menus p s → t ∈ map proj₁ menu → t ∈ targets p s
listed family member with ∈-map⁻ proj₁ member
... | move , inMenu , refl = ∈-map⁺ proj₁ (∈-concat⁺′ inMenu family)

-- A member of the supplied normal list appears with some valid fixed-basis certificate.
normal-listed : (xs : List Notification) (include : ∀ {m} → m ∈ xs → m ∈ basis) →
  ∀ {m} → m ∈ xs →
  S.normal m ∈ map proj₁ (normalChoices xs include)
normal-listed (_ ∷ xs) include (here refl) = here refl
normal-listed (_ ∷ xs) include (there member) = there (normal-listed xs (λ proof → include (there proof)) member)

-- Every independently permitted callback value is present in the finite result menu.
reply-listed : ∀ {m} → B.AllowedReply m → m ∈ map proj₁ replyChoices
reply-listed (B.allowNormal member) with ∈-map⁻ proj₁ (normal-listed basis (λ proof → proof) member)
... | choice , listed , refl = ∈-map⁺ proj₁ (∈-++⁺ˡ listed)
reply-listed B.allowCanceled = ∈-map⁺ proj₁
  (∈-++⁺ʳ (normalChoices basis (λ proof → proof)) (here refl))

-- Targets from one candidate operation embed through both map and concatenation.
part-listed : ∀ {p s} {A : Set} {choices : List A} (select : A → List (Move p s)) {choice t} →
  choice ∈ choices → t ∈ map proj₁ (select choice) →
  t ∈ map proj₁ (concat (map select choices))
part-listed select candidate target with ∈-map⁻ proj₁ target
... | move , inPart , refl = ∈-map⁺ proj₁ (∈-concat⁺′ inPart (∈-map⁺ select candidate))

-- A successful source lookup includes readiness regardless of proof identity.
readyOne-complete : ∀ {p c server next cs sc pc ps rc rs m} (allowed : B.AllowedReply m) →
  S.Step p server (S.nextReply m) next →
  D.pair c next cs sc pc ps rc rs ∈
    map proj₁ (readyOne p (D.pair c server cs sc pc ps rc rs) (m , allowed))
readyOne-complete {p} {server = server} {m = m} allowed pr
  with SX.lookup p server (S.nextReply m) | SX.next-complete pr
... | just (_ , _) | refl = here refl

-- Finite readiness omits no allowed independently guarded source callback target.
ready-complete : ∀ {p c server next cs sc pc ps rc rs m} →
  B.AllowedReply m → S.Step p server (S.nextReply m) next →
  D.pair c next cs sc pc ps rc rs ∈ map proj₁ (readyMoves p (D.pair c server cs sc pc ps rc rs))
ready-complete {p} {c} {server} {cs = cs} {sc} {pc} {ps} {rc} {rs} allowed pr
  with ∈-map⁻ proj₁ (reply-listed allowed)
... | (m , actual) , candidate , refl =
  part-listed (readyOne p (D.pair c server cs sc pc ps rc rs)) candidate (readyOne-complete actual pr)

-- Physical client commit completeness follows exact independent client lookup completeness.
clientCommitOne-complete : ∀ {p c next server cs sc ps rc rs m} →
  C.Step c (D.clientSendAction m) next →
  D.pair c server (cs ∷ʳ m) sc (just m) ps rc rs ∈
    map proj₁ (clientCommitOne p (D.pair c server cs sc nothing ps rc rs) m)
clientCommitOne-complete {c = c} {m = m} pr with CE.lookup (D.clientSendAction m) c | CE.next-complete pr
... | just (_ , _) | refl = here refl

-- Physical server commit completeness retains the already selected exact message.
serverCommitOne-complete : ∀ {p c server next cs sc pc rc rs m} →
  S.Step p server (D.serverSendAction m) next →
  D.pair c server cs (sc ∷ʳ m) pc (just m) rc rs ∈
    map proj₁ (serverCommitOne p (D.pair c server cs sc pc nothing rc rs) m)
serverCommitOne-complete {p} {server = server} {m = m} pr
  with SX.lookup p server (D.serverSendAction m) | SX.next-complete pr
... | just (_ , _) | refl = here refl

-- Actual FIFO-head client decoding is included whenever its source action is enabled.
clientDecode-complete : ∀ {p c next server cs sc pc ps rs m} →
  C.Step c (D.clientRecvAction m) next →
  D.pair c server cs sc pc ps (just m) rs ∈
    map proj₁ (clientDecodeMoves p (D.pair c server cs (m ∷ sc) pc ps nothing rs))
clientDecode-complete {c = c} {m = m} pr with CE.lookup (D.clientRecvAction m) c | CE.next-complete pr
... | just (_ , _) | refl = here refl

-- Actual FIFO-head command decoding obeys the same source-based completeness guarantee.
serverDecode-complete : ∀ {p c server next cs sc pc ps rc m} →
  S.Step p server (D.serverRecvAction m) next →
  D.pair c server cs sc pc ps rc (just m) ∈
    map proj₁ (serverDecodeMoves p (D.pair c server (m ∷ cs) sc pc ps rc nothing))
serverDecode-complete {p} {server = server} {m = m} pr
  with SX.lookup p server (D.serverRecvAction m) | SX.next-complete pr
... | just (_ , _) | refl = here refl

-- Every basis-restricted hidden source step has its exact target in the finite menu.
target-complete : ∀ {p s t} → B.Tau p s t → t ∈ targets p s
target-complete {p} {s} (B.clientInternal pr) with ∈-map⁻ proj₁ (CE.target-complete pr)
... | move , member , refl = listed (here refl) (∈-map⁺ proj₁ (∈-map⁺ (liftClient p s) member))
target-complete {p} {s} (B.serverInternal pr) with ∈-map⁻ proj₁ (SE.target-complete pr)
... | move , member , refl = listed (there (here refl)) (∈-map⁺ proj₁ (∈-map⁺ (liftServer p s) member))
target-complete {p} {s} (B.clientCallback classification pr) with ∈-map⁻ proj₁ (CB.complete (_ , classification , pr))
... | move , member , refl = listed (there (there (here refl))) (∈-map⁺ proj₁ (∈-map⁺ (liftCallback p s) member))
target-complete (B.serverCallback allowed pr) = listed (there (there (there (here refl)))) (ready-complete allowed pr)
target-complete (B.commitClient {message = D.request} pr) =
  listed (there (there (there (there (here refl))))) (client-request-listed pr)
  where
  -- Request is the first physical client commit candidate.
  client-request-listed : ∀ {p c next server cs sc ps rc rs} (pr : C.Step c C.sendRequest next) →
    D.pair c server (cs ∷ʳ D.request) sc (just D.request) ps rc rs ∈
      map proj₁ (clientCommitMoves p (D.pair c server cs sc nothing ps rc rs))
  client-request-listed pr with ∈-map⁻ proj₁ (clientCommitOne-complete pr)
  ... | move , member , refl = ∈-map⁺ proj₁ (∈-++⁺ˡ member)
target-complete (B.commitClient {message = D.quit} pr) =
  listed (there (there (there (there (here refl))))) (client-quit-listed pr)
  where
  -- Quit is the second physical client commit candidate.
  client-quit-listed : ∀ {p c next server cs sc ps rc rs} (pr : C.Step c C.sendQuit next) →
    D.pair c server (cs ∷ʳ D.quit) sc (just D.quit) ps rc rs ∈
      map proj₁ (clientCommitMoves p (D.pair c server cs sc nothing ps rc rs))
  client-quit-listed {p} {c} {server = server} {cs} {sc} {ps} {rc} {rs} pr
    with ∈-map⁻ proj₁ (clientCommitOne-complete pr)
  ... | move , member , refl = ∈-map⁺ proj₁
    (∈-++⁺ʳ (clientCommitOne p (D.pair c server cs sc nothing ps rc rs) D.request) member)
target-complete (B.commitServer {message = D.done} pr) =
  listed (there (there (there (there (there (here refl)))))) (server-done-listed pr)
  where
  -- Done is the first physical server commit candidate.
  server-done-listed : ∀ {p c server next cs sc pc rc rs} (pr : S.Step p server S.sendDone next) →
    D.pair c server cs (sc ∷ʳ D.done) pc (just D.done) rc rs ∈
      map proj₁ (serverCommitMoves p (D.pair c server cs sc pc nothing rc rs))
  server-done-listed pr with ∈-map⁻ proj₁ (serverCommitOne-complete pr)
  ... | move , member , refl = ∈-map⁺ proj₁ (∈-++⁺ˡ member)
target-complete (B.commitServer {message = D.reply m} (S.send {r} {w} {c = completed} {q} active)) =
  listed (there (there (there (there (there (here refl)))))) (server-reply-listed active)
  where
  -- The sender's selected value is the only reply commit candidate.
  server-reply-listed : ∀ {p c cs sc pc rc rs} (active : S.active r ≡ true) →
    D.pair c (S.state r w (S.selected m) completed q) cs (sc ∷ʳ D.reply m) pc (just (D.reply m)) rc rs ∈
      map proj₁ (serverCommitMoves p (D.pair c (S.state r w (S.selected m) completed q) cs sc pc nothing rc rs))
  server-reply-listed {p} {c} {cs} {sc} {pc} {rc} {rs} active
    with ∈-map⁻ proj₁ (serverCommitOne-complete (S.send active))
  ... | move , member , refl = ∈-map⁺ proj₁
    (∈-++⁺ʳ (serverCommitOne p (D.pair c (S.state r w (S.selected m) completed q) cs sc pc nothing rc rs) D.done) member)
target-complete (B.decodeClient pr) =
  listed (there (there (there (there (there (there (here refl))))))) (clientDecode-complete pr)
target-complete (B.decodeServer pr) =
  listed (there (there (there (there (there (there (there (here refl)))))))) (serverDecode-complete pr)
