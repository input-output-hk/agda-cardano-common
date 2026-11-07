{-# OPTIONS --safe #-}

-- Paired replay of two silenced endpoint logs (RequestNext and hidden normal replies erased).
-- Acceptance is certified through one canonical reconstruction; rejection is certified only by
-- the exact local silenced languages; anything else is reported as undetermined.
open import Data.Bool using (Bool)
open import Relation.Binary.Definitions using (DecidableEquality)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.PairedSilenced
  (Notification : Set) (notificationEq : DecidableEquality Notification)
  (representative : Notification) (hidden : Notification → Bool) where

open import Data.Bool using (T)
open import Data.List using (List; []; _∷_; _++_; map; replicate; filterᵇ)
open import Data.List.Properties using (filter-accept; filter-reject; filter-all)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (all-filter; map⁺; map⁻)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (T?)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification ⊤ as Rows
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Notification as CW
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Notification as SW
import Cardano_network.LeiosNotifyPipeLookahead.Wire.ClientSilenced Notification hidden as CS
import Cardano_network.LeiosNotifyPipeLookahead.Wire.ServerSilenced Notification hidden as SS
import Cardano_network.Replay.LeiosNotifyPipeLookahead.LocalPrecheck Notification ⊤ as Local
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecide Notification notificationEq representative
  as Check

------------------------------------------------------------------------
-- Generic filter facts

-- Mapping commutes with filtering by a predicate on the image.
map-filterᵇ : ∀ {A B : Set} (f : A → B) (p : B → Bool) xs →
  map f (filterᵇ (p ∘ f) xs) ≡ filterᵇ p (map f xs)
map-filterᵇ f p [] = refl
map-filterᵇ f p (x ∷ xs) with T? (p (f x))
... | yes px = trans (cong (map f) (filter-accept (T? ∘ (p ∘ f)) px))
  (trans (cong (f x ∷_) (map-filterᵇ f p xs)) (sym (filter-accept (T? ∘ p) px)))
... | no ¬px = trans (cong (map f) (filter-reject (T? ∘ (p ∘ f)) ¬px))
  (trans (map-filterᵇ f p xs) (sym (filter-reject (T? ∘ p) ¬px)))

-- Equal filtered tails stay equal under a common head.
filterᵇ-cons : ∀ {A : Set} (p : A → Bool) x {ys zs} →
  filterᵇ p ys ≡ filterᵇ p zs → filterᵇ p (x ∷ ys) ≡ filterᵇ p (x ∷ zs)
filterᵇ-cons p x same with T? (p x)
... | yes px = trans (filter-accept (T? ∘ p) px) (trans (cong (x ∷_) same) (sym (filter-accept (T? ∘ p) px)))
... | no ¬px = trans (filter-reject (T? ∘ p) ¬px) (trans same (sym (filter-reject (T? ∘ p) ¬px)))

------------------------------------------------------------------------
-- Row-level erasure

-- A client row survives the silenced logger exactly when its wire image does.
clientVisible : Rows.ClientRow → Bool
clientVisible = CS.visible ∘ Local.clientWire

-- A server row survives the silenced logger exactly when its wire image does.
serverVisible : Rows.ServerRow → Bool
serverVisible = SS.visible ∘ Local.serverWire

-- Visibility as a proposition on client rows.
ClientVisible : Rows.ClientRow → Set
ClientVisible = T ∘ clientVisible

-- Visibility as a proposition on server rows.
ServerVisible : Rows.ServerRow → Set
ServerVisible = T ∘ serverVisible

-- The logged projection of a full client row list.
eraseClient : List Rows.ClientRow → List Rows.ClientRow
eraseClient = filterᵇ clientVisible

-- The logged projection of a full server row list.
eraseServer : List Rows.ServerRow → List Rows.ServerRow
eraseServer = filterᵇ serverVisible

-- Some full paired source prefix whose two silenced projections are exactly the observed logs.
SilencedSourceTrace : S.Contract → List Rows.ClientRow → List Rows.ServerRow → Set
SilencedSourceTrace contract c s = Σ[ c′ ∈ List Rows.ClientRow ] Σ[ s′ ∈ List Rows.ServerRow ]
  (Check.SourceTrace contract c′ s′ × eraseClient c′ ≡ c × eraseServer s′ ≡ s)

-- Row erasure is wire erasure under the client wire translation.
client-erase-wire : ∀ c → CS.erase (map Local.clientWire c) ≡ map Local.clientWire (eraseClient c)
client-erase-wire c = sym (map-filterᵇ Local.clientWire CS.visible c)

-- Row erasure is wire erasure under the server wire translation.
server-erase-wire : ∀ s → SS.erase (map Local.serverWire s) ≡ map Local.serverWire (eraseServer s)
server-erase-wire s = sym (map-filterᵇ Local.serverWire SS.visible s)

------------------------------------------------------------------------
-- Necessity of the two local silenced languages

-- Every paired silenced witness erases each endpoint's actual full local wire trace.
local-necessary : ∀ {contract c s} → SilencedSourceTrace contract c s →
  CS.Silenced (map Local.clientWire c) × SS.Silenced contract (map Local.serverWire s)
local-necessary (c′ , s′ , (_ , merged , _ , run) , refl , refl) with Local.necessary merged run
... | client , server =
  (map Local.clientWire c′ , client , client-erase-wire c′) ,
  (map Local.serverWire s′ , server , server-erase-wire s′)

-- Every row of a silenced client log is visible.
client-visible : ∀ {c} → CS.Silenced (map Local.clientWire c) → All ClientVisible c
client-visible (ws , _ , same) = map⁻ (subst (All (T ∘ CS.visible)) same (all-filter (T? ∘ CS.visible) ws))

-- Every row of a silenced server log is visible.
server-visible : ∀ {contract s} → SS.Silenced contract (map Local.serverWire s) → All ServerVisible s
server-visible (ws , _ , same) = map⁻ (subst (All (T ∘ SS.visible)) same (all-filter (T? ∘ SS.visible) ws))

------------------------------------------------------------------------
-- Canonical reconstruction

-- Client silenced rows with the local client fill reinserted.
fillClient : List Rows.ClientRow → List Rows.ClientRow
fillClient c = map Local.clientRow (CS.fill (map Local.clientWire c))

-- Server silenced rows with the local server fill reinserted.
fillServer : List Rows.ServerRow → List Rows.ServerRow
fillServer s = map Local.serverRow (SS.fill (map Local.serverWire s))

-- Number of client Request sends.
clientRequests : List Rows.ClientRow → ℕ
clientRequests [] = 0
clientRequests (Rows.sendCommand D.request ∷ rows) = suc (clientRequests rows)
clientRequests (_ ∷ rows) = clientRequests rows

-- Number of server Request receives.
serverRequests : List Rows.ServerRow → ℕ
serverRequests [] = 0
serverRequests (Rows.receiveCommand D.request ∷ rows) = suc (serverRequests rows)
serverRequests (_ ∷ rows) = serverRequests rows

-- A block of client Request sends.
requests : ℕ → List Rows.ClientRow
requests d = replicate d (Rows.sendCommand D.request)

-- Insert d Request sends immediately before the first Quit, or append them when there is none.
pad : ℕ → List Rows.ClientRow → List Rows.ClientRow
pad d [] = requests d
pad d (Rows.sendCommand D.quit ∷ rows) = requests d ++ Rows.sendCommand D.quit ∷ rows
pad d (row ∷ rows) = row ∷ pad d rows

-- Both local fills, with the client padded by the server's surplus Request receives.
reconstruct : List Rows.ClientRow → List Rows.ServerRow → List Rows.ClientRow × List Rows.ServerRow
reconstruct c s = pad (serverRequests s′ ∸ clientRequests c′) c′ , s′
  where
  -- The two local fills, computed once.
  c′ = fillClient c
  s′ = fillServer s

------------------------------------------------------------------------
-- The reconstruction erases to its input

-- Client wire images of reconstructed rows are the wires they came from.
client-wire-roundtrip : ∀ ws → map Local.clientWire (map Local.clientRow ws) ≡ ws
client-wire-roundtrip [] = refl
client-wire-roundtrip (CW.request ∷ ws) = cong (CW.request ∷_) (client-wire-roundtrip ws)
client-wire-roundtrip (CW.quit ∷ ws) = cong (CW.quit ∷_) (client-wire-roundtrip ws)
client-wire-roundtrip (CW.done ∷ ws) = cong (CW.done ∷_) (client-wire-roundtrip ws)
client-wire-roundtrip (CW.reply r ∷ ws) = cong (CW.reply r ∷_) (client-wire-roundtrip ws)

-- Server wire images of reconstructed rows are the wires they came from.
server-wire-roundtrip : ∀ ws → map Local.serverWire (map Local.serverRow ws) ≡ ws
server-wire-roundtrip [] = refl
server-wire-roundtrip (SW.request ∷ ws) = cong (SW.request ∷_) (server-wire-roundtrip ws)
server-wire-roundtrip (SW.quit ∷ ws) = cong (SW.quit ∷_) (server-wire-roundtrip ws)
server-wire-roundtrip (SW.done ∷ ws) = cong (SW.done ∷_) (server-wire-roundtrip ws)
server-wire-roundtrip (SW.reply r ∷ ws) = cong (SW.reply r ∷_) (server-wire-roundtrip ws)

-- The client wire translation of row lists is injective.
client-injective : ∀ {xs ys} → map Local.clientWire xs ≡ map Local.clientWire ys → xs ≡ ys
client-injective {xs} {ys} same = trans (sym (back xs)) (trans (cong (map Local.clientRow) same) (back ys))
  where
  -- Each row returns from its wire image.
  back : ∀ rows → map Local.clientRow (map Local.clientWire rows) ≡ rows
  back [] = refl
  back (row ∷ rows) = cong₂ _∷_ (Local.client-roundtrip row) (back rows)

-- The server wire translation of row lists is injective.
server-injective : ∀ {xs ys} → map Local.serverWire xs ≡ map Local.serverWire ys → xs ≡ ys
server-injective {xs} {ys} same = trans (sym (back xs)) (trans (cong (map Local.serverRow) same) (back ys))
  where
  -- Each row returns from its wire image.
  back : ∀ rows → map Local.serverRow (map Local.serverWire rows) ≡ rows
  back [] = refl
  back (row ∷ rows) = cong₂ _∷_ (Local.server-roundtrip row) (back rows)

-- The client fill erases back to any all-visible wire list.
client-erase-fill : ∀ {ws} → All (T ∘ CS.visible) ws → CS.erase (CS.fill ws) ≡ ws
client-erase-fill {[]} [] = refl
client-erase-fill {CW.request ∷ _} (() ∷ _)
client-erase-fill {CW.quit ∷ ws} (_ ∷ rest) =
  trans (CS.erase-requests (CS.replies ws) (CW.quit ∷ ws)) (cong (CW.quit ∷_) (filter-all (T? ∘ CS.visible) rest))
client-erase-fill {CW.done ∷ ws} (_ ∷ rest) = cong (CW.done ∷_) (client-erase-fill rest)
client-erase-fill {CW.reply r ∷ ws} (v ∷ rest) =
  trans (filter-accept (T? ∘ CS.visible) v) (cong (CW.reply r ∷_) (client-erase-fill rest))

-- The server fill erases back to any all-visible wire list.
server-erase-fill : ∀ {ws} → All (T ∘ SS.visible) ws → SS.erase (SS.fill ws) ≡ ws
server-erase-fill {[]} [] = refl
server-erase-fill {SW.request ∷ _} (() ∷ _)
server-erase-fill {SW.quit ∷ ws} (_ ∷ rest) =
  trans (SS.erase-requests (SS.replies ws) (SW.quit ∷ ws)) (cong (SW.quit ∷_) (filter-all (T? ∘ SS.visible) rest))
server-erase-fill {SW.done ∷ ws} (_ ∷ rest) = cong (SW.done ∷_) (server-erase-fill rest)
server-erase-fill {SW.reply r ∷ ws} (v ∷ rest) =
  trans (filter-accept (T? ∘ SS.visible) v) (cong (SW.reply r ∷_) (server-erase-fill rest))

-- Filling all-visible client rows is undone by row erasure.
fillClient-erases : ∀ {c} → All ClientVisible c → eraseClient (fillClient c) ≡ c
fillClient-erases {c} visible = client-injective
  (trans (map-filterᵇ Local.clientWire CS.visible (fillClient c))
    (trans (cong CS.erase (client-wire-roundtrip (CS.fill (map Local.clientWire c))))
      (client-erase-fill (map⁺ visible))))

-- Filling all-visible server rows is undone by row erasure.
fillServer-erases : ∀ {s} → All ServerVisible s → eraseServer (fillServer s) ≡ s
fillServer-erases {s} visible = server-injective
  (trans (map-filterᵇ Local.serverWire SS.visible (fillServer s))
    (trans (cong SS.erase (server-wire-roundtrip (SS.fill (map Local.serverWire s))))
      (server-erase-fill (map⁺ visible))))

-- Request blocks are erased.
erase-requests : ∀ d rows → eraseClient (requests d ++ rows) ≡ eraseClient rows
erase-requests zero rows = refl
erase-requests (suc d) rows = erase-requests d rows

-- Padding with Requests leaves the client erasure unchanged.
erase-pad : ∀ d rows → eraseClient (pad d rows) ≡ eraseClient rows
erase-pad zero [] = refl
erase-pad (suc d) [] = erase-pad d []
erase-pad d (Rows.sendCommand D.quit ∷ rows) = erase-requests d _
erase-pad d (Rows.sendCommand D.request ∷ rows) = erase-pad d rows
erase-pad d (Rows.receiveResponse m ∷ rows) =
  filterᵇ-cons clientVisible (Rows.receiveResponse m) (erase-pad d rows)

-- For all-visible logs the reconstruction erases to exactly the observed rows.
reconstruct-erases : ∀ {c s} → All ClientVisible c → All ServerVisible s →
  eraseClient (proj₁ (reconstruct c s)) ≡ c × eraseServer (proj₂ (reconstruct c s)) ≡ s
reconstruct-erases {c} {s} cv sv =
  trans (erase-pad (serverRequests (fillServer s) ∸ clientRequests (fillClient c)) (fillClient c))
    (fillClient-erases cv) ,
  fillServer-erases sv

------------------------------------------------------------------------
-- Checking

-- Certified acceptance, certified rejection, or no claim; the latter retains why no claim is made:
-- both local silenced languages accept, yet the exact decider refutes the canonical reconstruction.
data Outcome (contract : S.Contract) (c : List Rows.ClientRow) (s : List Rows.ServerRow) : Set where
  accepted : SilencedSourceTrace contract c s → Outcome contract c s
  rejected : ¬ SilencedSourceTrace contract c s → Outcome contract c s
  undetermined : CS.Silenced (map Local.clientWire c) → SS.Silenced contract (map Local.serverWire s) →
    ¬ Check.SourceTrace contract (proj₁ (reconstruct c s)) (proj₂ (reconstruct c s)) → Outcome contract c s

-- Local silenced checks first (their failure is a certified rejection), then the exact paired
-- decider on the reconstruction (its success is a certified acceptance).
check : (contract : S.Contract) (c : List Rows.ClientRow) (s : List Rows.ServerRow) → Outcome contract c s
check contract c s with CS.decide-silenced (map Local.clientWire c)
... | no absent = rejected λ witness → absent (proj₁ (local-necessary witness))
... | yes client with SS.decide-silenced contract (map Local.serverWire s)
...   | no absent = rejected λ witness → absent (proj₂ (local-necessary witness))
...   | yes server with Check.decide contract (proj₁ (reconstruct c s)) (proj₂ (reconstruct c s))
...     | yes trace = accepted (_ , _ , trace , reconstruct-erases (client-visible client) (server-visible server))
...     | no absent = undetermined client server absent
