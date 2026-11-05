{-# OPTIONS --safe #-}

-- Input-relative finite payload alphabets preserve whole fresh paired-driver runs.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.BasisAdequacy
  (Notification Return : Set) where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _∷ʳ_; map; concatMap)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-concatMap⁺)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import Relation.Nullary using (Dec; yes; no)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasis Notification Return as Basis
import Cardano_network.LeiosNotifyPipeLookahead.DriverPayloadMap Notification Return as PayloadMap

-- Any total renaming into a finite list transforms arbitrary runs into its restricted model.
module IntoBasis (basis : List Notification) (rename : Notification → Notification)
  (lands : ∀ value → rename value ∈ basis) where

  module B = Basis basis
  module M = PayloadMap rename

  -- Canceled is admitted without data; every renamed normal selection carries actual membership.
  allowed : ∀ value → B.AllowedReply (M.reply value)
  allowed (S.normal value) = B.allowNormal (lands value)
  allowed S.canceled = B.allowCanceled

  -- Only serverCallback requires new membership; all other mapped moves keep their source evidence.
  tau : ∀ {p s t} → D.Tau p s t → B.Tau p (M.state s) (M.state t)
  tau (D.clientInternal pr) = B.clientInternal (M.clientTau pr)
  tau (D.serverInternal pr) = B.serverInternal (M.serverTau pr)
  tau (D.clientCallback callback pr) = B.clientCallback (M.clientCallback callback) (M.clientStep pr)
  tau (D.serverCallback {m = value} pr) = B.serverCallback (allowed value) (M.serverStep pr)
  tau (D.commitClient pr) = B.commitClient (M.clientSendStep pr)
  tau (D.commitServer {sc = sc} {m = value} pr) rewrite M.server-snoc sc value = B.commitServer (M.serverSendStep pr)
  tau (D.decodeClient pr) = B.decodeClient (M.clientRecvStep pr)
  tau (D.decodeServer pr) = B.decodeServer (M.serverRecvStep pr)

  -- Every source schedule is retained, not replaced by an unrelated candidate callback sequence.
  run : ∀ {p s rows t} → D.Run p s rows t → B.Run p (M.state s) (map M.event rows) (M.state t)
  run D.stop = B.stop
  run (D.internal pr rest) = B.internal (tau pr) (run rest)
  run (D.visible pr rest) = B.visible (M.step pr) (run rest)

-- Both Send and Receive occurrences supply exact normal values to the observable basis.
payloads : D.Event → List Notification
payloads (D.serverSend (D.reply (S.normal value))) = value ∷ []
payloads (D.clientRecv (D.reply (S.normal value))) = value ∷ []
payloads _ = []

-- A complete supplied input may include either endpoint or both, preserving its given order.
observedPayloads : List D.Event → List Notification
observedPayloads = concatMap payloads

-- Exact decidable equality is used only for the executable finite retraction, not a protocol guard.
module ForInput (notificationEq : DecidableEquality Notification)
  (representative : Notification) (input : List D.Event) where

  -- Keep every observed normal and one explicit inhabitant for all unobserved normal choices.
  basis : List Notification
  basis = representative ∷ observedPayloads input

  module B = Basis basis

  -- Membership decision retains equality proofs and does not assume a finite Notification carrier.
  member : (value : Notification) (values : List Notification) → Dec (value ∈ values)
  member value [] = no λ ()
  member value (head ∷ values) with notificationEq value head
  ... | yes equal = yes (here equal)
  ... | no different with member value values
  ...   | yes present = yes (there present)
  ...   | no absent = no λ { (here equal) → different equal ; (there present) → absent present }

  -- Values already named by the input remain exact; every other normal uses the explicit fallback.
  retract : Notification → Notification
  retract value with member value basis
  ... | yes _ = value
  ... | no _ = representative

  -- The total retraction always lands inside the declared finite callback basis.
  lands : ∀ value → retract value ∈ basis
  lands value with member value basis
  ... | yes present = present
  ... | no _ = here refl

  -- Every included value is fixed even if the basis contains duplicates.
  fixes : ∀ {value} → value ∈ basis → retract value ≡ value
  fixes {value} included with member value basis
  ... | yes _ = refl
  ... | no absent = ⊥-elim (absent included)

  module M = PayloadMap retract
  module Restricted = IntoBasis basis retract lands

  -- A packet's exact normal data is included whenever its complete driver record is in the input.
  payload-member : ∀ {row value} → row ∈ input → value ∈ payloads row → value ∈ observedPayloads input
  payload-member rowMember valueMember = ∈-concatMap⁺ payloads
    (Any.map (λ equal → subst (λ row → _ ∈ payloads row) equal valueMember) rowMember)

  -- Payload coverage alone is enough: neither endpoint identity nor packet kind is changed.
  event-fixed-payloads : ∀ {row} → (∀ {value} → value ∈ payloads row → value ∈ basis) → M.event row ≡ row
  event-fixed-payloads {D.clientSend value} covered = refl
  event-fixed-payloads {D.serverRecv value} covered = refl
  event-fixed-payloads {D.serverSend (D.reply (S.normal value))} covered
    rewrite fixes (covered (here refl)) = refl
  event-fixed-payloads {D.serverSend (D.reply S.canceled)} covered = refl
  event-fixed-payloads {D.serverSend D.done} covered = refl
  event-fixed-payloads {D.clientRecv (D.reply (S.normal value))} covered
    rewrite fixes (covered (here refl)) = refl
  event-fixed-payloads {D.clientRecv (D.reply S.canceled)} covered = refl
  event-fixed-payloads {D.clientRecv D.done} covered = refl

  -- Endpoint identity, message constructors and every observed payload are fixed by renaming.
  event-fixed : ∀ {row} → row ∈ input → M.event row ≡ row
  event-fixed present = event-fixed-payloads (λ included → there (payload-member present included))

  -- A merged record list may use any order if each normal value is covered by the fixed basis.
  rows-fixed-payloads : (rows : List D.Event) →
    (∀ {row value} → row ∈ rows → value ∈ payloads row → value ∈ basis) → map M.event rows ≡ rows
  rows-fixed-payloads [] covered = refl
  rows-fixed-payloads (row ∷ rows) covered rewrite event-fixed-payloads (covered (here refl)) =
    cong (row ∷_) (rows-fixed-payloads rows (λ member → covered (there member)))

  -- Source runs with covered payloads preserve their exact observations after hidden renaming.
  adequate-payloads : ∀ {p rows t} →
    (∀ {row value} → row ∈ rows → value ∈ payloads row → value ∈ basis) →
    D.Run p D.initial rows t → B.Run p D.initial rows (M.state t)
  adequate-payloads {rows = rows} covered source = subst (λ exact → B.Run _ D.initial exact _)
    (rows-fixed-payloads rows covered) (Restricted.run source)

  -- The same basis supports any ordered record list drawn from the supplied complete input(s).
  rows-fixed : (rows : List D.Event) → (∀ {row} → row ∈ rows → row ∈ input) → map M.event rows ≡ rows
  rows-fixed [] covered = refl
  rows-fixed (row ∷ rows) covered rewrite event-fixed (covered (here refl)) =
    cong (row ∷_) (rows-fixed rows (λ member → covered (there member)))

  -- Transform an actual fresh run while preserving every covered visible record exactly.
  adequate-covered : ∀ {p rows t} → (∀ {row} → row ∈ rows → row ∈ input) →
    D.Run p D.initial rows t → B.Run p D.initial rows (M.state t)
  adequate-covered {rows = rows} covered source = subst (λ exact → B.Run _ D.initial exact _)
    (rows-fixed rows covered) (Restricted.run source)

  -- In particular, every complete supplied finite input retains a genuine restricted source run.
  adequate : ∀ {p t} → D.Run p D.initial input t → B.Run p D.initial input (M.state t)
  adequate = adequate-covered (λ present → present)

  -- Unrestricted trace acceptance quantifies an actual finite source endpoint.
  SourceTrace : S.Contract → Set
  SourceTrace p = Σ[ target ∈ D.State ] D.Run p D.initial input target

  -- Restricted acceptance has exactly the same observations and retains a genuine endpoint.
  BasisTrace : S.Contract → Set
  BasisTrace p = Σ[ target ∈ D.State ] B.Run p D.initial input target

  -- The forward inclusion maps hidden payload choices rather than guessing a smaller witness.
  source→basis : ∀ {p} → SourceTrace p → BasisTrace p
  source→basis (target , source) = M.state target , adequate source

  -- Erasure of basis membership recovers the unchanged original paired driver execution.
  basis→source : ∀ {p} → BasisTrace p → SourceTrace p
  basis→source (target , restricted) = target , B.sound restricted

  -- Complete finite input languages coincide; this is not final-state equality or bisimulation.
  equivalence : ∀ {p} → (SourceTrace p → BasisTrace p) × (BasisTrace p → SourceTrace p)
  equivalence = source→basis , basis→source
