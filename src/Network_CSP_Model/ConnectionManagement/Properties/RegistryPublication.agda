{-# OPTIONS --guardedness #-}

-- Accepted successful publication identifies a unique, origin-certified entry.
module ConnectionManagement.Properties.RegistryPublication where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State using (negotiated)
import ConnectionManagement.Machine as Open
import ConnectionManagement.Rules.OriginMonitor as Single
open Single using (Target; workerId; handleId; Ticket; muxId; protocols; flow)
open import ConnectionManagement.Rules.AttributedOrigin using (Action; dispatch; erase)
import ConnectionManagement.Rules.AttributedOrigin as Attributed
import ConnectionManagement.Properties.AttributedOrigin as AP
import ConnectionManagement.Properties.OriginMonitor as SP
import ConnectionManagement.Properties.OriginMonitorInvariant as SI
open import ConnectionManagement.Properties.HandlerOrigin using (Origin; origin-step)
open import ConnectionManagement.Rules.OriginRegistry
import ConnectionManagement.Properties.OriginRegistry as Registry
open import ConnectionManagement.Properties.RegistryUnique using (Apart; Unique; reachable-unique)

publication : WorkerId → HandleId → DataFlow → Action
publication w hid f = dispatch (Open.handlerPublication w (negotiated hid f) Open.resultWritten)

-- Boolean registration checks expose an actual list member.
worker-member : ∀ w es → hasWorker w es ≡ true → Σ Entry (λ e → e ∈ es × w ≡ workerId (targetId e))
worker-member w [] ()
worker-member w (e ∷ es) eq with w ≟ workerId (targetId e)
... | yes same = e , here refl , same
... | no _ with worker-member w es eq
...   | found , member , same = found , there member , same

-- Pairwise separation rules out a second entry for the same worker.
apart-member : ∀ t es {e} → All (Apart t) (map targetId es) → e ∈ es → Apart t (targetId e)
apart-member t (e ∷ es) (p ∷ ps) (here refl) = p
apart-member t (e ∷ es) (p ∷ ps) (there member) = apart-member t es ps member
owner-unique : ∀ es {e other} → Unique es → e ∈ es → other ∈ es →
  workerId (targetId e) ≡ workerId (targetId other) → other ≡ e
owner-unique (e ∷ es) (apart ∷ unique) (here refl) (here refl) same = refl
owner-unique (e ∷ es) (apart ∷ unique) (here refl) (there member) same =
  ⊥-elim (proj₁ (apart-member (targetId e) es apart member) same)
owner-unique (e ∷ es) (apart ∷ unique) (there member) (here refl) same =
  ⊥-elim (proj₁ (apart-member (targetId e) es apart member) (sym same))
owner-unique (e ∷ es) (apart ∷ unique) (there first) (there second) same =
  owner-unique es unique first second same

-- Every member receives its own successful monitor step during drive.
drive-member : ∀ a c es {es′ e} → drive a c es ≡ just es′ → e ∈ es →
  Σ Single.State (λ local →
    Single.step (targetId e) (erase a) (Single.observed c (phase e)) ≡ just local ×
    entry (targetId e) (Single.phase local) ∈ es′)
drive-member a c (e ∷ es) eq member
  with Attributed.step (targetId e) a (Single.observed c (phase e)) in stepped
... | nothing = case eq of λ ()
... | just local with drive a c es in driven
...   | nothing = case eq of λ ()
...   | just rest with just-injective eq
...     | refl with member
...       | here refl = local , AP.step-projects (targetId e) a (Single.observed c (phase e)) stepped , here refl
...       | there tail with drive-member a c es driven tail
...         | later , accepted , present = later , accepted , there present

-- Soundness names both the pending entry and its published successor.
record Sound (w : WorkerId) (hid : HandleId) (f : DataFlow) (s s′ : State) : Set where
  field
    selected : Entry
    present : selected ∈ entries s
    owner : w ≡ workerId (targetId selected)
    ticket : Ticket
    pending : phase selected ≡ Single.awaitingPublication ticket
    handleMatches : hid ≡ handleId (targetId selected)
    negotiatedFlow : f ≡ flow ticket
    published : entry (targetId selected) (Single.published ticket) ∈ entries s′
    originBefore : Origin w hid (muxId ticket) (protocols ticket) f (machine s)
    originAfter : Origin w hid (muxId ticket) (protocols ticket) f (machine s′)
    uniqueOwner : ∀ other → other ∈ entries s → w ≡ workerId (targetId other) → other ≡ selected

-- The pre-state certificate supplies the allocated descriptor; publication itself
-- checks matching identity/flow, and exhaustive retention gives the post-state.
certify : ∀ w hid f s s′ e → e ∈ entries s → w ≡ workerId (targetId e) →
  drive (publication w hid f) (machine s) (entries s) ≡ just (entries s′) →
  Open.advance (erase (publication w hid f)) (machine s) ≡ just (machine s′) →
  Registry.Invariant s → Unique (entries s) → Sound w hid f s s′
certify w hid f s s′ e member refl driven advanced invariant unique
  with drive-member (publication (workerId (targetId e)) hid f) (machine s) (entries s) driven member
... | local , accepted , published with SP.accepted-publication (targetId e) hid f (Single.observed (machine s) (phase e)) accepted
... | tk , pending , refl , refl , now = record
  { selected = e; present = member; owner = refl; ticket = tk
  ; pending = pending; handleMatches = refl; negotiatedFlow = refl
  ; published = subst (λ ph → entry (targetId e) ph ∈ entries s′) now published
  ; originBefore = before
  ; originAfter = origin-step (erase (publication (workerId (targetId e)) (handleId (targetId e)) (flow tk))) (machine s) advanced before
  ; uniqueOwner = λ other otherMember same → owner-unique (entries s) unique member otherMember same }
  where
  before : Origin (workerId (targetId e)) (handleId (targetId e)) (muxId tk) (protocols tk) (flow tk) (machine s)
  before = subst (SI.TicketOrigin (targetId e) (machine s)) pending (proj₂ (All.lookup invariant member))

publication-sound : ∀ w hid f s {s′} → step (publication w hid f) s ≡ just s′ →
  Registry.Invariant s → Unique (entries s) → Sound w hid f s s′
publication-sound w hid f (registry c es) eq invariant unique with hasWorker w es in registered
... | false = case eq of λ ()
... | true with Open.advance (erase (publication w hid f)) c in advanced
...   | nothing = case eq of λ ()
...   | just c′ with drive (publication w hid f) c es in driven
...     | nothing = case eq of λ ()
...     | just es′ with just-injective eq
...       | refl with worker-member w es registered
...         | e , member , same = certify w hid f (registry c es) (registry c′ es′) e member same driven advanced invariant unique

-- Reachability discharges uniqueness; Supported discharges origin, separately.
reachable-publication : ∀ {c as s s′} w hid f (path : Executes (start c) as s) →
  Registry.Supported path → step (publication w hid f) s ≡ just s′ → Sound w hid f s s′
reachable-publication w hid f path supported eq = publication-sound w hid f _ eq
  (Registry.reachable path supported) (reachable-unique path)
