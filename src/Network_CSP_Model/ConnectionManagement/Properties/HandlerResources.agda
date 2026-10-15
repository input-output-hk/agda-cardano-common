{-# OPTIONS --guardedness #-}

-- Selection and fork establish resource existence, not negotiation coherence.
module ConnectionManagement.Properties.HandlerResources where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (Present; lookup-put)
import ConnectionManagement.Rules.CM as CM
import ConnectionManagement.Rules.Server as S

record Resources (w : WorkerId) (s : State) : Set where
  field
    original : HandlerStart
    found : lookup w (handlers s) ≡ just original
    entryExists : Present (handlerEntry original) (entries (cm s))
    socketExists : Present (handlerSocket original) (sockets s)
open Resources public

-- Queue changes have no effect on these resources.
queue-resources : ∀ queue {w s} → Resources w s → Resources w (record s { inboundInfo = queue })
queue-resources queue r = record
  { original = original r; found = found r
  ; entryExists = entryExists r; socketExists = socketExists r }

fresh-exists : ∀ r c {e c′} → CM.freshInbound r c ≡ just (CM.selected e c′) → Present e (entries c′)
fresh-exists r c eq with lookup (ident (nextEntry c)) (entries c)
... | just _ = case eq of λ ()
... | nothing with just-injective eq
...   | refl = _ , lookup-put _ _ (entries c)

existing-exists : ∀ e st r c {e′ c′} → CM.existingInbound e st r c ≡ just (CM.selected e′ c′) → Present e′ (entries c′)
existing-exists e reservedOutbound r c eq with just-injective eq
... | refl = _ , lookup-put _ _ (entries c)
existing-exists e (unnegotiated _ _ _) r c eq with just-injective eq
... | refl = _ , lookup-put _ _ (entries c)
existing-exists e (outboundUni _ _ _) r c ()
existing-exists e (outboundDup _ _ _ _) r c ()
existing-exists e (outboundIdle _ _ _ _) r c ()
existing-exists e (inboundIdle _ _ _ _) r c ()
existing-exists e (inboundActive _ _ _ _) r c ()
existing-exists e (duplexActive _ _ _) r c ()
existing-exists e (terminating _ _ _) r c eq = fresh-exists r c eq
existing-exists e (terminated _) r c eq = fresh-exists r c eq

-- Both reused and freshly allocated entry identities are backed by the heap.
selected-exists : ∀ l r c {e c′} → CM.selectInbound l r c ≡ just (CM.selected e c′) → Present e (entries c′)
selected-exists l r c eq with mapCell c
... | full _ = case eq of λ ()
... | taken w with owner l ≟ w
...   | no _ = case eq of λ ()
...   | yes _ with lookupConnection (key r) (savedMap l)
...     | nothing = fresh-exists r c eq
...     | just e with lookup e (entries c)
...       | nothing = case eq of λ ()
...       | just st = existing-exists e st r c eq

-- A raw fork does not check the captured entry. Its existence must be supplied,
-- for example by selected-exists; the socket and handler are written by fork.
fork-worker : ∀ w r l p e s {s′} → Present e (entries (cm s)) →
  S.stepWorker w (admissionWorker r (forkHandler l p e)) S.fork s ≡ just s′ →
  Resources (child r) s′
fork-worker w r l p e s present eq with lookup (child r) (handlers s) | lookup (child r) (admissions s)
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
... | nothing | nothing with just-injective eq
...   | refl = record
  { original = handlerStart e (socketRef r) p (key r)
  ; found = lookup-put _ _ (handlers s)
  ; entryExists = present; socketExists = _ , lookup-put _ _ (sockets s) }

fork-resources : ∀ w r l p e c {c′} →
  lookup w (admissions (world c)) ≡ just (admissionWorker r (forkHandler l p e)) →
  Present e (entries (cm (world c))) → advance (admissionStep w S.fork) c ≡ just c′ →
  Resources (child r) (world c′)
fork-resources w r l p e c pcFound present eq rewrite pcFound
  with S.stepWorker w (admissionWorker r (forkHandler l p e)) S.fork (world c) in stepped
... | nothing = case eq of λ ()
... | just s′ with just-injective eq
...   | refl = fork-worker w r l p e (world c) present stepped

-- Consecutive successful selection and fork discharge entry existence. No
-- assertion is made about arbitrary intervening actions or malformed fork PCs.
selection-fork-resources : ∀ w r l p c {c₁ c₂} →
  lookup w (admissions (world c)) ≡ just (admissionWorker r (selectEntry l p)) →
  advance (admissionStep w S.chooseEntry) c ≡ just c₁ →
  advance (admissionStep w S.fork) c₁ ≡ just c₂ → Resources (child r) (world c₂)
selection-fork-resources w r l p c pcFound selected forked rewrite pcFound
  with CM.selectInbound l r (cm (world c)) in selectedEq
... | nothing = case selected of λ ()
... | just CM.denied with just-injective selected
...   | refl rewrite lookup-put w (admissionWorker r (reject l forbidden)) (admissions (world c)) = case forked of λ ()
selection-fork-resources w r l p c pcFound selected forked | just (CM.selected e c′) with just-injective selected
... | refl = fork-resources w r l p e
  (replaceWorld c (S.setPC w (admissionWorker r (selectEntry l p)) (forkHandler l p e) (record (world c) { cm = c′ })))
  (lookup-put w _ (admissions (world c)))
  (selected-exists l r (cm (world c)) selectedEq) forked
