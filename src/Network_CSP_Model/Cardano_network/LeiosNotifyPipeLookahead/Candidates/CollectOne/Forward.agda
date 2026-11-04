{-# OPTIONS --safe #-}

-- Early collection is simulated by baseline completion tokens retained until shutdown.
module Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Forward
  (Notification : Set) where

open import Data.Bool using (true)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as B
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Notification as C

-- Inspection/polling refine the baseline's pre-registration reader phase.
reader : C.Reader → B.Reader
reader C.first = B.first
reader C.admit = B.admit
reader C.inspect = B.register
reader C.poll = B.register
reader C.register = B.register
reader C.awaitNext = B.awaitNext
reader C.signalQuit = B.signalQuit
reader C.flushing = B.flushing
reader C.doneReady = B.doneReady
reader C.closed = B.closed
reader C.raising = B.raising
reader C.failed = B.failed

-- Terminal handoff/closed phases have already discharged the extra baseline tokens.
Good : C.Reader → ℕ → Set
Good C.doneReady extra = extra ≡ 0
Good C.closed extra = extra ≡ 0
Good _ _ = ⊤

-- Both models agree on sender liveness through the collapsed reader phases.
active-reader : ∀ r → C.active r ≡ B.active (reader r)
active-reader C.first = refl
active-reader C.admit = refl
active-reader C.inspect = refl
active-reader C.poll = refl
active-reader C.register = refl
active-reader C.awaitNext = refl
active-reader C.signalQuit = refl
active-reader C.flushing = refl
active-reader C.doneReady = refl
active-reader C.closed = refl
active-reader C.raising = refl
active-reader C.failed = refl

-- The baseline differs only in the collapsed phase and retained extra completions.
lift : ℕ → C.State → B.State
lift extra (C.state r w sender completed flag) =
  B.state (reader r) w sender (completed + extra) flag

-- Ordinary receive phases retain exactly the same permitted commands.
reading : ∀ {r} → C.Reading r → B.Reading (reader r)
reading C.atFirst = B.atFirst
reading C.atNext = B.atNext

-- Equality of states supplies an empty source schedule without coinductive equality.
stay : ∀ {p s t} → s ≡ t → B.Run p s [] t
stay refl = B.stop

-- Moving one completion into the ghost extra count leaves the baseline state unchanged.
hit-state : ∀ {w sender completed flag extra} →
  lift (suc extra) (C.state C.register w sender completed flag) ≡
  lift extra (C.state C.poll w sender (suc completed) flag)
hit-state {completed = completed} {extra = extra} rewrite +-suc completed extra = refl

-- A candidate drained state can flush precisely the retained ghost tokens before handoff.
drain-extra : ∀ {p} extra → B.Run p (B.state B.flushing 0 B.idle extra true) []
  (B.state B.doneReady 0 B.idle 0 true)
drain-extra zero = B.internal B.drained B.stop
drain-extra (suc extra) = B.internal B.flush (drain-extra extra)

-- Each candidate hidden step is a finite baseline hidden run with a new ghost count.
tau : ∀ {p s t} → C.Tau s t → (extra : ℕ) → Good (C.reader s) extra →
  Σ[ more ∈ ℕ ] (Good (C.reader t) more × B.Run p (lift extra s) [] (lift more t))
tau C.admitted extra _ = extra , tt , B.internal B.admitted B.stop
tau C.excessive extra _ = extra , tt , B.internal B.excessive B.stop
tau (C.inspectZero _) extra _ = extra , tt , B.stop
tau (C.inspectPositive _) extra _ = extra , tt , B.stop
tau C.pollHit extra _ = suc extra , tt , stay (sym hit-state)
tau (C.pollMiss _) extra _ = extra , tt , B.stop
tau C.registered extra _ = extra , tt , B.internal B.registered B.stop
tau C.setQuit extra _ = extra , tt , B.internal B.setQuit B.stop
tau (C.claim {r = r} live) extra good = extra , good ,
  B.internal (B.claim (trans (sym (active-reader r)) live)) B.stop
tau (C.cancel {r = r} live) extra good = extra , good ,
  B.internal (B.cancel (trans (sym (active-reader r)) live)) B.stop
tau (C.retire {r = r} live) extra good = extra , good ,
  B.internal (B.retire (trans (sym (active-reader r)) live)) B.stop
tau C.flush extra _ = extra , tt , B.internal B.flush B.stop
tau C.drained extra _ = 0 , refl , drain-extra extra
tau C.abort extra _ = extra , tt , B.internal B.abort B.stop

-- Every visible source action, including exact reply-selection data, is retained.
visible : ∀ {p s a t} → C.Step p s a t → (extra : ℕ) → Good (C.reader s) extra →
  Good (C.reader t) extra × B.Run p (lift extra s) (a ∷ []) (lift extra t)
visible (C.receiveRequest canRead) extra _ = tt , B.visible (B.receiveRequest (reading canRead)) B.stop
visible (C.receiveQuit canRead) extra _ = tt , B.visible (B.receiveQuit (reading canRead)) B.stop
visible (C.choose {r = r} live allowed) extra good = good ,
  B.visible (B.choose (trans (sym (active-reader r)) live) allowed) B.stop
visible (C.send {r = r} live) extra good = good ,
  B.visible (B.send (trans (sym (active-reader r)) live)) B.stop
visible C.finish .0 refl = refl , B.visible B.finish B.stop

-- Structural induction simulates every finite candidate source run, not just fixtures.
run : ∀ {p s actions t} → C.Run p s actions t → (extra : ℕ) → Good (C.reader s) extra →
  Σ[ more ∈ ℕ ] (Good (C.reader t) more × B.Run p (lift extra s) actions (lift more t))
run C.stop extra good = extra , good , B.stop
run (C.internal step rest) extra good with tau step extra good
... | more , compatible , prefix with run rest more compatible
...   | final , finalGood , suffix = final , finalGood , B.append prefix suffix
run (C.visible step rest) extra good with visible step extra good
... | compatible , prefix with run rest extra compatible
...   | final , finalGood , suffix = final , finalGood , B.append prefix suffix

-- Fresh candidate source traces are baseline source traces without any extra premise.
from-initial : ∀ {p actions t} → C.Run p C.initial actions t →
  Σ[ extra ∈ ℕ ] (Good (C.reader t) extra × B.Run p B.initial actions (lift extra t))
from-initial execution = run execution 0 tt
