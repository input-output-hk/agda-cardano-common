{-# OPTIONS --safe #-}

open import Data.Bool using (Bool; true; false; not)

-- Exact client wire language after erasing RequestNext rows and hidden (Votes) normal replies.
module Cardano_network.LeiosNotifyPipeLookahead.Wire.ClientSilenced
  (Notification : Set) (hidden : Notification → Bool) where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; replicate; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Notification as W
open W using (Wire; request; quit; done; reply; normal; canceled)

-- Silenced rows: every request, and normal replies carrying a hidden notification.
visible : Wire → Bool
visible request = false
visible (reply (normal v)) = not (hidden v)
visible _ = true

-- The logged projection of a full wire trace.
erase : List Wire → List Wire
erase = filterᵇ visible

-- Reply credit and the Lead obligation are unobservable, so only the phase survives.
-- (`open` is an Agda keyword, hence `opened`.)
data SState : Set where
  opened quitSeen closed : SState

-- Visible-row steps; `hidden v ≡ false` marks a visible normal reply.
data SStep : SState → Wire → SState → Set where
  openNormal : ∀ {v} → hidden v ≡ false → SStep opened (reply (normal v)) opened
  openCancel : SStep opened (reply canceled) opened
  openQuit   : SStep opened quit quitSeen
  quitNormal : ∀ {v} → hidden v ≡ false → SStep quitSeen (reply (normal v)) quitSeen
  quitCancel : SStep quitSeen (reply canceled) quitSeen
  quitDone   : SStep quitSeen done closed

-- Offer a step only when the scrutinised hidden bit is false.
whenVisible : ∀ {A : Set} b → (b ≡ false → A) → Maybe A
whenVisible false k = just (k refl)
whenVisible true k = nothing

-- A known-false bit makes whenVisible return the supplied continuation.
whenVisible-false : ∀ {A : Set} {b} (k : b ≡ false → A) (h : b ≡ false) → whenVisible b k ≡ just (k h)
whenVisible-false k refl = refl

-- Proof-bearing successor lookup, deciding visibility of normal replies via `hidden`.
lookup : (s : SState) (e : Wire) → Maybe (Σ[ t ∈ SState ] SStep s e t)
lookup opened (reply (normal v)) = whenVisible (hidden v) λ h → _ , openNormal h
lookup opened (reply canceled) = just (_ , openCancel)
lookup opened quit = just (_ , openQuit)
lookup quitSeen (reply (normal v)) = whenVisible (hidden v) λ h → _ , quitNormal h
lookup quitSeen (reply canceled) = just (_ , quitCancel)
lookup quitSeen done = just (_ , quitDone)
lookup _ _ = nothing

-- Every permitted step has exactly the target and proof returned by lookup.
lookup-complete : ∀ {s e t} (pr : SStep s e t) → lookup s e ≡ just (t , pr)
lookup-complete (openNormal h) = whenVisible-false _ h
lookup-complete openCancel = refl
lookup-complete openQuit = refl
lookup-complete (quitNormal h) = whenVisible-false _ h
lookup-complete quitCancel = refl
lookup-complete quitDone = refl

-- Finite prefixes, as in the full wire machine; EOF is accepted in any state.
data SRun : SState → List Wire → SState → Set where
  stop : ∀ {s} → SRun s [] s
  step : ∀ {s t u e es} → SStep s e t → SRun t es u → SRun s (e ∷ es) u

-- Acceptance retains an actual silenced execution and its target.
SHasTrace : SState → List Wire → Set
SHasTrace s rows = Σ[ t ∈ SState ] SRun s rows t

-- Structural recursion with lookup completeness, mirroring Wire.Client.decide.
decide : (s : SState) (rows : List Wire) → Dec (SHasTrace s rows)
decide s [] = yes (_ , stop)
decide s (row ∷ rows) with lookup s row in found
... | just (next , pr) with decide next rows
...   | yes (last , rest) = yes (last , step pr rest)
...   | no deny = no λ { (_ , step actual rest) → bad actual rest }
  where
  -- Lookup completeness identifies the unique target before applying the suffix refutation.
  bad : ∀ {t u} → SStep s row t → SRun t rows u → ⊥
  bad actual rest with trans (sym found) (lookup-complete actual)
  ... | refl = deny (_ , rest)
decide s (row ∷ rows) | nothing = no λ { (_ , step pr rest) → impossible (trans (sym found) (lookup-complete pr)) }
  where
  -- An independently valid rule cannot have a missing lookup result.
  impossible : ∀ {t} {pr : SStep s row t} → nothing ≡ just (t , pr) → ⊥
  impossible ()

-- Rows observable in a log produced by some full client wire trace.
Silenced : List Wire → Set
Silenced rows = Σ[ ws ∈ List Wire ] (W.HasTrace W.initial ws × erase ws ≡ rows)

-- Number of replies in a post-Quit segment, up to Done or the end.
replies : List Wire → ℕ
replies [] = 0
replies (reply _ ∷ xs) = suc (replies xs)
replies (done ∷ xs) = 0
replies (_ ∷ xs) = replies xs

-- Reinsert one request per pre-Quit reply, and before Quit one per later reply.
fill : List Wire → List Wire
fill [] = []
fill (reply r ∷ xs) = request ∷ reply r ∷ fill xs
fill (quit ∷ xs) = replicate (replies xs) request ++ quit ∷ xs
fill (x ∷ xs) = x ∷ fill xs

-- Leading requests are invisible.
erase-requests : ∀ k ys → erase (replicate k request ++ ys) ≡ erase ys
erase-requests zero ys = refl
erase-requests (suc k) ys = erase-requests k ys

-- A block of k requests moves Open m to Open (m + k).
requests-run : ∀ {u ys} k m → W.Run (W.Open (m + k)) ys u → W.Run (W.Open m) (replicate k request ++ ys) u
requests-run {u} {ys} zero m r = subst (λ n → W.Run (W.Open n) ys u) (+-identityʳ m) r
requests-run {u} {ys} (suc k) m r =
  W.step W.sendRequest (requests-run k (suc m) (subst (λ n → W.Run (W.Open n) ys u) (+-suc m k) r))

-- Post-Quit suffixes run concretely from QuitSeen with exactly their reply count, unchanged by erase.
fill-quit : ∀ {xs t} → SRun quitSeen xs t → W.HasTrace (W.QuitSeen (replies xs)) xs × erase xs ≡ xs
fill-quit stop = (_ , W.stop) , refl
fill-quit (step (quitNormal h) rest) with fill-quit rest
... | (_ , r) , e rewrite h = (_ , W.step W.drainReply r) , cong (reply (normal _) ∷_) e
fill-quit (step quitCancel rest) with fill-quit rest
... | (_ , r) , e = (_ , W.step W.drainReply r) , cong (reply canceled ∷_) e
fill-quit (step quitDone stop) = (_ , W.step W.receiveDone W.stop) , refl
fill-quit (step quitDone (step () _))

-- Run-level soundness of fill from the opened phase.
fill-open : ∀ {rows t} → SRun opened rows t → W.HasTrace W.initial (fill rows) × erase (fill rows) ≡ rows
fill-open stop = (_ , W.stop) , refl
fill-open (step (openNormal h) rest) with fill-open rest
... | (_ , r) , e rewrite h = (_ , W.step W.sendRequest (W.step W.receiveReply r)) , cong (reply (normal _) ∷_) e
fill-open (step openCancel rest) with fill-open rest
... | (_ , r) , e = (_ , W.step W.sendRequest (W.step W.receiveReply r)) , cong (reply canceled ∷_) e
fill-open (step {es = xs} openQuit rest) with fill-quit rest
... | (_ , r) , e =
  (_ , requests-run (replies xs) 0 (W.step W.sendQuit r)) ,
  trans (erase-requests (replies xs) (quit ∷ xs)) (cong (quit ∷_) e)

-- Every silenced acceptance is the erasure of a concrete full wire trace.
fill-sound : ∀ {rows} → SHasTrace opened rows → W.HasTrace W.initial (fill rows) × erase (fill rows) ≡ rows
fill-sound (_ , r) = fill-open r

-- Forget reply credit and the Lead obligation, keeping only the phase.
abstract-state : W.State → SState
abstract-state (W.Open _) = opened
abstract-state W.Lead = opened
abstract-state (W.QuitSeen _) = quitSeen
abstract-state W.Closed = closed

-- A visible-or-hidden normal reply from the open phase erases to an open-phase run.
erase-run-openReply : ∀ {ws u} m → SRun opened (erase ws) u → SRun opened (erase (reply m ∷ ws)) u
erase-run-openReply canceled rest = step openCancel rest
erase-run-openReply (normal v) rest with hidden v in h
... | true = rest
... | false = step (openNormal h) rest

-- A concrete run erases to a silenced run between the abstracted states.
erase-run : ∀ {s ws t} → W.Run s ws t → SRun (abstract-state s) (erase ws) (abstract-state t)
erase-run W.stop = stop
erase-run (W.step W.sendRequest rest) = erase-run rest
erase-run (W.step W.finishRequest rest) = erase-run rest
erase-run (W.step (W.receiveReply {m = m}) rest) = erase-run-openReply m (erase-run rest)
erase-run (W.step (W.earlyReply {m = m}) rest) = erase-run-openReply m (erase-run rest)
erase-run (W.step W.sendQuit rest) = step openQuit (erase-run rest)
erase-run (W.step (W.drainReply {m = canceled}) rest) = step quitCancel (erase-run rest)
erase-run (W.step (W.drainReply {m = normal v}) rest) with hidden v in h
... | true = erase-run rest
... | false = step (quitNormal h) (erase-run rest)
erase-run (W.step W.receiveDone rest) = step quitDone (erase-run rest)

-- Every erasure of a concrete trace is in the silenced language.
erase-complete : ∀ {ws} → W.HasTrace W.initial ws → SHasTrace opened (erase ws)
erase-complete (_ , r) = _ , erase-run r

-- Exact decision of the silenced client language.
decide-silenced : (rows : List Wire) → Dec (Silenced rows)
decide-silenced rows with decide opened rows
... | yes acc = yes (fill rows , fill-sound acc)
... | no deny = no λ { (ws , tr , refl) → deny (erase-complete tr) }
