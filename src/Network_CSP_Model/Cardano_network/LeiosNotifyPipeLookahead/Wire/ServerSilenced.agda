{-# OPTIONS --safe #-}

open import Data.Bool using (Bool; true; false; not)

-- Exact server wire language after erasing RequestNext rows and hidden (Votes) normal replies.
module Cardano_network.LeiosNotifyPipeLookahead.Wire.ServerSilenced
  (Notification : Set) (hidden : Notification → Bool) where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; replicate; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Notification as W
open W using (Wire; request; quit; done; reply; Contract; genericNext; nodeNext; normal; canceled)

-- Silenced rows: every request, and normal replies carrying a hidden notification.
visible : Wire → Bool
visible request = false
visible (reply (normal v)) = not (hidden v)
visible _ = true

-- The logged projection of a full wire trace.
erase : List Wire → List Wire
erase = filterᵇ visible

-- Request credit is unobservable, so only the phase of the concrete state survives.
-- (`open` is an Agda keyword, hence `opened`.)
data SState : Set where
  opened quitSeen cancelOnly closed : SState

-- Visible-row steps; `hidden v ≡ false` marks a visible normal reply.
data SStep : Contract → SState → Wire → SState → Set where
  openNormal  : ∀ {p v} → hidden v ≡ false → SStep p opened (reply (normal v)) opened
  openCancel  : SStep genericNext opened (reply canceled) opened
  openQuit    : ∀ {p} → SStep p opened quit quitSeen
  quitNormal  : ∀ {p v} → hidden v ≡ false → SStep p quitSeen (reply (normal v)) quitSeen
  quitCancelG : SStep genericNext quitSeen (reply canceled) quitSeen
  quitCancelN : SStep nodeNext quitSeen (reply canceled) cancelOnly
  onlyCancel  : ∀ {p} → SStep p cancelOnly (reply canceled) cancelOnly
  quitDone    : ∀ {p} → SStep p quitSeen done closed
  onlyDone    : ∀ {p} → SStep p cancelOnly done closed

-- Offer a step only when the scrutinised hidden bit is false.
whenVisible : ∀ {A : Set} b → (b ≡ false → A) → Maybe A
whenVisible false k = just (k refl)
whenVisible true k = nothing

-- A known-false bit makes whenVisible return the supplied continuation.
whenVisible-false : ∀ {A : Set} {b} (k : b ≡ false → A) (h : b ≡ false) → whenVisible b k ≡ just (k h)
whenVisible-false k refl = refl

-- Proof-bearing successor lookup, deciding visibility of normal replies via `hidden`.
lookup : (p : Contract) (s : SState) (e : Wire) → Maybe (Σ[ t ∈ SState ] SStep p s e t)
lookup p opened (reply (normal v)) = whenVisible (hidden v) λ h → _ , openNormal h
lookup genericNext opened (reply canceled) = just (_ , openCancel)
lookup p opened quit = just (_ , openQuit)
lookup p quitSeen (reply (normal v)) = whenVisible (hidden v) λ h → _ , quitNormal h
lookup genericNext quitSeen (reply canceled) = just (_ , quitCancelG)
lookup nodeNext quitSeen (reply canceled) = just (_ , quitCancelN)
lookup p cancelOnly (reply canceled) = just (_ , onlyCancel)
lookup p quitSeen done = just (_ , quitDone)
lookup p cancelOnly done = just (_ , onlyDone)
lookup _ _ _ = nothing

-- Every permitted step has exactly the target and proof returned by lookup.
lookup-complete : ∀ {p s e t} (pr : SStep p s e t) → lookup p s e ≡ just (t , pr)
lookup-complete (openNormal h) = whenVisible-false _ h
lookup-complete openCancel = refl
lookup-complete openQuit = refl
lookup-complete (quitNormal h) = whenVisible-false _ h
lookup-complete quitCancelG = refl
lookup-complete quitCancelN = refl
lookup-complete onlyCancel = refl
lookup-complete quitDone = refl
lookup-complete onlyDone = refl

-- Finite prefixes, as in the full wire machine; EOF is accepted in any state.
data SRun (p : Contract) : SState → List Wire → SState → Set where
  stop : ∀ {s} → SRun p s [] s
  step : ∀ {s t u e es} → SStep p s e t → SRun p t es u → SRun p s (e ∷ es) u

-- Acceptance retains an actual silenced execution and its target.
SHasTrace : Contract → SState → List Wire → Set
SHasTrace p s rows = Σ[ t ∈ SState ] SRun p s rows t

-- Structural recursion with lookup completeness, mirroring Wire.Server.decide.
decide : (p : Contract) (s : SState) (rows : List Wire) → Dec (SHasTrace p s rows)
decide p s [] = yes (_ , stop)
decide p s (row ∷ rows) with lookup p s row in found
... | just (next , pr) with decide p next rows
...   | yes (last , rest) = yes (last , step pr rest)
...   | no deny = no λ { (_ , step actual rest) → bad actual rest }
  where
  -- Lookup completeness identifies the unique target before applying the suffix refutation.
  bad : ∀ {t u} → SStep p s row t → SRun p t rows u → ⊥
  bad actual rest with trans (sym found) (lookup-complete actual)
  ... | refl = deny (_ , rest)
decide p s (row ∷ rows) | nothing = no λ { (_ , step pr rest) → impossible (trans (sym found) (lookup-complete pr)) }
  where
  -- An independently valid rule cannot have a missing lookup result.
  impossible : ∀ {t} {pr : SStep p s row t} → nothing ≡ just (t , pr) → ⊥
  impossible ()

-- Rows observable in a log produced by some full server wire trace.
Silenced : Contract → List Wire → Set
Silenced p rows = Σ[ ws ∈ List Wire ] (W.HasTrace p W.initial ws × erase ws ≡ rows)

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
requests-run : ∀ {p u ys} k m → W.Run p (W.Open (m + k)) ys u → W.Run p (W.Open m) (replicate k request ++ ys) u
requests-run {p} {u} {ys} zero m r = subst (λ n → W.Run p (W.Open n) ys u) (+-identityʳ m) r
requests-run {p} {u} {ys} (suc k) m r =
  W.step W.receiveRequest (requests-run k (suc m) (subst (λ n → W.Run p (W.Open n) ys u) (+-suc m k) r))

-- Cancel-only suffixes run concretely from CancelOnly with exactly their reply count, unchanged by erase.
fill-cancelOnly : ∀ {p xs t} → SRun p cancelOnly xs t → W.HasTrace p (W.CancelOnly (replies xs)) xs × erase xs ≡ xs
fill-cancelOnly stop = (_ , W.stop) , refl
fill-cancelOnly (step onlyCancel rest) with fill-cancelOnly rest
... | (_ , r) , e = (_ , W.step W.canceledOnly r) , cong (reply canceled ∷_) e
fill-cancelOnly (step onlyDone stop) = (_ , W.step W.doneOnly W.stop) , refl
fill-cancelOnly (step onlyDone (step () _))

-- Post-Quit suffixes run concretely from QuitSeen with exactly their reply count, unchanged by erase.
fill-quit : ∀ {p xs t} → SRun p quitSeen xs t → W.HasTrace p (W.QuitSeen (replies xs)) xs × erase xs ≡ xs
fill-quit stop = (_ , W.stop) , refl
fill-quit (step (quitNormal h) rest) with fill-quit rest
... | (_ , r) , e rewrite h = (_ , W.step W.normalQuit r) , cong (reply (normal _) ∷_) e
fill-quit (step quitCancelG rest) with fill-quit rest
... | (_ , r) , e = (_ , W.step W.canceledQuitGeneric r) , cong (reply canceled ∷_) e
fill-quit (step quitCancelN rest) with fill-cancelOnly rest
... | (_ , r) , e = (_ , W.step W.canceledQuitNode r) , cong (reply canceled ∷_) e
fill-quit (step quitDone stop) = (_ , W.step W.doneQuit W.stop) , refl
fill-quit (step quitDone (step () _))

-- Run-level soundness of fill from the opened phase.
fill-open : ∀ {p rows t} → SRun p opened rows t → W.HasTrace p W.initial (fill rows) × erase (fill rows) ≡ rows
fill-open stop = (_ , W.stop) , refl
fill-open (step (openNormal h) rest) with fill-open rest
... | (_ , r) , e rewrite h = (_ , W.step W.receiveRequest (W.step W.normalOpen r)) , cong (reply (normal _) ∷_) e
fill-open (step openCancel rest) with fill-open rest
... | (_ , r) , e = (_ , W.step W.receiveRequest (W.step W.canceledOpen r)) , cong (reply canceled ∷_) e
fill-open (step {es = xs} openQuit rest) with fill-quit rest
... | (_ , r) , e =
  (_ , requests-run (replies xs) 0 (W.step W.receiveQuit r)) ,
  trans (erase-requests (replies xs) (quit ∷ xs)) (cong (quit ∷_) e)

-- Every silenced acceptance is the erasure of a concrete full wire trace.
fill-sound : ∀ {p rows} → SHasTrace p opened rows → W.HasTrace p W.initial (fill rows) × erase (fill rows) ≡ rows
fill-sound (_ , r) = fill-open r

-- Forget request credit, keeping only the phase.
abstract-state : W.State → SState
abstract-state (W.Open _) = opened
abstract-state (W.QuitSeen _) = quitSeen
abstract-state (W.CancelOnly _) = cancelOnly
abstract-state W.Closed = closed

-- A concrete run erases to a silenced run between the abstracted states.
erase-run : ∀ {p s ws t} → W.Run p s ws t → SRun p (abstract-state s) (erase ws) (abstract-state t)
erase-run W.stop = stop
erase-run (W.step W.receiveRequest rest) = erase-run rest
erase-run (W.step W.receiveQuit rest) = step openQuit (erase-run rest)
erase-run (W.step (W.normalOpen {value = v}) rest) with hidden v in h
... | true = erase-run rest
... | false = step (openNormal h) (erase-run rest)
erase-run (W.step (W.normalQuit {value = v}) rest) with hidden v in h
... | true = erase-run rest
... | false = step (quitNormal h) (erase-run rest)
erase-run (W.step W.canceledOpen rest) = step openCancel (erase-run rest)
erase-run (W.step W.canceledQuitGeneric rest) = step quitCancelG (erase-run rest)
erase-run (W.step W.canceledQuitNode rest) = step quitCancelN (erase-run rest)
erase-run (W.step W.canceledOnly rest) = step onlyCancel (erase-run rest)
erase-run (W.step W.doneQuit rest) = step quitDone (erase-run rest)
erase-run (W.step W.doneOnly rest) = step onlyDone (erase-run rest)

-- Every erasure of a concrete trace is in the silenced language.
erase-complete : ∀ {p ws} → W.HasTrace p W.initial ws → SHasTrace p opened (erase ws)
erase-complete (_ , r) = _ , erase-run r

-- Exact decision of the silenced server language.
decide-silenced : (p : Contract) (rows : List Wire) → Dec (Silenced p rows)
decide-silenced p rows with decide p opened rows
... | yes acc = yes (fill rows , fill-sound acc)
... | no deny = no λ { (ws , tr , refl) → deny (erase-complete tr) }
