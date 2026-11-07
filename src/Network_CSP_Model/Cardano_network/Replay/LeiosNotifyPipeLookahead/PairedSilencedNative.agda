{-# OPTIONS --guardedness #-}

-- Paired silenced logs transported to the native lookahead trees: two silenced logs are the
-- erasures of an actual native paired PTree execution exactly when they are those of a source run.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.PairedSilencedNative (p : Params) where

open import Data.List using (List; [])
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification ⊤ as Rows
open import Cardano_network.Replay.LeiosNotifyPipeLookahead.Silenced p using (isVotes)
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PairedSilenced Notification notificationEq (votes []) isVotes
  as Paired
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecideNative p as Bridge

-- Endpoint coordinates and the declared server contract stay fixed throughout a trace.
module At (contract : S.Contract) (cl sl : Link) (cd sd : Dir) where
  -- The exact paired source/native trace equivalence at these coordinates.
  module Native = Bridge.At contract cl sl cd sd

  -- Some full native paired execution whose two silenced row projections are exactly the logs.
  SilencedNativeTrace : List Rows.ClientRow → List Rows.ServerRow → Set₁
  SilencedNativeTrace c s = Σ[ c′ ∈ List Rows.ClientRow ] Σ[ s′ ∈ List Rows.ServerRow ]
    (Native.NativeTrace c′ s′ × Paired.eraseClient c′ ≡ c × Paired.eraseServer s′ ≡ s)

  -- The same hidden full rows witness both sides, via the exact paired native equivalence.
  equivalence : ∀ c s →
    (Paired.SilencedSourceTrace contract c s → SilencedNativeTrace c s) ×
    (SilencedNativeTrace c s → Paired.SilencedSourceTrace contract c s)
  equivalence c s =
    (λ { (c′ , s′ , trace , sameC , sameS) → c′ , s′ , proj₁ (Native.equivalence c′ s′) trace , sameC , sameS }) ,
    (λ { (c′ , s′ , native , sameC , sameS) → c′ , s′ , proj₂ (Native.equivalence c′ s′) native , sameC , sameS })

  -- A paired silenced verdict over native traces; undetermined keeps only the native refutation of
  -- the canonical reconstruction, never a refutation of the silenced logs.
  data NativeOutcome (c : List Rows.ClientRow) (s : List Rows.ServerRow) : Set₁ where
    accepted : SilencedNativeTrace c s → NativeOutcome c s
    rejected : ¬ SilencedNativeTrace c s → NativeOutcome c s
    undetermined : ¬ Native.NativeTrace (proj₁ (Paired.reconstruct c s)) (proj₂ (Paired.reconstruct c s)) →
      NativeOutcome c s

  -- Paired.check transported along the equivalences.
  check-native : ∀ c s → NativeOutcome c s
  check-native c s with Paired.check contract c s
  ... | Paired.accepted trace = accepted (proj₁ (equivalence c s) trace)
  ... | Paired.rejected absent = rejected (absent ∘ proj₂ (equivalence c s))
  ... | Paired.undetermined _ _ absent = undetermined (absent ∘ proj₂ (Native.equivalence _ _))
