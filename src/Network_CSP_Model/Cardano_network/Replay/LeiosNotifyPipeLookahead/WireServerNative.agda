{-# OPTIONS --guardedness #-}

-- Exact server-wire observation of the existing native lookahead tree; callback APIs are explicitly erased.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.WireServerNative (p : Params) where

open import Data.List using (List; []; _∷_; mapMaybe)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary using (Dec; yes; no)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
import Cardano_network.LeiosNotifyPipe p as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Payloads.Notification as W
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerQuotient Payloads.Notification as Quotient
import Cardano_network.Replay.LeiosNotifyPipeLookahead.WireNative p as Transport

-- The quotient's concrete projection is exactly the declared deletion observer.
wire-mapMaybe : ∀ actions → W.wire actions ≡ mapMaybe W.observe actions
wire-mapMaybe [] = refl
wire-mapMaybe (S.recvRequest ∷ actions) rewrite wire-mapMaybe actions = refl
wire-mapMaybe (S.recvQuit ∷ actions) rewrite wire-mapMaybe actions = refl
wire-mapMaybe (S.sendDone ∷ actions) rewrite wire-mapMaybe actions = refl
wire-mapMaybe (S.nextReply _ ∷ actions) = wire-mapMaybe actions
wire-mapMaybe (S.sendReply _ ∷ actions) rewrite wire-mapMaybe actions = refl

-- Every endpoint/contract uses the same exact Notification values as the quotient.
module For (contract : S.Contract) (l : Link) (d : Dir) where
  module Observation = Transport.For W.Wire W.observe contract l d

  -- Source evidence uses precisely the quotient's wire projection, including exact reply fields.
  SourceTrace : List W.Wire → Set
  SourceTrace rows = Σ[ actions ∈ List S.Action ] Σ[ target ∈ S.State ]
    (S.Run contract S.initial actions target × W.wire actions ≡ rows)

  -- A native trace carries its actual API-inclusive event list and projected wire equality.
  NativeTrace : List W.Wire → Set₁
  NativeTrace = Observation.NativeTrace

  -- Projection equality transports source witnesses without assuming callbacks never occurred.
  source-observation : ∀ {rows} → SourceTrace rows → Observation.SourceTrace rows
  source-observation (actions , target , source , same) = actions , target , source ,
    trans (sym (wire-mapMaybe actions)) same

  -- The inverse transport retains the exact source run, target and complete selected payloads.
  observation-source : ∀ {rows} → Observation.SourceTrace rows → SourceTrace rows
  observation-source (actions , target , source , same) = actions , target , source ,
    trans (wire-mapMaybe actions) same

  -- Every accepted source-wire prefix has an exact native realization with callback APIs hidden only observationally.
  realize : ∀ {rows} → SourceTrace rows → NativeTrace rows
  realize source = Observation.realize (source-observation source)

  -- Every actual native-wire prefix reconstructs a source witness at the same fresh endpoint.
  sound : ∀ {rows} → NativeTrace rows → SourceTrace rows
  sound native = observation-source (Observation.sound native)

  -- Native and independent source wire languages coincide; neither endpoint treats EOF as return.
  equivalence : ∀ rows → (SourceTrace rows → NativeTrace rows) × (NativeTrace rows → SourceTrace rows)
  equivalence rows = realize , sound

  -- The exact native wire language is decidable through the proved quotient, never by a fuel cutoff.
  decide : (rows : List W.Wire) → Dec (NativeTrace rows)
  decide rows with Quotient.decide-source contract rows
  ... | yes source = yes (realize source)
  ... | no absent = no λ native → absent (sound native)
