{-# OPTIONS --guardedness #-}

-- The literal is byte-for-byte the adjacent exported artifact (trace_files.py).
-- Agda checks its printer equality, re-import and original initialized endpoint.
module ConnectionManagement.Exploration.ExportHandshakeFailure where

open import Data.Char using (Char)
open import Data.List using (List; map; length)
open import ConnectionManagement.Exploration.Finite using (Covered; covered-left)
open import Data.String using (toList)
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
import ConnectionManagement.Exploration.HandshakeFailure as Witness
import ConnectionManagement.Exploration.Text as Text
import ConnectionManagement.Negative.SupervisedHandshakeFailure as Native
import ConnectionManagement.Rules.PoolRelays as Relays
module W = Witness.W
module M = Witness.Model
module Codec = Text M.O.Outer M.O.OuterAction M.O.outerStep W.candidates

covered : Covered W.actions W.candidates
covered = covered-left W.actions W.relaysActions

wire : List Char
wire = toList ".\n+.\n++.\n+++.\n++++.\n+++++.\n++++++.\n+++++++.\n++++++++.\n+++++++++.\n:.\n:+.\n:++.\n:+++.\n:++++.\n:+++++.\n:++++++.\n:+++++++.\n:++++++++.\n:+++++++++.\n::.\n::+.\n::++.\n::+++.\n::++++.\n::+++++.\n::++++++.\n::+++++++.\n::++++++++.\n::+++++++++.\n:::.\n:::+.\n:::++.\n:::+++.\n:::++++.\n:::+++++.\n:::++++++.\n:::+++++++.\n:::++++++++.\n:::+++++++++.\n"

abstract
  file-is-print : wire ≡ Codec.print {as = W.actions} covered
  file-is-print = refl

  initialized-run : Codec.Raw.Executes W.start W.actions W.end
  initialized-run = M.B.to-raw {s = W.start} {as = W.actions} {t = W.end} (M.B.lift-run (just Relays.running) Native.initialized-to-cleanup)

imported-labels : Codec.parse (length W.actions) wire ≡ just W.actions
imported-labels = trans
  (cong (Codec.parse (length W.actions)) file-is-print)
  (Codec.round-trip {as = W.actions} covered)

-- The generic certified-acceptance theorem turns this checked certificate
-- into acceptance by check, with these exact actions and initialized endpoint.
imported-run : Codec.Imported W.start (length W.actions) wire W.actions W.end
imported-run = Codec.imported imported-labels initialized-run
