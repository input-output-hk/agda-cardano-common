{-# OPTIONS --guardedness #-}

-- Existing chains need preservation of lookups, not equality of whole tables.
module ConnectionManagement.Properties.HandlerTableRetention where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (trans)
open import ConnectionManagement.Properties.IGTableRetention
open import ConnectionManagement.Properties.HandlerReferences

retains-chain : ∀ {q mid s ig ig′} → Retains ig ig′ → Chain q mid s ig → Chain q mid s ig′
retains-chain {mid = mid} eff ch with muxesRetained eff mid (muxValue ch) (muxFound ch)
... | m′ , found , same = record
  { originalHandler = originalHandler ch; publishedHandle = publishedHandle ch
  ; negotiatedFlow = negotiatedFlow ch; handleValue = handleValue ch; muxValue = m′
  ; handlerFound = handlerFound ch; promiseFound = promiseFound ch
  ; handleFound = handlesRetained eff _ _ (handleFound ch); handleMux = handleMux ch
  ; muxFound = found; keyMatches = trans same (keyMatches ch)
  ; entryPresent = entryPresent ch; socketPresent = socketPresent ch }
