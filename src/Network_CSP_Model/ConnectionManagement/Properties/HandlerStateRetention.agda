{-# OPTIONS --guardedness #-}

-- Retained table lookups transport resource and published-chain evidence.
module ConnectionManagement.Properties.HandlerStateRetention where

open import ConnectionManagement.Properties.StateRetention
open import ConnectionManagement.Properties.HandlerResources
open import ConnectionManagement.Properties.HandlerReferences

resources-retained : ∀ {w s s′} → Retains s s′ → Resources w s → Resources w s′
resources-retained eff r = record
  { original = original r; found = handlersRetained eff _ _ (found r)
  ; entryExists = entriesRetained eff _ (entryExists r)
  ; socketExists = socketsRetained eff _ (socketExists r) }
retains-chain : ∀ {w mid s s′ ig} → Retains s s′ → Chain w mid s ig → Chain w mid s′ ig
retains-chain eff ch = record
  { originalHandler = originalHandler ch; publishedHandle = publishedHandle ch
  ; negotiatedFlow = negotiatedFlow ch; handleValue = handleValue ch; muxValue = muxValue ch
  ; handlerFound = handlersRetained eff _ _ (handlerFound ch)
  ; promiseFound = resultsRetained eff _ _ (promiseFound ch)
  ; handleFound = handleFound ch; handleMux = handleMux ch; muxFound = muxFound ch
  ; keyMatches = keyMatches ch; entryPresent = entriesRetained eff _ (entryPresent ch)
  ; socketPresent = socketsRetained eff _ (socketPresent ch) }
