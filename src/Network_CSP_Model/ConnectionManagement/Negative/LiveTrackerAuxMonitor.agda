{-# OPTIONS --guardedness #-}

-- A real initialized dequeue exercises the nonempty selected-PC payload clause.
module ConnectionManagement.Negative.LiveTrackerAuxMonitor where
open import ConnectionManagement.Negative.MuxResultMonitor using
 (bearerClosed; owner; clean0; clean1; clean-edge1; actual-initializer; initialized-clean-head)
open import ConnectionManagement.Properties.LiveTrackerAuxCoreInitialized bearerClosed using (module MonitorEndpoint)
open MonitorEndpoint using (Valid; monitor-from-initial; monitor-step-preserves)
import ConnectionManagement.MuxResultMonitor as Monitor

initialized-selected-content : Valid clean1
initialized-selected-content = monitor-step-preserves (Monitor.consume owner) clean0 clean-edge1
 (monitor-from-initial _ actual-initializer initialized-clean-head)
