---
title: Communicating Sequential Processes
layout: page
---

```
module Traces.Cardano where
```
This module introduces traces of a Cardano network in an abstract, observable sense.

It builds on work done by Brian Bush and Yves Hauser in the [https://github.com/input-output-hk/ouroboros-leios/blame/main/leios-trace-hs/src/LeiosEvents.hs](Leios R&D project).

## Events

The datatype of events that can be observed.
```
-- TODO: Stub for now
data Event : Set where
  Slot : Event
  NoIBGenerated : Event
  IBGenerated : Event
  IBSent : Event
  IBRecieved : Event
  TXGenerated : Event
  TXRecieved : Event
  EBGenerated : Event
  EBRecieved : Event
```
