{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound14 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredCloseBudget5Edge0 as S70
import ConnectionManagement.Negative.FullConfiguredCloseBudget5 as S71
import ConnectionManagement.Negative.FullConfiguredCloseBudget6Edge0 as S72
import ConnectionManagement.Negative.FullConfiguredCloseBudget6 as S73
import ConnectionManagement.Negative.FullConfiguredCloseEdge0 as S74
import ConnectionManagement.Negative.FullConfiguredClose as S75
import ConnectionManagement.Negative.FullConfiguredKeepAliveContractEdge0 as S76
import ConnectionManagement.Negative.FullConfiguredKeepAliveContractEdge1 as S77
import ConnectionManagement.Negative.FullConfiguredKeepAliveContract as S78
import ConnectionManagement.Negative.FullConfiguredKeepAliveReturnBudget0Edge0 as S79
import ConnectionManagement.Negative.FullConfiguredKeepAliveReturnBudget0 as S80
import ConnectionManagement.Negative.FullConfiguredKeepAliveReturn as S81
import ConnectionManagement.Negative.FullConfiguredKeepAlivePublish as S82
import ConnectionManagement.Negative.FullConfiguredKeepAliveDeregister as S83
import ConnectionManagement.Negative.FullConfiguredKeepAliveBody as S84
import ConnectionManagement.Negative.FullConfiguredKeepAliveSelectBudget0Edge0 as S85
import ConnectionManagement.Negative.FullConfiguredKeepAliveSelectBudget0 as S86
import ConnectionManagement.Negative.FullConfiguredKeepAliveSelect as S87
import ConnectionManagement.Negative.FullConfiguredKeepAliveBudget0Edge0 as S88
import ConnectionManagement.Negative.FullConfiguredKeepAliveBudget0 as S89
import ConnectionManagement.Negative.FullConfiguredKeepAlive as S90
import ConnectionManagement.Negative.FullConfiguredMuxScopeBudget0Edge0 as S91
import ConnectionManagement.Negative.FullConfiguredMuxScopeBudget0 as S92
import ConnectionManagement.Negative.FullConfiguredMuxScopeBudget1Edge0 as S93
import ConnectionManagement.Negative.FullConfiguredMuxScopeBudget1 as S94

abstract
  path70 : B.Runs (configure S70.s0) S70.actions (configure S70.s1)
  path70 = B.more {t = configure S70.s1} refl (B.done)

  path71 : B.Runs (configure S71.s0) S71.actions (configure S71.s1)
  path71 = B.more {t = configure S71.s1} refl (B.done)

  path72 : B.Runs (configure S72.s0) S72.actions (configure S72.s1)
  path72 = B.more {t = configure S72.s1} refl (B.done)

  path73 : B.Runs (configure S73.s0) S73.actions (configure S73.s1)
  path73 = B.more {t = configure S73.s1} refl (B.done)

  path74 : B.Runs (configure S74.s0) S74.actions (configure S74.s1)
  path74 = B.more {t = configure S74.s1} refl (B.done)

  path75 : B.Runs (configure S75.s0) S75.actions (configure S75.s1)
  path75 = B.more {t = configure S75.s1} refl (B.done)

  path76 : B.Runs (configure S76.s0) S76.actions (configure S76.s1)
  path76 = B.more {t = configure S76.s1} refl (B.done)

  path77 : B.Runs (configure S77.s0) S77.actions (configure S77.s1)
  path77 = B.more {t = configure S77.s1} refl (B.done)

  path78 : B.Runs (configure S78.s0) S78.actions (configure S78.s1)
  path78 = B.more {t = configure S78.s1} refl (B.done)

  path79 : B.Runs (configure S79.s0) S79.actions (configure S79.s1)
  path79 = B.more {t = configure S79.s1} refl (B.done)

  path80 : B.Runs (configure S80.s0) S80.actions (configure S80.s1)
  path80 = B.more {t = configure S80.s1} refl (B.done)

  path81 : B.Runs (configure S81.s0) S81.actions (configure S81.s1)
  path81 = B.more {t = configure S81.s1} refl (B.done)

  path82 : B.Runs (configure S82.s0) S82.actions (configure S82.s1)
  path82 = B.more {t = configure S82.s1} refl (B.done)

  path83 : B.Runs (configure S83.s0) S83.actions (configure S83.s1)
  path83 = B.more {t = configure S83.s1} refl (B.done)

  path84 : B.Runs (configure S84.s0) S84.actions (configure S84.s1)
  path84 = B.more {t = configure S84.s1} refl (B.done)

  path85 : B.Runs (configure S85.s0) S85.actions (configure S85.s1)
  path85 = B.more {t = configure S85.s1} refl (B.done)

  path86 : B.Runs (configure S86.s0) S86.actions (configure S86.s1)
  path86 = B.more {t = configure S86.s1} refl (B.done)

  path87 : B.Runs (configure S87.s0) S87.actions (configure S87.s1)
  path87 = B.more {t = configure S87.s1} refl (B.done)

  path88 : B.Runs (configure S88.s0) S88.actions (configure S88.s1)
  path88 = B.more {t = configure S88.s1} refl (B.done)

  path89 : B.Runs (configure S89.s0) S89.actions (configure S89.s1)
  path89 = B.more {t = configure S89.s1} refl (B.done)

  path90 : B.Runs (configure S90.s0) S90.actions (configure S90.s1)
  path90 = B.more {t = configure S90.s1} refl (B.done)

  path91 : B.Runs (configure S91.s0) S91.actions (configure S91.s1)
  path91 = B.more {t = configure S91.s1} refl (B.done)

  path92 : B.Runs (configure S92.s0) S92.actions (configure S92.s1)
  path92 = B.more {t = configure S92.s1} refl (B.done)

  path93 : B.Runs (configure S93.s0) S93.actions (configure S93.s1)
  path93 = B.more {t = configure S93.s1} refl (B.done)

  path94 : B.Runs (configure S94.s0) S94.actions (configure S94.s1)
  path94 = B.more {t = configure S94.s1} refl (B.done)

