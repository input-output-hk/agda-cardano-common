{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound16 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredReleaseBudget2Edge0 as S120
import ConnectionManagement.Negative.FullConfiguredReleaseBudget2 as S121
import ConnectionManagement.Negative.FullConfiguredReleaseBudget3Edge0 as S122
import ConnectionManagement.Negative.FullConfiguredReleaseBudget3 as S123
import ConnectionManagement.Negative.FullConfiguredReleaseEdge0 as S124
import ConnectionManagement.Negative.FullConfiguredRelease as S125
import ConnectionManagement.Negative.FullConfiguredColdCleanupBudget0Edge0 as S126
import ConnectionManagement.Negative.FullConfiguredColdCleanupBudget0 as S127
import ConnectionManagement.Negative.FullConfiguredColdCleanupBudget1Edge0 as S128
import ConnectionManagement.Negative.FullConfiguredColdCleanupBudget1 as S129
import ConnectionManagement.Negative.FullConfiguredColdCleanupEdge0 as S130
import ConnectionManagement.Negative.FullConfiguredColdCleanup as S131
import ConnectionManagement.Negative.FullConfiguredColdReceiptBudget0Edge0 as S132
import ConnectionManagement.Negative.FullConfiguredColdReceiptBudget0 as S133
import ConnectionManagement.Negative.FullConfiguredColdReceiptBudget1Edge0 as S134
import ConnectionManagement.Negative.FullConfiguredColdReceiptBudget1 as S135
import ConnectionManagement.Negative.FullConfiguredColdReceiptEdge0 as S136
import ConnectionManagement.Negative.FullConfiguredColdReceipt as S137
import ConnectionManagement.Negative.FullConfiguredColdBudget0Edge0 as S138
import ConnectionManagement.Negative.FullConfiguredColdBudget0 as S139
import ConnectionManagement.Negative.FullConfiguredColdBudget1Edge0 as S140
import ConnectionManagement.Negative.FullConfiguredColdBudget1 as S141
import ConnectionManagement.Negative.FullConfiguredColdBudget2Edge0 as S142
import ConnectionManagement.Negative.FullConfiguredColdBudget2 as S143
import ConnectionManagement.Negative.FullConfiguredCold as S144

abstract
  path120 : B.Runs (configure S120.s0) S120.actions (configure S120.s1)
  path120 = B.more {t = configure S120.s1} refl (B.done)

  path121 : B.Runs (configure S121.s0) S121.actions (configure S121.s1)
  path121 = B.more {t = configure S121.s1} refl (B.done)

  path122 : B.Runs (configure S122.s0) S122.actions (configure S122.s1)
  path122 = B.more {t = configure S122.s1} refl (B.done)

  path123 : B.Runs (configure S123.s0) S123.actions (configure S123.s1)
  path123 = B.more {t = configure S123.s1} refl (B.done)

  path124 : B.Runs (configure S124.s0) S124.actions (configure S124.s1)
  path124 = B.more {t = configure S124.s1} refl (B.done)

  path125 : B.Runs (configure S125.s0) S125.actions (configure S125.s1)
  path125 = B.more {t = configure S125.s1} refl (B.done)

  path126 : B.Runs (configure S126.s0) S126.actions (configure S126.s1)
  path126 = B.more {t = configure S126.s1} refl (B.done)

  path127 : B.Runs (configure S127.s0) S127.actions (configure S127.s1)
  path127 = B.more {t = configure S127.s1} refl (B.done)

  path128 : B.Runs (configure S128.s0) S128.actions (configure S128.s1)
  path128 = B.more {t = configure S128.s1} refl (B.done)

  path129 : B.Runs (configure S129.s0) S129.actions (configure S129.s1)
  path129 = B.more {t = configure S129.s1} refl (B.done)

  path130 : B.Runs (configure S130.s0) S130.actions (configure S130.s1)
  path130 = B.more {t = configure S130.s1} refl (B.done)

  path131 : B.Runs (configure S131.s0) S131.actions (configure S131.s1)
  path131 = B.more {t = configure S131.s1} refl (B.done)

  path132 : B.Runs (configure S132.s0) S132.actions (configure S132.s1)
  path132 = B.more {t = configure S132.s1} refl (B.done)

  path133 : B.Runs (configure S133.s0) S133.actions (configure S133.s1)
  path133 = B.more {t = configure S133.s1} refl (B.done)

  path134 : B.Runs (configure S134.s0) S134.actions (configure S134.s1)
  path134 = B.more {t = configure S134.s1} refl (B.done)

  path135 : B.Runs (configure S135.s0) S135.actions (configure S135.s1)
  path135 = B.more {t = configure S135.s1} refl (B.done)

  path136 : B.Runs (configure S136.s0) S136.actions (configure S136.s1)
  path136 = B.more {t = configure S136.s1} refl (B.done)

  path137 : B.Runs (configure S137.s0) S137.actions (configure S137.s1)
  path137 = B.more {t = configure S137.s1} refl (B.done)

  path138 : B.Runs (configure S138.s0) S138.actions (configure S138.s1)
  path138 = B.more {t = configure S138.s1} refl (B.done)

  path139 : B.Runs (configure S139.s0) S139.actions (configure S139.s1)
  path139 = B.more {t = configure S139.s1} refl (B.done)

  path140 : B.Runs (configure S140.s0) S140.actions (configure S140.s1)
  path140 = B.more {t = configure S140.s1} refl (B.done)

  path141 : B.Runs (configure S141.s0) S141.actions (configure S141.s1)
  path141 = B.more {t = configure S141.s1} refl (B.done)

  path142 : B.Runs (configure S142.s0) S142.actions (configure S142.s1)
  path142 = B.more {t = configure S142.s1} refl (B.done)

  path143 : B.Runs (configure S143.s0) S143.actions (configure S143.s1)
  path143 = B.more {t = configure S143.s1} refl (B.done)

  path144 : B.Runs (configure S144.s0) S144.actions (configure S144.s1)
  path144 = B.more {t = configure S144.s1} refl (B.done)

