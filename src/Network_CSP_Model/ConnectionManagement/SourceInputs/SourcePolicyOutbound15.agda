{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound15 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredMuxScopeBudget2Edge0 as S95
import ConnectionManagement.Negative.FullConfiguredMuxScopeBudget2 as S96
import ConnectionManagement.Negative.FullConfiguredMuxScopeEdge0 as S97
import ConnectionManagement.Negative.FullConfiguredMuxScope as S98
import ConnectionManagement.Negative.FullConfiguredMuxCloseBudget0Edge0 as S99
import ConnectionManagement.Negative.FullConfiguredMuxCloseBudget0 as S100
import ConnectionManagement.Negative.FullConfiguredMuxCloseBudget1Edge0 as S101
import ConnectionManagement.Negative.FullConfiguredMuxCloseBudget1 as S102
import ConnectionManagement.Negative.FullConfiguredMuxCloseBudget2Edge0 as S103
import ConnectionManagement.Negative.FullConfiguredMuxCloseBudget2 as S104
import ConnectionManagement.Negative.FullConfiguredMuxCloseEdge0 as S105
import ConnectionManagement.Negative.FullConfiguredMuxClose as S106
import ConnectionManagement.Negative.FullConfiguredMuxBudget0Edge0 as S107
import ConnectionManagement.Negative.FullConfiguredMuxBudget0 as S108
import ConnectionManagement.Negative.FullConfiguredMuxBudget1Edge0 as S109
import ConnectionManagement.Negative.FullConfiguredMuxBudget1 as S110
import ConnectionManagement.Negative.FullConfiguredMuxBudget2Edge0 as S111
import ConnectionManagement.Negative.FullConfiguredMuxBudget2 as S112
import ConnectionManagement.Negative.FullConfiguredMuxBudget3Edge0 as S113
import ConnectionManagement.Negative.FullConfiguredMuxBudget3 as S114
import ConnectionManagement.Negative.FullConfiguredMux as S115
import ConnectionManagement.Negative.FullConfiguredReleaseBudget0Edge0 as S116
import ConnectionManagement.Negative.FullConfiguredReleaseBudget0 as S117
import ConnectionManagement.Negative.FullConfiguredReleaseBudget1Edge0 as S118
import ConnectionManagement.Negative.FullConfiguredReleaseBudget1 as S119

abstract
  path95 : B.Runs (configure S95.s0) S95.actions (configure S95.s1)
  path95 = B.more {t = configure S95.s1} refl (B.done)

  path96 : B.Runs (configure S96.s0) S96.actions (configure S96.s1)
  path96 = B.more {t = configure S96.s1} refl (B.done)

  path97 : B.Runs (configure S97.s0) S97.actions (configure S97.s1)
  path97 = B.more {t = configure S97.s1} refl (B.done)

  path98 : B.Runs (configure S98.s0) S98.actions (configure S98.s1)
  path98 = B.more {t = configure S98.s1} refl (B.done)

  path99 : B.Runs (configure S99.s0) S99.actions (configure S99.s1)
  path99 = B.more {t = configure S99.s1} refl (B.done)

  path100 : B.Runs (configure S100.s0) S100.actions (configure S100.s1)
  path100 = B.more {t = configure S100.s1} refl (B.done)

  path101 : B.Runs (configure S101.s0) S101.actions (configure S101.s1)
  path101 = B.more {t = configure S101.s1} refl (B.done)

  path102 : B.Runs (configure S102.s0) S102.actions (configure S102.s1)
  path102 = B.more {t = configure S102.s1} refl (B.done)

  path103 : B.Runs (configure S103.s0) S103.actions (configure S103.s1)
  path103 = B.more {t = configure S103.s1} refl (B.done)

  path104 : B.Runs (configure S104.s0) S104.actions (configure S104.s1)
  path104 = B.more {t = configure S104.s1} refl (B.done)

  path105 : B.Runs (configure S105.s0) S105.actions (configure S105.s1)
  path105 = B.more {t = configure S105.s1} refl (B.done)

  path106 : B.Runs (configure S106.s0) S106.actions (configure S106.s1)
  path106 = B.more {t = configure S106.s1} refl (B.done)

  path107 : B.Runs (configure S107.s0) S107.actions (configure S107.s1)
  path107 = B.more {t = configure S107.s1} refl (B.done)

  path108 : B.Runs (configure S108.s0) S108.actions (configure S108.s1)
  path108 = B.more {t = configure S108.s1} refl (B.done)

  path109 : B.Runs (configure S109.s0) S109.actions (configure S109.s1)
  path109 = B.more {t = configure S109.s1} refl (B.done)

  path110 : B.Runs (configure S110.s0) S110.actions (configure S110.s1)
  path110 = B.more {t = configure S110.s1} refl (B.done)

  path111 : B.Runs (configure S111.s0) S111.actions (configure S111.s1)
  path111 = B.more {t = configure S111.s1} refl (B.done)

  path112 : B.Runs (configure S112.s0) S112.actions (configure S112.s1)
  path112 = B.more {t = configure S112.s1} refl (B.done)

  path113 : B.Runs (configure S113.s0) S113.actions (configure S113.s1)
  path113 = B.more {t = configure S113.s1} refl (B.done)

  path114 : B.Runs (configure S114.s0) S114.actions (configure S114.s1)
  path114 = B.more {t = configure S114.s1} refl (B.done)

  path115 : B.Runs (configure S115.s0) S115.actions (configure S115.s1)
  path115 = B.more {t = configure S115.s1} refl (B.done)

  path116 : B.Runs (configure S116.s0) S116.actions (configure S116.s1)
  path116 = B.more {t = configure S116.s1} refl (B.done)

  path117 : B.Runs (configure S117.s0) S117.actions (configure S117.s1)
  path117 = B.more {t = configure S117.s1} refl (B.done)

  path118 : B.Runs (configure S118.s0) S118.actions (configure S118.s1)
  path118 = B.more {t = configure S118.s1} refl (B.done)

  path119 : B.Runs (configure S119.s0) S119.actions (configure S119.s1)
  path119 = B.more {t = configure S119.s1} refl (B.done)

