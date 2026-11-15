{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound17 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredCompleteBudget0Edge0 as S145
import ConnectionManagement.Negative.FullConfiguredCompleteBudget0 as S146
import ConnectionManagement.Negative.FullConfiguredCompleteBudget1Edge0 as S147
import ConnectionManagement.Negative.FullConfiguredCompleteBudget1 as S148
import ConnectionManagement.Negative.FullConfiguredCompleteBudget2Edge0 as S149
import ConnectionManagement.Negative.FullConfiguredCompleteBudget2 as S150
import ConnectionManagement.Negative.FullConfiguredCompleteBudget3Edge0 as S151
import ConnectionManagement.Negative.FullConfiguredCompleteBudget3 as S152
import ConnectionManagement.Negative.FullConfiguredCompleteBudget4Edge0 as S153
import ConnectionManagement.Negative.FullConfiguredCompleteBudget4 as S154
import ConnectionManagement.Negative.FullConfiguredCompleteEdge0 as S155
import ConnectionManagement.Negative.FullConfiguredComplete as S156

abstract
  path145 : B.Runs (configure S145.s0) S145.actions (configure S145.s1)
  path145 = B.more {t = configure S145.s1} refl (B.done)

  path146 : B.Runs (configure S146.s0) S146.actions (configure S146.s1)
  path146 = B.more {t = configure S146.s1} refl (B.done)

  path147 : B.Runs (configure S147.s0) S147.actions (configure S147.s1)
  path147 = B.more {t = configure S147.s1} refl (B.done)

  path148 : B.Runs (configure S148.s0) S148.actions (configure S148.s1)
  path148 = B.more {t = configure S148.s1} refl (B.done)

  path149 : B.Runs (configure S149.s0) S149.actions (configure S149.s1)
  path149 = B.more {t = configure S149.s1} refl (B.done)

  path150 : B.Runs (configure S150.s0) S150.actions (configure S150.s1)
  path150 = B.more {t = configure S150.s1} refl (B.done)

  path151 : B.Runs (configure S151.s0) S151.actions (configure S151.s1)
  path151 = B.more {t = configure S151.s1} refl (B.done)

  path152 : B.Runs (configure S152.s0) S152.actions (configure S152.s1)
  path152 = B.more {t = configure S152.s1} refl (B.done)

  path153 : B.Runs (configure S153.s0) S153.actions (configure S153.s1)
  path153 = B.more {t = configure S153.s1} refl (B.done)

  path154 : B.Runs (configure S154.s0) S154.actions (configure S154.s1)
  path154 = B.more {t = configure S154.s1} refl (B.done)

  path155 : B.Runs (configure S155.s0) S155.actions (configure S155.s1)
  path155 = B.more {t = configure S155.s1} refl (B.done)

  path156 : B.Runs (configure S156.s0) S156.actions (configure S156.s1)
  path156 = B.more {t = configure S156.s1} refl (B.done)

