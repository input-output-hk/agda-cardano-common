{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound13 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredWarmBudget0 as S45
import ConnectionManagement.Negative.FullConfiguredWarmBudget1Edge0 as S46
import ConnectionManagement.Negative.FullConfiguredWarmBudget1 as S47
import ConnectionManagement.Negative.FullConfiguredWarmBudget2Edge0 as S48
import ConnectionManagement.Negative.FullConfiguredWarmBudget2 as S49
import ConnectionManagement.Negative.FullConfiguredWarmBudget3Edge0 as S50
import ConnectionManagement.Negative.FullConfiguredWarmBudget3 as S51
import ConnectionManagement.Negative.FullConfiguredWarmBudget4Edge0 as S52
import ConnectionManagement.Negative.FullConfiguredWarmBudget4 as S53
import ConnectionManagement.Negative.FullConfiguredWarmBudget5Edge0 as S54
import ConnectionManagement.Negative.FullConfiguredWarmBudget5 as S55
import ConnectionManagement.Negative.FullConfiguredWarmBudget6Edge0 as S56
import ConnectionManagement.Negative.FullConfiguredWarmBudget6 as S57
import ConnectionManagement.Negative.FullConfiguredWarmEdge0 as S58
import ConnectionManagement.Negative.FullConfiguredWarm as S59
import ConnectionManagement.Negative.FullConfiguredCloseBudget0Edge0 as S60
import ConnectionManagement.Negative.FullConfiguredCloseBudget0 as S61
import ConnectionManagement.Negative.FullConfiguredCloseBudget1Edge0 as S62
import ConnectionManagement.Negative.FullConfiguredCloseBudget1 as S63
import ConnectionManagement.Negative.FullConfiguredCloseBudget2Edge0 as S64
import ConnectionManagement.Negative.FullConfiguredCloseBudget2 as S65
import ConnectionManagement.Negative.FullConfiguredCloseBudget3Edge0 as S66
import ConnectionManagement.Negative.FullConfiguredCloseBudget3 as S67
import ConnectionManagement.Negative.FullConfiguredCloseBudget4Edge0 as S68
import ConnectionManagement.Negative.FullConfiguredCloseBudget4 as S69

abstract
  path45 : B.Runs (configure S45.s0) S45.actions (configure S45.s1)
  path45 = B.more {t = configure S45.s1} refl (B.done)

  path46 : B.Runs (configure S46.s0) S46.actions (configure S46.s1)
  path46 = B.more {t = configure S46.s1} refl (B.done)

  path47 : B.Runs (configure S47.s0) S47.actions (configure S47.s1)
  path47 = B.more {t = configure S47.s1} refl (B.done)

  path48 : B.Runs (configure S48.s0) S48.actions (configure S48.s1)
  path48 = B.more {t = configure S48.s1} refl (B.done)

  path49 : B.Runs (configure S49.s0) S49.actions (configure S49.s1)
  path49 = B.more {t = configure S49.s1} refl (B.done)

  path50 : B.Runs (configure S50.s0) S50.actions (configure S50.s1)
  path50 = B.more {t = configure S50.s1} refl (B.done)

  path51 : B.Runs (configure S51.s0) S51.actions (configure S51.s1)
  path51 = B.more {t = configure S51.s1} refl (B.done)

  path52 : B.Runs (configure S52.s0) S52.actions (configure S52.s1)
  path52 = B.more {t = configure S52.s1} refl (B.done)

  path53 : B.Runs (configure S53.s0) S53.actions (configure S53.s1)
  path53 = B.more {t = configure S53.s1} refl (B.done)

  path54 : B.Runs (configure S54.s0) S54.actions (configure S54.s1)
  path54 = B.more {t = configure S54.s1} refl (B.done)

  path55 : B.Runs (configure S55.s0) S55.actions (configure S55.s1)
  path55 = B.more {t = configure S55.s1} refl (B.done)

  path56 : B.Runs (configure S56.s0) S56.actions (configure S56.s1)
  path56 = B.more {t = configure S56.s1} refl (B.done)

  path57 : B.Runs (configure S57.s0) S57.actions (configure S57.s1)
  path57 = B.more {t = configure S57.s1} refl (B.done)

  path58 : B.Runs (configure S58.s0) S58.actions (configure S58.s1)
  path58 = B.more {t = configure S58.s1} refl (B.done)

  path59 : B.Runs (configure S59.s0) S59.actions (configure S59.s1)
  path59 = B.more {t = configure S59.s1} refl (B.done)

  path60 : B.Runs (configure S60.s0) S60.actions (configure S60.s1)
  path60 = B.more {t = configure S60.s1} refl (B.done)

  path61 : B.Runs (configure S61.s0) S61.actions (configure S61.s1)
  path61 = B.more {t = configure S61.s1} refl (B.done)

  path62 : B.Runs (configure S62.s0) S62.actions (configure S62.s1)
  path62 = B.more {t = configure S62.s1} refl (B.done)

  path63 : B.Runs (configure S63.s0) S63.actions (configure S63.s1)
  path63 = B.more {t = configure S63.s1} refl (B.done)

  path64 : B.Runs (configure S64.s0) S64.actions (configure S64.s1)
  path64 = B.more {t = configure S64.s1} refl (B.done)

  path65 : B.Runs (configure S65.s0) S65.actions (configure S65.s1)
  path65 = B.more {t = configure S65.s1} refl (B.done)

  path66 : B.Runs (configure S66.s0) S66.actions (configure S66.s1)
  path66 = B.more {t = configure S66.s1} refl (B.done)

  path67 : B.Runs (configure S67.s0) S67.actions (configure S67.s1)
  path67 = B.more {t = configure S67.s1} refl (B.done)

  path68 : B.Runs (configure S68.s0) S68.actions (configure S68.s1)
  path68 = B.more {t = configure S68.s1} refl (B.done)

  path69 : B.Runs (configure S69.s0) S69.actions (configure S69.s1)
  path69 = B.more {t = configure S69.s1} refl (B.done)

