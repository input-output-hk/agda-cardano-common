{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyInbound6 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.InboundConfiguredTxContract1 as S50
import ConnectionManagement.Negative.InboundConfiguredTxContract2 as S51
import ConnectionManagement.Negative.InboundConfiguredTxResult0 as S52
import ConnectionManagement.Negative.InboundConfiguredTxResult1 as S53
import ConnectionManagement.Negative.InboundConfiguredTxResult2 as S54
import ConnectionManagement.Negative.InboundConfiguredTxResult3 as S55
import ConnectionManagement.Negative.InboundConfiguredNotifyContract0 as S56
import ConnectionManagement.Negative.InboundConfiguredNotifyContract1 as S57
import ConnectionManagement.Negative.InboundConfiguredNotifyResult0 as S58

abstract
  path50 : B.Runs (configure S50.s0) S50.actions (configure S50.s3)
  path50 = B.more {t = configure S50.s1} refl (B.more {t = configure S50.s2} refl (B.more {t = configure S50.s3} refl (B.done)))

  path51 : B.Runs (configure S51.s0) S51.actions (configure S51.s1)
  path51 = B.more {t = configure S51.s1} refl (B.done)

  path52 : B.Runs (configure S52.s0) S52.actions (configure S52.s3)
  path52 = B.more {t = configure S52.s1} refl (B.more {t = configure S52.s2} refl (B.more {t = configure S52.s3} refl (B.done)))

  path53 : B.Runs (configure S53.s0) S53.actions (configure S53.s3)
  path53 = B.more {t = configure S53.s1} refl (B.more {t = configure S53.s2} refl (B.more {t = configure S53.s3} refl (B.done)))

  path54 : B.Runs (configure S54.s0) S54.actions (configure S54.s3)
  path54 = B.more {t = configure S54.s1} refl (B.more {t = configure S54.s2} refl (B.more {t = configure S54.s3} refl (B.done)))

  path55 : B.Runs (configure S55.s0) S55.actions (configure S55.s3)
  path55 = B.more {t = configure S55.s1} refl (B.more {t = configure S55.s2} refl (B.more {t = configure S55.s3} refl (B.done)))

  path56 : B.Runs (configure S56.s0) S56.actions (configure S56.s3)
  path56 = B.more {t = configure S56.s1} refl (B.more {t = configure S56.s2} refl (B.more {t = configure S56.s3} refl (B.done)))

  path57 : B.Runs (configure S57.s0) S57.actions (configure S57.s3)
  path57 = B.more {t = configure S57.s1} refl (B.more {t = configure S57.s2} refl (B.more {t = configure S57.s3} refl (B.done)))

  path58 : B.Runs (configure S58.s0) S58.actions (configure S58.s3)
  path58 = B.more {t = configure S58.s1} refl (B.more {t = configure S58.s2} refl (B.more {t = configure S58.s3} refl (B.done)))

