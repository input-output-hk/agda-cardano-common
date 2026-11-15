{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyInbound7 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.InboundConfiguredNotifyResult1 as S59
import ConnectionManagement.Negative.InboundConfiguredNotifyResult2 as S60
import ConnectionManagement.Negative.InboundConfiguredNotifyResult3 as S61
import ConnectionManagement.Negative.InboundConfiguredLeiosFetchContract0 as S62
import ConnectionManagement.Negative.InboundConfiguredLeiosFetchContract1 as S63
import ConnectionManagement.Negative.InboundConfiguredLeiosFetchResult0 as S64
import ConnectionManagement.Negative.InboundConfiguredLeiosFetchResult1 as S65
import ConnectionManagement.Negative.InboundConfiguredLeiosFetchResult2 as S66

abstract
  path59 : B.Runs (configure S59.s0) S59.actions (configure S59.s3)
  path59 = B.more {t = configure S59.s1} refl (B.more {t = configure S59.s2} refl (B.more {t = configure S59.s3} refl (B.done)))

  path60 : B.Runs (configure S60.s0) S60.actions (configure S60.s3)
  path60 = B.more {t = configure S60.s1} refl (B.more {t = configure S60.s2} refl (B.more {t = configure S60.s3} refl (B.done)))

  path61 : B.Runs (configure S61.s0) S61.actions (configure S61.s3)
  path61 = B.more {t = configure S61.s1} refl (B.more {t = configure S61.s2} refl (B.more {t = configure S61.s3} refl (B.done)))

  path62 : B.Runs (configure S62.s0) S62.actions (configure S62.s3)
  path62 = B.more {t = configure S62.s1} refl (B.more {t = configure S62.s2} refl (B.more {t = configure S62.s3} refl (B.done)))

  path63 : B.Runs (configure S63.s0) S63.actions (configure S63.s2)
  path63 = B.more {t = configure S63.s1} refl (B.more {t = configure S63.s2} refl (B.done))

  path64 : B.Runs (configure S64.s0) S64.actions (configure S64.s3)
  path64 = B.more {t = configure S64.s1} refl (B.more {t = configure S64.s2} refl (B.more {t = configure S64.s3} refl (B.done)))

  path65 : B.Runs (configure S65.s0) S65.actions (configure S65.s3)
  path65 = B.more {t = configure S65.s1} refl (B.more {t = configure S65.s2} refl (B.more {t = configure S65.s3} refl (B.done)))

  path66 : B.Runs (configure S66.s0) S66.actions (configure S66.s3)
  path66 = B.more {t = configure S66.s1} refl (B.more {t = configure S66.s2} refl (B.more {t = configure S66.s3} refl (B.done)))

