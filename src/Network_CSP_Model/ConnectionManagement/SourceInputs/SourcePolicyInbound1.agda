{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyInbound1 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.InboundConfiguredAdmission8 as S8
import ConnectionManagement.Negative.InboundConfiguredAdmission9 as S9
import ConnectionManagement.Negative.InboundConfiguredAdmission10 as S10
import ConnectionManagement.Negative.InboundConfiguredAdmission11 as S11
import ConnectionManagement.Negative.InboundConfiguredAdmission12 as S12
import ConnectionManagement.Negative.InboundConfiguredStart0 as S13
import ConnectionManagement.Negative.InboundConfiguredStart1 as S14
import ConnectionManagement.Negative.InboundConfiguredStart2 as S15

abstract
  path8 : B.Runs (configure S8.s0) S8.actions (configure S8.s3)
  path8 = B.more {t = configure S8.s1} refl (B.more {t = configure S8.s2} refl (B.more {t = configure S8.s3} refl (B.done)))

  path9 : B.Runs (configure S9.s0) S9.actions (configure S9.s3)
  path9 = B.more {t = configure S9.s1} refl (B.more {t = configure S9.s2} refl (B.more {t = configure S9.s3} refl (B.done)))

  path10 : B.Runs (configure S10.s0) S10.actions (configure S10.s3)
  path10 = B.more {t = configure S10.s1} refl (B.more {t = configure S10.s2} refl (B.more {t = configure S10.s3} refl (B.done)))

  path11 : B.Runs (configure S11.s0) S11.actions (configure S11.s3)
  path11 = B.more {t = configure S11.s1} refl (B.more {t = configure S11.s2} refl (B.more {t = configure S11.s3} refl (B.done)))

  path12 : B.Runs (configure S12.s0) S12.actions (configure S12.s2)
  path12 = B.more {t = configure S12.s1} refl (B.more {t = configure S12.s2} refl (B.done))

  path13 : B.Runs (configure S13.s0) S13.actions (configure S13.s3)
  path13 = B.more {t = configure S13.s1} refl (B.more {t = configure S13.s2} refl (B.more {t = configure S13.s3} refl (B.done)))

  path14 : B.Runs (configure S14.s0) S14.actions (configure S14.s3)
  path14 = B.more {t = configure S14.s1} refl (B.more {t = configure S14.s2} refl (B.more {t = configure S14.s3} refl (B.done)))

  path15 : B.Runs (configure S15.s0) S15.actions (configure S15.s3)
  path15 = B.more {t = configure S15.s1} refl (B.more {t = configure S15.s2} refl (B.more {t = configure S15.s3} refl (B.done)))

