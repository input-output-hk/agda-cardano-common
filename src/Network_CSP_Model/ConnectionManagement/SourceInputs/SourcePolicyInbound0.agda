{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyInbound0 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.InboundConfiguredAdmission0 as S0
import ConnectionManagement.Negative.InboundConfiguredAdmission1 as S1
import ConnectionManagement.Negative.InboundConfiguredAdmission2 as S2
import ConnectionManagement.Negative.InboundConfiguredAdmission3 as S3
import ConnectionManagement.Negative.InboundConfiguredAdmission4 as S4
import ConnectionManagement.Negative.InboundConfiguredAdmission5 as S5
import ConnectionManagement.Negative.InboundConfiguredAdmission6 as S6
import ConnectionManagement.Negative.InboundConfiguredAdmission7 as S7

abstract
  path0 : B.Runs (configure S0.s0) S0.actions (configure S0.s3)
  path0 = B.more {t = configure S0.s1} refl (B.more {t = configure S0.s2} refl (B.more {t = configure S0.s3} refl (B.done)))

  path1 : B.Runs (configure S1.s0) S1.actions (configure S1.s3)
  path1 = B.more {t = configure S1.s1} refl (B.more {t = configure S1.s2} refl (B.more {t = configure S1.s3} refl (B.done)))

  path2 : B.Runs (configure S2.s0) S2.actions (configure S2.s3)
  path2 = B.more {t = configure S2.s1} refl (B.more {t = configure S2.s2} refl (B.more {t = configure S2.s3} refl (B.done)))

  path3 : B.Runs (configure S3.s0) S3.actions (configure S3.s3)
  path3 = B.more {t = configure S3.s1} refl (B.more {t = configure S3.s2} refl (B.more {t = configure S3.s3} refl (B.done)))

  path4 : B.Runs (configure S4.s0) S4.actions (configure S4.s3)
  path4 = B.more {t = configure S4.s1} refl (B.more {t = configure S4.s2} refl (B.more {t = configure S4.s3} refl (B.done)))

  path5 : B.Runs (configure S5.s0) S5.actions (configure S5.s3)
  path5 = B.more {t = configure S5.s1} refl (B.more {t = configure S5.s2} refl (B.more {t = configure S5.s3} refl (B.done)))

  path6 : B.Runs (configure S6.s0) S6.actions (configure S6.s3)
  path6 = B.more {t = configure S6.s1} refl (B.more {t = configure S6.s2} refl (B.more {t = configure S6.s3} refl (B.done)))

  path7 : B.Runs (configure S7.s0) S7.actions (configure S7.s3)
  path7 = B.more {t = configure S7.s1} refl (B.more {t = configure S7.s2} refl (B.more {t = configure S7.s3} refl (B.done)))

