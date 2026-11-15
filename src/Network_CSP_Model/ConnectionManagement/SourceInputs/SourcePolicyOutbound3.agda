{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound3 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredPromote as S3

abstract
  path3 : B.Runs (configure S3.s0) S3.actions (configure S3.s21)
  path3 = B.more {t = configure S3.s1} refl (B.more {t = configure S3.s2} refl (B.more {t = configure S3.s3} refl (B.more {t = configure S3.s4} refl (B.more {t = configure S3.s5} refl (B.more {t = configure S3.s6} refl (B.more {t = configure S3.s7} refl (B.more {t = configure S3.s8} refl (B.more {t = configure S3.s9} refl (B.more {t = configure S3.s10} refl (B.more {t = configure S3.s11} refl (B.more {t = configure S3.s12} refl (B.more {t = configure S3.s13} refl (B.more {t = configure S3.s14} refl (B.more {t = configure S3.s15} refl (B.more {t = configure S3.s16} refl (B.more {t = configure S3.s17} refl (B.more {t = configure S3.s18} refl (B.more {t = configure S3.s19} refl (B.more {t = configure S3.s20} refl (B.more {t = configure S3.s21} refl (B.done)))))))))))))))))))))

