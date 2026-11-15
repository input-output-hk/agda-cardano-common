{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound0 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredContractAcquire as S0

abstract
  path0 : B.Runs (configure S0.s0) S0.actions (configure S0.s25)
  path0 = B.more {t = configure S0.s1} refl (B.more {t = configure S0.s2} refl (B.more {t = configure S0.s3} refl (B.more {t = configure S0.s4} refl (B.more {t = configure S0.s5} refl (B.more {t = configure S0.s6} refl (B.more {t = configure S0.s7} refl (B.more {t = configure S0.s8} refl (B.more {t = configure S0.s9} refl (B.more {t = configure S0.s10} refl (B.more {t = configure S0.s11} refl (B.more {t = configure S0.s12} refl (B.more {t = configure S0.s13} refl (B.more {t = configure S0.s14} refl (B.more {t = configure S0.s15} refl (B.more {t = configure S0.s16} refl (B.more {t = configure S0.s17} refl (B.more {t = configure S0.s18} refl (B.more {t = configure S0.s19} refl (B.more {t = configure S0.s20} refl (B.more {t = configure S0.s21} refl (B.more {t = configure S0.s22} refl (B.more {t = configure S0.s23} refl (B.more {t = configure S0.s24} refl (B.more {t = configure S0.s25} refl (B.done)))))))))))))))))))))))))

