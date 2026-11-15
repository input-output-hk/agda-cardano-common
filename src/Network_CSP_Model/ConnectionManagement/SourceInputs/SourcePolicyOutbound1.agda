{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound1 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredStartup as S1

abstract
  path1 : B.Runs (configure S1.s0) S1.actions (configure S1.s18)
  path1 = B.more {t = configure S1.s1} refl (B.more {t = configure S1.s2} refl (B.more {t = configure S1.s3} refl (B.more {t = configure S1.s4} refl (B.more {t = configure S1.s5} refl (B.more {t = configure S1.s6} refl (B.more {t = configure S1.s7} refl (B.more {t = configure S1.s8} refl (B.more {t = configure S1.s9} refl (B.more {t = configure S1.s10} refl (B.more {t = configure S1.s11} refl (B.more {t = configure S1.s12} refl (B.more {t = configure S1.s13} refl (B.more {t = configure S1.s14} refl (B.more {t = configure S1.s15} refl (B.more {t = configure S1.s16} refl (B.more {t = configure S1.s17} refl (B.more {t = configure S1.s18} refl (B.done))))))))))))))))))

