{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound7 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredDemote as S10

abstract
  path10 : B.Runs (configure S10.s0) S10.actions (configure S10.s18)
  path10 = B.more {t = configure S10.s1} refl (B.more {t = configure S10.s2} refl (B.more {t = configure S10.s3} refl (B.more {t = configure S10.s4} refl (B.more {t = configure S10.s5} refl (B.more {t = configure S10.s6} refl (B.more {t = configure S10.s7} refl (B.more {t = configure S10.s8} refl (B.more {t = configure S10.s9} refl (B.more {t = configure S10.s10} refl (B.more {t = configure S10.s11} refl (B.more {t = configure S10.s12} refl (B.more {t = configure S10.s13} refl (B.more {t = configure S10.s14} refl (B.more {t = configure S10.s15} refl (B.more {t = configure S10.s16} refl (B.more {t = configure S10.s17} refl (B.more {t = configure S10.s18} refl (B.done))))))))))))))))))

