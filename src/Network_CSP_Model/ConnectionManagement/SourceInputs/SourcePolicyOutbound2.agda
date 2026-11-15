{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound2 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredEstablished as S2

abstract
  path2 : B.Runs (configure S2.s0) S2.actions (configure S2.s21)
  path2 = B.more {t = configure S2.s1} refl (B.more {t = configure S2.s2} refl (B.more {t = configure S2.s3} refl (B.more {t = configure S2.s4} refl (B.more {t = configure S2.s5} refl (B.more {t = configure S2.s6} refl (B.more {t = configure S2.s7} refl (B.more {t = configure S2.s8} refl (B.more {t = configure S2.s9} refl (B.more {t = configure S2.s10} refl (B.more {t = configure S2.s11} refl (B.more {t = configure S2.s12} refl (B.more {t = configure S2.s13} refl (B.more {t = configure S2.s14} refl (B.more {t = configure S2.s15} refl (B.more {t = configure S2.s16} refl (B.more {t = configure S2.s17} refl (B.more {t = configure S2.s18} refl (B.more {t = configure S2.s19} refl (B.more {t = configure S2.s20} refl (B.more {t = configure S2.s21} refl (B.done)))))))))))))))))))))

