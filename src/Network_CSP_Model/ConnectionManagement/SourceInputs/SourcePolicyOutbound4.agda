{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound4 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredHot2 as S4
import ConnectionManagement.Negative.FullConfiguredHot3 as S5
import ConnectionManagement.Negative.FullConfiguredHot4 as S6

abstract
  path4 : B.Runs (configure S4.s0) S4.actions (configure S4.s8)
  path4 = B.more {t = configure S4.s1} refl (B.more {t = configure S4.s2} refl (B.more {t = configure S4.s3} refl (B.more {t = configure S4.s4} refl (B.more {t = configure S4.s5} refl (B.more {t = configure S4.s6} refl (B.more {t = configure S4.s7} refl (B.more {t = configure S4.s8} refl (B.done))))))))

  path5 : B.Runs (configure S5.s0) S5.actions (configure S5.s8)
  path5 = B.more {t = configure S5.s1} refl (B.more {t = configure S5.s2} refl (B.more {t = configure S5.s3} refl (B.more {t = configure S5.s4} refl (B.more {t = configure S5.s5} refl (B.more {t = configure S5.s6} refl (B.more {t = configure S5.s7} refl (B.more {t = configure S5.s8} refl (B.done))))))))

  path6 : B.Runs (configure S6.s0) S6.actions (configure S6.s8)
  path6 = B.more {t = configure S6.s1} refl (B.more {t = configure S6.s2} refl (B.more {t = configure S6.s3} refl (B.more {t = configure S6.s4} refl (B.more {t = configure S6.s5} refl (B.more {t = configure S6.s6} refl (B.more {t = configure S6.s7} refl (B.more {t = configure S6.s8} refl (B.done))))))))

