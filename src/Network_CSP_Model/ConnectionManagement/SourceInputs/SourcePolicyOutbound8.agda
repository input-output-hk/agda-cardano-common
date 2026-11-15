{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound8 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredBodies as S11
import ConnectionManagement.Negative.FullConfiguredChain as S12

abstract
  path11 : B.Runs (configure S11.s0) S11.actions (configure S11.s12)
  path11 = B.more {t = configure S11.s1} refl (B.more {t = configure S11.s2} refl (B.more {t = configure S11.s3} refl (B.more {t = configure S11.s4} refl (B.more {t = configure S11.s5} refl (B.more {t = configure S11.s6} refl (B.more {t = configure S11.s7} refl (B.more {t = configure S11.s8} refl (B.more {t = configure S11.s9} refl (B.more {t = configure S11.s10} refl (B.more {t = configure S11.s11} refl (B.more {t = configure S11.s12} refl (B.done))))))))))))

  path12 : B.Runs (configure S12.s0) S12.actions (configure S12.s10)
  path12 = B.more {t = configure S12.s1} refl (B.more {t = configure S12.s2} refl (B.more {t = configure S12.s3} refl (B.more {t = configure S12.s4} refl (B.more {t = configure S12.s5} refl (B.more {t = configure S12.s6} refl (B.more {t = configure S12.s7} refl (B.more {t = configure S12.s8} refl (B.more {t = configure S12.s9} refl (B.more {t = configure S12.s10} refl (B.done))))))))))

