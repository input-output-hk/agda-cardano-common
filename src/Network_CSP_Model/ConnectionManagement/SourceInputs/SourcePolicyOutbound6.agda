{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound6 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredHot as S9

abstract
  path9 : B.Runs (configure S9.s0) S9.actions (configure S9.s16)
  path9 = B.more {t = configure S9.s1} refl (B.more {t = configure S9.s2} refl (B.more {t = configure S9.s3} refl (B.more {t = configure S9.s4} refl (B.more {t = configure S9.s5} refl (B.more {t = configure S9.s6} refl (B.more {t = configure S9.s7} refl (B.more {t = configure S9.s8} refl (B.more {t = configure S9.s9} refl (B.more {t = configure S9.s10} refl (B.more {t = configure S9.s11} refl (B.more {t = configure S9.s12} refl (B.more {t = configure S9.s13} refl (B.more {t = configure S9.s14} refl (B.more {t = configure S9.s15} refl (B.more {t = configure S9.s16} refl (B.done))))))))))))))))

