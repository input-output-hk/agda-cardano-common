{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound5 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredHot18 as S7
import ConnectionManagement.Negative.FullConfiguredHot19 as S8

abstract
  path7 : B.Runs (configure S7.s0) S7.actions (configure S7.s8)
  path7 = B.more {t = configure S7.s1} refl (B.more {t = configure S7.s2} refl (B.more {t = configure S7.s3} refl (B.more {t = configure S7.s4} refl (B.more {t = configure S7.s5} refl (B.more {t = configure S7.s6} refl (B.more {t = configure S7.s7} refl (B.more {t = configure S7.s8} refl (B.done))))))))

  path8 : B.Runs (configure S8.s0) S8.actions (configure S8.s8)
  path8 = B.more {t = configure S8.s1} refl (B.more {t = configure S8.s2} refl (B.more {t = configure S8.s3} refl (B.more {t = configure S8.s4} refl (B.more {t = configure S8.s5} refl (B.more {t = configure S8.s6} refl (B.more {t = configure S8.s7} refl (B.more {t = configure S8.s8} refl (B.done))))))))

