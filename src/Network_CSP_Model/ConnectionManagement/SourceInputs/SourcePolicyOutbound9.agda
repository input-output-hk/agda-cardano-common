{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound9 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredFetchTx as S13
import ConnectionManagement.Negative.FullConfiguredNotify as S14

abstract
  path13 : B.Runs (configure S13.s0) S13.actions (configure S13.s8)
  path13 = B.more {t = configure S13.s1} refl (B.more {t = configure S13.s2} refl (B.more {t = configure S13.s3} refl (B.more {t = configure S13.s4} refl (B.more {t = configure S13.s5} refl (B.more {t = configure S13.s6} refl (B.more {t = configure S13.s7} refl (B.more {t = configure S13.s8} refl (B.done))))))))

  path14 : B.Runs (configure S14.s0) S14.actions (configure S14.s9)
  path14 = B.more {t = configure S14.s1} refl (B.more {t = configure S14.s2} refl (B.more {t = configure S14.s3} refl (B.more {t = configure S14.s4} refl (B.more {t = configure S14.s5} refl (B.more {t = configure S14.s6} refl (B.more {t = configure S14.s7} refl (B.more {t = configure S14.s8} refl (B.more {t = configure S14.s9} refl (B.done)))))))))

