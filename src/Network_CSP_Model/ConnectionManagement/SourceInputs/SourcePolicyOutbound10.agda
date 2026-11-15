{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound10 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredLeiosFetch as S15
import ConnectionManagement.Negative.FullConfiguredResult2Body as S16
import ConnectionManagement.Negative.FullConfiguredResult2 as S17

abstract
  path15 : B.Runs (configure S15.s0) S15.actions (configure S15.s10)
  path15 = B.more {t = configure S15.s1} refl (B.more {t = configure S15.s2} refl (B.more {t = configure S15.s3} refl (B.more {t = configure S15.s4} refl (B.more {t = configure S15.s5} refl (B.more {t = configure S15.s6} refl (B.more {t = configure S15.s7} refl (B.more {t = configure S15.s8} refl (B.more {t = configure S15.s9} refl (B.more {t = configure S15.s10} refl (B.done))))))))))

  path16 : B.Runs (configure S16.s0) S16.actions (configure S16.s6)
  path16 = B.more {t = configure S16.s1} refl (B.more {t = configure S16.s2} refl (B.more {t = configure S16.s3} refl (B.more {t = configure S16.s4} refl (B.more {t = configure S16.s5} refl (B.more {t = configure S16.s6} refl (B.done))))))

  path17 : B.Runs (configure S17.s0) S17.actions (configure S17.s6)
  path17 = B.more {t = configure S17.s1} refl (B.more {t = configure S17.s2} refl (B.more {t = configure S17.s3} refl (B.more {t = configure S17.s4} refl (B.more {t = configure S17.s5} refl (B.more {t = configure S17.s6} refl (B.done))))))

