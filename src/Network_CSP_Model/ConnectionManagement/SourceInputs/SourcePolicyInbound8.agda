{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyInbound8 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.InboundConfiguredLeiosFetchResult3 as S67
import ConnectionManagement.Negative.InboundConfiguredMux0 as S68
import ConnectionManagement.Negative.InboundConfiguredMux1 as S69
import ConnectionManagement.Negative.InboundConfiguredMux2 as S70
import ConnectionManagement.Negative.InboundConfiguredMux3 as S71
import ConnectionManagement.Negative.InboundConfiguredMux4 as S72
import ConnectionManagement.Negative.InboundConfiguredMux5 as S73
import ConnectionManagement.Negative.InboundConfiguredMux6 as S74

abstract
  path67 : B.Runs (configure S67.s0) S67.actions (configure S67.s3)
  path67 = B.more {t = configure S67.s1} refl (B.more {t = configure S67.s2} refl (B.more {t = configure S67.s3} refl (B.done)))

  path68 : B.Runs (configure S68.s0) S68.actions (configure S68.s3)
  path68 = B.more {t = configure S68.s1} refl (B.more {t = configure S68.s2} refl (B.more {t = configure S68.s3} refl (B.done)))

  path69 : B.Runs (configure S69.s0) S69.actions (configure S69.s3)
  path69 = B.more {t = configure S69.s1} refl (B.more {t = configure S69.s2} refl (B.more {t = configure S69.s3} refl (B.done)))

  path70 : B.Runs (configure S70.s0) S70.actions (configure S70.s3)
  path70 = B.more {t = configure S70.s1} refl (B.more {t = configure S70.s2} refl (B.more {t = configure S70.s3} refl (B.done)))

  path71 : B.Runs (configure S71.s0) S71.actions (configure S71.s3)
  path71 = B.more {t = configure S71.s1} refl (B.more {t = configure S71.s2} refl (B.more {t = configure S71.s3} refl (B.done)))

  path72 : B.Runs (configure S72.s0) S72.actions (configure S72.s3)
  path72 = B.more {t = configure S72.s1} refl (B.more {t = configure S72.s2} refl (B.more {t = configure S72.s3} refl (B.done)))

  path73 : B.Runs (configure S73.s0) S73.actions (configure S73.s3)
  path73 = B.more {t = configure S73.s1} refl (B.more {t = configure S73.s2} refl (B.more {t = configure S73.s3} refl (B.done)))

  path74 : B.Runs (configure S74.s0) S74.actions (configure S74.s3)
  path74 = B.more {t = configure S74.s1} refl (B.more {t = configure S74.s2} refl (B.more {t = configure S74.s3} refl (B.done)))

