{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- LeiosNotify (cardano-blueprint table, no pipelining): CLEAN TERMINATION of the real
-- pair `sys` of `LeiosNotifyQuit` (client at `(l , lo)`, renamed server, wire
-- synchronised, api / done open).  ∀ `Params`, ∀ link `l`.
--
-- THE RESULTS, each about every √-free trace `s` of `sys` (`sys ⟹∖√⟨ s ⟩ W`):
--   (2a) `done-last`: an event carrying MsgDone is the LAST event of the trace — nothing
--        at all follows it (no wire event, no api / done event either) — and the state it
--        leads to has terminated (√ is the only move left).
--   (2b) `quit-irrevocable`: whatever follows an event carrying MsgQuit is a PREFIX of
--        [the server's peer-local done , MsgDone]; hence (`quit-only-done`) every wire
--        event after MsgQuit carries MsgDone — no RequestNext, no notification, no
--        MsgCanceled, no second MsgQuit, and no api event of either peer.
--   (2c) `joint-termination`: every reachable state is `Par⊤ wire C S` with the client
--        component `C` returned iff the server component `S` has (no half-closed state),
--        and a returned state has both components returned.  The phase-level core is
--        `jEndC` / `jEndS`: in every joint phase of the invariant `J` the client is at End
--        (`cE`) iff the server is (`sE`).
--   (2d) `handshake-only`: a trace after which `sys` has terminated projects (`wire`) to
--        `w₀ ++ [MsgQuit , MsgDone]` with the EXACT events the peers send (their fixed
--        envelope `time₀` / sender mode / `length₀`), `w₀` free of both; so MsgQuit and
--        MsgDone each occur exactly once in `wire s`.
--
-- THE METHOD.  Not via `sys-conforms`: `LNPSpec` accepts every envelope, so table-level
-- reasoning would only give "SOME event carrying MsgQuit", and (2b)'s strongest form
-- speaks of the server's done event, which `wire` erases.  Instead every result reads the
-- abstract run of the product abstraction `SysA` (`Gen.runE`, the same run `sys-conforms`
-- is built on): a step carrying MsgQuit / MsgDone is the rendezvous `cSQ`/`sQi` resp.
-- `cDn`/`sDS` (`quitStep`, `doneStep`), after which three post-quit phases (`PostQ`) owe an
-- exact remaining trace (`postQ`); (2d) transfers an owed closing trace backwards along the
-- run (`oweStep`), and (2c) uses `J` through `Walk.walk`.  Constructive (no `Classical`).
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.LeiosNotifyQuitTerm (p : Params) where

open import Data.Bool using (T)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-conicalˡ; ++-conicalʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-assoc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
import Data.Unit as U
open import Data.Unit.Polymorphic using (tt)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Class.DecEq using (_≟_)

open import Process_Trees
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.Data p
open import Cardano_network.LeiosNotifyP p
open import Cardano_network.Parametric.Leios.LeiosNotifyQuit p

open import CSP.Operators LNPEv-≟ using (Par⊤)
open import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv}
open import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv} using (_⟹∖√⟨_⟩_)

------------------------------------------------------------------------
-- §0  Messages carried by events, and counting them (no link content)
------------------------------------------------------------------------

-- the LeiosNotify message a wire event carries (nothing for api / done events)
msgOf : Event → Maybe MessageLeiosNotifyP
msgOf (evLabel _ (sendLNP _ _)    (_ , _ , _ , leiosNotifyP m)) = just m
msgOf (evLabel _ (receiveLNP _ _) (_ , _ , _ , leiosNotifyP m)) = just m
msgOf _                                                         = nothing

-- `e` is a wire event carrying the protocol message `m`
CarriesW : MessageLeiosNotifyP → Event → Set
CarriesW m e = msgOf e ≡ just m

-- 1 if an optional message is `m`, else 0
hit : MessageLeiosNotifyP → Maybe MessageLeiosNotifyP → ℕ
hit _ nothing   = 0
hit m (just m′) with m′ ≟ m
... | yes _ = 1
... | no  _ = 0

-- the number of events of a trace carrying the message `m`
occ : MessageLeiosNotifyP → List Event → ℕ
occ m []      = 0
occ m (e ∷ s) = hit m (msgOf e) + occ m s

-- counting distributes over concatenation
occ-++ : ∀ m a b → occ m (a ++ b) ≡ occ m a + occ m b
occ-++ m []      b = refl
occ-++ m (e ∷ a) b = trans (cong (hit m (msgOf e) +_) (occ-++ m a b))
                           (sym (+-assoc (hit m (msgOf e)) (occ m a) (occ m b)))

-- a prefix without `m` adds nothing to the count
occ-tail : ∀ m w₀ t → occ m w₀ ≡ 0 → occ m (w₀ ++ t) ≡ occ m t
occ-tail m w₀ t c = trans (occ-++ m w₀ t) (cong (_+ occ m t) c)

-- a trace carrying neither closing message (MsgQuit, MsgDone)
Clean : List Event → Set
Clean w = occ MsgLNPQuit w ≡ 0 × occ MsgLNPDone w ≡ 0

------------------------------------------------------------------------
-- everything below is for one link `l`
------------------------------------------------------------------------

module _ (l : Link) where

  open Gen l (SysA l) using (ARun; r0; rτ; rE; runE)
  open Walk l (SysA l) (λ σ → σ) (λ a → a) using (walk)

  -- this link's abstract labels, read as events
  ⌞_⌟ : Lab l → Event
  ⌞_⌟ = ⌜_⌝ l

  -- MsgQuit on the wire, exactly as the client sends it
  Qe : Event
  Qe = ⌞ wS lo (pay l FromInitiator MsgLNPQuit) ⌟

  -- MsgDone on the wire, exactly as the server sends it
  De : Event
  De = ⌞ wR lo (pay l FromResponder MsgLNPDone) ⌟

  -- the server's peer-local done (between MsgQuit and MsgDone)
  dnE : Event
  dnE = ⌞ dn hi ⌟

  -- the client phase of a system state
  cOf : SysS l → CS l
  cOf σ = proj₁ (proj₁ σ)

  -- a label carrying a message is a wire label
  wireOf : ∀ ω {m} → CarriesW m ⌞ ω ⌟ → InE l (wireES l) ω
  wireOf (wS _ _)   _ = U.tt
  wireOf (wR _ _)   _ = U.tt
  wireOf (ap _ _ _) ()
  wireOf (dn _)     ()

  -- an off-wire event is dropped by the projection
  offWire : ∀ ω {s} → ¬ InE l (wireES l) ω → wire l (⌞ ω ⌟ ∷ s) ≡ wire l s
  offWire (wS _ _)   ¬w = ⊥-elim (¬w U.tt)
  offWire (wR _ _)   ¬w = ⊥-elim (¬w U.tt)
  offWire (ap _ _ _) _  = refl
  offWire (dn _)     _  = refl

  -- the suffix of an abstract run after a given prefix of its trace
  dropA : ∀ s₁ {s₂ σ σ″} → ARun σ (s₁ ++ s₂) σ″ → Σ[ σ′ ∈ SysS l ] ARun σ′ s₂ σ″
  dropA []       r        = _ , r
  dropA (e ∷ s₁) (rτ _ r) = dropA (e ∷ s₁) r
  dropA (e ∷ s₁) (rE _ r) = dropA s₁ r

  ------------------------------------------------------------------------
  -- §1  After MsgQuit: three phases, each owing an exact remaining trace
  ------------------------------------------------------------------------

  -- the joint phases after MsgQuit (loop-back flags free): both in StQuit; the server's
  -- done reported; both at End
  data PostQ : SysS l → Set where
    pq2 : ∀ {f g} → PostQ ((cQ , f) , (sQ , g))
    pq3 : ∀ {f g} → PostQ ((cQ , f) , (sD , g))
    pq4 : ∀ {f g} → PostQ ((cE , f) , (sE , g))

  -- the visible events a post-quit phase still owes before √
  owedQ : ∀ {σ} → PostQ σ → List Event
  owedQ pq2 = dnE ∷ De ∷ []
  owedQ pq3 = De ∷ []
  owedQ pq4 = []

  -- a post-quit phase owing nothing has terminated
  fin0 : ∀ {σ} (q : PostQ σ) → owedQ q ≡ [] → Abs.Fin (SysA l) σ
  fin0 pq4 _ = U.tt , U.tt
  fin0 pq2 ()
  fin0 pq3 ()

  -- every run from a post-quit phase pays off part of the owed trace, exactly, and ends
  -- in a post-quit phase owing the rest
  postQ : ∀ {σ s σ′} → ARun σ s σ′ → (q : PostQ σ) → Σ[ q′ ∈ PostQ σ′ ] (s ++ owedQ q′ ≡ owedQ q)
  postQ r0 q = q , refl
  postQ (rτ (P1.pτL cτQ) ar) pq2 = postQ ar pq2
  postQ (rτ (P1.pτR sτQ) ar) pq2 = postQ ar pq2
  postQ (rτ (P1.pτL cτQ) ar) pq3 = postQ ar pq3
  postQ (rE (P1.psR _ sDn) ar) pq2 with postQ ar pq3
  ... | q′ , eq = q′ , cong (dnE ∷_) eq
  postQ (rE (P1.psy _ cDn sDS) ar) pq3 with postQ ar pq4
  ... | q′ , eq = q′ , cong (De ∷_) eq
  postQ (rE (P1.psL ¬w cDn) _)  pq2 = ⊥-elim (¬w U.tt)
  postQ (rE (P1.psL ¬w cDn) _)  pq3 = ⊥-elim (¬w U.tt)
  postQ (rE (P1.psR ¬w sDS) _)  pq3 = ⊥-elim (¬w U.tt)

  -- a system step carrying MsgQuit is the rendezvous `cSQ` / `sQi`: both peers in StQuit
  quitStep : ∀ {σ ω σ′} → Abs.Stp (SysA l) σ (ev′ ω) σ′ → CarriesW MsgLNPQuit ⌞ ω ⌟
           → Σ[ q ∈ PostQ σ′ ] (owedQ q ≡ dnE ∷ De ∷ [])
  quitStep (P1.psL {ω = ω} ¬w _) c = ⊥-elim (¬w (wireOf ω c))
  quitStep (P1.psR {ω = ω} ¬w _) c = ⊥-elim (¬w (wireOf ω c))
  quitStep (P1.psy _ cSQ sQi) _ = pq2 , refl
  quitStep (P1.psy _ cSR sRN) ()
  quitStep (P1.psy _ (cRA _) (sNA _)) ()
  quitStep (P1.psy _ (cRO _ _) (sNO _ _)) ()
  quitStep (P1.psy _ (cRT _) (sNT _)) ()
  quitStep (P1.psy _ (cRV _) (sNV _)) ()
  quitStep (P1.psy _ cRC sNC) ()
  quitStep (P1.psy _ cDn sDS) ()
  quitStep (P1.psy _ (cRN _) ()) _
  quitStep (P1.psy _ (cQi _) ()) _
  quitStep (P1.psy _ (cDA _) ()) _
  quitStep (P1.psy _ (cDO _ _) ()) _
  quitStep (P1.psy _ (cDT _) ()) _
  quitStep (P1.psy _ (cDV _) ()) _

  -- a system step carrying MsgDone is the rendezvous `cDn` / `sDS`: both peers at End
  doneStep : ∀ {σ ω σ′} → Abs.Stp (SysA l) σ (ev′ ω) σ′ → CarriesW MsgLNPDone ⌞ ω ⌟
           → Σ[ q ∈ PostQ σ′ ] (owedQ q ≡ [])
  doneStep (P1.psL {ω = ω} ¬w _) c = ⊥-elim (¬w (wireOf ω c))
  doneStep (P1.psR {ω = ω} ¬w _) c = ⊥-elim (¬w (wireOf ω c))
  doneStep (P1.psy _ cDn sDS) _ = pq4 , refl
  doneStep (P1.psy _ cSR sRN) ()
  doneStep (P1.psy _ cSQ sQi) ()
  doneStep (P1.psy _ (cRA _) (sNA _)) ()
  doneStep (P1.psy _ (cRO _ _) (sNO _ _)) ()
  doneStep (P1.psy _ (cRT _) (sNT _)) ()
  doneStep (P1.psy _ (cRV _) (sNV _)) ()
  doneStep (P1.psy _ cRC sNC) ()
  doneStep (P1.psy _ (cRN _) ()) _
  doneStep (P1.psy _ (cQi _) ()) _
  doneStep (P1.psy _ (cDA _) ()) _
  doneStep (P1.psy _ (cDO _ _) ()) _
  doneStep (P1.psy _ (cDT _) ()) _
  doneStep (P1.psy _ (cDV _) ()) _

  -- a run starting with an event carrying MsgQuit continues with a prefix of the owed
  -- [server's done , MsgDone]
  afterQ : ∀ {σ e s σ′} → ARun σ (e ∷ s) σ′ → CarriesW MsgLNPQuit e
         → Σ[ u ∈ List Event ] (s ++ u ≡ dnE ∷ De ∷ [])
  afterQ (rτ _ ar) c = afterQ ar c
  afterQ (rE a ar) c with quitStep a c
  ... | q , eq with postQ ar q
  ...   | q′ , eq′ = owedQ q′ , trans eq′ eq

  -- (the end of a run that starts with an event carrying MsgDone)
  doneEnd : ∀ {σ s σ′} → ARun σ s σ′ → Σ[ q ∈ PostQ σ ] (owedQ q ≡ []) → s ≡ [] × Abs.Fin (SysA l) σ′
  doneEnd {s = s} ar (q , o) with postQ ar q
  ... | q′ , eq = ++-conicalˡ s _ e₀ , fin0 q′ (++-conicalʳ s _ e₀)
    where
    -- the run pays off an empty debt
    e₀ : s ++ owedQ q′ ≡ []
    e₀ = trans eq o

  -- a run starting with an event carrying MsgDone has nothing after it, and ends at End
  afterD : ∀ {σ e s σ′} → ARun σ (e ∷ s) σ′ → CarriesW MsgLNPDone e → s ≡ [] × Abs.Fin (SysA l) σ′
  afterD (rτ _ ar) c = afterD ar c
  afterD (rE a ar) c = doneEnd ar (doneStep a c)

  ------------------------------------------------------------------------
  -- §2  (2a) DONE IS LAST, (2b) QUIT IS IRREVOCABLE
  ------------------------------------------------------------------------

  -- (2a) DONE IS LAST.  If a √-free trace of `sys` has an event carrying MsgDone, that
  -- event is the trace's last one — NOTHING follows it, wire, api or done — and the state
  -- reached has terminated (`sys` can only do √ there)
  done-last : ∀ {s₁ e s₂ W} → sys l ⟹∖√⟨ s₁ ++ e ∷ s₂ ⟩ W → CarriesW MsgLNPDone e
            → s₂ ≡ [] × PTree.force W ≡ ret tt
  done-last {s₁} r c with runE (sys₀ l) r
  ... | _ , ar , pos with afterD (proj₂ (dropA s₁ ar)) c
  ...   | e₂ , fn = e₂ , AbsI.introR (SysI l) pos fn

  -- (2b) QUIT IS IRREVOCABLE.  Whatever follows an event carrying MsgQuit in a √-free
  -- trace of `sys` is a prefix of [the server's peer-local done , MsgDone (exact)]
  quit-irrevocable : ∀ {s₁ e s₂ W} → sys l ⟹∖√⟨ s₁ ++ e ∷ s₂ ⟩ W → CarriesW MsgLNPQuit e
                   → Σ[ u ∈ List Event ] (s₂ ++ u ≡ dnE ∷ De ∷ [])
  quit-irrevocable {s₁} r c with runE (sys₀ l) r
  ... | _ , ar , _ = afterQ (proj₂ (dropA s₁ ar)) c

  -- a wire event carries MsgDone
  WireDone : Event → Set
  WireDone e = T (isWE l e) → CarriesW MsgLNPDone e

  -- every prefix of [server's done , MsgDone] has only MsgDone on the wire
  tailAll : ∀ s {u} → s ++ u ≡ dnE ∷ De ∷ [] → All WireDone s
  tailAll []                _    = []
  tailAll (_ ∷ [])          refl = (λ ()) ∷ []
  tailAll (_ ∷ _ ∷ [])      refl = (λ ()) ∷ (λ _ → refl) ∷ []
  tailAll (_ ∷ _ ∷ _ ∷ _)   ()

  -- (2b) … hence every wire event after MsgQuit carries MsgDone: no RequestNext, no
  -- notification, no MsgCanceled, no second MsgQuit
  quit-only-done : ∀ {s₁ e s₂ W} → sys l ⟹∖√⟨ s₁ ++ e ∷ s₂ ⟩ W → CarriesW MsgLNPQuit e
                 → All WireDone s₂
  quit-only-done {s₂ = s₂} r c = tailAll s₂ (proj₂ (quit-irrevocable r c))

  ------------------------------------------------------------------------
  -- §3  (2c) JOINT TERMINATION
  ------------------------------------------------------------------------

  -- in every joint phase of `J`, a client at End has a server at End …
  jEndC : ∀ {c s f g} → J l c s → CFin l (c , f) → SFin l (s , g)
  jEndC q4     _ = U.tt
  jEndC j1     ()
  jEndC j2     ()
  jEndC j3     ()
  jEndC (j4 _) ()
  jEndC (j5 _) ()
  jEndC q1     ()
  jEndC q2     ()
  jEndC q3     ()

  -- … and a server at End has a client at End
  jEndS : ∀ {c s f g} → J l c s → SFin l (s , g) → CFin l (c , f)
  jEndS q4     _ = U.tt
  jEndS j1     ()
  jEndS j2     ()
  jEndS j3     ()
  jEndS (j4 _) ()
  jEndS (j5 _) ()
  jEndS q1     ()
  jEndS q2     ()
  jEndS q3     ()

  -- (2c) JOINT TERMINATION.  Every √-free-reachable state of `sys` is the client
  -- component `C` in parallel with the server component `S`, where `C` has returned iff
  -- `S` has (there is no half-closed state), and if the state itself has terminated, both
  -- components have
  joint-termination : ∀ {s W} → sys l ⟹∖√⟨ s ⟩ W
    → Σ[ C ∈ Tree ] Σ[ S ∈ Tree ]
        ( W ≡ Par⊤ (wireES l) C S
        × (PTree.force C ≡ ret tt → PTree.force S ≡ ret tt)
        × (PTree.force S ≡ ret tt → PTree.force C ≡ ret tt)
        × (PTree.force W ≡ ret tt → PTree.force C ≡ ret tt × PTree.force S ≡ ret tt))
  joint-termination {W = W} r with runE (sys₀ l) r
  ... | _ , ar , (C , S , eqW , pc , ps) with walk ar j1
  ...   | j , _ =
          C , S , eqW
        , (λ e → sIntroR l ps (jEndC j (cElimR l pc e)))
        , (λ e → cIntroR l pc (jEndS j (sElimR l ps e)))
        , both
    where
    -- a terminated pair has both components terminated
    both : PTree.force W ≡ ret tt → PTree.force C ≡ ret tt × PTree.force S ≡ ret tt
    both e with Abs.elimR (SysA l) (C , S , eqW , pc , ps) e
    ... | cf , sf = cIntroR l pc cf , sIntroR l ps sf

  ------------------------------------------------------------------------
  -- §4  (2d) HANDSHAKE-ONLY TERMINATION
  ------------------------------------------------------------------------

  -- a projected trace: a clean prefix, then exactly MsgQuit and MsgDone
  OwePre : List Event → Set₁
  OwePre w = Σ[ w₀ ∈ List Event ] (w ≡ w₀ ++ Qe ∷ De ∷ [] × Clean w₀)

  -- what the rest of a terminating run projects to, by the client's phase: before the
  -- client sends MsgQuit, a clean prefix then [MsgQuit , MsgDone]; in StQuit, [MsgDone];
  -- at End, nothing
  Owe : CS l → List Event → Set₁
  Owe cQ w = w ≡ De ∷ []
  Owe cE w = w ≡ []
  Owe _  w = OwePre w

  -- what a step puts in front of a trace
  lead : ALbl l → List Event → List Event
  lead τ′      s = s
  lead (ev′ ω) s = ⌞ ω ⌟ ∷ s

  -- a wire event carrying neither closing message extends the clean prefix
  consW : ∀ e {w} → hit MsgLNPQuit (msgOf e) ≡ 0 → hit MsgLNPDone (msgOf e) ≡ 0 → OwePre w → OwePre (e ∷ w)
  consW e hq hd (w₀ , eq , cq , cd) = e ∷ w₀ , cong (e ∷_) eq , cong₂ _+_ hq cq , cong₂ _+_ hd cd

  -- every system step transfers the owed projection backwards
  oweStep : ∀ {σ ℓ σ′ s} → Abs.Stp (SysA l) σ ℓ σ′ → Owe (cOf σ′) (wire l s) → Owe (cOf σ) (wire l (lead ℓ s))
  oweStep (P1.pτL cτI) i = i
  oweStep (P1.pτL cτB) i = i
  oweStep (P1.pτL cτQ) i = i
  oweStep (P1.pτR _)   i = i
  oweStep {s = s} (P1.psR {ω = ω} ¬w _) i = subst (Owe _) (sym (offWire ω {s} ¬w)) i
  oweStep (P1.psL _ (cRN _))   i = i
  oweStep (P1.psL _ (cQi _))   i = i
  oweStep (P1.psL _ (cDA _))   i = i
  oweStep (P1.psL _ (cDO _ _)) i = i
  oweStep (P1.psL _ (cDT _))   i = i
  oweStep (P1.psL _ (cDV _))   i = i
  oweStep (P1.psL ¬w cSR)       _ = ⊥-elim (¬w U.tt)
  oweStep (P1.psL ¬w cSQ)       _ = ⊥-elim (¬w U.tt)
  oweStep (P1.psL ¬w (cRA _))   _ = ⊥-elim (¬w U.tt)
  oweStep (P1.psL ¬w (cRO _ _)) _ = ⊥-elim (¬w U.tt)
  oweStep (P1.psL ¬w (cRT _))   _ = ⊥-elim (¬w U.tt)
  oweStep (P1.psL ¬w (cRV _))   _ = ⊥-elim (¬w U.tt)
  oweStep (P1.psL ¬w cRC)       _ = ⊥-elim (¬w U.tt)
  oweStep (P1.psL ¬w cDn)       _ = ⊥-elim (¬w U.tt)
  oweStep (P1.psy _ cSR _)       i = consW _ refl refl i
  oweStep (P1.psy _ cSQ _)       i = [] , cong (Qe ∷_) i , refl , refl
  oweStep (P1.psy _ (cRA _) _)   i = consW _ refl refl i
  oweStep (P1.psy _ (cRO _ _) _) i = consW _ refl refl i
  oweStep (P1.psy _ (cRT _) _)   i = consW _ refl refl i
  oweStep (P1.psy _ (cRV _) _)   i = consW _ refl refl i
  oweStep (P1.psy _ cRC _)       i = consW _ refl refl i
  oweStep (P1.psy _ cDn sDS)     i = cong (De ∷_) i
  oweStep (P1.psy _ (cRN _) ())   _
  oweStep (P1.psy _ (cQi _) ())   _
  oweStep (P1.psy _ (cDA _) ())   _
  oweStep (P1.psy _ (cDO _ _) ()) _
  oweStep (P1.psy _ (cDT _) ())   _
  oweStep (P1.psy _ (cDV _) ())   _

  -- a terminated system state owes nothing (its client is at End)
  oweFin : ∀ {σ} → Abs.Fin (SysA l) σ → Owe (cOf σ) []
  oweFin {(cE , _) , _}   _ = refl
  oweFin {(cI , _) , _}   (() , _)
  oweFin {(cB , _) , _}   (() , _)
  oweFin {(cQ , _) , _}   (() , _)
  oweFin {(cR , _) , _}   (() , _)
  oweFin {(cS , _) , _}   (() , _)
  oweFin {(cD _ , _) , _} (() , _)

  -- every abstract run ending at termination projects to what its start owes
  oweRun : ∀ {σ s σ′} → ARun σ s σ′ → Abs.Fin (SysA l) σ′ → Owe (cOf σ) (wire l s)
  oweRun r0                 f = oweFin f
  oweRun (rτ {s = s} a ar) f = oweStep {s = s} a (oweRun ar f)
  oweRun (rE {s = s} a ar) f = oweStep {s = s} a (oweRun ar f)

  -- (2d) HANDSHAKE-ONLY TERMINATION.  If `sys` has terminated after a √-free trace `s`,
  -- then `wire s` is a prefix carrying neither MsgQuit nor MsgDone, followed by EXACTLY
  -- the client's MsgQuit and the server's MsgDone; so MsgQuit and MsgDone each occur
  -- exactly once in `wire s`
  handshake-only : ∀ {s W} → sys l ⟹∖√⟨ s ⟩ W → PTree.force W ≡ ret tt
                 → OwePre (wire l s) × occ MsgLNPQuit (wire l s) ≡ 1 × occ MsgLNPDone (wire l s) ≡ 1
  handshake-only r eq with runE (sys₀ l) r
  ... | _ , ar , pos with oweRun ar (Abs.elimR (SysA l) pos eq)
  ...   | w₀ , weq , cq , cd =
          (w₀ , weq , cq , cd)
        , trans (cong (occ MsgLNPQuit) weq) (occ-tail MsgLNPQuit w₀ _ cq)
        , trans (cong (occ MsgLNPDone) weq) (occ-tail MsgLNPDone w₀ _ cd)
