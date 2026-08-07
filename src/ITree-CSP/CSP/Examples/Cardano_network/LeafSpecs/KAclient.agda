{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- LeafSpecs — the KeepAlive CLIENT peer's τ-free component spec, and the
-- stable-failures leaf obligation
--
--     KAclientSpec l d ⊑F KAclientA l d      (for EVERY link and direction)
--
-- Cost-measurement spike for the four-node liveness `⊑F` campaign: one
-- representative leaf obligation of the twelve peer kinds, proved
-- end-to-end and generic in `(l , d)` (so one proof covers every instance
-- of this peer kind).
--
-- METHOD.  `KAclientSpec` is an explicit corecursive FSM over the shared
-- `Net_Api Payload` alphabet with SEVEN positions and NO `iter`/`loop0`
-- wrapper and no τ at all.  The obligation is discharged by a fresh
-- one-way failure simulation (`FSimFromRel` → `fsim→⊑F`), whose relation
-- pairs the eleven reachable impl states (the renamed `iter`/`iter-bind`
-- states of `KAclientStClient`) with the spec positions.
--
-- The proof is INDEPENDENT of `NetworkVerification/*`: it imports only
-- the peer under study, the generic semantics, and the rename/operator
-- layers.  No postulates, no holes, no NON_TERMINATING.
--
-- Two generic inversion lemmas carry the whole cost of the alphabet:
-- `ren-ev-inv` (a visible step of a renamed react node comes from a
-- source event in ι's image) and `ιKA⁻¹-inv` (ι's partial inverse is
-- injective on its domain).  Together they cut the per-state case
-- analysis from "every `Net_Api` channel" (16 constructors × 6 protocol
-- ids) down to "every `KAEv` constructor" (4, of which one splits into 4
-- api tags).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.LeafSpecs.KAclient (p : Params) where

open import Level using (0ℓ; lower)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; ≡-≟-identity)
open import Class.DecEq using (DecEq; _≟_)


open import Process_Trees
open PTree

open Params p

open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Data p
  using ( Payload; DecEq-Payload; Messages
        ; keepAlive; blockFetch; chainSync; txSubmission; leiosNotify; leiosFetch
        ; MessageKeepAlive; MsgKeepAlive; MsgKeepAliveResponse; MsgKADone )
open import CSP.Examples.Cardano_network.Net p

open import CSP.Examples.Cardano_network.NetworkPar p
  using ( KAclientA; ιKA; ιKA⁻¹; ιKA-linv )
open import CSP.Examples.Cardano_network.KeepAlive p
  using ( KAEv; KAEv-≟; sendKA; receiveKA; apiKAev; doneKA
        ; KAState; stClient; stServer; stDone; Rr; DecEq-Cookie²
        ; clientStep; KAclientStClient )

import CSP.Operators {E = KAEv} KAEv-≟ as SrcOp
import CSP.Rename {E₁ = KAEv} {E₂ = Net_Api Payload} ιKA ιKA⁻¹ ιKA-linv as RenKA
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op

open import Semantics.LTS      {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev )
open import Semantics.Refusals {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Offers; deadlock-no-offer )
open import Semantics.DRBisim  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( deadlock-no-τ )
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _⊑F_ )
open import Semantics.FailureSim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( FSim; fsim→⊑F )
open import Semantics.BisimFromRel {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( module FSimFromRel )

------------------------------------------------------------------------
-- Section 1 — small change: trees, payloads, menus, decidability diagonals
------------------------------------------------------------------------

-- process trees over the shared `Net_Api Payload` alphabet
NetTree : Set₁
NetTree = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- source trees of the KeepAlive peer (the pre-rename alphabet)
SrcTree : Set₁
SrcTree = PTree KAEv (ExtI KAEv) Rr

-- source trees of a KeepAlive *step* (an FSM position or a return)
StepTree : Set₁
StepTree = PTree KAEv (ExtI KAEv) (KAState ⊎ Rr)

-- the wire payload the client emits for a keepalive REQUEST carrying `c`
valMsg : Cookie → Payload
valMsg c = (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c))

-- the wire payload the client emits to terminate the protocol
valKAdone : Payload
valKAdone = (time₀ , FromInitiator , length₀ , keepAlive MsgKADone)

-- the visible-menu application of a forced node (nothing on non-react shapes)
visOf : NetTree → (at : AnyTypes (Net_Api Payload)) → proj₁ at → Maybe NetTree
visOf P at a with PTree.force P
... | react v _ = v at a
... | ret _     = nothing
... | sil _     = nothing

-- a `nothing ≡ just _` equation is absurd (used to refute non-offered events)
nj : ∀ {ℓ'} {A : Set ℓ'} {x : A} → nothing ≡ just x → ⊥
nj ()

-- `x ≟ x` computes to `yes refl` — one instance per domain the peer gates on
≟-diagL : (x : Link) → (x ≟ x) ≡ yes refl
≟-diagL x = ≡-≟-identity _≟_ refl

≟-diagD : (x : Dir) → (x ≟ x) ≡ yes refl
≟-diagD x = ≡-≟-identity _≟_ refl

≟-diagC : (x : Cookie) → (x ≟ x) ≡ yes refl
≟-diagC x = ≡-≟-identity _≟_ refl

≟-diagP : (x : Payload) → (x ≟ x) ≡ yes refl
≟-diagP x = ≡-≟-identity _≟_ refl

-- the errCookie carrier `Cookie × Cookie` (instance pinned as in `KeepAlive`)
≟-diagCC : (x : Cookie × Cookie) → (_≟_ ⦃ DecEq-Cookie² ⦄ x x) ≡ yes refl
≟-diagCC x = ≡-≟-identity (_≟_ ⦃ DecEq-Cookie² ⦄) refl

-- the source-alphabet event equality used by `Prefix`/`Output`
≟-diagKA : (x : AnyTypes KAEv) → KAEv-≟ x x ≡ yes refl
≟-diagKA x = ≡-≟-identity KAEv-≟ refl

------------------------------------------------------------------------
-- Section 2 — the injection ι is injective on its domain
------------------------------------------------------------------------

-- whatever `ιKA⁻¹` accepts is exactly the ι-image of what it returns; this is
-- what lets a proof recover the fired NETWORK event from the fired PEER event
ιKA⁻¹-inv : ∀ {A : Set} {e₂ : Net_Api Payload A} {e₁ : KAEv A}
          → ιKA⁻¹ e₂ ≡ just e₁ → e₂ ≡ ιKA e₁
ιKA⁻¹-inv {e₂ = input _ _ N2N_ChainSync}    eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = input _ _ N2N_BlockFetch}   eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = input _ _ N2N_TxSubmission} eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = input _ _ N2N_KeepAlive}    refl = refl
ιKA⁻¹-inv {e₂ = input _ _ N2N_LeiosNotify}  eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = input _ _ N2N_LeiosFetch}   eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = output _ _ N2N_ChainSync}    eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = output _ _ N2N_BlockFetch}   eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = output _ _ N2N_TxSubmission} eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = output _ _ N2N_KeepAlive}    refl = refl
ιKA⁻¹-inv {e₂ = output _ _ N2N_LeiosNotify}  eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = output _ _ N2N_LeiosFetch}   eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = done _ _ N2N_ChainSync}    eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = done _ _ N2N_BlockFetch}   eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = done _ _ N2N_TxSubmission} eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = done _ _ N2N_KeepAlive}    refl = refl
ιKA⁻¹-inv {e₂ = done _ _ N2N_LeiosNotify}  eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = done _ _ N2N_LeiosFetch}   eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = apiKA _ _ _} refl = refl
ιKA⁻¹-inv {e₂ = sndmsg _ _ _} eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = rcvmsg _ _ _} eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = tx _ _ _}     eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = sndack _ _ _} eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = rcvack _ _ _} eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = ack _ _ _}    eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = apiCS _ _ _}  eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = apiBF _ _ _}  eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = apiTS _ _ _}  eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = apiLN _ _ _}  eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = apiLF _ _ _}  eq = ⊥-elim (nj eq)
ιKA⁻¹-inv {e₂ = break _}      eq = ⊥-elim (nj eq)

------------------------------------------------------------------------
-- Section 3 — the implementation states, and generic step inversion
------------------------------------------------------------------------

-- impl HOME state: the renamed `iter` at a client FSM position
kacI : (l : Link) (d : Dir) → KAState → NetTree
kacI l d s = RenKA.renameMap (SrcOp.iter (clientStep l d) s)

-- impl MID state: the renamed `iter-bind` of a residual body tree
kacIB : (l : Link) (d : Dir) → StepTree → NetTree
kacIB l d t = RenKA.renameMap (SrcOp.iter-bind t (clientStep l d))

-- a VISIBLE step of a renamed react node fires a target event in ι's image,
-- comes from the corresponding source offer, and continues in the renaming of
-- that source continuation.  This is the lemma that keeps the per-state case
-- analysis inside the four-constructor source alphabet.
ren-ev-inv :
    (Q : SrcTree)
    {vQ  : (at : AnyTypes KAEv) → ContinueType at (Maybe SrcTree)}
    {τcQ : (i : AnyTypes (ExtI KAEv)) → ContinueType i (Maybe SrcTree)}
  → PTree.force Q ≡ react vQ τcQ
  → ∀ {A : Set} {e₂ : Net_Api Payload A} {a : A} {t′ : NetTree}
  → RenKA.renameMap Q ─[ ev (evl (evLabel A e₂ a)) ]─► t′
  → Σ[ e₁ ∈ KAEv A ] Σ[ Q′ ∈ SrcTree ]
      ( (ιKA⁻¹ e₂ ≡ just e₁) × (vQ (A , e₁) a ≡ just Q′) × (t′ ≡ RenKA.renameMap Q′) )
ren-ev-inv Q {vQ} eqQ {A} {e₂} {a} (sVis eqf br) with PTree.force Q | eqQ
ren-ev-inv Q {vQ} eqQ {A} {e₂} {a} (sVis eqf br) | _ | refl
  with ιKA⁻¹ e₂
     | subst (λ g → g (A , e₂) a ≡ just _) (sym (proj₁ (react-injective eqf))) br
... | nothing  | ()
... | just e₁  | br′ with vQ (A , e₁) a in eqv | br′
...   | nothing | ()
...   | just Q′ | refl = e₁ , Q′ , refl , eqv , refl

-- a renamed `iter-bind` over a STABLE source node (react, empty τ-part) has no τ
noτ-ib : (l : Link) (d : Dir) (Q : StepTree)
         {vq : (at : AnyTypes KAEv) → ContinueType at (Maybe StepTree)}
       → PTree.force Q ≡ react vq SrcOp.∅t
       → ∀ {X} → kacIB l d Q ─[ τ ]─► X → ⊥
noτ-ib l d Q eqQ (sSil eqf) with PTree.force Q | eqQ | eqf
... | _ | refl | ()
noτ-ib l d Q eqQ (sTau {i = A , eι₂} {a = a} eqf br) with PTree.force Q | eqQ
noτ-ib l d Q eqQ (sTau {i = A , eι₂} {a = a} eqf br) | _ | refl
  with RenKA.extBwd eι₂
     | subst (λ g → g (A , eι₂) a ≡ just _) (sym (proj₂ (react-injective eqf))) br
... | nothing  | ()
... | just eι₁ | ()

-- the terminated impl state (a `ret`, i.e. √-ready) has no τ
noτ-ret : (l : Link) (d : Dir) → ∀ {X}
        → kacIB l d (SrcOp.Ret (inj₂ tt)) ─[ τ ]─► X → ⊥
noτ-ret l d (sSil ())
noτ-ret l d (sTau () _)

------------------------------------------------------------------------
-- Section 4 — the τ-free specification FSM
------------------------------------------------------------------------

-- the six positions of the client spec (`kcTerm` is the √ position); the whole
-- protocol language of the peer is carried, only its state is made explicit
data KAcPos : Set where
  kcClient : KAcPos                     -- offering the api: request or done
  kcWmsg   : Cookie → KAcPos            -- about to put the request on the wire
  kcAwait  : Cookie → KAcPos            -- awaiting the response to `c`
  kcWdone  : KAcPos                     -- about to put the done on the wire
  kcErr    : Cookie → Cookie → KAcPos   -- about to report a cookie mismatch
  kcTerm   : KAcPos                     -- terminated (√)

-- the spec tree at a position (forward declarations: mutually corecursive)
kaSpec : (l : Link) (d : Dir) → KAcPos → NetTree
-- its visible menu over the shared alphabet: pull the target event back along ι
kaMenu : (l : Link) (d : Dir) (q : KAcPos)
       → (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe NetTree)
-- the menu proper, stated over the PEER alphabet (four constructors)
kaMenu₁ : (l : Link) (d : Dir) (q : KAcPos) {A : Set} (e₁ : KAEv A) (a : A) → Maybe NetTree

force (kaSpec l d kcTerm) = ret tt
force (kaSpec l d q)      = react (kaMenu l d q) Op.∅t

kaMenu l d q (A , e₂) a with ιKA⁻¹ e₂
... | nothing = nothing
... | just e₁ = kaMenu₁ l d q e₁ a

kaMenu₁ l d kcClient (apiKAev l′ d′ sendKAMsg) c with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (kaSpec l d (kcWmsg c))
... | _        | _        = nothing
kaMenu₁ l d kcClient (apiKAev l′ d′ sendKADone) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (kaSpec l d kcWdone)
... | _        | _        = nothing
kaMenu₁ l d (kcWmsg c) (sendKA l′ d′) a with l′ ≟ l | d′ ≟ d | a ≟ valMsg c
... | yes refl | yes refl | yes _ = just (kaSpec l d (kcAwait c))
... | _        | _        | _     = nothing
kaMenu₁ l d (kcAwait c) (receiveKA l′ d′) (_ , _ , _ , keepAlive (MsgKeepAliveResponse c′))
  with l′ ≟ l | d′ ≟ d | c ≟ c′
... | yes refl | yes refl | yes _ = just (kaSpec l d kcClient)
... | yes refl | yes refl | no  _ = just (kaSpec l d (kcErr c c′))
... | no _     | _        | _     = nothing
... | yes refl | no _     | _     = nothing
kaMenu₁ l d kcWdone (sendKA l′ d′) a with l′ ≟ l | d′ ≟ d | a ≟ valKAdone
... | yes refl | yes refl | yes _ = just (kaSpec l d kcTerm)
... | _        | _        | _     = nothing
kaMenu₁ l d (kcErr c c′) (apiKAev l′ d′ errCookie) v with l′ ≟ l | d′ ≟ d | v ≟ (c , c′)
... | yes refl | yes refl | yes _ = just (kaSpec l d kcTerm)
... | _        | _        | _     = nothing
kaMenu₁ l d _ _ _ = nothing

-- THE SPEC: the τ-free explicit FSM abstracting the renamed KeepAlive client peer
KAclientSpec : (l : Link) (d : Dir) → NetTree
KAclientSpec l d = kaSpec l d kcClient

------------------------------------------------------------------------
-- Section 5 — the firing equations of the spec …
------------------------------------------------------------------------

-- the client position offers the request api (binding the cookie)
specFireMsg : (l : Link) (d : Dir) (c : Cookie)
            → kaMenu l d kcClient (Cookie , apiKA l d sendKAMsg) c
              ≡ just (kaSpec l d (kcWmsg c))
specFireMsg l d c rewrite ≟-diagL l | ≟-diagD d = refl

-- the client position offers the done api
specFireDone : (l : Link) (d : Dir) (a : ApiKACar sendKADone)
             → kaMenu l d kcClient (ApiKACar sendKADone , apiKA l d sendKADone) a
               ≡ just (kaSpec l d kcWdone)
specFireDone l d a rewrite ≟-diagL l | ≟-diagD d = refl

-- the request goes on the wire
specFireWmsg : (l : Link) (d : Dir) (c : Cookie)
             → kaMenu l d (kcWmsg c) (Payload , input l d N2N_KeepAlive) (valMsg c)
               ≡ just (kaSpec l d (kcAwait c))
specFireWmsg l d c rewrite ≟-diagL l | ≟-diagD d | ≟-diagP (valMsg c) = refl

-- the done goes on the wire
specFireWdone : (l : Link) (d : Dir)
              → kaMenu l d kcWdone (Payload , input l d N2N_KeepAlive) valKAdone
                ≡ just (kaSpec l d kcTerm)
specFireWdone l d rewrite ≟-diagL l | ≟-diagD d | ≟-diagP valKAdone = refl

-- a response with the MATCHING cookie returns to the client position
specFireAwaitOk : (l : Link) (d : Dir) (c : Cookie) (t : Time) (m : Mode) (n : Length)
                → kaMenu l d (kcAwait c) (Payload , output l d N2N_KeepAlive)
                    (t , m , n , keepAlive (MsgKeepAliveResponse c))
                  ≡ just (kaSpec l d kcClient)
specFireAwaitOk l d c t m n rewrite ≟-diagL l | ≟-diagD d | ≟-diagC c = refl

-- a response with a MISMATCHING cookie moves to the error position
specFireAwaitErr : (l : Link) (d : Dir) (c c′ : Cookie) (t : Time) (m : Mode) (n : Length)
                 → ¬ (c ≡ c′)
                 → kaMenu l d (kcAwait c) (Payload , output l d N2N_KeepAlive)
                     (t , m , n , keepAlive (MsgKeepAliveResponse c′))
                   ≡ just (kaSpec l d (kcErr c c′))
specFireAwaitErr l d c c′ t m n ¬q rewrite ≟-diagL l | ≟-diagD d with c ≟ c′
... | yes q = ⊥-elim (¬q q)
... | no  _ = refl

-- the error position reports the mismatch and terminates
specFireErr : (l : Link) (d : Dir) (c c′ : Cookie)
            → kaMenu l d (kcErr c c′) (ApiKACar errCookie , apiKA l d errCookie) (c , c′)
              ≡ just (kaSpec l d kcTerm)
specFireErr l d c c′ rewrite ≟-diagL l | ≟-diagD d | ≟-diagCC (c , c′) = refl

------------------------------------------------------------------------
-- Section 6 — … and the matching firing equations of the implementation
------------------------------------------------------------------------

-- the impl client state offers the request api on its own link/direction
implFireMsg : (l : Link) (d : Dir) (c : Cookie)
            → visOf (kacI l d stClient) (Cookie , apiKA l d sendKAMsg) c
              ≡ just (kacIB l d (SrcOp.Output (sendKA l d) (valMsg c)
                                   (SrcOp.Ret (inj₁ (stServer c)))))
implFireMsg l d c rewrite ≟-diagL l | ≟-diagD d = refl

-- the impl client state offers the done api
implFireDone : (l : Link) (d : Dir) (a : ApiKACar sendKADone)
             → visOf (kacI l d stClient) (ApiKACar sendKADone , apiKA l d sendKADone) a
               ≡ just (kacIB l d (SrcOp.Output (sendKA l d) valKAdone
                                    (SrcOp.Ret (inj₁ stDone))))
implFireDone l d a rewrite ≟-diagL l | ≟-diagD d = refl

-- the impl puts the request on the wire
implFireWmsg : (l : Link) (d : Dir) (c : Cookie)
             → visOf (kacIB l d (SrcOp.Output (sendKA l d) (valMsg c)
                                    (SrcOp.Ret (inj₁ (stServer c)))))
                 (Payload , input l d N2N_KeepAlive) (valMsg c)
               ≡ just (kacIB l d (SrcOp.Ret (inj₁ (stServer c))))
implFireWmsg l d c rewrite ≟-diagKA (Payload , sendKA l d) | ≟-diagP (valMsg c) = refl

-- the impl puts the done on the wire
implFireWdone : (l : Link) (d : Dir)
              → visOf (kacIB l d (SrcOp.Output (sendKA l d) valKAdone
                                     (SrcOp.Ret (inj₁ stDone))))
                  (Payload , input l d N2N_KeepAlive) valKAdone
                ≡ just (kacIB l d (SrcOp.Ret (inj₁ stDone)))
implFireWdone l d rewrite ≟-diagKA (Payload , sendKA l d) | ≟-diagP valKAdone = refl

-- the impl accepts a response with the MATCHING cookie
implFireAwaitOk : (l : Link) (d : Dir) (c : Cookie) (t : Time) (m : Mode) (n : Length)
                → visOf (kacI l d (stServer c)) (Payload , output l d N2N_KeepAlive)
                    (t , m , n , keepAlive (MsgKeepAliveResponse c))
                  ≡ just (kacIB l d (SrcOp.Ret (inj₁ stClient)))
implFireAwaitOk l d c t m n rewrite ≟-diagL l | ≟-diagD d | ≟-diagC c = refl

-- the impl accepts a response with a MISMATCHING cookie and reports it
implFireAwaitErr : (l : Link) (d : Dir) (c c′ : Cookie) (t : Time) (m : Mode) (n : Length)
                 → ¬ (c ≡ c′)
                 → visOf (kacI l d (stServer c)) (Payload , output l d N2N_KeepAlive)
                     (t , m , n , keepAlive (MsgKeepAliveResponse c′))
                   ≡ just (kacIB l d (SrcOp.Output (apiKAev l d errCookie) (c , c′)
                                        (SrcOp.Ret (inj₂ tt))))
implFireAwaitErr l d c c′ t m n ¬q rewrite ≟-diagL l | ≟-diagD d with c ≟ c′
... | yes q = ⊥-elim (¬q q)
... | no  _ = refl

-- the impl reports the mismatch and terminates
implFireErr : (l : Link) (d : Dir) (c c′ : Cookie)
            → visOf (kacIB l d (SrcOp.Output (apiKAev l d errCookie) (c , c′)
                                   (SrcOp.Ret (inj₂ tt))))
                (ApiKACar errCookie , apiKA l d errCookie) (c , c′)
              ≡ just (kacIB l d (SrcOp.Ret (inj₂ tt)))
implFireErr l d c c′
  rewrite ≟-diagKA (ApiKACar errCookie , apiKAev l d errCookie) | ≟-diagCC (c , c′) = refl

------------------------------------------------------------------------
-- Section 7 — the simulation relation
------------------------------------------------------------------------

-- reachable impl states ↔ spec positions.  `c*` are the STABLE (react-headed)
-- states, `m*` the transient `sil`-headed loop-back states of `iter`.
data KACRel (l : Link) (d : Dir) : NetTree → NetTree → Set₁ where
  cClient : KACRel l d (kacI l d stClient) (kaSpec l d kcClient)
  cWmsg   : (c : Cookie)
          → KACRel l d (kacIB l d (SrcOp.Output (sendKA l d) (valMsg c)
                                      (SrcOp.Ret (inj₁ (stServer c)))))
                       (kaSpec l d (kcWmsg c))
  mAwait  : (c : Cookie)
          → KACRel l d (kacIB l d (SrcOp.Ret (inj₁ (stServer c))))
                       (kaSpec l d (kcAwait c))
  cAwait  : (c : Cookie)
          → KACRel l d (kacI l d (stServer c)) (kaSpec l d (kcAwait c))
  mClient : KACRel l d (kacIB l d (SrcOp.Ret (inj₁ stClient))) (kaSpec l d kcClient)
  cWdone  : KACRel l d (kacIB l d (SrcOp.Output (sendKA l d) valKAdone
                                      (SrcOp.Ret (inj₁ stDone))))
                       (kaSpec l d kcWdone)
  mDone   : KACRel l d (kacIB l d (SrcOp.Ret (inj₁ stDone))) (kaSpec l d kcTerm)
  cErr    : (c c′ : Cookie)
          → KACRel l d (kacIB l d (SrcOp.Output (apiKAev l d errCookie) (c , c′)
                                      (SrcOp.Ret (inj₂ tt))))
                       (kaSpec l d (kcErr c c′))
  cTerm   : KACRel l d (kacIB l d (SrcOp.Ret (inj₂ tt))) (kaSpec l d kcTerm)
  cDead   : KACRel l d (deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
                                 {R = ⊤ {0ℓ}})
                       deadlock

------------------------------------------------------------------------
-- Section 8 — forward visible/√ simulation
------------------------------------------------------------------------

kacFwdE : (l : Link) (d : Dir) → ∀ {P Q : NetTree} {lb : Event√ (⊤ {0ℓ})} {P′}
        → KACRel l d P Q → P ─[ ev lb ]─► P′
        → Σ[ Q′ ∈ NetTree ] ((Q ═[ ev lb ]═► Q′) × KACRel l d P′ Q′)
kacFwdE l d cClient (sRet ())
kacFwdE l d cClient (sVis eqf br)
  with ren-ev-inv (SrcOp.iter (clientStep l d) stClient) refl (sVis eqf br)
... | sendKA _ _                , _  , _   , eqv , _    = ⊥-elim (nj eqv)
... | receiveKA _ _             , _  , _   , eqv , _    = ⊥-elim (nj eqv)
... | doneKA _ _                , _  , _   , eqv , _    = ⊥-elim (nj eqv)
... | apiKAev _ _ errCookie     , _  , _   , eqv , _    = ⊥-elim (nj eqv)
... | apiKAev _ _ recvKACookie  , _  , _   , eqv , _    = ⊥-elim (nj eqv)
... | apiKAev l′ d′ sendKAMsg   , Q′ , eqι , eqv , refl with l′ ≟ l | d′ ≟ d
...   | no _     | _        = ⊥-elim (nj eqv)
...   | yes refl | no _     = ⊥-elim (nj eqv)
...   | yes refl | yes refl rewrite ιKA⁻¹-inv eqι | sym (just-injective eqv)
        = _ , wev τ*-refl (sVis refl (specFireMsg l d _)) τ*-refl , cWmsg _
kacFwdE l d cClient (sVis eqf br)
    | apiKAev l′ d′ sendKADone  , Q′ , eqι , eqv , refl with l′ ≟ l | d′ ≟ d
...   | no _     | _        = ⊥-elim (nj eqv)
...   | yes refl | no _     = ⊥-elim (nj eqv)
...   | yes refl | yes refl rewrite ιKA⁻¹-inv eqι | sym (just-injective eqv)
        = _ , wev τ*-refl (sVis refl (specFireDone l d _)) τ*-refl , cWdone

kacFwdE l d (cWmsg c) (sRet ())
kacFwdE l d (cWmsg c) (sVis {a = a} eqf br)
  with ren-ev-inv (SrcOp.iter-bind (SrcOp.Output (sendKA l d) (valMsg c)
                                      (SrcOp.Ret (inj₁ (stServer c)))) (clientStep l d))
                  refl (sVis eqf br)
... | receiveKA _ _   , _  , _   , eqv , _    = ⊥-elim (nj eqv)
... | doneKA _ _      , _  , _   , eqv , _    = ⊥-elim (nj eqv)
... | apiKAev _ _ _   , _  , _   , eqv , _    = ⊥-elim (nj eqv)
... | sendKA l′ d′    , Q′ , eqι , eqv , refl with l ≟ l′ | d ≟ d′
...   | no _     | _        = ⊥-elim (nj eqv)
...   | yes refl | no _     = ⊥-elim (nj eqv)
...   | yes refl | yes refl with a ≟ valMsg c | eqv
...     | no _     | eqv′ = ⊥-elim (nj eqv′)
...     | yes refl | eqv′ rewrite ιKA⁻¹-inv eqι | sym (just-injective eqv′)
          = _ , wev τ*-refl (sVis refl (specFireWmsg l d c)) τ*-refl , mAwait c

kacFwdE l d cWdone (sRet ())
kacFwdE l d cWdone (sVis {a = a} eqf br)
  with ren-ev-inv (SrcOp.iter-bind (SrcOp.Output (sendKA l d) valKAdone
                                      (SrcOp.Ret (inj₁ stDone))) (clientStep l d))
                  refl (sVis eqf br)
... | receiveKA _ _   , _  , _   , eqv , _    = ⊥-elim (nj eqv)
... | doneKA _ _      , _  , _   , eqv , _    = ⊥-elim (nj eqv)
... | apiKAev _ _ _   , _  , _   , eqv , _    = ⊥-elim (nj eqv)
... | sendKA l′ d′    , Q′ , eqι , eqv , refl with l ≟ l′ | d ≟ d′
...   | no _     | _        = ⊥-elim (nj eqv)
...   | yes refl | no _     = ⊥-elim (nj eqv)
...   | yes refl | yes refl with a ≟ valKAdone | eqv
...     | no _     | eqv′ = ⊥-elim (nj eqv′)
...     | yes refl | eqv′ rewrite ιKA⁻¹-inv eqι | sym (just-injective eqv′)
          = _ , wev τ*-refl (sVis refl (specFireWdone l d)) τ*-refl , mDone

kacFwdE l d (cAwait c) (sRet ())
kacFwdE l d (cAwait c) (sVis {a = a} eqf br)
  with ren-ev-inv (SrcOp.iter (clientStep l d) (stServer c)) refl (sVis eqf br)
... | sendKA _ _      , _  , _   , eqv , _    = ⊥-elim (nj eqv)
... | doneKA _ _      , _  , _   , eqv , _    = ⊥-elim (nj eqv)
... | apiKAev _ _ _   , _  , _   , eqv , _    = ⊥-elim (nj eqv)
... | receiveKA l′ d′ , Q′ , eqι , eqv , refl with a | eqv
...   | _ , _ , _ , keepAlive (MsgKeepAlive _)         | eqv′ = ⊥-elim (nj eqv′)
...   | _ , _ , _ , keepAlive MsgKADone                | eqv′ = ⊥-elim (nj eqv′)
...   | _ , _ , _ , blockFetch _                       | eqv′ = ⊥-elim (nj eqv′)
...   | _ , _ , _ , chainSync _                        | eqv′ = ⊥-elim (nj eqv′)
...   | _ , _ , _ , txSubmission _                     | eqv′ = ⊥-elim (nj eqv′)
...   | _ , _ , _ , leiosNotify _                      | eqv′ = ⊥-elim (nj eqv′)
...   | _ , _ , _ , leiosFetch _                       | eqv′ = ⊥-elim (nj eqv′)
...   | t , m , n , keepAlive (MsgKeepAliveResponse c′) | eqv′ with l′ ≟ l | d′ ≟ d
...     | no _     | _     = ⊥-elim (nj eqv′)
...     | yes refl | no _  = ⊥-elim (nj eqv′)
...     | yes refl | yes refl with c ≟ c′ | eqv′
...       | yes refl | eqv″ rewrite ιKA⁻¹-inv eqι | sym (just-injective eqv″)
            = _ , wev τ*-refl (sVis refl (specFireAwaitOk l d c t m n)) τ*-refl , mClient
...       | no ¬q    | eqv″ rewrite ιKA⁻¹-inv eqι | sym (just-injective eqv″)
            = _ , wev τ*-refl (sVis refl (specFireAwaitErr l d c c′ t m n ¬q)) τ*-refl
                , cErr c c′

kacFwdE l d (cErr c c′) (sRet ())
kacFwdE l d (cErr c c′) (sVis {a = a} eqf br)
  with ren-ev-inv (SrcOp.iter-bind (SrcOp.Output (apiKAev l d errCookie) (c , c′)
                                      (SrcOp.Ret (inj₂ tt))) (clientStep l d))
                  refl (sVis eqf br)
... | sendKA _ _    , _ , _ , eqv , _ = ⊥-elim (nj eqv)
... | receiveKA _ _ , _ , _ , eqv , _ = ⊥-elim (nj eqv)
... | doneKA _ _    , _ , _ , eqv , _ = ⊥-elim (nj eqv)
... | apiKAev l′ d′ sendKAMsg , _ , _ , eqv , _ with l ≟ l′ | d ≟ d′
...   | no _     | _        = ⊥-elim (nj eqv)
...   | yes refl | no _     = ⊥-elim (nj eqv)
...   | yes refl | yes refl = ⊥-elim (nj eqv)
kacFwdE l d (cErr c c′) (sVis {a = a} eqf br)
    | apiKAev l′ d′ sendKADone , _ , _ , eqv , _ with l ≟ l′ | d ≟ d′
...   | no _     | _        = ⊥-elim (nj eqv)
...   | yes refl | no _     = ⊥-elim (nj eqv)
...   | yes refl | yes refl = ⊥-elim (nj eqv)
kacFwdE l d (cErr c c′) (sVis {a = a} eqf br)
    | apiKAev l′ d′ recvKACookie , _ , _ , eqv , _ with l ≟ l′ | d ≟ d′
...   | no _     | _        = ⊥-elim (nj eqv)
...   | yes refl | no _     = ⊥-elim (nj eqv)
...   | yes refl | yes refl = ⊥-elim (nj eqv)
kacFwdE l d (cErr c c′) (sVis {a = a} eqf br)
    | apiKAev l′ d′ errCookie , Q′ , eqι , eqv , refl with l ≟ l′ | d ≟ d′
...   | no _     | _        = ⊥-elim (nj eqv)
...   | yes refl | no _     = ⊥-elim (nj eqv)
...   | yes refl | yes refl with a ≟ (c , c′) | eqv
...     | no _     | eqv′ = ⊥-elim (nj eqv′)
...     | yes refl | eqv′ rewrite ιKA⁻¹-inv eqι | sym (just-injective eqv′)
          = _ , wev τ*-refl (sVis refl (specFireErr l d c c′)) τ*-refl , cTerm

-- the transient `sil`-headed states have no visible step at all
kacFwdE l d mClient    (sRet ())
kacFwdE l d mClient    (sVis () _)
kacFwdE l d (mAwait c) (sRet ())
kacFwdE l d (mAwait c) (sVis () _)
kacFwdE l d mDone      (sRet ())
kacFwdE l d mDone      (sVis () _)
-- the terminated state performs √ and both sides go to `deadlock`
kacFwdE l d cTerm (sRet refl) = _ , wev τ*-refl (sRet refl) τ*-refl , cDead
kacFwdE l d cTerm (sVis () _)
kacFwdE l d cDead st = ⊥-elim (deadlock-no-offer st)

------------------------------------------------------------------------
-- Section 9 — forward τ simulation (the spec stays put: it is τ-free)
------------------------------------------------------------------------

kacFwdT : (l : Link) (d : Dir) → ∀ {P Q P′ : NetTree}
        → KACRel l d P Q → P ─[ τ ]─► P′
        → Σ[ Q′ ∈ NetTree ] ((Q ═[ τ ]═► Q′) × KACRel l d P′ Q′)
kacFwdT l d cClient st =
  ⊥-elim (noτ-ib l d (clientStep l d stClient) refl st)
kacFwdT l d (cAwait c) st =
  ⊥-elim (noτ-ib l d (clientStep l d (stServer c)) refl st)
kacFwdT l d (cWmsg c) st =
  ⊥-elim (noτ-ib l d (SrcOp.Output (sendKA l d) (valMsg c)
                        (SrcOp.Ret (inj₁ (stServer c)))) refl st)
kacFwdT l d cWdone st =
  ⊥-elim (noτ-ib l d (SrcOp.Output (sendKA l d) valKAdone
                        (SrcOp.Ret (inj₁ stDone))) refl st)
kacFwdT l d (cErr c c′) st =
  ⊥-elim (noτ-ib l d (SrcOp.Output (apiKAev l d errCookie) (c , c′)
                        (SrcOp.Ret (inj₂ tt))) refl st)
kacFwdT l d mClient    (sSil refl) = _ , wτ τ*-refl , cClient
kacFwdT l d mClient    (sTau () _)
kacFwdT l d (mAwait c) (sSil refl) = _ , wτ τ*-refl , cAwait c
kacFwdT l d (mAwait c) (sTau () _)
kacFwdT l d mDone      (sSil refl) = _ , wτ τ*-refl , cTerm
kacFwdT l d mDone      (sTau () _)
kacFwdT l d cTerm      (sSil ())
kacFwdT l d cTerm      (sTau () _)
kacFwdT l d cDead st = ⊥-elim (deadlock-no-τ st)

------------------------------------------------------------------------
-- Section 10 — the stability obligation: spec offers ⊆ impl offers
------------------------------------------------------------------------

-- at the client position the spec offers exactly the two api events the impl does
inclClient : (l : Link) (d : Dir) (e : Event√ (⊤ {0ℓ}))
           → Offers (kaSpec l d kcClient) e → Offers (kacI l d stClient) e
inclClient l d _ (_ , sRet ())
inclClient l d _ (_ , sVis {at = A , e₂} {a = a} refl br) with ιKA⁻¹ e₂ in eqι | br
... | nothing                         | ()
... | just (sendKA _ _)               | ()
... | just (receiveKA _ _)            | ()
... | just (doneKA _ _)               | ()
... | just (apiKAev _ _ errCookie)    | ()
... | just (apiKAev _ _ recvKACookie) | ()
... | just (apiKAev l′ d′ sendKAMsg)  | br′ with l′ ≟ l | d′ ≟ d
...   | no _     | _        = ⊥-elim (nj br′)
...   | yes refl | no _     = ⊥-elim (nj br′)
...   | yes refl | yes refl rewrite ιKA⁻¹-inv eqι = _ , sVis refl (implFireMsg l d a)
inclClient l d _ (_ , sVis {at = A , e₂} {a = a} refl br)
    | just (apiKAev l′ d′ sendKADone) | br′ with l′ ≟ l | d′ ≟ d
...   | no _     | _        = ⊥-elim (nj br′)
...   | yes refl | no _     = ⊥-elim (nj br′)
...   | yes refl | yes refl rewrite ιKA⁻¹-inv eqι = _ , sVis refl (implFireDone l d a)

-- at the request-send position the spec offers exactly the one wire value
inclWmsg : (l : Link) (d : Dir) (c : Cookie) (e : Event√ (⊤ {0ℓ}))
         → Offers (kaSpec l d (kcWmsg c)) e
         → Offers (kacIB l d (SrcOp.Output (sendKA l d) (valMsg c)
                                (SrcOp.Ret (inj₁ (stServer c))))) e
inclWmsg l d c _ (_ , sRet ())
inclWmsg l d c _ (_ , sVis {at = A , e₂} {a = a} refl br) with ιKA⁻¹ e₂ in eqι | br
... | nothing              | ()
... | just (receiveKA _ _) | ()
... | just (doneKA _ _)    | ()
... | just (apiKAev _ _ _) | ()
... | just (sendKA l′ d′)  | br′ with l′ ≟ l | d′ ≟ d
...   | no _     | _        = ⊥-elim (nj br′)
...   | yes refl | no _     = ⊥-elim (nj br′)
...   | yes refl | yes refl with a ≟ valMsg c | br′
...     | no _     | br″ = ⊥-elim (nj br″)
...     | yes refl | br″ rewrite ιKA⁻¹-inv eqι = _ , sVis refl (implFireWmsg l d c)

-- at the done-send position the spec offers exactly the one wire value
inclWdone : (l : Link) (d : Dir) (e : Event√ (⊤ {0ℓ}))
          → Offers (kaSpec l d kcWdone) e
          → Offers (kacIB l d (SrcOp.Output (sendKA l d) valKAdone
                                 (SrcOp.Ret (inj₁ stDone)))) e
inclWdone l d _ (_ , sRet ())
inclWdone l d _ (_ , sVis {at = A , e₂} {a = a} refl br) with ιKA⁻¹ e₂ in eqι | br
... | nothing              | ()
... | just (receiveKA _ _) | ()
... | just (doneKA _ _)    | ()
... | just (apiKAev _ _ _) | ()
... | just (sendKA l′ d′)  | br′ with l′ ≟ l | d′ ≟ d
...   | no _     | _        = ⊥-elim (nj br′)
...   | yes refl | no _     = ⊥-elim (nj br′)
...   | yes refl | yes refl with a ≟ valKAdone | br′
...     | no _     | br″ = ⊥-elim (nj br″)
...     | yes refl | br″ rewrite ιKA⁻¹-inv eqι = _ , sVis refl (implFireWdone l d)

-- while awaiting, the spec accepts exactly the response payloads the impl does
inclAwait : (l : Link) (d : Dir) (c : Cookie) (e : Event√ (⊤ {0ℓ}))
          → Offers (kaSpec l d (kcAwait c)) e → Offers (kacI l d (stServer c)) e
inclAwait l d c _ (_ , sRet ())
inclAwait l d c _ (_ , sVis {at = A , e₂} {a = a} refl br) with ιKA⁻¹ e₂ in eqι | br
... | nothing              | ()
... | just (sendKA _ _)    | ()
... | just (doneKA _ _)    | ()
... | just (apiKAev _ _ _) | ()
... | just (receiveKA l′ d′) | br′ with a | br′
...   | _ , _ , _ , keepAlive (MsgKeepAlive _)         | ()
...   | _ , _ , _ , keepAlive MsgKADone                | ()
...   | _ , _ , _ , blockFetch _                       | ()
...   | _ , _ , _ , chainSync _                        | ()
...   | _ , _ , _ , txSubmission _                     | ()
...   | _ , _ , _ , leiosNotify _                      | ()
...   | _ , _ , _ , leiosFetch _                       | ()
...   | t , m , n , keepAlive (MsgKeepAliveResponse c′) | br″ with l′ ≟ l | d′ ≟ d
...     | no _     | _     = ⊥-elim (nj br″)
...     | yes refl | no _  = ⊥-elim (nj br″)
...     | yes refl | yes refl with c ≟ c′ | br″
...       | yes refl | _ rewrite ιKA⁻¹-inv eqι
            = _ , sVis refl (implFireAwaitOk l d c t m n)
...       | no ¬q    | _ rewrite ιKA⁻¹-inv eqι
            = _ , sVis refl (implFireAwaitErr l d c c′ t m n ¬q)

-- at the error position the spec offers exactly the mismatch report
inclErr : (l : Link) (d : Dir) (c c′ : Cookie) (e : Event√ (⊤ {0ℓ}))
        → Offers (kaSpec l d (kcErr c c′)) e
        → Offers (kacIB l d (SrcOp.Output (apiKAev l d errCookie) (c , c′)
                               (SrcOp.Ret (inj₂ tt)))) e
inclErr l d c c′ _ (_ , sRet ())
inclErr l d c c′ _ (_ , sVis {at = A , e₂} {a = a} refl br) with ιKA⁻¹ e₂ in eqι | br
... | nothing                         | ()
... | just (sendKA _ _)               | ()
... | just (receiveKA _ _)            | ()
... | just (doneKA _ _)               | ()
... | just (apiKAev _ _ sendKAMsg)    | ()
... | just (apiKAev _ _ sendKADone)   | ()
... | just (apiKAev _ _ recvKACookie) | ()
... | just (apiKAev l′ d′ errCookie)  | br′ with l′ ≟ l | d′ ≟ d
...   | no _     | _        = ⊥-elim (nj br′)
...   | yes refl | no _     = ⊥-elim (nj br′)
...   | yes refl | yes refl with a ≟ (c , c′) | br′
...     | no _     | br″ = ⊥-elim (nj br″)
...     | yes refl | br″ rewrite ιKA⁻¹-inv eqι = _ , sVis refl (implFireErr l d c c′)

-- the `FSimFromRel` stability obligation: the spec is already stable wherever the
-- impl is (both are react nodes with an empty τ-part), and its offers are included
kacStab : (l : Link) (d : Dir) → ∀ {P Q : NetTree} → KACRel l d P Q → isStable P
        → Σ[ Q′ ∈ NetTree ]
            ( (Q ─[τ*]─► Q′) × isStable Q′
            × (∀ (e : Event√ (⊤ {0ℓ})) → Offers Q′ e → Offers P e) )
kacStab l d cClient    _  = _ , τ*-refl , (λ _ _ → refl) , inclClient l d
kacStab l d (cWmsg c)  _  = _ , τ*-refl , (λ _ _ → refl) , inclWmsg l d c
kacStab l d (cAwait c) _  = _ , τ*-refl , (λ _ _ → refl) , inclAwait l d c
kacStab l d cWdone     _  = _ , τ*-refl , (λ _ _ → refl) , inclWdone l d
kacStab l d (cErr c c′) _ = _ , τ*-refl , (λ _ _ → refl) , inclErr l d c c′
kacStab l d cDead      _  = _ , τ*-refl , (λ _ _ → refl) , (λ _ o → o)
kacStab l d mClient    st = ⊥-elim (lower st)
kacStab l d (mAwait c) st = ⊥-elim (lower st)
kacStab l d mDone      st = ⊥-elim (lower st)
kacStab l d cTerm      st = ⊥-elim (lower st)

------------------------------------------------------------------------
-- Section 11 — the impl never diverges (every τ-chain is at most one step)
------------------------------------------------------------------------

kacNdiv : (l : Link) (d : Dir) → ∀ {P Q : NetTree} → KACRel l d P Q → Diverges P → ⊥
kacNdiv l d cClient dv =
  noτ-ib l d (clientStep l d stClient) refl (dv .Diverges.step)
kacNdiv l d (cAwait c) dv =
  noτ-ib l d (clientStep l d (stServer c)) refl (dv .Diverges.step)
kacNdiv l d (cWmsg c) dv =
  noτ-ib l d (SrcOp.Output (sendKA l d) (valMsg c)
                (SrcOp.Ret (inj₁ (stServer c)))) refl (dv .Diverges.step)
kacNdiv l d cWdone dv =
  noτ-ib l d (SrcOp.Output (sendKA l d) valKAdone
                (SrcOp.Ret (inj₁ stDone))) refl (dv .Diverges.step)
kacNdiv l d (cErr c c′) dv =
  noτ-ib l d (SrcOp.Output (apiKAev l d errCookie) (c , c′)
                (SrcOp.Ret (inj₂ tt))) refl (dv .Diverges.step)
kacNdiv l d mClient dv
  with dv .Diverges.next | dv .Diverges.step | dv .Diverges.rest
... | _ | sSil refl | rest =
        noτ-ib l d (clientStep l d stClient) refl (rest .Diverges.step)
... | _ | sTau () _ | _
kacNdiv l d (mAwait c) dv
  with dv .Diverges.next | dv .Diverges.step | dv .Diverges.rest
... | _ | sSil refl | rest =
        noτ-ib l d (clientStep l d (stServer c)) refl (rest .Diverges.step)
... | _ | sTau () _ | _
kacNdiv l d mDone dv
  with dv .Diverges.next | dv .Diverges.step | dv .Diverges.rest
... | _ | sSil refl | rest = noτ-ret l d (rest .Diverges.step)
... | _ | sTau () _ | _
kacNdiv l d cTerm dv = noτ-ret l d (dv .Diverges.step)
kacNdiv l d cDead dv = deadlock-no-τ (dv .Diverges.step)

------------------------------------------------------------------------
-- Section 12 — the leaf obligation
------------------------------------------------------------------------

-- the coinduction principle instantiated with the KA-client relation
module KACFS (l : Link) (d : Dir) =
  FSimFromRel (KACRel l d) (kacFwdE l d) (kacFwdT l d) (kacStab l d) (kacNdiv l d)

-- THE LEAF OBLIGATION: the τ-free spec is refined, in stable failures, by the
-- renamed KeepAlive client peer — on every link and in every direction
KAclientSpec-⊑F : ∀ (l : Link) (d : Dir) → KAclientSpec l d ⊑F KAclientA l d
KAclientSpec-⊑F l d = fsim→⊑F (KACFS.rel→fsim l d cClient)
