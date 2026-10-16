{-# OPTIONS --guardedness #-}

-- Component views for SERVER SOUNDNESS (trace-replay Phase 5, Increment 1).
-- Every reachable state of `serverModel bs` is `C P Ta Tb S`: the renamed
-- producer `P`, the two serving threads `Ta ⦀ Tb`, the body store `S`.  This
-- module inverts each component's steps at each of its reachable states, and
-- splits a composite step into component steps (`comp-τ`, `comp-ev`).
-- The store helpers hoisted from the Increment 0 probe live here too.
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
module Cardano_network.Replay.LeiosFetchServerParts where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Unit using (tt)
import Data.Unit.Polymorphic as PU
open import Function using (case_of_)
open import Level using (lift)
open import Relation.Nullary using (¬_; yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Process_Trees using (PTree; ExtI; AnyTypes; react; ret; sil; base; pair; fin; isStable)
open import Cardano_network.Base using (N2N_LeiosFetch; hi; FromResponder)
open import Cardano_network.Replay.ReplayParams using (replayParams; replayLP; replayTopo)
open import Cardano_network.Params using (module Params)
open import Class.DecEq using (DecEq; _≟_)
open import Class.DecEq.Instances using (DecEq-List)
open import Cardano_network.Net replayParams
  using ( Net_Api; Net_Api-≟; apiLP; store; ApiLPTag
        ; lfpReqBlockRequest; lfpSendBlock; lfpReqBlockTxsRequest; lfpSendBlockTxs )
open import Cardano_network.Data replayParams using (Payload; MsgLFPBlock; MsgLFPBlockTxs)
open import Cardano_network.LeiosFetchP replayParams
  using (LFPEv; LFPEv-≟; serverStepP; LFPState; stIdle; stBlock; stBlockTxs; stDone; doneLFP)
open import Cardano_network.Parametric.Leios.PeersP replayParams using (ιLFP; ιLFP⁻¹; ιLFP-linv)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLFP replayParams
  using ( ιLFP-rinv; Rd; snd; SIdleV; sIdleV; SBlkV; sbBlk; sBlkV; STxsV; stxTxs; sTxsV )
open import Cardano_network.Replay.LeiosFetchServerModel
open import Cardano_network.ApiAlphabet replayParams using (apiES)
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open NLL.Generic replayParams replayLP replayTopo apiES (λ _ → tt)
  using (ebServeBody; ebTxsServeBody; serveTxs)
import Cardano_network.LeiosFetchP replayParams as LFP
import Cardano_network.Net replayParams as Net
import Cardano_network.Data replayParams as Data

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (EventSet; ∅ES; _□_; □-mt; mergeVis; _>>=_; iter-bind; _∥⇘_⇙_; _⦀_; _⊓_)
import CSP.Operators {E = LFPEv} LFPEv-≟ as LOp
import CSP.Rename {E₁ = LFPEv} {E₂ = Net_Api Payload} ιLFP ιLFP⁻¹ ιLFP-linv as RenLFP
import CSP.Laws.Traces.RenameDeadlock {E₁ = LFPEv} {E₂ = Net_Api Payload} ιLFP ιLFP⁻¹ ιLFP-linv as RD
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (Event; evLabel; _─[_]─►_; ev; evl; √; τ; sVis; sSil; sTau; sRet)
import Semantics.LTS {E = LFPEv} {I = ExtI LFPEv} as F
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (⟹-refl; ⟹-ev)
open import Semantics.Stability {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (mk-stable; stable→react; stable-no-τ; stable-not-ret)
open import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload})
  using (Par-τ-elim; ParτR; τL; τR; Par-ev-elim; ParevR; evSync; evL; evR; evBoth; ev√)
open import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload})
  using (loop-pfx-ev-inv; loop-pfx-no-τ; loop-out-ev-inv; loop-out-no-τ; Prefix-cont-fires)
import CSP.Laws.Traces.PrefixInversion LFPEv-≟ as PIL
import CSP.Laws.DivFree.Loop LFPEv-≟ as LoopL
import CSP.Laws.DivFree.Loop (Net_Api-≟ {Payload}) as LoopN
open LoopN using (itτ; itBack; bind-ev-elim; beL; beK; bind-ret-inv; loopStep)
open import CSP.Laws.DivFree.Closure (Net_Api-≟ {Payload}) using (bind-τ-elim; bτL; bτK)
open import CSP.Laws.Traces.TraceLawsBind (Net_Api-≟ {Payload}) using (fBind-react; fBind-ret)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono (Net_Api-≟ {Payload}) using (□-ev-elim; evP; evQ; evPQ)
open import CSP.Laws.Bisim.Laws (Net_Api-≟ {Payload}) using (⊓-τ-inv)
open import CSP.Laws.Bisim.IterCong (Net_Api-≟ {Payload}) using (fIter-react)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload})
  using (AllT; AllL; _∷_; AllT-□; AllT-⟶; AllT-Output; AllT-Ret; AllT-Stop; AllT->>=)

------------------------------------------------------------------------
-- Vocabulary
------------------------------------------------------------------------

instance
  -- the EB-body DecEq the store's menu was built with
  decEBR : DecEq (Params.EB replayParams)
  decEBR = Params.decEB replayParams

-- is a label in the api sync set
AE : Event → Set
AE (evLabel X e a) = EventSet.mem apiES (X , e) a

-- is a label in the store sync set
SE : Event → Set
SE (evLabel X e a) = EventSet.mem storeES (X , e) a

-- which api command a label is, if any (tells the two threads' alphabets apart)
data Tag : Set where
  -- BlockRequest report / Block command / BlockTxsRequest report / BlockTxs command / other
  tReqB tSendB tReqT tSendT tOther : Tag

-- the api command of a label
tag : Event → Tag
tag (evLabel _ (apiLP _ _ lfpReqBlockRequest) _)    = tReqB
tag (evLabel _ (apiLP _ _ lfpSendBlock) _)          = tSendB
tag (evLabel _ (apiLP _ _ lfpReqBlockTxsRequest) _) = tReqT
tag (evLabel _ (apiLP _ _ lfpSendBlockTxs) _)       = tSendT
tag _                                               = tOther

-- a single output fires only its own value and continues with its tree (any alphabet)
module OutInv {ℓ ℓe} {E : Set ℓ → Set ℓe} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
  open import CSP.Operators E-≟ using (Output)
  import Semantics.LTS {E = E} {I = ExtI E} as L

  -- the output inversion
  out-ev : ∀ {ℓr} {R : Set ℓr} {B : Set ℓ} ⦃ _ : DecEq B ⦄ {ce : E B} {v : B} {P : PTree E (ExtI E) R}
             {x : L.Event} {t′ : PTree E (ExtI E) R}
         → Output ce v P L.─[ L.ev (L.evl x) ]─► t′ → x ≡ L.evLabel B ce v × t′ ≡ P
  out-ev {B = B} {ce = ce} {v = v} (L.sVis {at = A , e} {a = a} refl br) with E-≟ (B , ce) (A , e)
  ... | no _ = case br of λ ()
  ... | yes refl with a ≟ v
  ...   | yes refl = refl , sym (just-injective br)
  ...   | no _     = case br of λ ()

open OutInv (Net_Api-≟ {Payload}) using (out-ev)
open OutInv LFPEv-≟ renaming (out-ev to out-evL) using ()

------------------------------------------------------------------------
-- The producer (renamed LeiosFetch server), at any round state
------------------------------------------------------------------------

-- a producer event as the composite performs it
renE : F.Event → Event
renE (F.evLabel A e a) = evLabel A (ιLFP e) a

-- the renamed producer once its source tree has moved to `t′` inside its loop
peerAfter : Rd → Proc
peerAfter t′ = RenLFP.renameMap (LOp.iter-bind t′ (serverStepP lS dS))

-- the visible inverse of the rename returns exactly a preimage
ivi-elim : ∀ {A} {e₂ : Net_Api Payload A} {b : A} {at : AnyTypes LFPEv} {a : Σ.proj₁ at}
         → RenLFP.ι-vis-inv (A , e₂) b ≡ just (at , a)
         → Σ[ e₁ ∈ LFPEv A ] (_≡_ {A = RenLFP.ConcEvent₁} (at , a) ((A , e₁) , b) × e₂ ≡ ιLFP e₁)
ivi-elim {e₂ = e₂} eq with ιLFP⁻¹ e₂ in r
ivi-elim eq | just e₁ with eq
... | refl = e₁ , refl , ιLFP-rinv r
ivi-elim eq | nothing with eq
... | ()

-- no producer event is a store event
renE-not-store : ∀ x → ¬ SE (renE x)
renE-not-store (F.evLabel _ (LFP.sendLFP _ _) _)    ()
renE-not-store (F.evLabel _ (LFP.receiveLFP _ _) _) ()
renE-not-store (F.evLabel _ (LFP.apiLPev _ _ _) _)  ()
renE-not-store (F.evLabel _ (LFP.doneLFP _ _) _)    ()

-- a visible step of the producer is a renamed step of its source round
peer-ev : ∀ {t e W} → peerAfter t ─[ ev (evl e) ]─► W
        → Σ[ x ∈ F.Event ] Σ[ t′ ∈ Rd ] (t F.─[ F.ev (F.evl x) ]─► t′ × e ≡ renE x × W ≡ peerAfter t′)
peer-ev {t} st with RD.ren-ev-inv {inv = RenLFP.ι-vis-inv} {P = LOp.iter-bind t (serverStepP lS dS)} st
... | inj₂ (_ , () , _)
... | inj₁ ((A₁ , e₁′) , a , (A , e₂) , b , P₁ , stP , inv≡ , refl , refl)
  with LoopL.iter-ev-elim t (serverStepP lS dS) stP
...   | t′ , st₂ , refl with ivi-elim inv≡
...     | e₁ , refl , refl = F.evLabel A e₁ b , t′ , st₂ , refl , refl

-- a silent step of the producer is a silent step of its round, or the loop-back
peer-τ : ∀ {t W} → peerAfter t ─[ τ ]─► W
       → (Σ[ t′ ∈ Rd ] (t F.─[ F.τ ]─► t′ × W ≡ peerAfter t′))
       ⊎ (Σ[ a ∈ LFPState ] (PTree.force t ≡ ret (inj₁ a) × W ≡ peerAfter (serverStepP lS dS a)))
peer-τ {t} st with RD.ren-τ-inv {inv = RenLFP.ι-vis-inv} {P = LOp.iter-bind t (serverStepP lS dS)} st
... | P₁ , stP , refl with LoopL.iter-τ-elim t (serverStepP lS dS) stP
...   | LoopL.itτ t′ st′ refl  = inj₁ (t′ , st′ , refl)
...   | LoopL.itBack a eq refl = inj₂ (a , eq , refl)

-- a producer whose round is a τ-free menu has no silent move
p-no-τ : ∀ {t W v} → PTree.force t ≡ react v LOp.∅t → ¬ (peerAfter t ─[ τ ]─► W)
p-no-τ eqt st with peer-τ st
... | inj₁ (_ , F.sSil eq , _)    = case trans (sym eqt) eq of λ ()
... | inj₁ (_ , F.sTau eq br , _) with trans (sym eqt) eq
...   | refl = case br of λ ()
p-no-τ eqt st | inj₂ (_ , eq , _) = case trans (sym eqt) eq of λ ()

-- a producer at a loop-back has no visible move
p-ret-no-ev : ∀ {st e W} → ¬ (peerAfter (LOp.Ret (inj₁ st)) ─[ ev (evl e) ]─► W)
p-ret-no-ev st with peer-ev st
... | _ , _ , F.sVis () _ , _

-- the producer's request report: the reported value, then the loop-back to `st`
p-out-ev : ∀ {m : ApiLPTag} ⦃ _ : DecEq (Net.ApiLPCar m) ⦄ {v st e W}
         → peerAfter (LOp.Output (LFP.apiLPev lS dS m) v (LOp.Ret (inj₁ st))) ─[ ev (evl e) ]─► W
         → e ≡ evLabel _ (apiLP lS dS m) v × W ≡ peerAfter (LOp.Ret (inj₁ st))
p-out-ev st with peer-ev st
... | x , t′ , stx , refl , refl with out-evL stx
...   | refl , refl = refl , refl

-- the producer's wire send of `msg`, then the loop-back to Idle
p-snd-ev : ∀ {msg e W} → peerAfter (snd lS dS FromResponder msg stIdle) ─[ ev (evl e) ]─► W
         → e ≡ renE (F.evLabel _ (LFP.sendLFP lS dS) (Params.time₀ replayParams , FromResponder , Params.length₀ replayParams , Data.leiosFetchP msg))
           × W ≡ peerAfter (LOp.Ret (inj₁ stIdle))
p-snd-ev st with peer-ev st
... | x , t′ , stx , refl , refl with out-evL stx
...   | refl , refl = refl , refl

-- the producer after Done: only the (api-synchronised) `done`
p-done-ev : ∀ {e W} → peerAfter (doneLFP lS dS LOp.⟶₀ LOp.Ret (inj₁ stDone)) ─[ ev (evl e) ]─► W
          → Σ[ u ∈ _ ] e ≡ evLabel _ (Net.done lS dS N2N_LeiosFetch) u
p-done-ev st with peer-ev st
... | x , t′ , stx , refl , refl with PIL.⟶₀-ev-inv stx
...   | u , refl , _ = u , refl

-- a producer resting at `st`: at its loop-back or at the head of the `st` round
data PRest (st : LFPState) : Proc → Set₁ where
  -- the loop-back τ to `st` is still pending
  pBack : PRest st (peerAfter (LOp.Ret (inj₁ st)))
  -- at the head of the `st` round
  pHead : PRest st (peerAfter (serverStepP lS dS st))

-- a resting producer's τ is its loop-back
prest-τ : ∀ {st P P′} → PRest st P → P ─[ τ ]─► P′ → PRest st P′
prest-τ pBack st with peer-τ st
... | inj₁ (_ , F.sSil () , _)
... | inj₁ (_ , F.sTau () _ , _)
... | inj₂ (_ , refl , refl) = pHead
prest-τ {stIdle}     pHead st = ⊥-elim (p-no-τ refl st)
prest-τ {stBlock}    pHead st = ⊥-elim (p-no-τ refl st)
prest-τ {stBlockTxs} pHead st = ⊥-elim (p-no-τ refl st)
prest-τ {stDone}     pHead st with peer-τ st
... | inj₁ (_ , F.sSil () , _)
... | inj₁ (_ , F.sTau () _ , _)
... | inj₂ (_ , () , _)

-- the Idle producer's moves: one of its three wire receives
pidle-ev : ∀ {P e W} → PRest stIdle P → P ─[ ev (evl e) ]─► W
         → Σ[ x ∈ F.Event ] Σ[ t′ ∈ Rd ] (SIdleV lS dS x t′ × e ≡ renE x × W ≡ peerAfter t′)
pidle-ev pBack st = ⊥-elim (p-ret-no-ev st)
pidle-ev pHead st with peer-ev st
... | x , t′ , stx , refl , refl = x , t′ , sIdleV stx , refl , refl

-- the Block-state producer's moves: take the body `eb` from the application
pblk-ev : ∀ {P e W} → PRest stBlock P → P ─[ ev (evl e) ]─► W
        → Σ[ eb ∈ Params.EB replayParams ]
            (e ≡ evLabel _ (apiLP lS dS lfpSendBlock) eb × W ≡ peerAfter (snd lS dS FromResponder (MsgLFPBlock eb) stIdle))
pblk-ev pBack st = ⊥-elim (p-ret-no-ev st)
pblk-ev pHead st with peer-ev st
... | x , t′ , stx , refl , refl with sBlkV stx
...   | sbBlk eb = eb , refl , refl

-- the BlockTxs-state producer's moves: take the reply `(q , es)` from the application
ptx-ev : ∀ {P e W} → PRest stBlockTxs P → P ─[ ev (evl e) ]─► W
       → Σ[ qe ∈ Net.ApiLPCar lfpSendBlockTxs ]
           (e ≡ evLabel _ (apiLP lS dS lfpSendBlockTxs) qe
            × W ≡ peerAfter (snd lS dS FromResponder (MsgLFPBlockTxs (proj₁ qe) (proj₂ qe)) stIdle))
ptx-ev pBack st = ⊥-elim (p-ret-no-ev st)
ptx-ev pHead st with peer-ev st
... | x , t′ , stx , refl , refl with sTxsV stx
...   | stxTxs q es = (q , es) , refl , refl

------------------------------------------------------------------------
-- The two serving threads
------------------------------------------------------------------------

-- the EB-serve round of the session (node 0 drives `hi`, its producer's direction)
bodyA : Proc
bodyA = ebServeBody nS lS hi

-- the tx-closure-serve round of the session
bodyB : Proc
bodyB = ebTxsServeBody nS lS hi

-- a serving loop over `body` whose current round has reached `b`
lat : Proc → Proc → Proc
lat body b = iter-bind (b >>= (λ a′ → Op.Ret (inj₁ a′))) (loopStep (λ _ → body))

-- the EB-serve round after the report of point `q`: read the body from the store
a1 : Net.ApiLPCar lfpReqBlockRequest → Proc
a1 q = getBodyEvS (proj₁ q) Op.⟶ (λ eb → Op.Output (apiLP lS hi lfpSendBlock) eb Op.Skip)

-- the EB-serve round after the store handed over `eb`: command the Block
a2 : Params.EB replayParams → Proc
a2 eb = Op.Output (apiLP lS hi lfpSendBlock) eb Op.Skip

-- the tx-closure round after the report of `(q , bm)`: confirm the EB is held
b1 : Net.ApiLPCar lfpReqBlockTxsRequest → Proc
b1 qb = getBodyEvS (proj₁ (proj₁ qb)) Op.⟶ (λ _ → serveTxs nS lS hi (proj₁ qb) (proj₂ qb) [])

-- the tx-closure round's reply for point `q` (no mempool: the closure is empty)
b2 : Net.ApiLPCar lfpReqBlockRequest → Proc
b2 q = Op.Output ⦃ Data.DecEq-TxsReply ⦄ (apiLP lS hi lfpSendBlockTxs) (q , []) Op.Skip

-- with `ebTxs = const []` every offset is skipped: the reply is the empty closure
serveTxs-flat : ∀ q bm acc
              → serveTxs nS lS hi q bm acc ≡ Op.Output ⦃ Data.DecEq-TxsReply ⦄ (apiLP lS hi lfpSendBlockTxs) (q , acc) Op.Skip
serveTxs-flat q []       acc = refl
serveTxs-flat q (o ∷ os) acc = serveTxs-flat q os acc

-- the threads, as the composite starts them
threadsS-lat : threadsS ≡ (lat bodyA bodyA ⦀ lat bodyB bodyB)
threadsS-lat = refl

-- thread A at its loop head takes only the BlockRequest report
a0-ev : ∀ {e T′} → lat bodyA bodyA ─[ ev (evl e) ]─► T′
      → Σ[ q ∈ Net.ApiLPCar lfpReqBlockRequest ] (e ≡ evLabel _ (apiLP lS hi lfpReqBlockRequest) q × T′ ≡ lat bodyA (a1 q))
a0-ev st with loop-pfx-ev-inv _ _ _ st
... | q , refl , refl = q , refl , refl

-- thread A after the report takes only a body read for the reported hash
a1-ev : ∀ {q e T′} → lat bodyA (a1 q) ─[ ev (evl e) ]─► T′
      → Σ[ eb ∈ Params.EB replayParams ] (e ≡ evLabel _ (getBodyEvS (proj₁ q)) eb × T′ ≡ lat bodyA (a2 eb))
a1-ev st with loop-pfx-ev-inv _ _ _ st
... | eb , refl , refl = eb , refl , refl

-- thread A with the body takes only its Block command
a2-ev : ∀ {eb e T′} → lat bodyA (a2 eb) ─[ ev (evl e) ]─► T′
      → e ≡ evLabel _ (apiLP lS hi lfpSendBlock) eb × T′ ≡ lat bodyA Op.Skip
a2-ev st with loop-out-ev-inv _ _ _ _ st
... | refl , refl = refl , refl

-- thread B at its loop head takes only the BlockTxsRequest report
b0-ev : ∀ {e T′} → lat bodyB bodyB ─[ ev (evl e) ]─► T′
      → Σ[ qb ∈ Net.ApiLPCar lfpReqBlockTxsRequest ] (e ≡ evLabel _ (apiLP lS hi lfpReqBlockTxsRequest) qb × T′ ≡ lat bodyB (b1 qb))
b0-ev st with loop-pfx-ev-inv _ _ _ st
... | qb , refl , refl = qb , refl , refl

-- thread B after the report takes only a body read for the reported hash, then replies
b1-ev : ∀ {qb e T′} → lat bodyB (b1 qb) ─[ ev (evl e) ]─► T′
      → Σ[ eb ∈ Params.EB replayParams ] (e ≡ evLabel _ (getBodyEvS (proj₁ (proj₁ qb))) eb × T′ ≡ lat bodyB (b2 (proj₁ qb)))
b1-ev {qb} st with loop-pfx-ev-inv _ _ _ st
... | eb , refl , refl = eb , refl , cong (lat bodyB) (serveTxs-flat (proj₁ qb) (proj₂ qb) [])

-- thread B with the reply takes only its BlockTxs command
b2-ev : ∀ {q e T′} → lat bodyB (b2 q) ─[ ev (evl e) ]─► T′
      → e ≡ evLabel _ (apiLP lS hi lfpSendBlockTxs) (q , []) × T′ ≡ lat bodyB Op.Skip
b2-ev st with loop-out-ev-inv ⦃ Data.DecEq-TxsReply ⦄ _ _ _ _ st
... | refl , refl = refl , refl

-- a finished round's only move is the loop-back τ to the head
skip-τ : ∀ {body T′} → lat body Op.Skip ─[ τ ]─► T′ → T′ ≡ lat body body
skip-τ (sSil refl) = refl
skip-τ (sTau () _)

-- a finished round has no visible move
skip-no-ev : ∀ {body e T′} → ¬ (lat body Op.Skip ─[ ev (evl e) ]─► T′)
skip-no-ev (sVis () _)

-- a serving thread at rest: at its loop head, or with its loop-back pending
data ERest (body : Proc) : Proc → Set₁ where
  -- at the head of the round
  eHead : ERest body (lat body body)
  -- the loop-back τ is pending
  eBack : ERest body (lat body Op.Skip)

-- a resting thread's τ is its loop-back
erest-τ : ∀ {body T T′} → (∀ {U} → ¬ (lat body body ─[ τ ]─► U)) → ERest body T → T ─[ τ ]─► T′ → ERest body T′
erest-τ nt eHead st = ⊥-elim (nt st)
erest-τ nt eBack st with skip-τ st
... | refl = eHead

-- resting thread A's τ
erestA-τ : ∀ {T T′} → ERest bodyA T → T ─[ τ ]─► T′ → ERest bodyA T′
erestA-τ = erest-τ (loop-pfx-no-τ _ _ _)

-- resting thread B's τ
erestB-τ : ∀ {T T′} → ERest bodyB T → T ─[ τ ]─► T′ → ERest bodyB T′
erestB-τ = erest-τ (loop-pfx-no-τ _ _ _)

-- resting thread A's moves: the BlockRequest report
erestA-ev : ∀ {T e T′} → ERest bodyA T → T ─[ ev (evl e) ]─► T′
          → Σ[ q ∈ Net.ApiLPCar lfpReqBlockRequest ] (e ≡ evLabel _ (apiLP lS hi lfpReqBlockRequest) q × T′ ≡ lat bodyA (a1 q))
erestA-ev eHead st = a0-ev st
erestA-ev eBack st = ⊥-elim (skip-no-ev st)

-- resting thread B's moves: the BlockTxsRequest report
erestB-ev : ∀ {T e T′} → ERest bodyB T → T ─[ ev (evl e) ]─► T′
          → Σ[ qb ∈ Net.ApiLPCar lfpReqBlockTxsRequest ] (e ≡ evLabel _ (apiLP lS hi lfpReqBlockTxsRequest) qb × T′ ≡ lat bodyB (b1 qb))
erestB-ev eHead st = b0-ev st
erestB-ev eBack st = ⊥-elim (skip-no-ev st)

-- a thread's alphabet at a state: api or store labels only
Alph : Proc → Set₁
Alph T = ∀ {e T′} → T ─[ ev (evl e) ]─► T′ → AE e ⊎ SE e

-- resting thread A's alphabet
alphA-rest : ∀ {T} → ERest bodyA T → Alph T
alphA-rest r st with erestA-ev r st
... | _ , refl , _ = inj₁ ptt

-- resting thread B's alphabet
alphB-rest : ∀ {T} → ERest bodyB T → Alph T
alphB-rest r st with erestB-ev r st
... | _ , refl , _ = inj₁ ptt

-- thread A's alphabet while reading the body
alphA1 : ∀ {q} → Alph (lat bodyA (a1 q))
alphA1 {q} st with a1-ev {q} st
... | _ , refl , _ = inj₂ ptt

-- thread A's alphabet while commanding the Block
alphA2 : ∀ {eb} → Alph (lat bodyA (a2 eb))
alphA2 {eb} st with a2-ev {eb} st
... | refl , _ = inj₁ ptt

-- thread B's alphabet while reading the body
alphB1 : ∀ {qb} → Alph (lat bodyB (b1 qb))
alphB1 {qb} st with b1-ev {qb} st
... | _ , refl , _ = inj₂ ptt

-- thread B's alphabet while commanding the BlockTxs
alphB2 : ∀ {q} → Alph (lat bodyB (b2 q))
alphB2 {q} st with b2-ev {q} st
... | refl , _ = inj₁ ptt

------------------------------------------------------------------------
-- The body store (hoisted from the Increment 0 probe, plus the body read)
------------------------------------------------------------------------

-- every label of a store round is a store event (`Stores.body-All`'s shape)
bodyAll : ∀ bs → AllT SE (bodyStep nS bs)
bodyAll bs = AllT-□ (AllT-⟶ (putBodyEv nS) (λ _ → ptt) (λ _ → AllT-Ret)) (obA bs)
  where
    -- the keyed menu
    obA : ∀ xs → AllT SE (offerBodies nS bs xs)
    obA []         = AllT-Stop
    obA (eb ∷ ebs) = AllT-□ (AllT-Output (getBodyEvS eb) eb ptt AllT-Ret) (obA ebs)

-- every first move of the store is a store event
store-ev : ∀ {bs X e a M} → bodyStore nS bs ─[ ev (evl (evLabel X e a)) ]─► M
         → EventSet.mem storeES (X , e) a
store-ev {bs} st with LoopN.iter-ev-elim _ _ st
... | _ , st₁ , _ with AllT->>= (bodyAll bs) (λ _ → AllT-Ret) (⟹-ev st₁ ⟹-refl)
...   | p ∷ _ = p

-- a `□` of two react nodes forces to the merged node
□-force-rr : ∀ {P Q : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Bodies} {vP τcP vQ τcQ}
           → PTree.force P ≡ react vP τcP → PTree.force Q ≡ react vQ τcQ
           → PTree.force (P □ Q) ≡ react (mergeVis vP vQ) (□-mt (react vP τcP) (react vQ τcQ) P Q)
□-force-rr {P} {Q} eqP eqQ with PTree.force P | PTree.force Q
... | react _ _ | react _ _ = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | ret _     | _         = case eqP of λ ()
... | sil _ | _ = case eqP of λ ()
... | react _ _ | ret _     = case eqQ of λ ()
... | react _ _ | sil _ = case eqQ of λ ()

-- a `□` of two stable menus is stable (`Stability.ExtChoice.stable-□`, kept local
-- so this module does not import the FD layer)
□-stable : ∀ {P Q : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Bodies}
         → isStable P → isStable Q → isStable (P □ Q)
□-stable {P} {Q} sP sQ with stable→react {t = P} sP | stable→react {t = Q} sQ
... | vP , τcP , eqP , hP | vQ , τcQ , eqQ , hQ = mk-stable {t = P □ Q} (□-force-rr eqP eqQ) mt
  where
    -- the merged τ-map is everywhere nothing
    mt : ∀ i a → □-mt (react vP τcP) (react vQ τcQ) P Q i a ≡ nothing
    mt (_ , base _)            a = refl
    mt (_ , fin)               a = refl
    mt (_ , pair (base _) _)   a = refl
    mt (_ , pair (pair _ _) _) a = refl
    mt (_ , pair fin i) (lift fzero , a)        rewrite hP (_ , i) a = refl
    mt (_ , pair fin i) (lift (fsuc fzero) , a) rewrite hQ (_ , i) a = refl
    mt (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = refl

-- a bind of a stable tree is stable
bind-stable : ∀ {ℓs} {S : Set ℓs} {P : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Bodies}
                {k : Bodies → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) S}
            → isStable P → isStable (P >>= k)
bind-stable {P = P} {k = k} sP with stable→react {t = P} sP
... | v , τc , eqP , h = mk-stable {t = P >>= k} (fBind-react k P eqP) bt
  where
    -- the bound τ-map reads `τc`, which is everywhere nothing
    bt : ∀ i a → Op.bindT k (react v τc) i a ≡ nothing
    bt i a rewrite h i a = refl

-- a loop body that is stable at its head makes the loop stable there
iter-stable : ∀ {ℓr} {A : Set} {R : Set ℓr} {t : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (A ⊎ R)}
                {k : A → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (A ⊎ R)}
            → isStable t → isStable (iter-bind t k)
iter-stable {t = t} {k = k} sP with stable→react {t = t} sP
... | v , τc , eqP , h = mk-stable {t = iter-bind t k} (fIter-react k t eqP) it
  where
    -- the loop's τ-map reads `τc`, which is everywhere nothing
    it : ∀ i a → Op.iterT k (react v τc) i a ≡ nothing
    it i a rewrite h i a = refl

-- the body store is stable at its loop head, whatever it holds
store-stable : ∀ bs → isStable (bodyStore nS bs)
store-stable bs =
  iter-stable {t = bodyStep nS bs >>= kR}
    (bind-stable {S = Bodies ⊎ PU.⊤} {P = bodyStep nS bs} {k = kR} (□-stable {P = Op.Prefix (putBodyEv nS) _} {Q = offerBodies nS bs bs} (λ _ _ → refl) (ob bs)))
  where
    -- the loop's continuation into the next round
    kR : Bodies → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (Bodies ⊎ PU.⊤)
    kR a′ = Op.Ret (inj₁ a′)

    -- the keyed menu is stable
    ob : ∀ xs → isStable (offerBodies nS bs xs)
    ob []         = λ _ _ → refl
    ob (eb ∷ ebs) = □-stable {P = Op.Output (getBodyEvS eb) eb (Op.Ret bs)} {Q = offerBodies nS bs ebs}
                      (λ _ _ → refl) (ob ebs)

-- a store round's residual that drains back to `Ret bs` by τs alone
data Drains (bs : Bodies) (c : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Bodies) : Set₁ where
  drains : (∀ {r} → PTree.force c ≡ ret r → r ≡ bs)
         → (∀ {x c′} → ¬ (c ─[ ev (evl x) ]─► c′))
         → (∀ {c′} → c ─[ τ ]─► c′ → Drains bs c′)
         → Drains bs c

-- `Ret bs` drains
drains-ret : ∀ {bs} → Drains bs (Op.Ret bs)
drains-ret = drains (λ { refl → refl }) (λ { (sVis () _) }) (λ { (sSil ()) ; (sTau () _) })

-- an internal choice of draining residuals drains
drains-⊓ : ∀ {bs P Q} → Drains bs P → Drains bs Q → Drains bs (P ⊓ Q)
drains-⊓ {bs} {P} {Q} dP dQ = drains (λ ()) (λ { (sVis refl ()) }) τc
  where
    -- the choice's τs pick an operand
    τc : ∀ {c′} → (P ⊓ Q) ─[ τ ]─► c′ → Drains bs c′
    τc st with ⊓-τ-inv P Q st
    ... | inj₁ refl = dP
    ... | inj₂ refl = dQ

-- a body read off the keyed menu returns the body with the asked hash, and drains
ob-get : ∀ {bs} xs {h x c} → offerBodies nS bs xs ─[ ev (evl (evLabel _ (getBodyEvS h) x)) ]─► c
       → x ≡ h × Drains bs c
ob-get []         (sVis refl ())
ob-get {bs} (eb ∷ ebs) st with □-ev-elim (Op.Output (getBodyEvS eb) eb (Op.Ret bs)) (offerBodies nS bs ebs) st
... | evP stO with out-ev stO
...   | refl , refl = refl , drains-ret
ob-get (eb ∷ ebs) st | evQ stR = ob-get ebs stR
ob-get (eb ∷ ebs) st | evPQ stO stR with out-ev stO | ob-get ebs stR
...   | refl , refl | refl , dR = refl , drains-⊓ drains-ret dR

-- a body read off one store round comes from the menu (the deposit arm is another channel)
round-get : ∀ {bs h x c} {k : Params.EB replayParams → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Bodies}
          → (Op.Prefix (putBodyEv nS) k □ offerBodies nS bs bs) ─[ ev (evl (evLabel _ (getBodyEvS h) x)) ]─► c
          → x ≡ h × Drains bs c
round-get {bs} {h} {x} {k = k} st with □-ev-elim (Op.Prefix (putBodyEv nS) k) (offerBodies nS bs bs) st
... | evP (sVis refl br) with Prefix-cont-fires {e = getBodyEvS h} {a = x} {ce = putBodyEv nS} {P = k} br
...   | () , _
round-get {bs} st | evQ stR = ob-get bs stR
round-get {bs} {h} {x} {k = k} st | evPQ (sVis refl br) _ with Prefix-cont-fires {e = getBodyEvS h} {a = x} {ce = putBodyEv nS} {P = k} br
...   | () , _

-- the store mid-round, its round residual at `c`
smid : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Bodies → Proc
smid c = iter-bind (c >>= (λ a′ → Op.Ret (inj₁ a′))) (loopStep (bodyStep nS))

-- a body read off the store at its loop head: the asked body, and the store goes mid-round
store-get : ∀ {bs h x S′} → bodyStore nS bs ─[ ev (evl (evLabel _ (getBodyEvS h) x)) ]─► S′
          → x ≡ h × Σ[ c ∈ PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Bodies ] (Drains bs c × S′ ≡ smid c)
store-get {bs} st with LoopN.iter-ev-elim _ _ st
... | t′ , st₁ , refl with bind-ev-elim _ (bodyStep nS bs) st₁
...   | beK r _ (sVis () _)
...   | beL c st₂ refl with round-get st₂
...     | eq , d = eq , c , d , refl

-- the store at rest: at its loop head, or mid-round on a draining residual
data SRest (bs : Bodies) : Proc → Set₁ where
  -- at the loop head
  sHead : SRest bs (bodyStore nS bs)
  -- mid-round, draining back to the head
  sMid  : ∀ {c} → Drains bs c → SRest bs (smid c)

-- the store mid-round has no visible move
smid-no-ev : ∀ {bs c x S′} → Drains bs c → ¬ (smid c ─[ ev (evl x) ]─► S′)
smid-no-ev {c = c} (drains _ nev _) st with LoopN.iter-ev-elim _ _ st
... | t′ , st₁ , refl with bind-ev-elim _ c st₁
...   | beL c′ stc _ = nev stc
...   | beK r _ (sVis () _)

-- the store mid-round moves silently, and is back at its head once drained
smid-τ : ∀ {bs c S′} → Drains bs c → smid c ─[ τ ]─► S′ → SRest bs S′
smid-τ {c = c} (drains dret _ dτ) st with LoopN.iter-τ-elim _ _ st
... | itτ t′ st₁ refl with bind-τ-elim _ c st₁
...   | bτL c′ stc refl = sMid (dτ stc)
...   | bτK r _ (sSil ())
...   | bτK r _ (sTau () _)
smid-τ {c = c} (drains dret _ dτ) st | itBack a′ eq refl with bind-ret-inv _ c eq
... | r , eqc with trans (sym eq) (fBind-ret _ c eqc) | dret eqc
...   | refl | refl = sHead

-- a resting store's τ keeps it at rest
srest-τ : ∀ {bs S S′} → SRest bs S → S ─[ τ ]─► S′ → SRest bs S′
srest-τ {bs} sHead st = ⊥-elim (stable-no-τ (store-stable bs) st)
srest-τ (sMid d) st = smid-τ d st

-- a resting store's alphabet: store labels only
srest-alph : ∀ {bs S e S′} → SRest bs S → S ─[ ev (evl e) ]─► S′ → SE e
srest-alph {bs} sHead st = store-ev {bs} st
srest-alph (sMid d) st = ⊥-elim (smid-no-ev d st)

-- a resting store hands over exactly the body with the asked hash (`ebHash = id`)
srest-get : ∀ {bs S h x S′} → SRest bs S → S ─[ ev (evl (evLabel _ (getBodyEvS h) x)) ]─► S′
          → x ≡ h × SRest bs S′
srest-get {bs} sHead st with store-get {bs} st
... | eq , c , d , refl = eq , sMid d
srest-get (sMid d) st = ⊥-elim (smid-no-ev d st)

------------------------------------------------------------------------
-- The composite: a step of `C P Ta Tb S` is a step of its components
------------------------------------------------------------------------

-- the composite at producer P, threads Ta ⦀ Tb and store S
C : Proc → Proc → Proc → Proc → Proc
C P Ta Tb S = (P ∥⇘ apiES ⇙ (Ta ⦀ Tb)) ∥⇘ storeES ⇙ S

-- `srvAt` is the composite with the store at its loop head
srvAt-C : ∀ P bs → srvAt P threadsS bs ≡ C P (lat bodyA bodyA) (lat bodyB bodyB) (bodyStore nS bs)
srvAt-C P bs = refl

-- a composite τ: one component's τ
data Cτ (P Ta Tb S : Proc) : Proc → Set₁ where
  -- the producer's
  τP : ∀ {P′}  → P  ─[ τ ]─► P′  → Cτ P Ta Tb S (C P′ Ta Tb S)
  -- thread A's
  τA : ∀ {Ta′} → Ta ─[ τ ]─► Ta′ → Cτ P Ta Tb S (C P Ta′ Tb S)
  -- thread B's
  τB : ∀ {Tb′} → Tb ─[ τ ]─► Tb′ → Cτ P Ta Tb S (C P Ta Tb′ S)
  -- the store's
  τS : ∀ {S′}  → S  ─[ τ ]─► S′  → Cτ P Ta Tb S (C P Ta Tb S′)

-- the composite τ inversion
comp-τ : ∀ {P Ta Tb S M} → C P Ta Tb S ─[ τ ]─► M → Cτ P Ta Tb S M
comp-τ {P} {Ta} {Tb} {S} st with Par-τ-elim storeES _ (P ∥⇘ apiES ⇙ (Ta ⦀ Tb)) S st
... | τR _ stS refl = τS stS
... | τL _ stI refl with Par-τ-elim apiES _ P (Ta ⦀ Tb) stI
...   | τL _ stP refl = τP stP
...   | τR _ stT refl with Par-τ-elim ∅ES _ Ta Tb stT
...     | τL _ stA refl = τA stA
...     | τR _ stB refl = τB stB

-- a composite visible step: the producer alone, an api rendezvous of the producer with a
-- thread, a store rendezvous of a thread with the store, or both threads on one label
data CEv (P Ta Tb S : Proc) (e : Event) : Proc → Set₁ where
  -- the producer alone (wire I/O)
  eP    : ∀ {P′} → ¬ AE e → ¬ SE e → P ─[ ev (evl e) ]─► P′ → CEv P Ta Tb S e (C P′ Ta Tb S)
  -- producer and thread A on an api label
  eAA   : ∀ {P′ Ta′} → AE e → P ─[ ev (evl e) ]─► P′ → Ta ─[ ev (evl e) ]─► Ta′ → CEv P Ta Tb S e (C P′ Ta′ Tb S)
  -- producer and thread B on an api label
  eAB   : ∀ {P′ Tb′} → AE e → P ─[ ev (evl e) ]─► P′ → Tb ─[ ev (evl e) ]─► Tb′ → CEv P Ta Tb S e (C P′ Ta Tb′ S)
  -- thread A and the store on a store label
  eSA   : ∀ {Ta′ S′} → SE e → Ta ─[ ev (evl e) ]─► Ta′ → S ─[ ev (evl e) ]─► S′ → CEv P Ta Tb S e (C P Ta′ Tb S′)
  -- thread B and the store on a store label
  eSB   : ∀ {Tb′ S′} → SE e → Tb ─[ ev (evl e) ]─► Tb′ → S ─[ ev (evl e) ]─► S′ → CEv P Ta Tb S e (C P Ta Tb′ S′)
  -- both threads offer the label (ruled out per state: one thread always rests)
  eBoth : ∀ {Ta′ Tb′ M} → Ta ─[ ev (evl e) ]─► Ta′ → Tb ─[ ev (evl e) ]─► Tb′ → CEv P Ta Tb S e M

-- an api-or-store label outside both sets is impossible
alph-out : ∀ {e} → AE e ⊎ SE e → ¬ AE e → ¬ SE e → ⊥
alph-out (inj₁ a) na _  = na a
alph-out (inj₂ s) _  ns = ns s

-- no producer move is a store label
peer-ns : ∀ {t e W} → peerAfter t ─[ ev (evl e) ]─► W → ¬ SE e
peer-ns stP m with peer-ev stP
... | x , _ , _ , refl , _ = renE-not-store x m

-- no resting producer move is a store label
prest-ns : ∀ {st P e W} → PRest st P → P ─[ ev (evl e) ]─► W → ¬ SE e
prest-ns pBack = peer-ns
prest-ns pHead = peer-ns

-- the composite visible-step inversion, given the components' alphabets
comp-ev : ∀ {P Ta Tb S e M} → (∀ {x P′} → P ─[ ev (evl x) ]─► P′ → ¬ SE x)
        → Alph Ta → Alph Tb → (∀ {x S′} → S ─[ ev (evl x) ]─► S′ → SE x)
        → C P Ta Tb S ─[ ev (evl e) ]─► M → CEv P Ta Tb S e M
comp-ev {P} {Ta} {Tb} {S} {evLabel X c a} hP hA hB hS st = outer (Par-ev-elim storeES _ _ S st)
  where
    -- the producer never performs a store label
    pns : ∀ {P′} → SE (evLabel X c a) → P ─[ ev (evl (evLabel X c a)) ]─► P′ → ⊥
    pns m stP = hP stP m

    -- the threads on a store label
    thrS : ∀ {T′ S′} → SE (evLabel X c a) → (Ta ⦀ Tb) ─[ ev (evl (evLabel X c a)) ]─► T′
         → S ─[ ev (evl (evLabel X c a)) ]─► S′
         → CEv P Ta Tb S (evLabel X c a) ((P ∥⇘ apiES ⇙ T′) ∥⇘ storeES ⇙ S′)
    thrS m stT stS with Par-ev-elim ∅ES _ Ta Tb stT
    ... | evSync () _ _
    ... | evL _ stA      = eSA m stA stS
    ... | evR _ stB      = eSB m stB stS
    ... | evBoth _ stA stB = eBoth stA stB

    -- the threads on an api label, with the producer
    thrA : ∀ {P′ T′} → AE (evLabel X c a) → P ─[ ev (evl (evLabel X c a)) ]─► P′
         → (Ta ⦀ Tb) ─[ ev (evl (evLabel X c a)) ]─► T′
         → CEv P Ta Tb S (evLabel X c a) ((P′ ∥⇘ apiES ⇙ T′) ∥⇘ storeES ⇙ S)
    thrA m stP stT with Par-ev-elim ∅ES _ Ta Tb stT
    ... | evSync () _ _
    ... | evL _ stA      = eAA m stP stA
    ... | evR _ stB      = eAB m stP stB
    ... | evBoth _ stA stB = eBoth stA stB

    -- the threads alone on a label in neither set: impossible
    thrO : ∀ {T′} → ¬ AE (evLabel X c a) → ¬ SE (evLabel X c a)
         → (Ta ⦀ Tb) ─[ ev (evl (evLabel X c a)) ]─► T′ → ⊥
    thrO na ns stT with Par-ev-elim ∅ES _ Ta Tb stT
    ... | evSync () _ _
    ... | evL _ stA      = alph-out {evLabel X c a} (hA stA) na ns
    ... | evR _ stB      = alph-out {evLabel X c a} (hB stB) na ns
    ... | evBoth _ stA _ = alph-out {evLabel X c a} (hA stA) na ns

    -- the inner parallel on a store label
    innerS : ∀ {I′ S′} → SE (evLabel X c a)
           → ParevR apiES (λ _ _ → ptt) P (Ta ⦀ Tb) I′ (evl (evLabel X c a))
           → S ─[ ev (evl (evLabel X c a)) ]─► S′
           → CEv P Ta Tb S (evLabel X c a) (I′ ∥⇘ storeES ⇙ S′)
    innerS m (evSync _ stP _)  stS = ⊥-elim (pns m stP)
    innerS m (evL _ stP)       stS = ⊥-elim (pns m stP)
    innerS m (evR _ stT)       stS = thrS m stT stS
    innerS m (evBoth _ stP _)  stS = ⊥-elim (pns m stP)

    -- the inner parallel on a non-store label
    innerO : ∀ {I′} → ¬ SE (evLabel X c a)
           → ParevR apiES (λ _ _ → ptt) P (Ta ⦀ Tb) I′ (evl (evLabel X c a))
           → CEv P Ta Tb S (evLabel X c a) (I′ ∥⇘ storeES ⇙ S)
    innerO ns (evSync ma stP stT) = thrA ma stP stT
    innerO ns (evL na stP)        = eP na ns stP
    innerO ns (evR na stT)        = ⊥-elim (thrO na ns stT)
    innerO ns (evBoth na _ stT)   = ⊥-elim (thrO na ns stT)

    -- the outer parallel's cases
    outer : ∀ {M} → ParevR storeES (λ _ _ → ptt) (P ∥⇘ apiES ⇙ (Ta ⦀ Tb)) S M (evl (evLabel X c a))
          → CEv P Ta Tb S (evLabel X c a) M
    outer (evSync m stI stS) = innerS m (Par-ev-elim apiES _ P (Ta ⦀ Tb) stI) stS
    outer (evL ns stI)       = innerO ns (Par-ev-elim apiES _ P (Ta ⦀ Tb) stI)
    outer (evR ns stS)       = ⊥-elim (ns (hS stS))
    outer (evBoth ns _ stS)  = ⊥-elim (ns (hS stS))
