{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- M1a': single-instance terminable refinement carrier (GENERIC Data).
--
-- `p1` single-instance Params (numLinks = 1, one (lo , N2N_ChainSync)
-- instance, abstract data domains = ⊤); the module is parametric in the
-- forwarded payload `(Data : Set) ⦃ DecEq Data ⦄`.  It instantiates the
-- terminable copy-spec / multiplexer handles `spec0 = CopySpecT`,
-- `net0 = NetworkT` over `NetT Data`, and declares the `RState`
-- bisimulation-carrier GADT: one constructor per reachable joint config.
--
-- GENERIC-DATA METHOD (Route A, explicit-decode).  The value-carrying
-- writer offers `Op.Output e x P` (sndmsg/tx/rcvmsg/output) fire only when
-- the offered value matches (`x ≟ x`), which is stuck for abstract Data.
-- We follow `NetworkRefinementGen.agda`:
--   * every reachable state is written as an EXPLICIT composite term
--     (assembled by `mkNet` from the leaf residuals that `NetworkT.agda`
--     now exports — no internal `with`/`x ≟ x` redex), so it REDUCES; and
--   * each `─[_]─►` step is proved with an offer-equation `where`-helper
--     that discharges the surface `x ≟ x` by `rewrite ≟-diag` (Hedberg,
--     `≡-≟-identity`, proven — NO postulate).
-- The buffered value `x` is held only by the four in-flight writer leaves
-- (I1/T1/Rc1/O1); every ack-stage and loop-back state is `x`-free.
--
-- STATUS (work stopped here, 2026-07-09): the `mkDR`/`mkDRˢ` guarded
-- builders and the theorem `CopySpecT-≈FD-NetworkT : CopySpecT ≈FD NetworkT`
-- are assembled and typecheck with the EXACT type — but the theorem is
-- proven MODULO 3 remaining postulates: it is NOT a complete proof.
--
--   DISCHARGED (real, no postulate):  nd-spec, sim-bwd-tau, sim-bwd-ev.
--   REMAINING (postulated, 3):        nd-net, sim-fwd-ev, sim-fwd-tau
--                                     — the network-side step inversion
--                                     + network non-divergence.
--
-- The residual 3 are the BlockFetch-scale content: inverting every step of
-- the composed 6-leaf multiplexer term.  A logically-complete `sim-fwd-ev`
-- was written but did NOT typecheck in feasible time/memory (deep
-- normalisation of the composite term — the same cost documented for the
-- four-node system), so it was discarded.  Completing these needs the
-- cost-controlled `mkNet`/explicit-decode + `Par-τ-elim`/`Hide-τ-elim`
-- inversion discipline throughout; deferred.  Real & checked: the 16-state
-- generic-Data carrier, all `─[_]─►` step lemmas, the builder assembly /
-- guardedness / orientation, the mdone-drain, and the exact theorem type.
------------------------------------------------------------------------

open import Level using (0ℓ; lift)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Bool using (true)
open import Data.Product using (_,_; _×_; proj₁; proj₂; Σ; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; ≡-≟-identity; sym; trans; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using
  (IDs; Dir; lo; hi; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission; N2N_KeepAlive; N2N_LeiosNotify; N2N_LeiosFetch)

module CSP.Examples.Cardano_network.Terminable.NetworkTRefinement
  (Data : Set) ⦃ _ : DecEq Data ⦄ where

open PTree
open ExtI

------------------------------------------------------------------------
-- The single-instance Params `p1`.
------------------------------------------------------------------------

-- trivial decidable equality on ⊤ (every pair equal)
instance
  decEq⊤ : DecEq ⊤
  decEq⊤ = record { _≟_ = λ _ _ → yes refl }

-- single-instance params: numLinks = 1, linkConfig = one (lo , N2N_ChainSync)
p1 : Params
p1 = record
  { Cookie = ⊤ ; Block = ⊤ ; Txid = ⊤ ; LSlot = ⊤
  ; VoterId = ⊤ ; LFBitmap = ⊤ ; VoteBlob = ⊤
  ; numLinks = 1
  ; linkConfig = λ _ → (lo , N2N_ChainSync) ∷ []
  ; decCookie  = decEq⊤ ; decBlock    = decEq⊤ ; decTxid    = decEq⊤
  ; decLSlot   = decEq⊤ ; decVoterId  = decEq⊤ ; decLFBitmap = decEq⊤
  ; decVoteBlob = decEq⊤
  ; Time = ⊤ ; Length = ⊤ ; time₀ = tt ; length₀ = tt
  ; decTime = decEq⊤ ; decLength = decEq⊤ }

------------------------------------------------------------------------
-- Instantiate the terminable copy-spec / multiplexer at `p1`, `Data`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Net p1 using (Link)
open import CSP.Examples.Cardano_network.Terminable.NetT p1
  using ( NetT; NetT-≟
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; mdone )
open import CSP.Examples.Cardano_network.Terminable.NetworkT p1 Data

open import CSP.Operators {E = NetT Data} (NetT-≟ {Data})
  using (iter-bind; Output; pchoice; Ret; Prefix₀; _∥⇘_⇙_; _∖_; _⦀_; chanSet; Skip)

-- the terminable copy spec  (CopySpec analogue)
spec0 : NetProc
spec0 = CopySpecT

-- the terminable multiplexer (Network analogue)
net0 : NetProc
net0 = NetworkT

l0 : Link
l0 = fz

------------------------------------------------------------------------
-- The sync/hide EventSets at value level (exactly NetworkT's forms).
------------------------------------------------------------------------
csSRd' csRSd' csTAd' csMD' csSR' csRS' csTA' : _
csSRd' = chanSet csSRd csSRd-dec
csRSd' = chanSet csRSd csRSd-dec
csTAd' = chanSet csTAd csTAd-dec
csMD'  = chanSet csMD  csMD-dec
csSR'  = chanSet csSR  csSR-dec
csRS'  = chanSet csRS  csRS-dec
csTA'  = chanSet csTA  csTA-dec

------------------------------------------------------------------------
-- `mkNet`: reassemble the whole composite from the six leaf residuals
-- (Input / Output leaves + the four drainers), in the EXACT operator form
-- of `NetworkT.NetworkT`.  `mkNet I0 O0 T0 R0 Rc0 Sa0 ≡ net0` by `refl`.
------------------------------------------------------------------------
mkNet : (inp out trans rcvk recv sndk : NetProc) → NetProc
mkNet inp out trans rcvk recv sndk =
  ((((inp ⦀ Skip) ⦀ Skip) ∥⇘ csSRd' ⇙ (trans ∥⇘ csMD' ⇙ rcvk)) ∖ csSR'
    ∥⇘ csTAd' ⇙
   (((out ⦀ Skip) ⦀ Skip) ∥⇘ csRSd' ⇙ (recv  ∥⇘ csMD' ⇙ sndk)) ∖ csRS')
    ∖ csTA'

-- base composite equals net0 (validates `mkNet` against `NetworkT`).
net0-mkNet : net0 ≡ mkNet (InputT l0 lo N2N_ChainSync) (OutputT l0 lo N2N_ChainSync)
                          (TransmitterT allInstances) (RcvAckT allInstances)
                          (ReceiverT allInstances) (SndAckT allInstances)
net0-mkNet = refl

------------------------------------------------------------------------
-- Leaf residual states (explicit; no `with`).  The iter continuation `k`
-- of each leaf is `λ _ → pchoice <menu>` (its exported top-level menu).
-- Only the four in-flight writer residuals I1/T1/Rc1/O1 carry `x`.
------------------------------------------------------------------------

-- InputT: input?x → sndmsg!x → rcvack → loop
I1e : Data → NetProc                 -- holding x, about to sndmsg!x
I1e x = iter-bind (Output (sndmsg l0 lo N2N_ChainSync) x
                    (rcvack l0 lo N2N_ChainSync ⟶₀ Ret (inj₁ Poly.tt)))
                  (λ _ → pchoice (inputTV l0 lo N2N_ChainSync))
I2e : NetProc                        -- x consumed, awaiting rcvack
I2e = iter-bind (rcvack l0 lo N2N_ChainSync ⟶₀ Ret (inj₁ Poly.tt))
                (λ _ → pchoice (inputTV l0 lo N2N_ChainSync))
Ige : NetProc                        -- loop-back guard (sil → InputT)
Ige = iter-bind (Ret (inj₁ Poly.tt)) (λ _ → pchoice (inputTV l0 lo N2N_ChainSync))

-- TransmitterT: sndmsg?x → tx!x → loop  (carries the live set)
T1e : Data → NetProc                 -- holding x, about to tx!x
T1e x = iter-bind (Output (tx l0 lo N2N_ChainSync) x (Ret (inj₁ allInstances)))
                  transmitterTStep
Tge : NetProc                        -- loop-back guard
Tge = iter-bind (Ret (inj₁ allInstances)) transmitterTStep

-- ReceiverT: tx?x → rcvmsg!x → loop
Rc1e : Data → NetProc                -- holding x, about to rcvmsg!x
Rc1e x = iter-bind (Output (rcvmsg l0 lo N2N_ChainSync) x (Ret (inj₁ allInstances)))
                   receiverTStep
Rcge : NetProc                       -- loop-back guard
Rcge = iter-bind (Ret (inj₁ allInstances)) receiverTStep

-- OutputT: rcvmsg?x → output!x → sndack → loop
O1e : Data → NetProc                 -- holding x, about to output!x
O1e x = iter-bind (Output (output l0 lo N2N_ChainSync) x
                    (sndack l0 lo N2N_ChainSync ⟶₀ Ret (inj₁ Poly.tt)))
                  (λ _ → pchoice (outputTV l0 lo N2N_ChainSync))
O2e : NetProc                        -- x emitted, awaiting sndack
O2e = iter-bind (sndack l0 lo N2N_ChainSync ⟶₀ Ret (inj₁ Poly.tt))
                (λ _ → pchoice (outputTV l0 lo N2N_ChainSync))
Oge : NetProc                        -- loop-back guard
Oge = iter-bind (Ret (inj₁ Poly.tt)) (λ _ → pchoice (outputTV l0 lo N2N_ChainSync))

-- SndAckT: sndack → ack → loop
Sa1e : NetProc                       -- about to ack (payload-free)
Sa1e = iter-bind (ack l0 lo N2N_ChainSync ⟶₀ Ret (inj₁ allInstances)) sndAckTStep
Sage : NetProc                       -- loop-back guard
Sage = iter-bind (Ret (inj₁ allInstances)) sndAckTStep

-- RcvAckT: ack → rcvack → loop
R1e : NetProc                        -- about to rcvack (payload-free)
R1e = iter-bind (rcvack l0 lo N2N_ChainSync ⟶₀ Ret (inj₁ allInstances)) rcvAckTStep
Rge : NetProc                        -- loop-back guard
Rge = iter-bind (Ret (inj₁ allInstances)) rcvAckTStep

-- initial leaf handles (the un-advanced processes)
I0 O0 T0 R0 Rc0 Sa0 : NetProc
I0  = InputT l0 lo N2N_ChainSync
O0  = OutputT l0 lo N2N_ChainSync
T0  = TransmitterT allInstances
R0  = RcvAckT allInstances
Rc0 = ReceiverT allInstances
Sa0 = SndAckT allInstances

------------------------------------------------------------------------
-- The explicit spine states (all reducible).  Canonical order:
--   input, sndmsg, tx, rcvmsg, output, sndack, ack, rcvack.
------------------------------------------------------------------------
W1 : Data → NetProc     -- post input?x
W1 x = mkNet (I1e x) O0    T0     R0  Rc0     Sa0
W2 : Data → NetProc     -- post sndmsg!x
W2 x = mkNet I2e     O0    (T1e x) R0 Rc0     Sa0
W3 : Data → NetProc     -- post tx!x
W3 x = mkNet I2e     O0    Tge    R0  (Rc1e x) Sa0
W4 : Data → NetProc     -- post rcvmsg!x  (offers output!x)
W4 x = mkNet I2e     (O1e x) Tge  R0  Rcge    Sa0
W5 : Data → NetProc     -- post output!x
W5 x = mkNet I2e     O2e   Tge    R0  Rcge    Sa0
W6 : NetProc            -- post sndack   (x-free from here)
W6 = mkNet I2e     Oge   Tge    R0  Rcge    Sa1e
W7 : NetProc            -- post ack
W7 = mkNet I2e     Oge   Tge    R1e Rcge    Sage
W8 : NetProc            -- post rcvack   (all six leaves at loop-back guards)
W8 = mkNet Ige     Oge   Tge    Rge Rcge    Sage

------------------------------------------------------------------------
-- Spec-side reachable states (CopyT cell inside two ⦀ Skip wrappers).
------------------------------------------------------------------------
C1e : Data → NetProc                 -- CopyT holding x, about to output!x
C1e x = iter-bind (Output (output l0 lo N2N_ChainSync) x (Ret (inj₁ Poly.tt)))
                  (λ _ → pchoice (copyTMenu l0 lo N2N_ChainSync))
Cge : NetProc                        -- CopyT loop-back guard
Cge = iter-bind (Ret (inj₁ Poly.tt)) (λ _ → pchoice (copyTMenu l0 lo N2N_ChainSync))

S1 : Data → NetProc     -- spec after input?x  (offers output!x)
S1 x = ((C1e x ⦀ Skip) ⦀ Skip)
S2 : NetProc            -- spec after output!x (loop-back guard)
S2 = ((Cge ⦀ Skip) ⦀ Skip)

spec0-mkSpec : spec0 ≡ ((CopyT l0 lo N2N_ChainSync ⦀ Skip) ⦀ Skip)
spec0-mkSpec = refl

------------------------------------------------------------------------
-- LTS setup + Hedberg reflexivity for the stuck `x ≟ x`.
------------------------------------------------------------------------
open import Semantics.LTS {E = NetT Data} {I = ExtI (NetT Data)} hiding (Diverges)
open import Semantics.WeakBisim {E = NetT Data} {I = ExtI (NetT Data)}
  using (_─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev; WSimF; τ*-trans)
open import Semantics.DRBisim {E = NetT Data} {I = ExtI (NetT Data)}
  using (Diverges; DRbisim; _≈DR_; drbisim-sym; deadlock-converges; deadlock-no-τ)
open import Semantics.FailuresDivergences {E = NetT Data} {I = ExtI (NetT Data)}
  using (_≈FD_)
open import Semantics.DRImpliesFD {E = NetT Data} {I = ExtI (NetT Data)}
  using (drbisim→≈FD)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open DRbisim
open WSimF

NetR : Set
NetR = Poly.⊤ {0ℓ}

-- read the visible-offer / τ continuation out of a node.
vis-of : NodeKind (NetT Data) (ExtI (NetT Data)) NetR
       → (at : AnyTypes (NetT Data)) → proj₁ at → Maybe NetProc
vis-of (react v _) = v
vis-of _           = λ _ _ → nothing

τ-of : NodeKind (NetT Data) (ExtI (NetT Data)) NetR
     → (i : AnyTypes (ExtI (NetT Data))) → proj₁ i → Maybe NetProc
τ-of (react _ τc) = τc
τ-of _            = λ _ _ → nothing

-- Hedberg reflexivity (proven, not postulated): discharges stuck `x ≟ x`.
≟-diag : ∀ (x : Data) → (x ≟ x) ≡ yes refl
≟-diag x = ≡-≟-identity _≟_ refl

-- visible labels / event indices.
inputAt outputAt : AnyTypes (NetT Data)
inputAt  = (Data , input  l0 lo N2N_ChainSync)
outputAt = (Data , output l0 lo N2N_ChainSync)

inputLbl outputLbl : Data → Event√ NetR
inputLbl  x = evl (evLabel Data (input  l0 lo N2N_ChainSync) x)
outputLbl x = evl (evLabel Data (output l0 lo N2N_ChainSync) x)

mdoneAt : AnyTypes (NetT Data)
mdoneAt = (⊤ , mdone l0 lo N2N_ChainSync)
mdoneLbl : Event√ NetR
mdoneLbl = evl (evLabel ⊤ (mdone l0 lo N2N_ChainSync) tt)

-- hidden-τ ExtI indices (top-Par syncs = pair fin (base e); side-hidden τ's =
-- pair fin (pair fin (pair fin (base e))); message events carry `x`, acks `⊤`).
sndmsgIdx rcvmsgIdx sndackIdx rcvackIdx txIdx ackIdx : AnyTypes (ExtI (NetT Data))
sndmsgIdx = _ , pair (fin {n = 2}) (pair (fin {n = 2}) (pair (fin {n = 2}) (base (sndmsg l0 lo N2N_ChainSync))))
rcvmsgIdx = _ , pair (fin {n = 2}) (pair (fin {n = 2}) (pair (fin {n = 2}) (base (rcvmsg l0 lo N2N_ChainSync))))
sndackIdx = _ , pair (fin {n = 2}) (pair (fin {n = 2}) (pair (fin {n = 2}) (base (sndack l0 lo N2N_ChainSync))))
rcvackIdx = _ , pair (fin {n = 2}) (pair (fin {n = 2}) (pair (fin {n = 2}) (base (rcvack l0 lo N2N_ChainSync))))
txIdx     = _ , pair (fin {n = 2}) (base (tx  l0 lo N2N_ChainSync))
ackIdx    = _ , pair (fin {n = 2}) (base (ack l0 lo N2N_ChainSync))

sndmsgVal rcvmsgVal : Data → proj₁ sndmsgIdx
sndmsgVal x = lift fz , (lift fz , (lift (fs fz) , x))
rcvmsgVal x = lift fz , (lift (fs fz) , (lift (fs fz) , x))
txVal : Data → proj₁ txIdx
txVal x = lift (fs fz) , x
sndackVal : proj₁ sndackIdx
sndackVal = lift fz , (lift (fs fz) , (lift (fs fz) , tt))
rcvackVal : proj₁ rcvackIdx
rcvackVal = lift fz , (lift fz , (lift (fs fz) , tt))
ackVal : proj₁ ackIdx
ackVal = lift (fs fz) , tt

------------------------------------------------------------------------
-- Spine step lemmas.  Each is `refl`-certified via an offer-equation
-- where-helper; the four writer steps (sndmsg/tx/rcvmsg/output) discharge
-- the surface `x ≟ x` by `rewrite ≟-diag`.  The ack-stage steps are
-- `x`-free (`refl`).
------------------------------------------------------------------------

-- input?x : net0 ⇒ W1 (reader ⇒ no x≟x)
net0─input─►W1 : ∀ x → net0 ─[ ev (inputLbl x) ]─► W1 x
net0─input─►W1 x = sVis {at = inputAt} refl refl

-- spec input?x : spec0 ⇒ S1
spec0─input─►S1 : ∀ x → spec0 ─[ ev (inputLbl x) ]─► S1 x
spec0─input─►S1 x = sVis {at = inputAt} refl refl

-- sndmsg!x (hidden) : W1 ⇒ W2   (writer)
W1─τ─►W2 : ∀ x → W1 x ─[ τ ]─► W2 x
W1─τ─►W2 x = sTau {i = sndmsgIdx} {a = sndmsgVal x} refl (offer x)
  where offer : ∀ y → τ-of (force (W1 y)) sndmsgIdx (sndmsgVal y) ≡ just (W2 y)
        offer y rewrite ≟-diag y = refl

-- tx!x (hidden) : W2 ⇒ W3   (writer)
W2─τ─►W3 : ∀ x → W2 x ─[ τ ]─► W3 x
W2─τ─►W3 x = sTau {i = txIdx} {a = txVal x} refl (offer x)
  where offer : ∀ y → τ-of (force (W2 y)) txIdx (txVal y) ≡ just (W3 y)
        offer y rewrite ≟-diag y = refl

-- rcvmsg!x (hidden) : W3 ⇒ W4   (writer)
W3─τ─►W4 : ∀ x → W3 x ─[ τ ]─► W4 x
W3─τ─►W4 x = sTau {i = rcvmsgIdx} {a = rcvmsgVal x} refl (offer x)
  where offer : ∀ y → τ-of (force (W3 y)) rcvmsgIdx (rcvmsgVal y) ≡ just (W4 y)
        offer y rewrite ≟-diag y = refl

-- output!x : W4 ⇒ W5   (writer, visible)
W4─output─►W5 : ∀ x → W4 x ─[ ev (outputLbl x) ]─► W5 x
W4─output─►W5 x = sVis {at = outputAt} refl (offer x)
  where offer : ∀ y → vis-of (force (W4 y)) outputAt y ≡ just (W5 y)
        offer y rewrite ≟-diag y = refl

-- sndack (hidden) : W5 ⇒ W6   (x-free)
W5─τ─►W6 : ∀ x → W5 x ─[ τ ]─► W6
W5─τ─►W6 x = sTau {i = sndackIdx} {a = sndackVal} refl refl

-- ack (hidden) : W6 ⇒ W7   (x-free)
W6─τ─►W7 : W6 ─[ τ ]─► W7
W6─τ─►W7 = sTau {i = ackIdx} {a = ackVal} refl refl

-- rcvack (hidden) : W7 ⇒ W8   (x-free; enters the loop-back diamond)
W7─τ─►W8 : W7 ─[ τ ]─► W8
W7─τ─►W8 = sTau {i = rcvackIdx} {a = rcvackVal} refl refl

-- spec output!x : S1 ⇒ S2   (writer)
S1─output─►S2 : ∀ x → S1 x ─[ ev (outputLbl x) ]─► S2
S1─output─►S2 x = sVis {at = outputAt} refl (offer x)
  where offer : ∀ y → vis-of (force (S1 y)) outputAt y ≡ just S2
        offer y rewrite ≟-diag y = refl

-- W4 x offers output!x (both sides do — the observable synchronisation point).
W4-offers-output : ∀ x → is-just (vis-of (force (W4 x)) outputAt x) ≡ true
W4-offers-output x rewrite ≟-diag x = refl

------------------------------------------------------------------------
-- Loop-back diamond.  After W8 the six leaf guards are all `sil (leaf₀)`;
-- they resolve as interleaving τ-branches.  Every state here is `x`-free
-- (the value is already emitted), so the successors extract by `succτ` and
-- the steps hold by `refl` (no `≟-diag` needed).  We enumerate the
-- CANONICAL resolution order (Input, Transmitter, Receiver, Output,
-- SndAck, RcvAck) closing back to `net0`; the full τ-confluence closure
-- (all interleavings) is the same set of leaf-guard subsets and is handled
-- uniformly by `mkDR`'s inversion in M1b.
------------------------------------------------------------------------

-- guard-resolution τ extractor (x-free ⇒ reduces definitionally).
succτ : NetProc → (i : AnyTypes (ExtI (NetT Data))) → proj₁ i → NetProc
succτ p i a with τ-of (force p) i a
... | just t  = t
... | nothing = p

-- Guard τ indices.  Inputs/Outputs sit one Par level shallower (depth 4)
-- than the four drainers (depth 5, inside the extra `∥⇘csMD⇙` Par).  The
-- value tags select: outer-hide own-τ (fz) · top-Par side (Tx=fz, Rx=fs fz)
-- · side-hide own-τ (fz) · side-inner-Par side (Inputs/Outputs=fz, TR/RS=fs
-- fz) · [drainers only] inner Par side (P=fz, Q=fs fz) · leaf `oneτ` (fz).
idx4 idx5 : AnyTypes (ExtI (NetT Data))
idx4 = _ , pair (fin {n = 2}) (pair (fin {n = 2}) (pair (fin {n = 2}) (pair (fin {n = 2}) (fin {n = 1}))))
idx5 = _ , pair (fin {n = 2}) (pair (fin {n = 2}) (pair (fin {n = 2}) (pair (fin {n = 2}) (pair (fin {n = 2}) (fin {n = 1})))))

gInVal gOuVal : proj₁ idx4
gInVal = lift fz , (lift fz     , (lift fz , (lift fz     , lift fz)))     -- Inputs  (Tx P)
gOuVal = lift fz , (lift (fs fz) , (lift fz , (lift fz     , lift fz)))     -- Outputs (Rx P)

gTxVal gRaVal gRcVal gSaVal : proj₁ idx5
gTxVal = lift fz , (lift fz     , (lift fz , (lift (fs fz) , (lift fz     , lift fz))))  -- Transmitter (Tx Q, TR P)
gRaVal = lift fz , (lift fz     , (lift fz , (lift (fs fz) , (lift (fs fz) , lift fz))))  -- RcvAck      (Tx Q, TR Q)
gRcVal = lift fz , (lift (fs fz) , (lift fz , (lift (fs fz) , (lift fz     , lift fz))))  -- Receiver    (Rx Q, RS P)
gSaVal = lift fz , (lift (fs fz) , (lift fz , (lift (fs fz) , (lift (fs fz) , lift fz))))  -- SndAck      (Rx Q, RS Q)

------------------------------------------------------------------------
-- Terminable `mdone` entry (value-free; mdone carries ⊤).
------------------------------------------------------------------------
net0-offers-mdone : is-just (vis-of (force net0) mdoneAt tt) ≡ true
net0-offers-mdone = refl
spec0-offers-mdone : is-just (vis-of (force spec0) mdoneAt tt) ≡ true
spec0-offers-mdone = refl

-- Wd/Sd := the mdone-successors (both sides drive to √).
Wd : NetProc
Wd with vis-of (force net0) mdoneAt tt
... | just t  = t
... | nothing = net0
net0─mdone─►Wd : net0 ─[ ev mdoneLbl ]─► Wd
net0─mdone─►Wd = sVis {at = mdoneAt} refl refl

Sd : NetProc
Sd with vis-of (force spec0) mdoneAt tt
... | just t  = t
... | nothing = spec0
spec0─mdone─►Sd : spec0 ─[ ev mdoneLbl ]─► Sd
spec0─mdone─►Sd = sVis {at = mdoneAt} refl refl

------------------------------------------------------------------------
-- M2: the network `mdone`-drain to √.  After `mdone`, the two leaves are
-- `ret` and the four drainers are guard-`sil`s; because a `ret` operand is
-- transparent to `Par` (`par-hTauR`/`par-hTauL` pass through with no index
-- layer), the drain collapses in FOUR τ's to `ret tt`, then `√` → deadlock.
-- Enumerated as extracted terms + `refl`-certified steps (x-free).
------------------------------------------------------------------------

-- drain τ-indices (shallower than the loop-back diamond: the ret leaves add
-- no Par layer).  Transmitter first (depth 4), then the collapsing sils.
idxD4 : AnyTypes (ExtI (NetT Data))
idxD4 = _ , pair (fin {n = 2}) (pair (fin {n = 2}) (pair (fin {n = 2}) (pair (fin {n = 2}) (fin {n = 1}))))
idxD3 : AnyTypes (ExtI (NetT Data))
idxD3 = _ , pair (fin {n = 2}) (pair (fin {n = 2}) (pair (fin {n = 2}) (fin {n = 1})))
idxD2 : AnyTypes (ExtI (NetT Data))
idxD2 = _ , pair (fin {n = 2}) (pair (fin {n = 2}) (fin {n = 1}))

WdD1 : NetProc     -- Transmitter drained
WdD1 = succτ Wd idxD4 (lift fz , (lift fz , (lift fz , (lift fz , lift fz))))
Wd─τ─►WdD1 : Wd ─[ τ ]─► WdD1
Wd─τ─►WdD1 = sTau {i = idxD4} {a = lift fz , (lift fz , (lift fz , (lift fz , lift fz)))} refl refl

WdD2 : NetProc     -- Tx side collapsed (RcvAck drained)
WdD2 = succτ WdD1 idxD2 (lift fz , (lift fz , lift fz))
WdD1─τ─►WdD2 : WdD1 ─[ τ ]─► WdD2
WdD1─τ─►WdD2 = sTau {i = idxD2} {a = lift fz , (lift fz , lift fz)} refl refl

WdD3 : NetProc     -- Receiver drained
WdD3 = succτ WdD2 idxD3 (lift fz , (lift fz , (lift fz , lift fz)))
WdD2─τ─►WdD3 : WdD2 ─[ τ ]─► WdD3
WdD2─τ─►WdD3 = sTau {i = idxD3} {a = lift fz , (lift fz , (lift fz , lift fz))} refl refl

-- WdD3 is now a top-level sil (Rx side collapsed): the last guard (SndAck).
WdD4 : NetProc
WdD4 with force WdD3
... | sil t = t
... | _     = WdD3
WdD3─τ─►WdD4 : WdD3 ─[ τ ]─► WdD4
WdD3─τ─►WdD4 = sSil refl

-- fully drained: WdD4 = ret tt.
WdD4-ret : force WdD4 ≡ ret Poly.tt
WdD4-ret = refl

-- the network mdone-drain run to √  (Wd ─τ*→ WdD4 ─√→ deadlock).
drainWd : Wd ─[τ*]─► WdD4
drainWd = τ*-step Wd─τ─►WdD1 (τ*-step WdD1─τ─►WdD2 (τ*-step WdD2─τ─►WdD3 (τ*-step WdD3─τ─►WdD4 τ*-refl)))

Wd═√ : Wd ═[ ev (√ (Poly.tt {0ℓ})) ]═► deadlock
Wd═√ = wev drainWd (sRet WdD4-ret) τ*-refl

-- spec √: Sd = ret tt ─√→ deadlock.
Sd-force : force Sd ≡ ret (Poly.tt {0ℓ})
Sd-force = refl
Sd═√ : Sd ═[ ev (√ (Poly.tt {0ℓ})) ]═► deadlock
Sd═√ = wev τ*-refl (sRet Sd-force) τ*-refl


------------------------------------------------------------------------
-- Canonical loop-back diamond states + steps (x-free; refl).  After W8 the
-- six leaf guards are all `sil (leaf₀)`; they resolve as interleaving
-- τ-branches.  Every state here is `x`-free, so the successors extract by
-- `succτ` and the steps hold by `refl`.  Canonical resolution order
-- (Inputs, Transmitter, RcvAck, Outputs, Receiver, SndAck) closes back to
-- `net0`; the full τ-confluence closure (all interleavings = the same
-- leaf-guard subsets) is handled uniformly by `mkDR`'s inversion in M1b.
------------------------------------------------------------------------
G1 : NetProc                     -- Inputs guard resolved
G1 = succτ W8 idx4 gInVal
W8─τ─►G1 : W8 ─[ τ ]─► G1
W8─τ─►G1 = sTau {i = idx4} {a = gInVal} refl refl

G2 : NetProc                     -- + Transmitter
G2 = succτ G1 idx5 gTxVal
G1─τ─►G2 : G1 ─[ τ ]─► G2
G1─τ─►G2 = sTau {i = idx5} {a = gTxVal} refl refl

G3 : NetProc                     -- + RcvAck
G3 = succτ G2 idx5 gRaVal
G2─τ─►G3 : G2 ─[ τ ]─► G3
G2─τ─►G3 = sTau {i = idx5} {a = gRaVal} refl refl

G4 : NetProc                     -- + Outputs
G4 = succτ G3 idx4 gOuVal
G3─τ─►G4 : G3 ─[ τ ]─► G4
G3─τ─►G4 = sTau {i = idx4} {a = gOuVal} refl refl

G5 : NetProc                     -- + Receiver
G5 = succτ G4 idx5 gRcVal
G4─τ─►G5 : G4 ─[ τ ]─► G5
G4─τ─►G5 = sTau {i = idx5} {a = gRcVal} refl refl

-- last guard (SndAck) resolved ⇒ back to the idle composite.
G6 : NetProc
G6 = succτ G5 idx5 gSaVal
G5─τ─►G6 : G5 ─[ τ ]─► G6
G5─τ─►G6 = sTau {i = idx5} {a = gSaVal} refl refl

-- the loop-back diamond closes cleanly: all six guards resolved ⇒ `net0`.
diamond-closes : G6 ≡ net0
diamond-closes = refl

------------------------------------------------------------------------
-- The bisimulation carrier `RState W S`  (network config `W` ↔ spec state
-- `S`).  Every index is an explicit, reducible generic-Data state.
------------------------------------------------------------------------
data RState : NetProc → NetProc → Set₁ where
  -- both idle (initial pair): both offer input / mdone.
  rsIdle  : RState net0 spec0
  -- value x received; mux filling ↔ spec offering output.
  rsFill1 : ∀ x → RState (W1 x) (S1 x)
  rsFill2 : ∀ x → RState (W2 x) (S1 x)
  rsFill3 : ∀ x → RState (W3 x) (S1 x)
  -- value x past rcvmsg: net now offers output ↔ spec offers output.
  rsHold  : ∀ x → RState (W4 x) (S1 x)
  -- output emitted; ack settling ↔ spec back-loop guard.
  rsDrain5 : ∀ x → RState (W5 x) S2
  rsDrain6 : RState W6 S2
  rsDrain7 : RState W7 S2
  -- entering the loop-back diamond ↔ spec back-loop guard.
  rsDrain8 : RState W8 S2
  -- loop-back diamond (guards resolving; spec settled to idle-equivalent).
  rsG1 : RState G1 S2
  rsG2 : RState G2 S2
  rsG3 : RState G3 S2
  rsG4 : RState G4 S2
  rsG5 : RState G5 S2
  -- terminable: mdone fired at idle; both sides draining to √.
  rsMdone : RState Wd Sd
  -- terminal: both sides have drained to √/deadlock.
  rsDL : RState deadlock deadlock


------------------------------------------------------------------------
-- The DR-bisimulation builder `mkDR` and the failures-divergences theorem.
--
-- `mkDR`/`mkDRˢ` are the guarded corecursive builders (each RState config
-- discharges the four DRbisim fields, recursing into the successor RState
-- under the coinductive fields).  They delegate the per-step CORRESPONDENCE
-- to four inversion helpers (`sim-{fwd,bwd}-{ev,tau}`) and the DIVERGENCE
-- fields to two non-divergence lemmas (`nd-net`, `nd-spec`): the single
-- instance has no infinite τ-cycle (every buffered value progresses to
-- output; the diamond and mdone terminate), so both sides converge.
--
-- STATUS (M1b, this increment): the mkDR ASSEMBLY + the exact theorem
-- typecheck; the six delegated lemmas below are the residual inversion /
-- divergence content and are TEMPORARILY POSTULATED (see fd-m1b-report.md).
-- They are the M1b-completion targets; the recursion structure, guardedness,
-- orientation, and theorem type are all real and checked.
------------------------------------------------------------------------

-- ── residual inversion + divergence lemmas ────────────────────────────────
-- STILL POSTULATED (bulk / measure — next checkpoints): the network-side
-- inversion (`sim-fwd-*`) and network non-divergence (`nd-net`).
postulate
  sim-fwd-ev  : ∀ {W S} → RState W S → ∀ {l : Event√ NetR} {W′}
              → W ─[ ev l ]─► W′ → Σ[ S′ ∈ NetProc ] (S ═[ ev l ]═► S′ × RState W′ S′)
  sim-fwd-tau : ∀ {W S} → RState W S → ∀ {W′}
              → W ─[ τ ]─► W′ → Σ[ S′ ∈ NetProc ] (S ═[ τ ]═► S′ × RState W′ S′)
  -- network non-divergence (needs a per-state MAcc/measure argument).
  nd-net  : ∀ {W S} → RState W S → ¬ Diverges W

------------------------------------------------------------------------
-- DISCHARGED: `nd-spec` (spec non-divergence).
-- Technique from `NetworkRefinement.¬Diverges-CopySpec` (:396): the spec is
-- τ-stable ⇒ refute `Diverges` by case-splitting its first `step`.  ADAPTATION
-- for our `iter`-built `CopyT`: `S2` is NOT stable — it carries the single
-- loop-back guard-`sil` (`force S2 = sil spec0`); so `S2` makes exactly one τ
-- (to the stable `spec0`) and still cannot diverge.
------------------------------------------------------------------------

-- spec0 / S1 are τ-stable (everywhere-`nothing` composite τc): the 8 raw
-- `sTau` index shapes are all refuted (`CopySpec-stable` pattern).
spec0-noτ : ∀ {t} → spec0 ─[ τ ]─► t → ⊥
spec0-noτ (sSil ())
spec0-noτ (sTau {i = _ , fin}                 refl ())
spec0-noτ (sTau {i = _ , base _}              refl ())
spec0-noτ (sTau {i = _ , pair fin (base _)}   refl ())
spec0-noτ (sTau {i = _ , pair fin fin}        refl ())
spec0-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
spec0-noτ (sTau {i = _ , pair (base _) _}     refl ())
spec0-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

S1-noτ : ∀ {x t} → S1 x ─[ τ ]─► t → ⊥
S1-noτ (sSil ())
S1-noτ (sTau {i = _ , fin}                 refl ())
S1-noτ (sTau {i = _ , base _}              refl ())
S1-noτ (sTau {i = _ , pair fin (base _)}   refl ())
S1-noτ (sTau {i = _ , pair fin fin}        refl ())
S1-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
S1-noτ (sTau {i = _ , pair (base _) _}     refl ())
S1-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

-- Sd = ret tt (terminal √): no τ at all.
Sd-noτ : ∀ {t} → Sd ─[ τ ]─► t → ⊥
Sd-noτ (sSil ())
Sd-noτ (sTau () _)

-- a τ-stable state cannot diverge.
¬Div-stable : ∀ {t : NetProc} → (∀ {u} → t ─[ τ ]─► u → ⊥) → ¬ Diverges t
¬Div-stable noτ d = noτ (d .Diverges.step)

¬Div-spec0 : ¬ Diverges spec0
¬Div-spec0 = ¬Div-stable spec0-noτ
¬Div-S1 : ∀ {x} → ¬ Diverges (S1 x)
¬Div-S1 = ¬Div-stable S1-noτ
¬Div-Sd : ¬ Diverges Sd
¬Div-Sd = ¬Div-stable Sd-noτ

-- S2 forces to a top-level guard-`sil` to spec0.  (Matching `sSil refl`
-- directly on the composite leaves the unifier stuck on the nested `Par`
-- force, so we invert through this reduction lemma instead.)
S2-force : force S2 ≡ sil spec0
S2-force = refl

silINJ : ∀ {a b : NetProc} → (sil {E = NetT Data} {I = ExtI (NetT Data)} a) ≡ sil b → a ≡ b
silINJ refl = refl

silNOTreact : ∀ {a}
            {v : (at : AnyTypes (NetT Data)) → ContinueType at (Maybe NetProc)}
            {τc : (i : AnyTypes (ExtI (NetT Data))) → ContinueType i (Maybe NetProc)}
          → sil {E = NetT Data} {I = ExtI (NetT Data)} a ≡ react v τc → ⊥
silNOTreact ()

-- S2's only τ lands in spec0.
S2-τ-inv : ∀ {t} → S2 ─[ τ ]─► t → t ≡ spec0
S2-τ-inv (sSil eq)   = silINJ (trans (sym eq) S2-force)
S2-τ-inv (sTau eq _) = ⊥-elim (silNOTreact (trans (sym S2-force) eq))

-- S2 makes one guard-τ to spec0, which is stable ⇒ still no divergence.
¬Div-S2 : ¬ Diverges S2
¬Div-S2 d = ¬Div-spec0 (subst Diverges (S2-τ-inv (d .Diverges.step)) (d .Diverges.rest))

nd-spec : ∀ {W S} → RState W S → ¬ Diverges S
nd-spec rsIdle      = ¬Div-spec0
nd-spec (rsFill1 x) = ¬Div-S1
nd-spec (rsFill2 x) = ¬Div-S1
nd-spec (rsFill3 x) = ¬Div-S1
nd-spec (rsHold  x) = ¬Div-S1
nd-spec (rsDrain5 x) = ¬Div-S2
nd-spec rsDrain6    = ¬Div-S2
nd-spec rsDrain7    = ¬Div-S2
nd-spec rsDrain8    = ¬Div-S2
nd-spec rsG1        = ¬Div-S2
nd-spec rsG2        = ¬Div-S2
nd-spec rsG3        = ¬Div-S2
nd-spec rsG4        = ¬Div-S2
nd-spec rsG5        = ¬Div-S2
nd-spec rsMdone     = ¬Div-Sd
nd-spec rsDL        = deadlock-converges

------------------------------------------------------------------------
-- DISCHARGED: `sim-bwd-tau` (spec-side τ inversion).
-- The spec has exactly ONE τ anywhere: `S2`'s loop-back guard `S2 ─τ→ spec0`.
-- The network matches it WEAKLY by draining its current ack/diamond state all
-- the way to `net0` (a τ* run built from the existing `─[_]─►` step lemmas),
-- landing in the sibling `rsIdle : RState net0 spec0`.  All other spec states
-- are τ-stable ⇒ the τ is refuted.
------------------------------------------------------------------------

-- network τ* drain runs to net0 (the loop-back closes; G6 ≡ net0).
drainG5 : G5 ─[τ*]─► net0
drainG5 = τ*-step G5─τ─►G6 τ*-refl
drainG4 : G4 ─[τ*]─► net0
drainG4 = τ*-step G4─τ─►G5 drainG5
drainG3 : G3 ─[τ*]─► net0
drainG3 = τ*-step G3─τ─►G4 drainG4
drainG2 : G2 ─[τ*]─► net0
drainG2 = τ*-step G2─τ─►G3 drainG3
drainG1 : G1 ─[τ*]─► net0
drainG1 = τ*-step G1─τ─►G2 drainG2
drainW8 : W8 ─[τ*]─► net0
drainW8 = τ*-step W8─τ─►G1 drainG1
drainW7 : W7 ─[τ*]─► net0
drainW7 = τ*-step W7─τ─►W8 drainW8
drainW6 : W6 ─[τ*]─► net0
drainW6 = τ*-step W6─τ─►W7 drainW7
drainW5 : ∀ x → W5 x ─[τ*]─► net0
drainW5 x = τ*-step (W5─τ─►W6 x) drainW6

sim-bwd-tau : ∀ {W S} → RState W S → ∀ {S′}
            → S ─[ τ ]─► S′ → Σ[ W′ ∈ NetProc ] (W ═[ τ ]═► W′ × RState W′ S′)
sim-bwd-tau rsIdle      st = ⊥-elim (spec0-noτ st)
sim-bwd-tau (rsFill1 x) st = ⊥-elim (S1-noτ st)
sim-bwd-tau (rsFill2 x) st = ⊥-elim (S1-noτ st)
sim-bwd-tau (rsFill3 x) st = ⊥-elim (S1-noτ st)
sim-bwd-tau (rsHold  x) st = ⊥-elim (S1-noτ st)
sim-bwd-tau rsMdone     st = ⊥-elim (Sd-noτ st)
sim-bwd-tau (rsDrain5 x) st with S2-τ-inv st
... | refl = net0 , wτ (drainW5 x) , rsIdle
sim-bwd-tau rsDrain6 st with S2-τ-inv st
... | refl = net0 , wτ drainW6 , rsIdle
sim-bwd-tau rsDrain7 st with S2-τ-inv st
... | refl = net0 , wτ drainW7 , rsIdle
sim-bwd-tau rsDrain8 st with S2-τ-inv st
... | refl = net0 , wτ drainW8 , rsIdle
sim-bwd-tau rsG1 st with S2-τ-inv st
... | refl = net0 , wτ drainG1 , rsIdle
sim-bwd-tau rsG2 st with S2-τ-inv st
... | refl = net0 , wτ drainG2 , rsIdle
sim-bwd-tau rsG3 st with S2-τ-inv st
... | refl = net0 , wτ drainG3 , rsIdle
sim-bwd-tau rsG4 st with S2-τ-inv st
... | refl = net0 , wτ drainG4 , rsIdle
sim-bwd-tau rsG5 st with S2-τ-inv st
... | refl = net0 , wτ drainG5 , rsIdle
sim-bwd-tau rsDL    st = ⊥-elim (deadlock-no-τ st)

------------------------------------------------------------------------
-- DISCHARGED: `sim-bwd-ev` (spec-side visible inversion).
-- The spec offers exactly: input?a / mdone (at spec0), output!a (at S1),
-- and √ (at Sd = ret tt); S2/deadlock offer nothing.  Each maps to the
-- matching network weak step (built from the existing + M2 step lemmas)
-- and the sibling RState.
------------------------------------------------------------------------

-- network weak visible runs used by the matches.
net0═input : ∀ x → net0 ═[ ev (inputLbl x) ]═► W1 x
net0═input x = wev τ*-refl (net0─input─►W1 x) τ*-refl
net0═mdone : net0 ═[ ev mdoneLbl ]═► Wd
net0═mdone = wev τ*-refl net0─mdone─►Wd τ*-refl
W1═output : ∀ x → W1 x ═[ ev (outputLbl x) ]═► W5 x
W1═output x = wev (τ*-step (W1─τ─►W2 x) (τ*-step (W2─τ─►W3 x) (τ*-step (W3─τ─►W4 x) τ*-refl)))
                  (W4─output─►W5 x) τ*-refl
W2═output : ∀ x → W2 x ═[ ev (outputLbl x) ]═► W5 x
W2═output x = wev (τ*-step (W2─τ─►W3 x) (τ*-step (W3─τ─►W4 x) τ*-refl)) (W4─output─►W5 x) τ*-refl
W3═output : ∀ x → W3 x ═[ ev (outputLbl x) ]═► W5 x
W3═output x = wev (τ*-step (W3─τ─►W4 x) τ*-refl) (W4─output─►W5 x) τ*-refl
W4═output : ∀ x → W4 x ═[ ev (outputLbl x) ]═► W5 x
W4═output x = wev τ*-refl (W4─output─►W5 x) τ*-refl

-- S2 / deadlock offer nothing visible: refute a visible / √ step.
silNOTret : ∀ {a : NetProc} {x : NetR} → sil a ≡ ret x → ⊥
silNOTret ()

retNOTreact : ∀ {r : NetR}
              {v : (at : AnyTypes (NetT Data)) → ContinueType at (Maybe NetProc)}
              {τc : (i : AnyTypes (ExtI (NetT Data))) → ContinueType i (Maybe NetProc)}
            → ret {E = NetT Data} {I = ExtI (NetT Data)} r ≡ react v τc → ⊥
retNOTreact ()

-- spec0 offers input?a → S1 a and mdone → Sd; refute all else.
spec0-bwd-ev : ∀ {l : Event√ NetR} {S′} → spec0 ─[ ev l ]─► S′
             → Σ[ W′ ∈ NetProc ] (net0 ═[ ev l ]═► W′ × RState W′ S′)
spec0-bwd-ev (sVis {at = _ , input fz lo N2N_ChainSync} refl refl) = _ , net0═input _ , rsFill1 _
spec0-bwd-ev (sVis {at = _ , input fz lo N2N_BlockFetch} refl ())
spec0-bwd-ev (sVis {at = _ , input fz lo N2N_TxSubmission} refl ())
spec0-bwd-ev (sVis {at = _ , input fz lo N2N_KeepAlive} refl ())
spec0-bwd-ev (sVis {at = _ , input fz lo N2N_LeiosNotify} refl ())
spec0-bwd-ev (sVis {at = _ , input fz lo N2N_LeiosFetch} refl ())
spec0-bwd-ev (sVis {at = _ , input fz hi i′} refl ())
spec0-bwd-ev (sVis {at = _ , mdone fz lo N2N_ChainSync} refl refl) = _ , net0═mdone , rsMdone
spec0-bwd-ev (sVis {at = _ , mdone fz lo N2N_BlockFetch} refl ())
spec0-bwd-ev (sVis {at = _ , mdone fz lo N2N_TxSubmission} refl ())
spec0-bwd-ev (sVis {at = _ , mdone fz lo N2N_KeepAlive} refl ())
spec0-bwd-ev (sVis {at = _ , mdone fz lo N2N_LeiosNotify} refl ())
spec0-bwd-ev (sVis {at = _ , mdone fz lo N2N_LeiosFetch} refl ())
spec0-bwd-ev (sVis {at = _ , mdone fz hi i′} refl ())
spec0-bwd-ev (sVis {at = _ , output l′ d′ i′} refl ())
spec0-bwd-ev (sVis {at = _ , sndmsg l′ d′ i′} refl ())
spec0-bwd-ev (sVis {at = _ , rcvmsg l′ d′ i′} refl ())
spec0-bwd-ev (sVis {at = _ , tx l′ d′ i′} refl ())
spec0-bwd-ev (sVis {at = _ , sndack l′ d′ i′} refl ())
spec0-bwd-ev (sVis {at = _ , rcvack l′ d′ i′} refl ())
spec0-bwd-ev (sVis {at = _ , ack l′ d′ i′} refl ())
spec0-bwd-ev (sRet ())

-- S1 x offers output!x → S2; refute all else (generic-Data value via a′≟x).
S1-out-inv : ∀ {x} {l : Event√ NetR} {S′} → S1 x ─[ ev l ]─► S′ → (l ≡ outputLbl x) × (S′ ≡ S2)
S1-out-inv {x} (sVis {at = _ , output fz lo N2N_ChainSync} {a = a′} refl br) with a′ ≟ x | br
... | yes refl | refl = refl , refl
... | no ¬p | ()
S1-out-inv (sVis {at = _ , output fz lo N2N_BlockFetch} refl ())
S1-out-inv (sVis {at = _ , output fz lo N2N_TxSubmission} refl ())
S1-out-inv (sVis {at = _ , output fz lo N2N_KeepAlive} refl ())
S1-out-inv (sVis {at = _ , output fz lo N2N_LeiosNotify} refl ())
S1-out-inv (sVis {at = _ , output fz lo N2N_LeiosFetch} refl ())
S1-out-inv (sVis {at = _ , output fz hi i′} refl ())
S1-out-inv (sVis {at = _ , input l′ d′ i′} refl ())
S1-out-inv (sVis {at = _ , mdone l′ d′ i′} refl ())
S1-out-inv (sVis {at = _ , sndmsg l′ d′ i′} refl ())
S1-out-inv (sVis {at = _ , rcvmsg l′ d′ i′} refl ())
S1-out-inv (sVis {at = _ , tx l′ d′ i′} refl ())
S1-out-inv (sVis {at = _ , sndack l′ d′ i′} refl ())
S1-out-inv (sVis {at = _ , rcvack l′ d′ i′} refl ())
S1-out-inv (sVis {at = _ , ack l′ d′ i′} refl ())
S1-out-inv (sRet ())

-- S2 = sil: offers nothing visible.
S2-no-ev : ∀ {l : Event√ NetR} {S′} → S2 ─[ ev l ]─► S′ → ⊥
S2-no-ev (sVis eq _) = silNOTreact (trans (sym S2-force) eq)
S2-no-ev (sRet eq)   = silNOTret (trans (sym S2-force) eq)

-- the discharged spec-side visible inversion.
sim-bwd-ev : ∀ {W S} → RState W S → ∀ {l : Event√ NetR} {S′}
           → S ─[ ev l ]─► S′ → Σ[ W′ ∈ NetProc ] (W ═[ ev l ]═► W′ × RState W′ S′)
sim-bwd-ev rsIdle st = spec0-bwd-ev st
sim-bwd-ev (rsFill1 x) st with S1-out-inv st
... | refl , refl = _ , W1═output x , rsDrain5 x
sim-bwd-ev (rsFill2 x) st with S1-out-inv st
... | refl , refl = _ , W2═output x , rsDrain5 x
sim-bwd-ev (rsFill3 x) st with S1-out-inv st
... | refl , refl = _ , W3═output x , rsDrain5 x
sim-bwd-ev (rsHold  x) st with S1-out-inv st
... | refl , refl = _ , W4═output x , rsDrain5 x
sim-bwd-ev (rsDrain5 x) st = ⊥-elim (S2-no-ev st)
sim-bwd-ev rsDrain6 st = ⊥-elim (S2-no-ev st)
sim-bwd-ev rsDrain7 st = ⊥-elim (S2-no-ev st)
sim-bwd-ev rsDrain8 st = ⊥-elim (S2-no-ev st)
sim-bwd-ev rsG1 st = ⊥-elim (S2-no-ev st)
sim-bwd-ev rsG2 st = ⊥-elim (S2-no-ev st)
sim-bwd-ev rsG3 st = ⊥-elim (S2-no-ev st)
sim-bwd-ev rsG4 st = ⊥-elim (S2-no-ev st)
sim-bwd-ev rsG5 st = ⊥-elim (S2-no-ev st)
sim-bwd-ev rsMdone (sVis eq _) = ⊥-elim (retNOTreact (trans (sym Sd-force) eq))
sim-bwd-ev rsMdone (sRet refl) = _ , Wd═√ , rsDL
sim-bwd-ev rsDL (sVis refl ())
sim-bwd-ev rsDL (sRet ())

-- ── the guarded builders (REAL: assembly, guardedness, orientation) ───────
mkDR  : ∀ {W S} → RState W S → DRbisim NetR W S
mkDRˢ : ∀ {W S} → RState W S → DRbisim NetR S W

mkDR r .fwd .on-ev  st = let (S′ , ws , r′) = sim-fwd-ev  r st in S′ , ws , mkDR  r′
mkDR r .fwd .on-tau st = let (S′ , ws , r′) = sim-fwd-tau r st in S′ , ws , mkDR  r′
mkDR r .bwd .on-ev  st = let (W′ , ws , r′) = sim-bwd-ev  r st in W′ , ws , mkDRˢ r′
mkDR r .bwd .on-tau st = let (W′ , ws , r′) = sim-bwd-tau r st in W′ , ws , mkDRˢ r′
mkDR r .div→ d = ⊥-elim (nd-net  r d)
mkDR r .div← d = ⊥-elim (nd-spec r d)

mkDRˢ r .fwd .on-ev  st = let (W′ , ws , r′) = sim-bwd-ev  r st in W′ , ws , mkDRˢ r′
mkDRˢ r .fwd .on-tau st = let (W′ , ws , r′) = sim-bwd-tau r st in W′ , ws , mkDRˢ r′
mkDRˢ r .bwd .on-ev  st = let (S′ , ws , r′) = sim-fwd-ev  r st in S′ , ws , mkDR  r′
mkDRˢ r .bwd .on-tau st = let (S′ , ws , r′) = sim-fwd-tau r st in S′ , ws , mkDR  r′
mkDRˢ r .div→ d = ⊥-elim (nd-spec r d)
mkDRˢ r .div← d = ⊥-elim (nd-net  r d)

------------------------------------------------------------------------
-- M3 THEOREM.  The terminable copy spec is failures-divergences equivalent
-- to the terminable multiplexer, single instance, GENERIC Data.
------------------------------------------------------------------------
CopySpecT-≈FD-NetworkT : CopySpecT ≈FD NetworkT
CopySpecT-≈FD-NetworkT = drbisim→≈FD (drbisim-sym (mkDR rsIdle))

