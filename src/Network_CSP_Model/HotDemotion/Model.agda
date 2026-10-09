{-# OPTIONS --guardedness #-}

-- Hot→warm demotion (DESIGN.md §3–§4): one demotion of one outbound peer; each hot
-- mini-protocol is reduced to its behaviour after the governor writes Terminate.
-- Citations: RESEARCH.md (ouroboros-network 4b3ab76, ouroboros-consensus 27fa649ff).
module HotDemotion.Model where

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

-- the five hot mini-protocols (RESEARCH.md §1)
data Proto : Set where
  cs bf tx lf ln : Proto

-- LeiosNotify before / after ouroboros-consensus PR 2344
data Variant : Set where
  pre post : Variant

-- governor actions: start demotion (write Terminate, PSA:997-999), all hot returned (PSA:1007-1014),
-- deactivate timeout (PSA:1025-1033), peer ends Cold (AP:988-1017)
data GAct : Set where
  demote warm tmo cold : GAct

-- environment: a Praos header arrives, the remote sends a blocking MsgRequestTxIds, a Leios reply arrives
data EnvAct : Set where
  block txReq lnReply : EnvAct

-- protocol-internal progress, kept visible (no τ in the model): BlockFetch finishes its in-flight batch;
-- post-PR LeiosNotify sends MsgQuit; the remote LeiosNotify server answers it (MsgCanceled…, MsgDone)
data IntAct : Set where
  bfDrain lnQuit lnQuitDone : IntAct

-- the four channels; rtn p = hot protocol p returned (the governor's awaitAllResults, PSA:409-423)
data Ev : Set → Set where
  gov : Ev GAct
  rtn : Ev Proto
  env : Ev EnvAct
  int : Ev IntAct

-- decidable equality on the existential event index
Ev-≟ : (x y : AnyTypes Ev) → Dec (x ≡ y)
Ev-≟ (_ , gov) (_ , gov) = yes refl
Ev-≟ (_ , rtn) (_ , rtn) = yes refl
Ev-≟ (_ , env) (_ , env) = yes refl
Ev-≟ (_ , int) (_ , int) = yes refl
Ev-≟ (_ , gov) (_ , rtn) = no λ ()
Ev-≟ (_ , gov) (_ , env) = no λ ()
Ev-≟ (_ , gov) (_ , int) = no λ ()
Ev-≟ (_ , rtn) (_ , gov) = no λ ()
Ev-≟ (_ , rtn) (_ , env) = no λ ()
Ev-≟ (_ , rtn) (_ , int) = no λ ()
Ev-≟ (_ , env) (_ , gov) = no λ ()
Ev-≟ (_ , env) (_ , rtn) = no λ ()
Ev-≟ (_ , env) (_ , int) = no λ ()
Ev-≟ (_ , int) (_ , gov) = no λ ()
Ev-≟ (_ , int) (_ , rtn) = no λ ()
Ev-≟ (_ , int) (_ , env) = no λ ()

open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import CSP.Operators Ev-≟

-- return type of every process
U : Set
U = ⊤ {0ℓ}

-- the process type
Proc : Set₁
Proc = PTree Ev (ExtI Ev) U

-- a hot protocol's phase: running (before Terminate), waiting for an env event, needing an internal
-- step, post-PR LeiosNotify waiting for the server's answer to MsgQuit, ready to return, returned
data PSt : Set where
  running waitEnv needInt quitSent ready fin : PSt

-- governor phase: hot, awaiting all hot results under the timeout, Warm, timed out, Cold
data GPh : Set where
  hot awaiting warmD timedOut coldD : GPh

-- a model variant: LeiosNotify version, which env events the environment offers, whether the timeout exists
record Mode : Set where
  constructor mode
  field
    var    : Variant
    blocks : Bool
    txReqs : Bool
    lnLoad : Bool
    timer  : Bool
open Mode public

-- the model state
record St : Set where
  constructor mkSt
  field
    gph : GPh
    ps  : Proto → PSt
open St public

-- initial state: hot, every protocol running
st₀ : St
st₀ = mkSt hot (λ _ → running)

-- each protocol's phase right after Terminate (DESIGN.md §4 table)
afterTerm : Variant → Proto → PSt
afterTerm _    cs = waitEnv     -- ChainSync in StMustReply waits for a header
afterTerm _    bf = needInt     -- BlockFetch drains in-flight batches
afterTerm _    tx = waitEnv     -- TxSubmission2 outbound waits in StIdle for a blocking request
afterTerm _    lf = ready       -- LeiosFetch with nothing in flight stops at once
afterTerm pre  ln = waitEnv     -- pre-PR: owes replies; only a Leios reply lets it proceed
afterTerm post ln = needInt     -- post-PR: sends MsgQuit

-- set one protocol's phase
setP : Proto → PSt → (Proto → PSt) → (Proto → PSt)
setP p x f q = case (p , q) of λ where
  (cs , cs) → x ; (bf , bf) → x ; (tx , tx) → x ; (lf , lf) → x ; (ln , ln) → x
  _         → f q

-- one phase is fin
isFin : PSt → Bool
isFin fin = true
isFin _   = false

-- every hot protocol has returned
allFin : St → Bool
allFin s = isFin (ps s cs) ∧ isFin (ps s bf) ∧ isFin (ps s tx) ∧ isFin (ps s lf) ∧ isFin (ps s ln)

-- which protocol an env event serves
envFor : EnvAct → Proto
envFor block   = cs
envFor txReq   = tx
envFor lnReply = ln

-- the mode's flag for an env event
envOn : Mode → EnvAct → Bool
envOn m block   = blocks m
envOn m txReq   = txReqs m
envOn m lnReply = lnLoad m

-- the protocol an internal action belongs to, the phase it needs and the phase it yields
intMove : Variant → IntAct → Maybe (Proto × PSt × PSt)
intMove _    bfDrain    = just (bf , needInt , ready)
intMove post lnQuit     = just (ln , needInt , quitSent)
intMove post lnQuitDone = just (ln , quitSent , ready)
intMove pre  lnQuit     = nothing
intMove pre  lnQuitDone = nothing

-- phase equality as a Bool
eqP : PSt → PSt → Bool
eqP running running   = true
eqP waitEnv waitEnv   = true
eqP needInt needInt   = true
eqP quitSent quitSent = true
eqP ready ready       = true
eqP fin fin           = true
eqP _ _               = false

-- succeed with s′ when the current phase is the expected one
stepIf : PSt → PSt → St → Maybe St
stepIf x y s′ = if eqP x y then just s′ else nothing

-- one move of the whole system (governor and hot protocols synchronise on rtn; DESIGN.md §4's ∥ is this product)
sstep : (at : AnyTypes Ev) → proj₁ at → Mode → St → Maybe St
sstep (_ , gov) demote m (mkSt hot f)        = just (mkSt awaiting (afterTerm (var m)))
sstep (_ , gov) warm   m s@(mkSt awaiting f) = if allFin s then just (mkSt warmD f) else nothing
sstep (_ , gov) tmo    m (mkSt awaiting f)   = if timer m then just (mkSt timedOut f) else nothing
sstep (_ , gov) cold   m (mkSt timedOut f)   = just (mkSt coldD f)
sstep (_ , gov) _      _ _                   = nothing
sstep (_ , rtn) p      m (mkSt awaiting f)   = stepIf (f p) ready (mkSt awaiting (setP p fin f))
sstep (_ , rtn) _      _ _                   = nothing
sstep (_ , env) e      m (mkSt awaiting f)   =
  if envOn m e then stepIf (f (envFor e)) waitEnv (mkSt awaiting (setP (envFor e) ready f)) else nothing
sstep (_ , env) _      _ _                   = nothing
sstep (_ , int) a      m (mkSt awaiting f)   = case intMove (var m) a of λ where
  (just (p , need , yield)) → stepIf (f p) need (mkSt awaiting (setP p yield f))
  nothing                   → nothing
sstep (_ , int) _      _ _                   = nothing

-- the run is over: Warm or Cold reached
final : St → Bool
final (mkSt warmD _) = true
final (mkSt coldD _) = true
final _              = false

-- the system at a state, generated from sstep; it terminates (√) once final
SysAt : Mode → St → Proc
force (SysAt m s) with final s
... | true  = ret tt
... | false = react
  (λ where (X , ch) a → case sstep (X , ch) a m s of λ where
                          (just s′) → just (SysAt m s′)
                          nothing   → nothing)
  ∅t

-- the system under a mode
Sys : Mode → Proc
Sys m = SysAt m st₀

-- trace letters
lbl : (at : AnyTypes Ev) → proj₁ at → Event√ U
lbl (X , ch) a = evl (evLabel X ch a)

-- governor letter
GV : GAct → Event√ U
GV = lbl (GAct , gov)

-- return letter
RT : Proto → Event√ U
RT = lbl (Proto , rtn)

-- environment letter
EV : EnvAct → Event√ U
EV = lbl (EnvAct , env)

-- internal-progress letter
IN : IntAct → Event√ U
IN = lbl (IntAct , int)

-- the pure multi-step relation over sstep
data Steps (m : Mode) : St → List (Σ (AnyTypes Ev) proj₁) → St → Set₁ where
  done : ∀ {s} → Steps m s [] s
  more : ∀ {s s′ s″ at a w} → sstep at a m s ≡ just s′ → Steps m s′ w s″ → Steps m s ((at , a) ∷ w) s″

-- a block is refused before demote: ChainSync cannot be pre-finished (Review Focus 3)
block-only-when-waiting : ∀ m → sstep (EnvAct , env) block m st₀ ≡ nothing
block-only-when-waiting m = refl

-- with lnLoad off, a Leios reply is refused even while LeiosNotify waits
lnReply-off : ∀ v b t c → sstep (EnvAct , env) lnReply (mode v b t false c) (mkSt awaiting (afterTerm v)) ≡ nothing
lnReply-off v b t c = refl
