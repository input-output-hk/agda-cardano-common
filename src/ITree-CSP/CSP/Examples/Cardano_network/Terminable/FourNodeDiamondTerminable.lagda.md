# Terminable medium — graceful-shutdown demo (self-contained over `NetT`)

The terminable copy medium `CopySpecT`/`NetworkT` (built over the LOCAL
alphabet `Terminable.NetT`) runs each copy cell `(l, d, id)` normally until its
dedicated `mdone l d id` event fires, after which that cell terminates
gracefully (√). This module is **self-contained inside `Terminable/`**: it uses
only the local `NetT` alphabet and small local driver nodes (it does NOT pull in
the parent `Cardano_network` `Net_Api` peer stack, which has no `mdone`).

The `mdone` events are *not* in the hidden io set `ioES = {| input, output |}`,
so they stay observable at the top level — `mdone` is the marker that a medium
cell has been shut down.

```agda
{-# OPTIONS --guardedness #-}
```

```agda
import Data.Unit as U
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (refl)
open import Class.DecEq using (DecEq)

open import Level using (0ℓ)
open import Data.Fin using (zero)
open import Process_Trees using (PTree; ExtI; AnyTypes)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using (IDs; Dir; lo; hi; N2N_ChainSync)

module CSP.Examples.Cardano_network.Terminable.FourNodeDiamondTerminable where
```

## A minimal single-instance `Params`

All abstract data domains (and the forwarded payload) collapse to `⊤`; one TCP
link runs one `(lo , N2N_ChainSync)` instance.

```agda
instance
  decEq⊤ : DecEq U.⊤
  decEq⊤ = record { _≟_ = λ _ _ → yes refl }

import Data.Maybe as PMaybe

p : Params
p = record
  { Cookie = U.⊤ ; Block = U.⊤ ; Txid = U.⊤ ; LSlot = U.⊤
  ; VoterId = U.⊤ ; LFBitmap = U.⊤ ; VoteBlob = U.⊤
  ; numLinks = 1
  ; linkConfig = λ _ → (lo , N2N_ChainSync) ∷ []
  ; decCookie  = decEq⊤ ; decBlock    = decEq⊤ ; decTxid    = decEq⊤
  ; decLSlot   = decEq⊤ ; decVoterId  = decEq⊤ ; decLFBitmap = decEq⊤
  ; decVoteBlob = decEq⊤
  ; Time = U.⊤ ; Length = U.⊤ ; time₀ = U.tt ; length₀ = U.tt
  ; decTime = decEq⊤ ; decLength = decEq⊤
  -- Leios EB domains, inert here: both ⊤, no RB ever announces an EB
  ; EB = U.⊤ ; EBHash = U.⊤ ; decEB = decEq⊤ ; decEBHash = decEq⊤
  ; ebHash = λ _ → U.tt ; announcedEB = λ _ → PMaybe.nothing }
```

The local `NetT` alphabet (with `mdone`), the terminable medium/multiplexer, and
the operators over `NetT`:

```agda
open import CSP.Examples.Cardano_network.Net p using (Link)
open import CSP.Examples.Cardano_network.Terminable.NetT p
  using ( NetT; NetT-≟; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; mdone )
open import CSP.Examples.Cardano_network.Terminable.NetworkT p U.⊤
  using ( NetProc; CopyT; CopySpecT; NetworkT )

import CSP.Operators {E = NetT U.⊤} (NetT-≟ {U.⊤}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _∖_; chanSet; EventSet; Skip; Output; Prefix₀ )

l0 : Link
l0 = zero
```

## The hidden io set `{| input, output |}` (over `NetT`; excludes `mdone`)

```agda
ioSet : AnyTypes (NetT U.⊤) → Set
ioSet (_ , input  _ _ _) = U.⊤
ioSet (_ , output _ _ _) = U.⊤
ioSet _                  = ⊥

ioSet-dec : (at : AnyTypes (NetT U.⊤)) → Dec (ioSet at)
ioSet-dec (_ , input  _ _ _) = yes U.tt
ioSet-dec (_ , output _ _ _) = yes U.tt
ioSet-dec (_ , sndmsg _ _ _) = no λ ()
ioSet-dec (_ , rcvmsg _ _ _) = no λ ()
ioSet-dec (_ , tx     _ _ _) = no λ ()
ioSet-dec (_ , sndack _ _ _) = no λ ()
ioSet-dec (_ , rcvack _ _ _) = no λ ()
ioSet-dec (_ , ack    _ _ _) = no λ ()
ioSet-dec (_ , mdone  _ _ _) = no λ ()

ioES : EventSet
ioES = chanSet ioSet ioSet-dec
```

## Minimal local driver nodes

Small processes that exercise the medium on `input` / `output` / `mdone`
(payload `⊤`), standing in for a full peer stack:

```agda
-- feeds one value into the medium, then stops
producer : NetProc
producer = Output (input l0 lo N2N_ChainSync) U.tt Skip

-- consumes one value out of the medium, then stops
consumer : NetProc
consumer = Prefix₀ (output l0 lo N2N_ChainSync) Skip

-- signals graceful shutdown of the instance, then stops
shutdown : NetProc
shutdown = Prefix₀ (mdone l0 lo N2N_ChainSync) Skip

-- the (minimal) diamond nodes, interleaved
nodes : NetProc
nodes = producer ⦀ (consumer ⦀ (shutdown ⦀ Skip))
```

## The terminable system

The nodes composed with the terminable copy medium, synchronised on
`{| input, output |}`, which is then hidden; `mdone` stays observable (`∉ ioES`).

```agda
-- diamond nodes over the terminable copy medium; mdone stays observable (∉ ioES)
systemT : NetProc
systemT = (CopySpecT ∥⇘ ioES ⇙ nodes) ∖ ioES

-- the same nodes over the full terminable NetworkT multiplexer (parity)
systemT-mux : NetProc
systemT-mux = (NetworkT ∥⇘ ioES ⇙ nodes) ∖ ioES
```

## Isolated-cell termination witness

The key behavioural fact: graceful shutdown actually works. On the *isolated*
terminable copy cell `CopyT l0 lo N2N_ChainSync`, the `mdone l0 lo N2N_ChainSync`
event fires as a visible LTS step, and the cell terminates (√).

`CopyT l d id` is built with `iter`, so `force (CopyT l0 lo N2N_ChainSync)`
unfolds through `iter`/`iter-bind` to the `react (iterV k …) (iterT k …)` node
wrapping the cell's offer menu; its visible offer at `mdone l0 lo N2N_ChainSync`
reduces (via `iterV`/`viewV` and `l0 ≟ l0`, `lo ≟ lo`, `N2N_ChainSync ≟
N2N_ChainSync` all `yes refl`) to the menu's terminate branch `just (Ret (inj₂
tt))`, so `sVis refl refl` goes through directly.

```agda
open import Semantics.LTS {E = NetT U.⊤} {I = ExtI (NetT U.⊤)}
  using ( _─[_]─►_; sVis; ev; evl; evLabel )

-- mdone l0 lo N2N_ChainSync fires on the isolated terminable cell, terminating it (√)
mdone-fires : ∃[ P′ ]
  (CopyT l0 lo N2N_ChainSync
     ─[ ev (evl (evLabel U.⊤ (mdone l0 lo N2N_ChainSync) U.tt)) ]─► P′)
mdone-fires = _ , sVis {at = U.⊤ , mdone l0 lo N2N_ChainSync} {a = U.tt} refl refl
```

## Reading the witness

`mdone l d id` gracefully terminates instance `(l, d, id)`'s medium cell — the
cell reaches √ and thereafter offers nothing further on that instance's
`input`/`output` channels. The whole terminable medium reaches √ once **every**
configured instance has been `mdone`'d. Because `mdone ∉ ioES`, every such
shutdown stays observable at the `systemT` top level.
