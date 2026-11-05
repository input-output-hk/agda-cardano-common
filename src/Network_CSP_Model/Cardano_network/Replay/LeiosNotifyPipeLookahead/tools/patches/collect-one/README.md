# CollectOne review proposal

The pinned lookahead server retains completed jobs until Quit. A long connection
therefore retains historical bookkeeping and performs one final flush per past
request, even when the client has kept very little reply work outstanding.

[This minimal patch](collect-one.patch) proposes one optional completion
collection after admission and before registration of the current request. It
changes the existing `leiosNotifyServerPeerLookahead` in consensus revision
`2416493bfdbe93b761b3a4bb1ccf2b4a913e5e4b`: one file, 20 added lines and three
removed lines. It adds no public entry point, import, wire message, callback,
client or driver change. The patch has not been applied to an upstream checkout
or published.

## Proposed behavior

At `busy quitVar n`, `n` counts old registered, unflushed jobs; the accepted
current request has not yet registered its sender job.

- At Zero, proceed directly to the original AwaitLookahead body.
- At positive n, attempt exactly one `FlushSender` with an immediate optional
  fallback. Success removes one old completion; miss retains the old count.
- Both outcomes then register the current request exactly once through the
  extracted `awaitNext`. Neither branch re-enters `busy` before registration.

The responder, first ordinary Await, admission callback, Quit publication,
selected payload, cancellation transaction and final blocking drain remain
unchanged. A selected send can still block after Quit; collection does not
interrupt it. A normal reply selected before the true Quit flag can still be
sent afterward.

## Recommendation and evidence

Recommend this patch for upstream review as a targeted bookkeeping improvement.
The [reference-model proofs](../../../../../../../docs/specs/leiosnotify-collect-one-design.md#t6223-paired-policy-resource-bounds)
establish finite local source/wire equivalence, local safety/progress and a
1005 registered-job envelope for every fresh candidate run under the fixed
production paired node policy. The latter has no extra caller-supplied resource
premise; it is a mathematical model theorem, not Haskell refinement.

The [controlled actual-driver comparison](../../../../../../../docs/notes/leiosnotify-pipe-lookahead-completion-cost.md#collectone-actual-driver-comparison)
has 1224 passing fresh fixture processes and 64 corruption checks at GHC 9.6.7,
O0/O2, N1/N2, configured depths 1/1000 and three repetitions. Exact endpoint wire
streams and forced scheduling/fault assertions match the baseline. In observed
sequential histories through 10000 exchanges, the candidate retains one job and
needs one final flush, while the baseline retains and finally flushes n jobs.

At 100000 exchanges, quiet candidate median pre-Quit live heap is 33–106 KB
across eight groups, versus baseline 2.43–2.47 MB. Median shutdown is 39–67 μs
versus 16–26 ms. These are whole-fixture measurements at the documented gates.
The allocation tradeoff is a **0.22–0.46% increase in median total allocation**.
Work is collected earlier in normal operation; normal-operation throughput is
unmeasured. Diagnostic getter builds have different retirement gates and are
excluded from performance comparisons. The [immutable result record](../../results-t631-20261104.json)
contains the exact measurements, source pins and build/capture identities.

## Source correspondence and validation

[The source checker](../../collect_one_patch.py) reconstructs the exact
experimental peer source with the unchanged T6.1.1 generator. Its full-file
SHA-256 matches the peer source recorded for all ten candidate builds in
T6.3.1. It replaces the original function with that tested function body at the
existing entry point, changing only two occurrences of the entry-point name
and the explicitly recorded busy comment. Reversing those two source changes
gives **byte-for-byte function equality** with the tested candidate. No other
source bytes change.

The checker also runs `git apply --check`, applies the patch to an isolated
export, checks the resulting complete source, checks reverse application, and
reverses it to recover the pinned bytes exactly. It reads source with `git show`
and never changes an upstream checkout or the user's git index. The
[validation record](validation-20261105.json) retains the patch/source/helper/
T6.3.1-record hashes and exact comparison steps. This is a source/apply check;
no new GHC/Agda build or large experiment sweep is claimed. It does not prove
compiler preservation or Haskell semantic equivalence after renaming.

From this repository root, reproduce the lightweight checks with a new output
directory:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/collect_one_patch.py \
  --consensus /path/to/ouroboros-consensus \
  --out /tmp/leiosnotify-collect-one-patch-check
```

The helper checks the bundled patch against the canonical proposal. Its optional
`--write-bundle` flag regenerates the owned patch and validation record. Small
apply-check artifacts can use `/tmp`; the large T6.3.1 runtime artifacts remain
on disk under `/var/tmp/leiosnotify-t631-20261104/full/`.

## Remaining review and deployment questions

- Saturated throughput, normal-operation latency, real sockets/mux/CBOR,
  production payload sizes and full node callback/pump behavior are unmeasured.
  The existing profiles are controlled low-occupancy histories, including when
  configured depth is 1000.
- Case analysis forces the Int-backed Nat earlier than the baseline. Fault
  timing for forged/out-of-range inputs is not preserved by the successful
  trace theorem. Mathematical resource bounds do not supply a full runtime
  Nat/Int representation proof; signed client `arrived` range remains open.
- The 1005 bound relies on the fixed paired production policy. An unrestricted
  writer can still create unbounded unfinished work; optional collection alone
  is not an unconditional admission or denial-of-service bound.
- Haskell-to-model refinement, candidate native PTree/CSP correspondence,
  reverse paired inclusion, general runtime liveness, broader exceptional
  cleanup and whole-node shutdown remain open. A server return still need not
  mean a previously entered client handler has completed.
- Review against a different upstream revision must rebase and revalidate the
  source boundaries, API types and callback/driver assumptions. Adoption and
  upstream publication are separate from this packaged review proposal.

T6.3.2 now has a concrete review patch, source correspondence/apply checks and
this scoped recommendation. The certified arbitrary-log replay work in T7 can
continue independently against the unchanged baseline.
