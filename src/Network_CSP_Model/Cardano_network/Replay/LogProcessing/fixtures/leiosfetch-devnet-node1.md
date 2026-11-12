# Node1 LeiosFetch devnet fixture provenance

Source log:
`/home/rye/YE_Workspace_Research/Workspace_IOG/git_repos/leios-local/ouroboros-leios/demo/proto-devnet/tmp-devnet/node1/node.log`

Raw line range: **84607–987298**, inclusive, using 1-based physical file lines
of the supervisor-wrapped JSON log. The 12 selected LeiosFetch events in
the table below are retained in file order; intervening rows belong to other
events. The [raw fixture](leiosfetch-devnet-node1.log) copies those lines verbatim,
plus version line 6 and NewMux line 438 (14 supervisor-wrapped JSON rows in all). Source SHA-256:
`d3f3c0543ecad60761cd38bcbb95b16c8e486d6a5d485e15ee24c30114445d9d`.
The log records `gitRevision 7b8ca5a178ee47a6f34be88de299ce936588bf9d` at raw line 6.

[The fixture](leiosfetch-devnet-node1.txt) is the complete largest accepted
node1 session, normalized by `normalize_logs.py --fetch-only` as
`/tmp/leiosfetch-devnet-stage1/node1/s0001-server.txt`. Its connection is
`127.2.0.1:3001 127.2.0.2:3002`, server role, first NewMux generation (raw
NewMux line 438). It ends at capture EOF, with no Done event; acceptance is
only a prefix result. Its peer is node2's `s0001-client`.

| Fixture line | Raw log line | Event |
| --- | ---: | --- |
| 2 | 84607 | Recv BlockRequest |
| 3 | 84621 | Send Block |
| 4 | 85600 | Recv BlockTxsRequest |
| 5 | 85633 | Send BlockTxs |
| 6 | 92173 | Recv BlockRequest |
| 7 | 92178 | Send Block |
| 8 | 93180 | Recv BlockTxsRequest |
| 9 | 93188 | Send BlockTxs |
| 10 | 609637 | Recv BlockRequest |
| 11 | 609644 | Send Block |
| 12 | 987293 | Recv BlockRequest |
| 13 | 987298 | Send Block |

Provenance is a sidecar because `LeiosFetchParse.agda` accepts neither comments
nor blank lines. All hashes, counts, bitmaps and byte sizes are unchanged from
normalization; the normalized fixture has 12 events and is about 1.3 KB.
The test checks it directly and also normalizes the raw fixture with
`normalize_logs.py --fetch-only` into a temporary directory, checks equality to
the normalized fixture, and replays the resulting server session.
Build Main first, following the [build instructions](../../USAGE.md#build-outside-the-repository) (from `src/`):

```sh
agda --compile --ghc-dont-call-ghc --compile-dir=/tmp/leios-replay-build-stage1 Cardano_network/Replay/Main.agda +RTS -M2G -RTS
ghc --make -O -threaded -rtsopts -i/tmp/leios-replay-build-stage1 -main-is MAlonzo.Code.Cardano_network.Replay.Main /tmp/leios-replay-build-stage1/MAlonzo/Code/Cardano_network/Replay/Main.hs -o /tmp/leios-replay-build-stage1/Main +RTS -M2G -RTS
```

Run from the repo:

```sh
python3 -I -B src/Cardano_network/Replay/LogProcessing/test_leiosfetch_devnet.py /tmp/leios-replay-build-stage1/Main
```

Expected stdout: `current-schema node1 devnet fixtures normalized and accepted (12 events)`.
