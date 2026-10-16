#!/usr/bin/env python3
"""Compiled client/server control-checker tests; pass the path to the built Main."""
from pathlib import Path
import subprocess
import sys
import tempfile


def main(binary):
    binary = str(Path(binary).resolve())
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "client.txt"

        def check(events, expected, depth=None, header="role client"):
            path.write_text(header + "\n" + events)
            args = [binary, "--blockfetch-client", str(path)]
            if depth is not None:
                args.append(str(depth))
            result = subprocess.run(args, check=True, capture_output=True,
                                    text=True).stdout.strip()
            assert result.startswith(expected), (args, events, expected, result)

        rounds = ("Send RequestRange\nRecv StartBatch\nSend RequestRange\n"
                  "Recv Block\nRecv BatchDone\nSend RequestRange\n"
                  "Recv NoBlocks\nRecv StartBatch\nRecv BatchDone\nSend ClientDone\n")
        check(rounds, "accepted (10 events; BlockFetch client control only)", 2)
        check(rounds, "rejected at index 3", 1)
        check("Send RequestRange\n" * 100, "accepted (100 events")
        check("Send RequestRange\n" * 101, "rejected at index 101")
        check("Send RequestRange\n", "rejected at index 1", 0)
        check("Send ClientDone\n", "accepted (1 events", 0)
        check("", "accepted (0 events", 0)
        check("Send RequestRange\nRecv StartBatch\nRecv BatchDone\nSend ClientDone\n",
              "accepted (4 events", 1)
        for events, index in [
            ("Recv StartBatch\n", 1),
            ("Send RequestRange\nRecv Block\n", 2),
            ("Send RequestRange\nRecv StartBatch\nRecv NoBlocks\n", 3),
            ("Send RequestRange\nSend ClientDone\n", 2),
            ("Recv RequestRange\n", 1),
            ("Send ClientDone\nSend RequestRange\n", 2),
        ]:
            check(events, f"rejected at index {index}", 2)
        check("", "parse error at line 1", header="role server")
        check("Send RequestRange aa bb\n", "parse error at line 2")
        check("BlockFetch.Remote.Send.RequestRange\n"
              "BlockFetch.Remote.Receive.NoBlocks\n"
              "BlockFetch.Remote.Send.ClientDone\n", "accepted (3 events", 1)
        check("LeiosFetch.Remote.Receive.Block\n", "parse error at line 2")
        check("Send BlockRequest\n", "parse error at line 2")
        check("Send RequestRange\n", "usage:", -1)
        result = subprocess.run([binary, "--blockfetch-client"], check=True,
                                capture_output=True, text=True).stdout
        assert result.startswith("usage:"), result
        def server(events, expected, header="role server", extra=()):
            path.write_text(header + "\n" + events)
            args = [binary, "--blockfetch-server", str(path), *extra]
            result = subprocess.run(args, check=True, capture_output=True,
                                    text=True).stdout.strip()
            assert result.startswith(expected), (args, events, expected, result)

        server("Recv RequestRange\nSend StartBatch\nSend Block\nSend Block\n"
               "Send BatchDone\nRecv RequestRange\nSend NoBlocks\n"
               "Recv RequestRange\nSend StartBatch\nSend BatchDone\nRecv ClientDone\n",
               "accepted (11 events; BlockFetch server control only)")
        server("", "accepted (0 events")
        server("Recv ClientDone\n", "accepted (1 events")
        server("Recv RequestRange\n", "accepted (1 events")
        server("Recv RequestRange\nSend StartBatch\nSend Block\n", "accepted (3 events")
        for events, index in [
            ("Recv RequestRange\nRecv RequestRange\n", 2),
            ("Recv RequestRange\nSend StartBatch\nRecv RequestRange\n", 3),
            ("Send StartBatch\n", 1),
            ("Recv RequestRange\nSend Block\n", 2),
            ("Recv RequestRange\nSend BatchDone\n", 2),
            ("Recv RequestRange\nSend StartBatch\nSend NoBlocks\n", 3),
            ("Recv RequestRange\nSend StartBatch\nSend StartBatch\n", 3),
            ("Recv RequestRange\nRecv ClientDone\n", 2),
            ("Recv RequestRange\nSend StartBatch\nRecv ClientDone\n", 3),
            ("Send RequestRange\n", 1),
            ("Recv RequestRange\nRecv StartBatch\n", 2),
            ("Recv ClientDone\nRecv RequestRange\n", 2),
        ]:
            server(events, f"rejected at index {index}")
        server("BlockFetch.Remote.Receive.RequestRange\n"
               "BlockFetch.Remote.Send.NoBlocks\n"
               "BlockFetch.Remote.Receive.ClientDone\n", "accepted (3 events")
        server("", "parse error at line 1", header="role client")
        server("Send Block ab\n", "parse error at line 2")
        server("LeiosFetch.Remote.Send.Block\n", "parse error at line 2")
        server("Recv RequestRange\n", "usage:", extra=("2",))
        result = subprocess.run([binary, "--blockfetch-server"], check=True,
                                capture_output=True, text=True).stdout
        assert result.startswith("usage:"), result
        def shared(contents, expected, mode="--blockfetch", bounds=()):
            path.write_text(contents)
            args = [binary, mode, str(path), *map(str, bounds)]
            result = subprocess.run(args, check=True, capture_output=True,
                                    text=True).stdout.strip()
            assert result.startswith(expected), (args, contents, expected, result)

        shared("role client\n" + rounds, "accepted (10 events, 1 sessions)", bounds=(2,))
        shared("role client\n" + rounds, "rejected at index 3 (session 0)", bounds=(1,))
        shared("role server\nRecv RequestRange\nSend NoBlocks\nRecv ClientDone\n",
               "accepted (3 events, 1 sessions)", bounds=(0,))
        shared("role server\nRecv RequestRange\nRecv RequestRange\n",
               "rejected at index 2 (session 0)", bounds=(1000,))
        shared("role client\n" + "Send RequestRange\n" * 100, "accepted (100 events, 1 sessions)")
        shared("role client\n" + "Send RequestRange\n" * 101, "rejected at index 101 (session 0)")
        mixed = ("sessions blockfetch:client blockfetch:server fetch:client fetch:server notify:client notify:server\n"
                 "0 Send RequestRange\n1 Recv RequestRange\n2 Send BlockRequest ab 3\n"
                 "4 Send RequestNext\n0 Send RequestRange\n5 Recv RequestNext\n"
                 "3 Recv BlockRequest cd 4\n1 Send StartBatch\n0 Recv NoBlocks\n"
                 "1 Send Block\n2 Recv Block ab 20\n4 Recv Votes -\n"
                 "3 Send Block cd 20\n5 Send Votes -\n1 Send BatchDone\n"
                 "0 Recv StartBatch\n0 Recv BatchDone\n0 Send ClientDone\n1 Recv ClientDone\n")
        shared(mixed, "accepted (19 events, 6 sessions)", "--interleaved", (1, 1, 2))
        shared(mixed, "rejected at index 5 (session 0)", "--interleaved", (1, 1, 1))
        shared(mixed, "accepted (19 events, 6 sessions)", "--interleaved", (1, 1))
        shared("sessions blockfetch:client blockfetch:client\n0 Send RequestRange\n1 Recv NoBlocks\n",
               "rejected at index 2 (session 1)", "--interleaved", (1, 1, 2))
        shared("sessions fetch:client notify:client blockfetch:client\n2 Send RequestRange\n2 Send RequestRange\n",
               "accepted (2 events, 3 sessions)", "--interleaved", (0, 0, 2))
        shared("sessions fetch:client blockfetch:client\n0 Send BlockRequest ab 3\n",
               "rejected at index 1 (session 0)", "--interleaved", (0, 2, 2))
        shared("sessions notify:client blockfetch:client\n0 Send RequestNext\n",
               "rejected at index 1 (session 0)", "--interleaved", (2, 0, 2))
        shared("sessions blockfetch:client blockfetch:client\n0 Send ClientDone\n1 Send RequestRange\n",
               "accepted (2 events, 2 sessions)", "--interleaved", (1, 1, 1))
        shared("sessions blockfetch:client\n0 Send ClientDone\n0 Send RequestRange\n",
               "rejected at index 2 (session 0)", "--interleaved", (1, 1, 1))
        shared("sessions blockfetch:client\n0 LeiosFetch.Remote.Receive.Block\n",
               "parse error at line 2", "--interleaved")
        shared("sessions blockfetch:client\n1 Send RequestRange\n", "parse error at line 2", "--interleaved")
        for value in ("-1", "bad"):
            shared("role client\n", "usage:", bounds=(value,))
            shared("sessions\n", "usage:", "--interleaved", (1, 1, value))
        shared("role invalid\n", "parse error at line 1")
        shared("role server\nSend Block ab\n", "parse error at line 2")
        shared("role client\n", "usage:", bounds=(1, 2))
    print("BlockFetch role-dispatch and mixed-session CLI integration tests passed")


if __name__ == "__main__":
    main(sys.argv[1])
