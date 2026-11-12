#!/usr/bin/env python3
"""Replay the small current-schema devnet fixture with a compiled Main."""
from pathlib import Path
import subprocess
import sys
import tempfile


def main(binary):
    """Check stdout: Main does not encode protocol verdicts in its exit status."""
    fixture = Path(__file__).with_name('fixtures') / 'leiosfetch-devnet-node1.txt'
    # Keep the complete largest node1 session, including both transaction rounds.
    events = fixture.read_text().splitlines()
    assert events[0] == 'role server' and len(events) == 13
    result = subprocess.run([str(Path(binary).resolve()), str(fixture)],
                            check=True, capture_output=True, text=True, timeout=10)
    assert result.stdout.strip() == 'accepted (12 events)', result.stdout
    assert not result.stderr, result.stderr
    # Exercise raw current-schema JSON through the normalizer and compiled checker.
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp) / 'normalized'
        subprocess.run([sys.executable, '-I', '-B',
                        str(Path(__file__).with_name('normalize_logs.py')),
                        '--fetch-only', str(fixture.with_suffix('.log')), str(out)],
                       check=True, capture_output=True, text=True, timeout=10)
        sessions = sorted(out.glob('s*-server.txt'))
        assert len(sessions) == 1, sessions
        assert sessions[0].read_text() == fixture.read_text()
        raw_result = subprocess.run([str(Path(binary).resolve()), str(sessions[0])],
                                    check=True, capture_output=True, text=True, timeout=10)
        assert raw_result.stdout.strip() == 'accepted (12 events)', raw_result.stdout
        assert not raw_result.stderr, raw_result.stderr
    print('current-schema node1 devnet fixtures normalized and accepted (12 events)')


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: test_leiosfetch_devnet.py /path/to/Main')
    main(sys.argv[1])
