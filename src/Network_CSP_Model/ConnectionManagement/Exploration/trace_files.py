#!/usr/bin/env python3
"""Verify retained bytes against literals checked by the Agda certificates.

This is a byte transport check, not an Agda parser or execution proof. Run Agda
on Export<Name>.agda and Shrunk<Name>.agda after this check. No files are changed.
"""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
NAMES = ('HandshakeFailure', 'Inbound', 'TimeoutCooling', 'Outbound', 'TwoPeer', 'Overlap')


def main():
    for name in NAMES:
        source = (ROOT / f'Export{name}.agda').read_text()
        literal = re.search(r'^wire = toList (".*")$', source, re.MULTILINE)
        assert literal, name
        expected = json.loads(literal.group(1)).encode('ascii')
        actual = (ROOT / 'traces' / f'{name}.trace').read_bytes()
        assert actual == expected, f'{name}: artifact differs from checked literal'
        print(f'{name}: {len(actual.splitlines())} events, {len(actual)} bytes, identical')

    for name in ('Late', 'Purge', 'Foreign'):
        source = (ROOT / f'Shrunk{name}.agda').read_text()
        for kind in ('original', 'shrunk'):
            literal = re.search(
                rf'^{kind}-export : M.wire {kind} ≡ toList (".*")$',
                source, re.MULTILINE)
            assert literal, (name, kind)
            actual = (ROOT / 'traces' / f'{name}.{kind}.trace').read_bytes()
            assert actual == json.loads(literal.group(1)).encode('ascii'), (name, kind)
            print(f'{name}.{kind}: {len(actual.splitlines())} events, '
                  f'{len(actual)} bytes, identical')


if __name__ == '__main__':
    main()
