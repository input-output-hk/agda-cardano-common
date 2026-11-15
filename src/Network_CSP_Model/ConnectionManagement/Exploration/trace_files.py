#!/usr/bin/env python3
"""Verify retained bytes against the literals checked by the six Agda modules.

This is a byte transport check, not an Agda parser or execution proof. Run Agda
on Export<Name>.agda after this check. No files are changed by this script.
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


if __name__ == '__main__':
    main()
