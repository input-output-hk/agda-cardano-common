#!/usr/bin/env python3
"""Compatibility entry point for the shared explicit-pair manifest assembler."""
from pathlib import Path
import runpy

if __name__ == '__main__':
    runpy.run_path(str(Path(__file__).with_name('paired_sessions.py')), run_name='__main__')
