#!/usr/bin/env python3
"""Check the Lean wrapper's process-failure boundary without requiring Lean.

A tiny fake lake process exercises status/output combinations, not mathematical
verification. In particular a missing compiler or killed command must never
produce the wrapper's success receipt, including in quiet mode.
"""

import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


def main():
    wrapper = Path(__file__).resolve().parents[1] / "pg-iterate.sh"
    cases = (
        ("missing compiler", 127, "lake: command not found", 127),
        ("killed compiler", 137, "", 137),
        ("failed command with clean-looking audit", 7,
         "'example' depends on axioms: [propext, Quot.sound]", 7),
        ("clean success without an audit command", 0, "", 0),
        ("clean success with audit", 0,
         "'example' depends on axioms: [propext, Classical.choice, Quot.sound]", 0),
        ("admitted theorem", 0,
         "'example' depends on axioms: [propext, sorryAx]", 2),
        ("reported elaboration failure", 0, "input.lean:1:0: error: unknown constant", 1),
    )
    with TemporaryDirectory(prefix="arklib-pg-wrapper-") as directory:
        lake = Path(directory) / "lake"
        lake.write_text('#!/bin/sh\nprintf "%s\\n" "$ARKLIB_CHECK_OUTPUT"\n'
                        'exit "$ARKLIB_CHECK_EXIT"\n')
        lake.chmod(0o755)
        for name, status, output, expected in cases:
            for quiet in (False, True):
                env = dict(os.environ, PATH=directory + os.pathsep + os.environ["PATH"],
                           ARKLIB_CHECK_OUTPUT=output, ARKLIB_CHECK_EXIT=str(status))
                command = ["bash", str(wrapper)] + (["-q"] if quiet else []) + ["input.lean"]
                result = subprocess.run(command, env=env, text=True, capture_output=True, check=False)
                assert result.returncode == expected, (name, quiet, result)
                assert ("✅ OK" in result.stdout) == (expected == 0), (name, quiet, result)
                print(f"PASS: {name}; quiet={quiet}; exit={result.returncode}")
    print("PASS: 14 wrapper process-boundary checks. These are not Lean proof checks.")


if __name__ == "__main__":
    main()
