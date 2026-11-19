# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
import subprocess
from pathlib import Path

from hamcrest import assert_that, contains_string, equal_to

SCRIPT = Path(__file__).parent / "regen-rules.sh"


def test_reports_a_failed_clone(tmp_path):
    done = subprocess.run(
        ["bash", str(SCRIPT)],
        env={
            "PATH": "/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin",
            "PHINO_REPO": str(tmp_path / "missing"),
        },
        capture_output=True,
        text=True,
        check=False,
    )
    assert_that(done.returncode, equal_to(1), "Did not fail on a broken clone")
    assert_that(
        done.stderr,
        contains_string("FATAL: cannot clone"),
        "Did not explain why the clone failed",
    )
