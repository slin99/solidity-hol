#!/usr/bin/env python3
"""Current-source snapshot checks, run after the merge-window refresh."""

import hashlib
import json
import unittest

from test_yul_reconnaissance import ARTIFACT, ROOT, recon


class SnapshotFreshnessTests(unittest.TestCase):
    def test_every_fixture_is_the_source_it_was_made_from(self) -> None:
        artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
        for fixture in artifact["fixtures"]:
            with self.subTest(source=fixture["source"]):
                digest = hashlib.sha256(
                    (ROOT / fixture["source"]).read_bytes()
                ).hexdigest()
                self.assertEqual(fixture["sha256"], digest)

    def test_every_fixture_appears(self) -> None:
        artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
        listed = {fixture["source"] for fixture in artifact["fixtures"]}
        expected = {
            path.resolve().relative_to(ROOT).as_posix()
            for directory in recon.FIXTURE_DIRS
            for path in directory.glob("*.sol")
        }
        self.assertEqual(listed, expected)


if __name__ == "__main__":
    unittest.main()
