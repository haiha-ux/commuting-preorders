"""counts.orbit_count writes a file only when --out is given (run: python tests/test_orbit_count_output.py)."""

import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def run(cwd: Path, *extra: str) -> None:
    env = {**os.environ, "PYTHONPATH": str(ROOT)}
    subprocess.run([sys.executable, "-m", "counts.orbit_count", "--n-max", "4", "--workers", "1", *extra],
                   cwd=cwd, env=env, check=True, capture_output=True)


def test_no_out_writes_nothing():
    with tempfile.TemporaryDirectory() as d:
        run(Path(d))
        assert list(Path(d).iterdir()) == []


def test_out_writes_csv():
    with tempfile.TemporaryDirectory() as d:
        run(Path(d), "--out", "t.csv")
        assert (Path(d) / "t.csv").read_text().splitlines()[0] == "n,T,io,t,cio,rho,rho_io"


if __name__ == "__main__":
    test_no_out_writes_nothing()
    test_out_writes_csv()
    print("ok")
