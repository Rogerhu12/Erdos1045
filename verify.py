"""Check submission layout, build Lean, and audit the public theorems' axioms."""
from pathlib import Path
import argparse
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fresh', action='store_true', help='clean project build outputs first')
    parser.add_argument('--no-build', action='store_true', help='audit existing build artifacts only')
    args = parser.parse_args()
    if args.fresh and args.no_build:
        parser.error('--fresh and --no-build are mutually exclusive')
    env = os.environ.copy()
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    subprocess.run([sys.executable, 'scripts/check_submission.py'], cwd=ROOT, env=env, check=True)
    if not args.no_build:
        subprocess.run([sys.executable, 'build.py', *(['--fresh'] if args.fresh else [])],
                       cwd=ROOT, env=env, check=True)
    subprocess.run(['lake', 'env', 'lean', 'scripts/Audit.lean'], cwd=ROOT, env=env, check=True)
    subprocess.run(['lake', 'env', 'lean', 'scripts/AuditExplicitFinal.lean'],
                   cwd=ROOT, env=env, check=True)
    print('Lean axiom audit passed. Comparator/NanoDa is a separate Linux check.')

if __name__ == '__main__':
    main()
