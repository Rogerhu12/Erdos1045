"""Build the pinned Lake project from any supported platform."""
from pathlib import Path
import argparse
import os
import subprocess

ROOT = Path(__file__).resolve().parent

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fresh', action='store_true', help='clean project build outputs first')
    parser.add_argument('targets', nargs='*')
    args = parser.parse_args()
    env = os.environ.copy()
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    if args.fresh:
        subprocess.run(['lake', 'clean'], cwd=ROOT, env=env, check=True)
    subprocess.run(['lake', 'build', *args.targets], cwd=ROOT, env=env, check=True)

if __name__ == '__main__':
    main()
