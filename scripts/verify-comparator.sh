#!/usr/bin/env bash
set -euo pipefail

lean_only=false
if [ "$#" -eq 1 ] && [ "$1" = "--lean-only" ]; then
  lean_only=true
elif [ "$#" -ne 0 ]; then
  echo "usage: $0 [--lean-only]" >&2
  exit 2
fi

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cache_root=${PALOMAR_COMPARATOR_CACHE:-"$repository_root/.cache/palomar-comparator"}
bin_dir="$cache_root/bin"
comparator_dir="$cache_root/comparator"
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"

comparator_commit=575674928e239f5bc452aab72d1dd7b0f1326494
lean4export_commit=15f6055e299ad5b89345e533cc2192f4cc00f659
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

required_commands=(git go lake python3 systemd-run)
if [ "$lean_only" = false ]; then
  required_commands+=(cargo)
fi
for required_command in "${required_commands[@]}"; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run Comparator" >&2
    exit 1
  fi
done

python3 - "$repository_root/comparator.json" <<'PY'
import json
import pathlib
import sys

config_path = pathlib.Path(sys.argv[1])
try:
    config = json.loads(config_path.read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {config_path}: {error}", file=sys.stderr)
    raise SystemExit(1)

if not isinstance(config, dict) or config.get("enable_nanoda") is not True:
    print(
        f"error: {config_path}: enable_nanoda must be exactly true; "
        "the NanoDa replay is required",
        file=sys.stderr,
    )
    raise SystemExit(1)
PY

mkdir -p "$cache_root" "$bin_dir"

config_path="$repository_root/comparator.json"
if [ "$lean_only" = true ]; then
  config_path="$cache_root/comparator-lean-only.json"
  python3 - "$repository_root/comparator.json" "$config_path" <<'PY'
import json
import pathlib
import sys

config = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
config["enable_nanoda"] = False
pathlib.Path(sys.argv[2]).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY
  echo "Comparator mode: statement comparison, axiom restrictions and Lean kernel replay (NanoDa disabled)."
else
  echo "Comparator mode: statement comparison, axiom restrictions, Lean and NanoDa kernel replay."
fi

checkout_exact() {
  local repository=$1
  local destination=$2
  local commit=$3
  if [ ! -d "$destination/.git" ]; then
    git clone --filter=blob:none --no-checkout "$repository" "$destination"
  fi
  git -C "$destination" fetch --depth 1 origin "$commit"
  git -C "$destination" checkout --detach "$commit"
}

checkout_exact https://github.com/leanprover/lean4export.git "$lean4export_dir" "$lean4export_commit"

if [ ! -f "$lean4export_dir/lean-toolchain" ]; then
  echo "error: pinned lean4export revision $lean4export_commit has no lean-toolchain file" >&2
  echo "select a lean4export revision that declares its Lean toolchain" >&2
  exit 1
fi

project_toolchain=$(tr -d '[:space:]' < "$repository_root/lean-toolchain")
lean4export_toolchain=$(tr -d '[:space:]' < "$lean4export_dir/lean-toolchain")
if [ "$project_toolchain" != "$lean4export_toolchain" ]; then
  echo "error: project toolchain $project_toolchain does not match" >&2
  echo "the pinned lean4export toolchain $lean4export_toolchain" >&2
  echo "update lean4export_commit when changing lean-toolchain, then review" >&2
  echo "Comparator and NanoDa compatibility with the export format" >&2
  exit 1
fi

checkout_exact https://github.com/leanprover/comparator.git "$comparator_dir" "$comparator_commit"
if [ "$lean_only" = false ]; then
  checkout_exact https://github.com/robsimmons/nanoda_lib.git "$nanoda_dir" "$nanoda_commit"
fi

GOBIN="$bin_dir" go install "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"

(cd "$comparator_dir" && lake build comparator)
(cd "$lean4export_dir" && lake build lean4export)
if [ "$lean_only" = false ]; then
  (cd "$nanoda_dir" && cargo build --release --locked)
fi

cd "$repository_root"
lake exe cache get
systemd-run --user --wait --pipe --collect \
  --working-directory="$repository_root" \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --setenv=PATH="$PATH" \
  --setenv=LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" \
  --setenv=PALOMAR_LANDRUN_BIN="$bin_dir/landrun" \
  --setenv=COMPARATOR_LEAN4EXPORT="$lean4export_dir/.lake/build/bin/lean4export" \
  --setenv=COMPARATOR_NANODA="$nanoda_dir/target/release/nanoda_bin" \
  --setenv=COMPARATOR_LANDRUN="$repository_root/scripts/landrun-wrapper.sh" \
  -- lake env "$comparator_dir/.lake/build/bin/comparator" "$config_path"
