#!/usr/bin/env bash
# readme-inventory.sh -- deprecated shim.
#
# Module inventory tables are no longer pasted in by hand. A README opts into a
# machine-owned table by wrapping it in
#
#     <!-- BEGIN GENERATED: inventory dir=<path> -->
#     ... table ...
#     <!-- END GENERATED -->
#
# after which `check-module-invariants.sh --emit-inventory` rewrites every
# column except the hand-written trailing description, and the INV check in the
# same script fails if any block has gone stale. See that script's
# `--emit-inventory` header comment for the full marker-option list.
#
# This shim exists so an old invocation reports the replacement rather than
# emitting a table nobody will keep in sync.

set -euo pipefail

cat >&2 <<'MSG'
scripts/readme-inventory.sh is deprecated.

Module inventories are generated in place. Wrap the table in a README with

    <!-- BEGIN GENERATED: inventory dir=<path> -->
    <!-- END GENERATED -->

and then run:

    bash scripts/check-module-invariants.sh --emit-inventory          # write
    bash scripts/check-module-invariants.sh --emit-inventory --check  # verify
MSG
exit 2
