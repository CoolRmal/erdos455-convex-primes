# Scripts

These programs were used to design and cross-check the certificate. They are **not** part of
the proof: everything the proof relies on is computed and checked inside Lean.

* `gen_phi.c` — the max-plus value iteration of the paper in plain C. `./gen_phi 17 phi17.txt`
  computes the potential `φ` by one period of value iteration from zero (normalised to
  `max φ = 0`), checks one more period from `φ`, and reports `Λ = 295318` and `span φ = 109`.
  The file it writes has SHA-256
  `9ae840ca13532737580037705f8eae55a66c9b11aa00f9be74b3828e35c0dd07`, the hash given in the
  paper. It takes about 6 minutes.
* `packed_ref.py` — a reference implementation of the packed value iteration of
  `Erdos455/DP/Step.lean` (two components of `M / 3` fields of 9 bits, normalisation every 32
  steps). `python3 packed_ref.py phi13.txt` reproduces the growth rate `18748` for the modulus
  `15015`, and similarly for `15`, `105` and `1155`.
* `headroom.c` — the range of the values during the verification run, which justifies the field
  width `9` (values stay below `2⁸`) and the normalisation period `32`.
* `simd_volume.c` — the work of the packed iteration for various ways of splitting the residues
  into components (used to choose the split by the residue modulo `3`).
* `bench_checkers.sh` — times the Lean kernel, nanoda and con-ron (and, with `ALL=1`, the other
  checkers bundled with the toolchain) on an export of given declarations, with the same extra
  declarations that `lake comparator` exports.
