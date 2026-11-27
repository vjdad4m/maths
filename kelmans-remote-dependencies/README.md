# Kelmans: local repair by slides and one cleanup

For a prescribed final packing of three-vertex paths, a monotone slide inserts a tile of that final factor, sharing two vertices with the old tile it removes. A dependency points from an old tile to the old tile that owns the needed third vertex. The exact unavoidable old residue consists of the tiles that reach a targetless tile or a directed dependency cycle. Every other old tile can move in one sequence. With one final cleanup, completion is possible exactly when that residue contains at most one tile; when possible, the minimum number of slides is the number of nonfinal old tiles minus one, truncated at zero. The result also allows restricting which final tiles may be inserted during the slides.

Separately, for an original vacancy at distance at least `d` from all other original vacancies, any sequence of `n` slides, even nonmonotone, followed by one cleanup requires `d ≤ 3*(n+1)+1`. The proof counts occupied distance levels of changed old tiles and uses divisibility by three across a level with no changed tile.

These are theorems about the repair method. Neither proves that a suitable final factor always exists nor settles the Kelmans conjecture.

Run `bash kelmans-remote-dependencies/replay.sh` from the repository root with Lean 4.19 and the corresponding Mathlib on `LEAN_PATH`. The optional first argument is the repository root containing the already-published dependencies.
