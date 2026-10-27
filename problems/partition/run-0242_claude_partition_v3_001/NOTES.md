# partition v3: design notes

Same algorithm and proof as run 220, with the two inner loops (`hgeo`, `rowF`)
written as `Nat.rec` instead of structural recursion. Complete proof; builds
and passes the local judge.

Local instruction counts (valgrind/callgrind, kernel check only; these track
the official numbers closely):

| n | v2 (run 220) | v3 |
|---:|---:|---:|
| 14 | 7.2 M | 1.0 M |
| 22 | 13.7 M | 3.3 M |
| 32 | 24.1 M | 8.1 M |

**Result:** accepted in playground run 242 (17,770,587 instructions over 3 public cases). Formal entry 480; official daily evaluation of 2026-10-27: accepted, all cases ok, total 42,257,715.
