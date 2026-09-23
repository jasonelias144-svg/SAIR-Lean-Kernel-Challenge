# partition v3 (not yet run in the playground)

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

Queued for the next partition playground slot.
