# Working in the SAIR Lean Kernel Challenge repository

This repository follows the policy handbook at
https://github.com/jasonelias144-svg/policy-handbook. Read its orientation
(README.md) before your first session here. The rules below add to the
handbook; they never loosen it.

## Every session

1. Read `STATUS.md` and the open pull requests (handbook P1).
2. Work on a branch; never push to `main` (P3).
3. End by pushing, updating `STATUS.md` on your branch, and opening or updating
   the pull request (P1).

## Who decides

The founder decides what this project is for and who works on it. The technical
lead (Claude) decides everything about the code, and records an approval on
every pull request before it merges (P4). Intent questions go to the founder (P5).

## This repository

- **What it is:** the record of our Stage 1 entries in the SAIR Lean Kernel
  Challenge: every playground run, the final submitted files, and the official
  results.
- **State:** complete. All eight problems have a formal entry. The final
  evaluation runs after the 2026-11-20 deadline.
- **Test:** `cd final-submissions && sha256sum -c SHA256SUMS`, which proves the
  final files are byte-identical to what was submitted. CI runs it.
- **Lean work:** `tools/session-setup.sh` installs the pinned Lean toolchain
  and the challenge repository; `tools/icount-kernel.sh` counts kernel
  instructions locally.
- **Merge method:** merge commit (as in this repository's history)
- **Release:** none. Formal submissions go to the SAIR API, not GitHub.

## Rules specific to this repository

- **The entries are frozen.** For each problem, only the latest formal entry
  counts, even if it fails, and a failed one does not bring the earlier one
  back. **No formal submission is made without the founder's decision.** Any
  new candidate is tested in the playground first, and recorded in
  `SUBMISSIONS.md` (P5, P6).
- **`final-submissions/` changes only with a new formal entry,** together with
  `SHA256SUMS`, which must match the `rawUploadSha256` the server records.
- **The SAIR API key** lives only in the session environment (`SAIR_API_KEY`).
  Never print it, and never write it to a file, a commit or a message (P8).
- **Every playground run is kept,** rejected ones included, under
  `problems/<problem>/run-<id>_<name>/`.

## Always

- Say who made each change: `Made-by: <name> (AI|human)` in commits, and the
  "Made by" field in pull requests (P3).
- No secrets or personal data anywhere in the repository (P8).
- Report outcomes honestly: what you checked, and what you did not.
