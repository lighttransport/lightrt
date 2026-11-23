# Repository instructions for agents

## Git remotes

- **Never push to any remote without explicit permission from the user for that
  specific push.** Local commits are fine; `git push` (to any branch, including
  force pushes) is not.
- Do not infer push permission from a previous push, from a task/goal description,
  or from a request to "finish" or "close" work. If a task seems to require a
  push, stop and ask the user first.
- A push is authorized only when the user explicitly asks for it in the current
  request (for example, "push", "push this branch", or "commit and push").
- `git push --dry-run` does not change the remote, but still avoid it unless
  needed for a check the user asked for.

## Prepush audit (mandatory once push is authorized)

Before **any** authorized push, run the security-token check pass:

```sh
bash scripts/prepush_audit.sh                  # scans BASE..HEAD (the push range)
bash scripts/prepush_audit.sh --full-history   # optional: whole repository history
```

- **gitleaks** — rule/entropy scan over the push range (`--log-opts`); default
  ruleset, redacted output.
- **trufflehog** — scans the same range (`--since-commit`/`--branch`) with
  `--fail`, so *unverified* findings are fatal too: a token that fails live
  verification is still a leak. Handles linked worktrees by scanning the main
  worktree path.
- A narrow regex heuristic covers the case where a scanner is not installed;
  exit codes are `0` clean, `1` findings (**never push over a finding**), `2`
  range not determinable (set `PREPUSH_BASE=<rev>`), `77` both scanners missing
  (regex fallback only).
- If a **real** credential is found: rotate it first, then rewrite history
  (`git filter-repo`) before pushing. Allowlisting is only for false positives.
- The audit complements (does not replace) the manual checks: divergent-branch
  status, `git diff --check`, untracked/large files, secrets in docs, and test
  results.

Scanner discovery: `gitleaks` on `PATH`; `trufflehog` on `PATH` then
`~/go/bin/trufflehog`. Install: `go install github.com/gitleaks/gitleaks@latest`
and `go install github.com/trufflesecurity/trufflehog/v3@latest`.

See `CLAUDE.md` for build, test, and architecture guidance.
