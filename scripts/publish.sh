#!/usr/bin/env bash
# Publish only this project and its Git history, never a transcript.
# Successful execution requires an authenticated GitHub CLI and the Lean build.
set -euo pipefail
cd "$(dirname "$0")/.."
target='xiangyazi24/stanley-wilf'
target_url="https://github.com/${target}.git"
command -v gh >/dev/null 2>&1 || { echo 'GitHub CLI (gh) is required.' >&2; exit 127; }
command -v lake >/dev/null 2>&1 || { echo 'Lean/Lake is required before publication.' >&2; exit 127; }
account="$(gh api user --jq .login)"
if [[ "$account" != 'xiangyazi24' ]]; then
  echo "Refusing to publish: authenticated account is $account, expected xiangyazi24." >&2
  exit 1
fi
if [[ -n "$(git status --porcelain)" ]]; then
  echo 'Refusing to publish a dirty worktree. Commit reviewed changes first.' >&2
  exit 1
fi
if [[ "$(git branch --show-current)" != 'main' ]]; then
  echo 'Refusing to publish a branch other than main.' >&2
  exit 1
fi
origin="$(git remote get-url origin 2>/dev/null || true)"
bundle_origin=false
case "$origin" in
  ''|"$target_url"|"https://github.com/$target"|"git@github.com:$target.git"|"ssh://git@github.com/$target.git") ;;
  *)
    # Cloning a bundle makes that local bundle the origin. Preserve it rather
    # than refusing the very restoration command documented in the README.
    if [[ -f "$origin" ]] && git bundle verify "$origin" >/dev/null 2>&1; then
      if git remote get-url bundle-source >/dev/null 2>&1; then
        echo 'Refusing to replace the existing bundle-source remote.' >&2
        exit 1
      fi
      bundle_origin=true
    else
      echo 'Refusing to replace an origin that is neither the target repo nor a valid local bundle.' >&2
      exit 1
    fi
    ;;
esac
# A source-only or missing-compiler run does not pass this gate.
lake update
lake exe cache get
./scripts/check.sh
if [[ -f lake-manifest.json ]]; then
  git add lake-manifest.json
  if ! git diff --cached --quiet; then
    git commit -m 'chore: lock dependencies after successful Lean build'
  fi
fi
# A pre-existing target is allowed; an unrelated remote is not. If viewing
# fails because access is denied, creation also fails safely; no force push.
if ! gh repo view "$target" --json nameWithOwner >/dev/null 2>&1; then
  gh repo create "$target" --private --description 'Stanley–Wilf growth-limit formalization in Lean'
fi
if [[ "$bundle_origin" == true ]]; then
  git remote rename origin bundle-source
  origin=''
fi
if [[ -z "$origin" ]]; then
  git remote add origin "$target_url"
fi
# Validate push URLs too; an origin can have a separate pushurl.
while IFS= read -r push_url; do
  case "$push_url" in
    "$target_url"|"https://github.com/$target"|"git@github.com:$target.git"|"ssh://git@github.com/$target.git") ;;
    *) echo 'Refusing a push URL outside the explicitly requested repository.' >&2; exit 1 ;;
  esac
done < <(git remote get-url --push --all origin)
# Ordinary push rejects unrelated/non-fast-forward remote history.
git push --set-upstream origin main
