#!/bin/bash
set -eu

if [ ! -z ${CIRCLECI+x} ]; then
  export GIT_SSH_COMMAND="ssh -i ~/.ssh/id_ed25519 -o 'IdentitiesOnly=Yes'"
fi

REPO="$1"
shift

TMPDIR=$(mktemp -d)

OLDDIR="$PWD"

git clone -b gh-pages "$REPO" "$TMPDIR"

while [ ${#} -gt 0 ]; do
  SRC="$1"
  DST="$2"
  shift 2

  DSTDIR=$(dirname "$DST")

  rm -rf "$TMPDIR/$DST"

  mkdir -p "$TMPDIR/$DSTDIR"
  cp -r "$SRC" "$TMPDIR/$DST"

  cd "$TMPDIR"
  git add "$DST"
  cd "$OLDDIR"

done

cd "$TMPDIR"

LAST_SUBJECT=$(git log -1 --pretty=%s)

CI_SUBJECT="Deploy from CI"

if [ "$LAST_SUBJECT" = "$CI_SUBJECT" ]; then
  git commit --amend -C HEAD
else
  git commit -m "$CI_SUBJECT"
fi

git push -f

cd "$OLDDIR"

rm -rf "$TMPDIR"
