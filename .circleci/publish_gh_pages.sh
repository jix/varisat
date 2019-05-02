#!/bin/bash
set -eu

SRC="$1"
REPO="$2"
DST="$3"

if [ ! -z ${CIRCLECI+x} ]; then\
  # Git needs a user/email to commit under
  git config --global user.name "CI Deploy"
  git config --global user.email "ci@example.com"

  # We setup our ssh push key
  echo "$SSH_PRIVKEY" | base64 -d > ~/.ssh/id_ed25519
  echo "$SSH_PUBKEY" > ~/.ssh/id_ed25519.pub
  chmod -R go= ~/.ssh
  export GIT_SSH_COMMAND="ssh -i ~/.ssh/id_ed25519 -o 'IdentitiesOnly=Yes'"
fi

TMPDIR=$(mktemp -d)

DSTDIR=$(dirname "$DST")

git clone -b gh-pages "$REPO" "$TMPDIR"
rm -rf "$TMPDIR/$DST"

mkdir -p "$TMPDIR/$DSTDIR"
cp -r "$SRC" "$TMPDIR/$DST"

OLDDIR="$PWD"
cd "$TMPDIR"

git add "$DST"

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
