#!/bin/bash
set -eu

if [ ! -z ${CIRCLECI+x} ]; then
  # Git needs a user/email to commit under
  git config --global user.name "CI Deploy"
  git config --global user.email "ci@example.com"

  # We setup our ssh push key
  echo "$SSH_PRIVKEY" | base64 -d > ~/.ssh/id_ed25519
  echo "$SSH_PUBKEY" > ~/.ssh/id_ed25519.pub
  chmod -R go= ~/.ssh
fi
