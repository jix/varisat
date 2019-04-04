set -eu

# Don't run CI for gh-pages
cd "$1"
mkdir .circleci
cat <<EOF > .circleci/config.yml
jobs:
  build:
    docker:
      - image: jixone/rust-ci:master
    branches:
      ignore: gh-pages
    steps: []
EOF

# Git needs a user/email to commit under
git config --global user.name "CI Deploy"
git config --global user.email "ci@example.com"

# We create a new ininitial commit containing all the generated docs
git init
git add .
git commit -m 'Deploy developer documentation from CI'
git remote add origin "$2"

# We setup our ssh push key
echo "$SSH_PRIVKEY" | base64 -d > ~/.ssh/id_ed25519
echo "$SSH_PUBKEY" > ~/.ssh/id_ed25519.pub
chmod -R go= ~/.ssh
export GIT_SSH_COMMAND="ssh -i ~/.ssh/id_ed25519 -o 'IdentitiesOnly=Yes'"

# And overwrite the gh-pages branch
git push -f origin master:gh-pages
