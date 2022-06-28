# from https://stackoverflow.com/questions/9683279/make-the-current-commit-the-only-initial-commit-in-a-git-repository

git checkout --orphan newBranch
git add -A  # Add all files and commit them
git commit -m "reset entire history to save space, see prune.sh"
git branch -D gh-pages # Deletes the master branch
git branch -m gh-pages # Rename the current branch to master
git push -f origin gh-pages # Force push master branch to github
git gc --aggressive --prune=all     # remove the old files
