git sw master
mv .github/workflows/lockdown.yml.disabled .github/workflows/lockdown.yml
git a .github/workflows
git cm "Enable lockdown"
git push
lsv/admin/update-branches.sh
