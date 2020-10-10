if [ -f ".github/workflows/lockdown.yml.disabled" ]; then
    git sw master
    mv .github/workflows/lockdown.yml.disabled .github/workflows/lockdown.yml
    git a .github/workflows
    git cm "Enable lockdown"
    git push
    lsv/admin/update-branches.sh
else
    echo "[WARNING] Lockdown is NOT disabled!"
fi
