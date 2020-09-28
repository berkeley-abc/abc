students=( $(cut -d, -f1 < lsv/admin/participants-id.csv | tail -n +3) )
git sw master
for student in "${students[@]}"; do
    echo "Updating branch ${student} ..."
    git sw "${student}"
    git rebase master
    git push
    git sw master
done
