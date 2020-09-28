students=( $(cut -d, -f1 < lsv/admin/participants-id.csv | tail -n +3) )
git sw master
for student in "${students[@]}"; do
    echo "Creating branch ${student} ..."
    git br "${student}"
    git sw "${student}"
    git push --set-upstream origin "${student}"
    git sw master
done
