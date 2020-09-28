students=( $(cut -d, -f1 < lsv/admin/participants-id.csv | tail -n +3) )
git sw master
for student in "${students[@]}"; do
    echo "Deleting branch ${student} ..."
    git br -d "${student}"
    git push origin --delete "${student}"
done
