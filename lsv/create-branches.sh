students=( $(cut -d, -f1 < participants-id.csv | tail -n +3) )
for student in "${students[@]}"; do
    echo "Creating branch ${student} ..."
    git branch "${student}"
done
