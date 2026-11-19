#!/usr/bin/env bash
# Build pinned public ORFS sources in a new directory; no experiments run.
set -euo pipefail
root=$(cd "$(dirname "$0")" && pwd)
work=${1:?Usage: bash build-image.sh NEW_BUILD_DIRECTORY}
if [ -e "$work" ]; then
  echo "Refusing to reuse an existing source directory: $work" >&2
  exit 1
fi
git clone https://github.com/The-OpenROAD-Project/OpenROAD-flow-scripts.git "$work"
cd "$work"
git checkout --detach 1ff0d0814e153b15ba5cdcf591e11b0e2589f169
git submodule update --init --recursive
test "$(git -C tools/OpenROAD rev-parse HEAD)" = f9a6acaf77a58c03a8d1284d3fd64b33d0cfd3bc
test "$(git -C tools/yosys rev-parse HEAD)" = 5bafeb77dc71e054fa331ab9efa613e6fb0a1c49
test "$(git -C tools/yosys/abc rev-parse HEAD)" = 131a50dd773f21ebbfc51da1d182438382a04209
# Bound dependency compilation as in the experimental image.
git apply "$root/build-resources.patch"
export DOCKER_DEFAULT_PLATFORM=linux/amd64
./etc/DockerHelper.sh create -os=ubuntu22.04 -target=dev -tag=agr-paper -threads=4
./etc/DockerHelper.sh create -os=ubuntu22.04 -target=builder -tag=agr-paper -threads=4
docker tag openroad/flow-ubuntu22.04-builder:agr-paper agr-openroad:paper
docker image inspect agr-openroad:paper --format '{{.Id}}' > backend-image-id.txt
echo "Built agr-openroad:paper; image identity saved in $work/backend-image-id.txt"
