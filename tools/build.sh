# usage: bash build.sh [target]   -- syncs /work/out/lean154/src -> /root/lean154 and builds with 4 cores
source /root/.elan/env
cd /root/lean154
cp -r /work/out/lean154/src/. /root/lean154/
T=${1:-Srg154}
start=$(date +%s)
taskset -c 0-3 lake build $T 2>&1 | grep -v "^✔\|^info: \[" | tail -60
echo "EXIT=${PIPESTATUS[0]} elapsed=$(( $(date +%s) - start ))s"
