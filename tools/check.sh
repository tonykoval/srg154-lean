# usage: bash check.sh Srg154/File.lean  -- sync and elaborate one file, print errors
source /root/.elan/env
cp /work/out/lean154/src/Srg154/*.lean /root/lean154/Srg154/
cp /work/out/lean154/src/Srg154.lean /root/lean154/
cd /root/lean154
start=$(date +%s)
taskset -c 0-3 lake env lean "$1" 2>&1 | grep -v "push_neg\|^If you\|^open Lean\|^macro\|^  \`(tactic\|^\`\`\`" | head -${2:-80}
echo "elapsed=$(( $(date +%s) - start ))s"
