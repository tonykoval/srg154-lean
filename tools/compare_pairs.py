# Cross-check: Lean's pairs521 vs the paper's generator scripts/srg154_paper/regen_certificates.py (needed()).
import re, sys, collections
sys.path.insert(0, '/work/scripts/srg154_paper')
from regen_certificates import needed, kill
lean = [tuple(map(int, t)) for t in re.findall(r'\((-?\d+),\s*(-?\d+)\)', open('/work/out/lean154/pairs521_lean.txt').read())]
py = [(m, l) for kind, m, ab, ls in needed() for l in ls]
print('lean', len(lean), 'python', len(py))
print('same multiset:', collections.Counter(lean) == collections.Counter(py))
print('same order:', lean == py)
print('python verdicts:', collections.Counter(kill(m, l)[0] for m, l in py))
# second source: derivation-1 output out/srg154_rep2/hand_tools.txt
ht = [(int(a), int(b)) for a, b in re.findall(r'm=\s*(-?\d+) l=\s*(-?\d+)', open('/work/out/srg154_rep2/hand_tools.txt').read())]
print('hand_tools.txt', len(ht), 'same multiset as lean:', collections.Counter(ht) == collections.Counter(lean))
d1 = collections.Counter(ht) - collections.Counter(lean); d2 = collections.Counter(lean) - collections.Counter(ht)
print('only in hand_tools:', dict(d1)); print('only in lean:', dict(d2))
