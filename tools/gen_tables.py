# Parse Tables tab:lzero and tab:cert of docs/paper/srg154.tex into Lean data (pasted into PaperTables.lean).
import re
BS = chr(92)
tex = open('/work/docs/paper/srg154.tex', encoding='utf-8').read()
a = tex.index(BS + 'label{tab:lzero}'); b = tex.index(BS + 'end{longtable}', a)
lz = []
for line in tex[a:b].splitlines():
    line = line.strip()
    if not line.endswith(BS + BS):
        continue
    cells = [c.strip() for c in line[:-2].split('&')]
    if len(cells) == 4 and cells[0] in ('I', 'unit'):
        lz.append((int(cells[1]), int(cells[2]), [int(x) for x in cells[3].split(',')]))
a = tex.index(BS + 'label{tab:cert}'); b = tex.index(BS + 'end{longtable}', a)
rows = []
for line in tex[a:b].splitlines():
    line = line.strip()
    if not line.endswith(BS + BS) or line.startswith(BS):
        continue
    cells = [c.strip() for c in line[:-2].split('&')]
    if len(cells) != 9 or 'test' in cells[3]:
        continue
    ab, m, l, test, g, Q, S, t, data = cells
    num = lambda s: int(s.replace('$', ''))
    m, l, g, Q, S, t = map(num, (m, l, g, Q, S, t))
    if test == 'L1':
        tst = 'Test.L1'
    elif test == 'L2':
        vs = [] if 'emptyset' in data else re.findall(r'-?\d+', data.split('=')[1])
        tst = 'Test.L2 [' + ', '.join(vs) + ']'
    elif test == 'L3':
        p = re.findall(r'=(-?\d+)', data)
        tst = f'Test.L3 {p[0]} {p[1]}'
    else:
        tst = 'Test.special'
    rows.append(f'  ⟨{m}, {l}, {tst}, {g}, {Q}, {S}, {t}⟩')
print(len(lz), 'L0 rows;', len(rows), 'cert rows')
out = ['/-- Table `tab:lzero` as printed in the paper: `(m, ℓ_max, the ℓ passing (L0))`. -/',
       'def paperL0 : List (ℤ × ℕ × List ℤ) := [',
       ',\n'.join(f'  ({m}, {lm}, {ls})' for m, lm, ls in lz) + ']', '',
       '/-- Table `tab:cert` as printed in the paper: `⟨m, ℓ, test, γ, Q, S, t⟩`. -/',
       'def paperCert : List CertRow := [', ',\n'.join(rows) + ']']
open('/work/out/lean154/paper_tables_data.lean', 'w', encoding='utf-8').write('\n'.join(out) + '\n')
