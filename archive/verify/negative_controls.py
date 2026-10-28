r"""negative_controls.py -- corrupted copies of archived window-system records must be rejected by verify_designs.py.

For every record of the given files two kinds of corruption are made, one at a time:
  (a) one stored cross kappa_{c<-j} (c != j) changed by +1;
  (b) one own window W_{j<-j} shortened by one at its lower or at its upper end (if it has at least two elements).
Each corrupted record is checked by the same function as the archived ones (verify_designs.verify). A change (a) must
always be rejected. A shortening (b) is rejected whenever the stored own window is minimal at that end; if the
shortened record still satisfies every check (including the stored exact window bound minS), it is reported as
ACCEPTED: then it is itself a valid window system, i.e. the stored own window was longer than needed at that end.
usage (from the archive root): python3 verify/negative_controls.py FILE...
"""
import sys, os, copy
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import verify_designs as V

def corruptions(name, d):
    s = d['s']
    for c in range(s):
        for j in range(s):
            if c != j:
                e = copy.deepcopy(d); e['krow'][c][j] += 1
                yield 'cross', f'{name} kappa[{c}<-{j}]+1', e
    for j in range(s):
        lo, hi = d['W'][j][j]
        if hi - lo + 1 < 2: continue
        for end, w in (('lo', (lo + 1, hi)), ('hi', (lo, hi - 1))):
            e = copy.deepcopy(d); e['W'][j][j] = w
            yield 'own', f'{name} own window {j} shortened at {end}', e

if __name__ == '__main__':
    if not os.path.exists(V.HELPER): import subprocess; subprocess.run(['g++', '-O3', '-o', V.HELPER, V.HELPER + '.cpp'], check=True)
    base, cases = [], []
    for fn in sys.argv[1:]:
        for name, d in V.records(fn):
            base.append((name, d)); cases += list(corruptions(name, d))
    lines, npass = V.verify(base, V.HELPER)
    assert npass == len(base), 'an uncorrupted record fails'
    lines, _ = V.verify([(lab, e) for _, lab, e in cases], V.HELPER)
    cnt = {'cross': [0, 0], 'own': [0, 0]}
    for (kind, lab, _), ln in zip(cases, lines):
        rej = ln.startswith('FAIL'); cnt[kind][0] += 1; cnt[kind][1] += rej
        if kind == 'cross' and not rej: print('NOT REJECTED (error):', lab)
        if kind == 'own' and not rej: print('ACCEPTED (stored own window longer than needed):', lab)
    print(f"records: {len(base)} (all PASS uncorrupted)")
    print(f"cross changed by one: {cnt['cross'][1]}/{cnt['cross'][0]} rejected")
    print(f"own window shortened by one: {cnt['own'][1]}/{cnt['own'][0]} rejected, {cnt['own'][0] - cnt['own'][1]} accepted")
    sys.exit(0 if cnt['cross'][0] == cnt['cross'][1] else 1)
