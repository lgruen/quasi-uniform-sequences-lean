"""run_programs.py -- driver (no mathematics of its own): runs the search program's enumeration (search_lat.cpp, mode
"given v") and the audit's independent enumeration (audit_jit.cpp) on every row of check_vectors.tsv and compares their
exact lambda_jit(Lambda_v)^2 with the stored value; also the Korobov column (mode "kor" of both programs).
Compiles both programs into bin/ (relative to the current directory) with g++ -O2 -std=c++17 on first use.
    python3 residue_tables/run_programs.py          (from the archive root)
"""
import os, subprocess, re, math
HERE = os.path.dirname(os.path.abspath(__file__)); BIN = 'bin'
os.makedirs(BIN, exist_ok=True)
exe = {}
for name in ('search_lat', 'audit_jit'):
    exe[name] = os.path.join(BIN, name)
    if not os.path.exists(exe[name]):
        subprocess.run(['g++', '-O2', '-std=c++17', '-o', exe[name], os.path.join(HERE, name + '.cpp')], check=True)
rows = [l.rstrip('\n').split('\t') for l in open(os.path.join(HERE, 'check_vectors.tsv')) if l.strip() and not l.startswith('#')]
ok = True
for s, p, v, L, *_ in rows:
    out1 = subprocess.run([exe['search_lat'], p, s, v], capture_output=True, text=True).stdout
    out2 = subprocess.run([exe['audit_jit'], p, s, v], capture_output=True, text=True).stdout
    j1 = round(float(re.search(r'lambda_jit=([\d.]+)', out1).group(1)) ** 2)
    j2 = int(re.search(r'jit2=(\d+)', out2).group(1))
    good = j1 == j2 == int(L); ok &= good
    print('s=%s p=%5s v=%-22s stored %4s  search %4d  audit %4d %s' % (s, p, v, L, j1, j2, '' if good else '<-- MISMATCH'))
seen = set()
for s, p, v, L, srch, b, kor in rows:
    if kor.strip() == '-' or (s, p) in seen: continue
    seen.add((s, p))
    out1 = subprocess.run([exe['search_lat'], p, s, 'kor'], capture_output=True, text=True).stdout
    out2 = subprocess.run([exe['audit_jit'], p, s, 'kor'], capture_output=True, text=True).stdout
    j1 = round(float(re.search(r'lambda_jit=([\d.]+)', out1).group(1)) ** 2)
    j2 = int(re.search(r'jit2=(\d+)', out2).group(1))
    rho = int(round(int(p) ** (1 / int(s))))
    while rho ** int(s) > int(p): rho -= 1
    while (rho + 1) ** int(s) <= int(p): rho += 1
    good = j1 == j2 == (rho - 1) ** 2; ok &= good
    print('Korobov s=%s p=%5s rho=%d: search %d  audit %d  (rho-1)^2 = %d %s' % (s, p, rho, j1, j2, (rho - 1) ** 2, '' if good else '<-- MISMATCH'))
print('ALL OK' if ok else 'FAIL')
