"""j_check.py FILE Nmax -- the worst normalised separation J = min_{64<=N<=Nmax} delta(P_[N]) N^(1/3) of tab:practice for the
sequence given by a matrix file (format: practice/README.md): float64 points from the matrices (numpy, exact digit
arithmetic in the first floor(52/log2 p) digits), then the exact incremental toroidal minimum distance of every prefix
by mdist (practice/mdist.cpp, compiled to bin/mdist; the pipeline that re-checked tab:practice). Prints J and the N
where it is attained.  From the archive root:
    mkdir -p bin && g++ -O2 -std=c++17 -o bin/mdist practice/mdist.cpp
    uv run --with numpy python practice/j_check.py practice/residue_U_p31.txt 8388608"""
import sys, os, subprocess, numpy as np
fn, Nmax = sys.argv[1], int(sys.argv[2])
t = open(fn).read().split(); p, R, C = map(int, t[:3]); M = np.array(list(map(int, t[3:3 + 3 * R * C])), dtype=np.int64).reshape(3, R, C)
n = np.arange(Nmax, dtype=np.int64); dig = np.zeros((C, Nmax), dtype=np.int64); x = n.copy()
for j in range(C): dig[j] = x % p; x //= p
assert (x == 0).all()
R2 = min(R, int(52 / np.log2(p)))  # float64-exact digits
X = np.zeros((Nmax, 3))
for c in range(3):
    v = np.zeros(Nmax, dtype=np.int64)
    for i in range(R2): v = v * p + (M[c, i] @ dig) % p
    X[:, c] = v / float(p) ** R2
here = os.path.join(os.getcwd(), 'bin'); b = os.path.join(here, '_pts.bin'); out = os.path.join(here, '_drops.txt')
X.tofile(b); MD = os.path.join(here, 'mdist')
subprocess.run([MD, 'drops', b, '3', str(Nmax), out], check=True, capture_output=True); os.remove(b)
ev = [l.split() for l in open(out) if l.strip() and not l.startswith('#')]; os.remove(out)
Ns = [int(e[0]) for e in ev if e[0] != 'END']; d2 = [float(e[1]) for e in ev if e[0] != 'END']
best, at = 1e9, 0
for k, N in enumerate(Ns):
    if N < 64: continue
    c = d2[k] ** 0.5 * N ** (1 / 3)
    if c < best: best, at = c, N
# N=64 itself (running min holds from last drop <=64)
k = max(i for i, N in enumerate(Ns) if N <= 64); c64 = d2[k] ** 0.5 * 64 ** (1 / 3)
if c64 < best: best, at = c64, 64
print(f'{fn}: J = {best:.5f} at N = {at}')
