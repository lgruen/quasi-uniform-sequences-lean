"""run_programs.py -- driver (no mathematics) for the second and third programs of thm:p7 (Table tab:ca). From the archive root,
after  mkdir -p bin && g++ -O2 -std=c++17 -o bin/audit_cert p7_graph_certificate/code/audit_cert.cpp
                    && g++ -O2 -std=c++17 -o bin/li3 p7_graph_certificate/code/li3.cpp :
    python3 p7_graph_certificate/code/run_programs.py [G_JSON] [Q_JSON] [KMAX]
(defaults: p7_graph_certificate/G_sym_p7.json, p7_graph_certificate/J3_p7_graph_reference.txt.Q.json if present, else
the .Q.json written by verify_cert3.py next to the rebuilt witness, KMAX = 140).
(2) audit_cert: LB(w) of the table w, minimum over all 26 steps and all triples of the table in every column (does not
    use the frame).  Expected: minS 1, LB 0.142857 (= 1/7).
(3) li3 eval: the bound LB_K from the actual responses of the archived instance (cube roots of unity as places, theta = 1,
    the series Q of the witness), for K = 1..KMAX; LB_K is a running minimum over carry lengths <= K, so LB_4 = LB_KMAX
    = 1/7 means LB_K = 1/7 for 4 <= K <= KMAX."""
import sys, os, json, subprocess
G = sys.argv[1] if len(sys.argv) > 1 else 'p7_graph_certificate/G_sym_p7.json'
Qd = [f for f in ('p7_graph_certificate/J3_p7_graph_reference.txt.Q.json', 'p7_graph_certificate/J3_p7_graph_rebuilt.txt.Q.json') if os.path.exists(f)]
Q = sys.argv[2] if len(sys.argv) > 2 else Qd[0]
K = int(sys.argv[3]) if len(sys.argv) > 3 else 140
d = json.load(open(G)); p = d['p']
inp = f'{p}\n' + ''.join(f'{len(d["F"][c])}\n' + ''.join(f'{o} {x1} {x2}\n' for o, x1, x2 in d['F'][c]) for c in range(3))
print('(2) audit_cert on', G, ':', subprocess.run(['bin/audit_cert'], input=inp, capture_output=True, text=True, check=True).stdout.strip())
q = json.load(open(Q))['Q']; assert q[0] == q[1] == q[2] and q[0][0] == 1, 'li3 needs the symmetric scramble (one series Q)'
assert d['theta'] == 1 and sorted(x % p for x in d['places']) == [1, 2, 4], 'li3 needs the cube roots of unity and theta = 1'
out = subprocess.run(['bin/li3', 'eval', str(p), '1', str(K)] + [str(x) for x in q[0][1:K + 1]], capture_output=True, text=True, check=True).stdout
print('(3) li3 eval, LB_K from the actual responses:'); print(out.rstrip())
