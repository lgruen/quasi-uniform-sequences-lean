# exact lambda_jit(Lambda_v)^2 in 3D for given v (box enumeration; box radius B with B > sqrt(best)+1 certified)
import sys, itertools, math
def ljit2(v, p):
    best = None
    B = 2
    while True:
        for b in itertools.product(range(-B, B + 1), repeat=len(v)):
            if any(b) and sum(x * y for x, y in zip(v, b)) % p == 0:
                val = sum(max(0, abs(x) - 1) ** 2 for x in b)
                if best is None or val < best: best = val
        if best is not None and B >= math.isqrt(best) + 2: return best
        B *= 2
for p, v in [(13, (5, 3, 6)), (17, (4, 10, 16)), (23, (4, 14, 20)), (31, (10, 30, 7))]:
    l2 = ljit2(v, p); l = math.sqrt(l2)
    print(p, v, "ljit^2 =", l2, "P_{3K-1}: %.5f  P_3K incl: %.5f  allN: %.5f" % (l / p ** (1/3), l / p, l / p ** (1/3) / p))
