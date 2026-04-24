"""Debug: find valid systems with closure and fc=m_i."""
import itertools

def all_configs(ms):
    return list(itertools.product(*(range(m) for m in ms)))

def privileged_set(config, fs, ms):
    n = len(ms)
    priv = []
    for i in range(n):
        L = config[(i-1) % n]
        S = config[i]
        R = config[(i+1) % n]
        if fs[i](L, S, R) != S:
            priv.append(i)
    return priv

def apply_move(config, i, fs, ms):
    n = len(ms)
    L = config[(i-1) % n]
    S = config[i]
    R = config[(i+1) % n]
    new_s = fs[i](L, S, R)
    lst = list(config)
    lst[i] = new_s
    return tuple(lst)

def extract_good_cycle(ms, fs):
    configs = all_configs(ms)
    good = []
    successor = {}
    for c in configs:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 1:
            mover = priv[0]
            nxt = apply_move(c, mover, fs, ms)
            nxt_priv = privileged_set(nxt, fs, ms)
            if len(nxt_priv) == 1:
                good.append(c)
                successor[c] = (nxt, mover)

    if not good:
        return None

    # Try to find cycle from each good config
    good_set = set(good)
    for start in good:
        cycle = []
        current = start
        seen = set()
        while current in good_set and current not in seen:
            seen.add(current)
            nxt, mover = successor[current]
            cycle.append((current, mover))
            current = nxt
        if current == start and len(cycle) == len(good):
            return cycle

    return None

# Dijkstra Sol 1 n=3
print("=== Dijkstra Sol 1, n=3 ===")
n = 3; K = 3; ms = [K]*n
def f0(L,S,R):
    if S == L: return (S+1) % K
    return S
def fi(L,S,R):
    if S != L: return L
    return S
fs = [f0, fi, fi]
cycle = extract_good_cycle(ms, fs)
if cycle:
    CL = len(cycle)
    fc = [0]*n
    for c,m in cycle: fc[m] += 1
    print(f"  Cycle length: {CL}, fc: {fc}, ms: {ms}")
    for step,(c,m) in enumerate(cycle):
        print(f"    {step}: {c} mover={m}")
else:
    # Check the structure: follow from first good config
    configs = all_configs(ms)
    good = []
    for c in configs:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 1:
            mover = priv[0]
            nxt = apply_move(c, mover, fs, ms)
            nxt_priv = privileged_set(nxt, fs, ms)
            if len(nxt_priv) == 1:
                good.append((c, mover, nxt))

    print(f"  Good configs with good successors: {len(good)}")
    # Find cycles
    succ = {}
    for c, m, nxt in good:
        succ[c] = (nxt, m)

    visited_all = set()
    for c, m, nxt in good:
        if c in visited_all:
            continue
        chain = []
        curr = c
        seen = set()
        while curr in succ and curr not in seen:
            seen.add(curr)
            visited_all.add(curr)
            nx, mv = succ[curr]
            chain.append((curr, mv))
            curr = nx
        if curr in seen:
            # Found a cycle
            idx = None
            for i, (cc, mm) in enumerate(chain):
                if cc == curr:
                    idx = i
                    break
            if idx is not None:
                cyc = chain[idx:]
                fc_cyc = [0]*n
                for cc, mm in cyc:
                    fc_cyc[mm] += 1
                print(f"  Sub-cycle len={len(cyc)}, fc={fc_cyc}")
                for step, (cc, mm) in enumerate(cyc[:20]):
                    print(f"    {step}: {cc} mover={mm}")

# Now: the REAL question is about abstract good cycles, not specific systems.
# The claim is about ANY good cycle. Let me work with the abstract model.
print("\n" + "="*60)
print("Abstract good cycle model")
print("="*60)

# A good cycle is defined abstractly: CL configs, each with exactly one mover,
# moverAt fires and produces the next config.
# fc(i) = m_i for all i.
# ms are {2,3} only.

# For n=3, ms=(3,3,3): CL = sum(ms) - n = 6 (? no, product / ?)
# Actually CL is just the length of the cycle. For Dijkstra sol1: CL = product - n + 1? No.
# CL is determined by the system. For ms = (3,3,3), typically CL = 3*3 = 9.
# For Sol 3 v1 ms=(2,3,...,3), CL = 3n-2.

# The claim says fc(i) = m_i. So each proc fires exactly m_i times.
# CL = sum(m_i).

# For ms = (3,3,3): CL = 9.
# For ms = (2,3,3): CL = 8.
# For ms = (2,3,3,3): CL = 11.

# Let me think about this differently. We need to work with
# the verifier to find actual valid systems.

# Use the project's verifier
import sys
sys.path.insert(0, './claude')
try:
    from verifier import verify_system as vs_orig
    print("  Loaded project verifier")
except:
    print("  Could not load project verifier")

# Let me use the known M_5=96 witness: ms=(2,2,2,3,4)
# But that has m=4, not {2,3} only.

# For pure {2,3} systems, the claim is about sub-threshold product.
# M_n = 4*3^(n-2), so sub-threshold = product < 4*3^(n-2).

# At n=5: 4*3^3 = 108. Sub-threshold products with ms in {2,3}:
# 2^5 = 32, 2^4*3 = 48, 2^3*3^2 = 72, 2^2*3^3 = 108 (threshold)
# Sub-threshold: 32, 48, 72. All have >= 3 binary.

# The claim is that NO valid system exists at sub-threshold product.
# So we can't find actual valid systems to test!

# The claim is about HYPOTHETICAL good cycles: if such a cycle existed,
# what would happen to Hamming-1 pairs?

# So I need to work with the ABSTRACT good cycle model.
# Generate all possible mover sequences and config sequences.

print("\nKey insight: The claim is about HYPOTHETICAL cycles.")
print("We need to analyze the abstract structure, not find valid systems.")
print()

# Abstract model: n procs on a ring, ms = (m_0,...,m_{n-1}) with m_i in {2,3}.
# A good cycle: sequence of configs c_0, c_1, ..., c_{CL-1}
# where CL = sum(m_i), and moverAt(s) fires to produce c_{s+1 mod CL}.
# fc(i) = m_i: each proc fires exactly m_i times.

# Hamming-1 property:
# If c_j and c_k differ at exactly position p, then for all t:
#   moverAt(j+t) = moverAt(k+t)

# This is a CONSTRAINT on the cycle structure.

# Proof approach: show that if movers disagree at some step,
# the Hamming distance between the "parallel" configs changes
# in a way that prevents the cycle from closing.

# Let's define:
# a_t = c_{(j+t) mod CL}
# b_t = c_{(k+t) mod CL}
# Both are subsequences of the SAME cycle.

# At t=0: H(a_0, b_0) = 1 (differ at p).
# At t=CL: a_CL = a_0, b_CL = b_0, so H(a_CL, b_CL) = 1.

# Mover at time t for the a-sequence: moverAt(j+t mod CL)
# Mover at time t for the b-sequence: moverAt(k+t mod CL)

# If a_t and b_t are at positions j+t and k+t in the cycle,
# the movers are just the movers at those positions in the cycle.

# The key: a_t is obtained from a_{t-1} by firing moverAt(j+t-1).
# And b_t is obtained from b_{t-1} by firing moverAt(k+t-1).
# These are DIFFERENT movers (generally), because j != k.

# So the claim is: if we advance a and b by their respective
# movers from the cycle, H(a_t, b_t) = 1 for all t.

# Actually wait. Let me re-read the claim.
# "moverAt(j+t) = moverAt(k+t) for all t"
# This means the mover at position j+t in the cycle equals
# the mover at position k+t in the cycle.
# i.e., the mover sequence is periodic with period k-j.

# Let d = k - j. The claim is: moverAt(s) = moverAt(s+d) for all s.
# This means the mover sequence has period d (dividing CL).

# And this follows from H(c_s, c_{s+d}) = 1 for all s
# (if configs at distance d always differ at exactly one position).

# Let me verify: if H(c_s, c_{s+d}) = 1 for all s,
# then at each step, the mover's context is either:
# (a) identical in both (if mover is far from the differing position) -> same mover
# (b) differs (if mover is near) -> but mover is the same proc, just different context

# Actually, the claim is about moverAt: the IDENTITY of the mover proc,
# not the context. So even if the context differs, if the SAME proc
# is privileged in both configs, that's fine.

# The subtlety: could it happen that proc m is privileged in c_s
# but NOT in c_{s+d}, and some other proc m' is privileged in c_{s+d}?
# If c_s and c_{s+d} differ at position p, then:
# - Any proc not in {p, p-1, p+1} has identical (L,S,R) -> same privilege status
# - So if moverAt(s) not in {p, p-1, p+1}: moverAt(s) is privileged in c_{s+d} too
#   But since c_{s+d} has exactly 1 privileged, moverAt(s) = moverAt(s+d). Done.
# - If moverAt(s) in {p, p-1, p+1}: the context differs. Need to show same proc is still privileged.

# This is the hard case. Let me think about it more carefully.

# Actually: if H(c_s, c_{s+d}) = 1 at position p_s (which may depend on s),
# then after both fire their movers:
# H(c_{s+1}, c_{s+d+1}) = ?

# Case 1: moverAt(s) = moverAt(s+d) = m, m not in {p_s, p_s-1, p_s+1}.
#   Both fire same proc m. c_s and c_{s+d} differ at p_s.
#   After firing m: c_{s+1} and c_{s+d+1} still differ at p_s (since m != p_s).
#   m's new value: f_m(L_m, S_m, R_m). Same context in both -> same new value.
#   So H stays 1 at position p_s.

# Case 2: moverAt(s) = moverAt(s+d) = m, m in {p_s, p_s-1, p_s+1}.
#   Both fire m, but m's context differs between c_s and c_{s+d}.
#   m's value changes to f_m(L, S, R) in c_s and f_m(L', S', R') in c_{s+d}.
#   Need to track what happens to H.

# Case 2a: m = p_s. S differs. After firing: S changes in both.
#   c_s[p] = v, c_{s+d}[p] = w, v != w.
#   After: c_{s+1}[p] = f(L, v, R), c_{s+d+1}[p] = f(L, w, R).
#   (L and R are same since only position p differs.)
#   Could be: f(L,v,R) = f(L,w,R) -> H drops to 0!
#   Or f(L,v,R) != f(L,w,R) -> H stays 1 at p.

# Hmm, so movers could agree but Hamming distance could change!
# And if H drops to 0 at some point, then c_s = c_{s+d},
# meaning the cycle has period d. Then moverAt(s) = moverAt(s+d) trivially.

# But what if H increases? If moverAt(s) != moverAt(s+d), then
# two different procs fire, potentially changing H by up to 2.

print("Moving to analytical tracking of Hamming evolution...")
print("Case analysis needed for mover in {p, p-1, p+1}.")
