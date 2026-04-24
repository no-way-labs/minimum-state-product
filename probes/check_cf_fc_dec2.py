#!/usr/bin/env python3
"""Check: are fc-nondec 6-tuple transitions a superset of nonneg CF boundary transitions?"""
import sys, os, re
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from itertools import product as cartesian
from collections import defaultdict


def encode6(c, n):
    return ((((c[0] * 3 + c[1]) * 3 + c[2]) * 3 + c[n-3]) * 3 + c[n-2]) * 2 + c[n-1]


def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def delta_fc_local(L, S, R, S_new):
    return ((1 if L != S_new else 0) - (1 if L != S else 0) +
            (1 if S_new != R else 0) - (1 if S != R else 0))


# Build fc-nondec 6-tuple edge set (from compute_full_rank.py logic)
def TBotVal(L,S,R):
    t={(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    return t.get((L,S,R),0)
def TLowVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    return t.get((L,S,R),0)
def TMidVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R),0)
def THighVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    return t.get((L,S,R),0)
def TTopVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    return t.get((L,S,R),0)


def encode(c0, c1, c2, cN3, cN2, cN1):
    return ((((c0 * 3 + c1) * 3 + c2) * 3 + cN3) * 3 + cN2) * 2 + cN1


fc_nondec_edges = set()
for c0 in range(2):
 for c1 in range(3):
  for c2 in range(3):
   for cN3 in range(3):
    for cN2 in range(3):
     for cN1 in range(2):
      se = encode(c0,c1,c2,cN3,cN2,cN1)
      nc0=TBotVal(cN1,c0,c1)
      if nc0!=c0 and delta_fc_local(cN1,c0,c1,nc0)>=0:
        fc_nondec_edges.add((se, encode(nc0,c1,c2,cN3,cN2,cN1)))
      nc1=TLowVal(c0,c1,c2)
      if nc1!=c1 and delta_fc_local(c0,c1,c2,nc1)>=0:
        fc_nondec_edges.add((se, encode(c0,nc1,c2,cN3,cN2,cN1)))
      for c3 in range(3):
        nc2=TMidVal(c1,c2,c3)
        if nc2!=c2 and delta_fc_local(c1,c2,c3,nc2)>=0:
          fc_nondec_edges.add((se, encode(c0,c1,nc2,cN3,cN2,cN1)))
      for cn4 in range(3):
        ncN3=TMidVal(cn4,cN3,cN2)
        if ncN3!=cN3 and delta_fc_local(cn4,cN3,cN2,ncN3)>=0:
          fc_nondec_edges.add((se, encode(c0,c1,c2,ncN3,cN2,cN1)))
      ncN2=THighVal(cN3,cN2,cN1)
      if ncN2!=cN2 and delta_fc_local(cN3,cN2,cN1,ncN2)>=0:
        fc_nondec_edges.add((se, encode(c0,c1,c2,cN3,ncN2,cN1)))
      ncN1=TTopVal(cN2,cN1,c0)
      if ncN1!=cN1 and delta_fc_local(cN2,cN1,c0,ncN1)>=0:
        fc_nondec_edges.add((se, encode(c0,c1,c2,cN3,cN2,ncN1)))

print(f'Fc-nondec 6-tuple edges: {len(fc_nondec_edges)}')

# Now check: for each n, are nonneg CF boundary steps covered?
for n_val in range(5, 10):
    ms, fs = build_system(n_val)
    n = n_val
    configs = list(cartesian(*[range(m) for m in ms]))
    fc_cache = {c: fc(c, n) for c in configs}

    tp_edges = []
    for c_tup in configs:
        c_list = list(c_tup)
        for i in range(n):
            L = c_list[(i - 1) % n]
            S = c_list[i]
            R = c_list[(i + 1) % n]
            new_val = fs[i](L, S, R)
            if new_val != S:
                s_list = list(c_list)
                s_list[i] = new_val
                s_tup = tuple(s_list)
                dfc = fc_cache[s_tup] - fc_cache[c_tup]
                tp_edges.append((c_tup, s_tup, i, dfc))

    tp_adj = defaultdict(list)
    tp_nodes = set()
    for c, s, pos, dfc in tp_edges:
        tp_adj[c].append(s)
        tp_nodes.add(c)
        tp_nodes.add(s)

    g = {c: 0 for c in tp_nodes}
    for _ in range(len(tp_nodes) + 1):
        changed = False
        for c in tp_nodes:
            for s in tp_adj.get(c, []):
                val = fc_cache[s] - fc_cache[c] + g[s]
                if val > g[c]:
                    g[c] = val
                    changed = True
        if not changed:
            break
    phi = {c: fc_cache[c] + g[c] for c in tp_nodes}

    missing = 0
    total_nonneg_bnd = 0
    missing_examples = []
    for c, s, pos, dfc in tp_edges:
        if phi.get(s, 0) == phi.get(c, 0) and dfc >= 0:
            e_c = encode6(c, n)
            e_s = encode6(s, n)
            if e_c != e_s:
                total_nonneg_bnd += 1
                if (e_c, e_s) not in fc_nondec_edges:
                    missing += 1
                    if len(missing_examples) < 3:
                        missing_examples.append((c, s, pos, dfc, e_c, e_s))

    print(f'n={n}: nonneg CF bnd changed={total_nonneg_bnd}, not in fc_nondec={missing}')
    for ex in missing_examples:
        c, s, pos, dfc, ec, es = ex
        print(f'  Example: pos={pos}, dfc={dfc}, c={c}, s={s}, 6t=({ec},{es})')
        # Check local delta
        L = c[(pos-1) % n]
        S = c[pos]
        R = c[(pos+1) % n]
        new_val = s[pos]
        local_d = delta_fc_local(L, S, R, new_val)
        print(f'    L={L}, S={S}, R={R}, new={new_val}, local_delta={local_d}')
