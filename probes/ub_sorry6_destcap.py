"""
Verify destination-cap for Pn1:(2,0,0) c1=0: PhiFull(c') = fc(c') always.
Also check sorry 7 (c1=2) and the pattern.
"""
import itertools

# CUP-2 tables (same as analysis script)
def TBotVal(L,S,R):
    t={(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    return t.get((L,S,R),0)
def TLowVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    return t.get((L,S,R),0)
def TMidVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R),0)
def THighVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    return t.get((L,S,R),0)
def TTopVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    return t.get((L,S,R),0)

def output_val(n,i,L,S,R):
    if i==0:return TBotVal(L,S,R)
    if i==1:return TLowVal(L,S,R)
    if i==n-1:return TTopVal(L,S,R)
    if i==n-2:return THighVal(L,S,R)
    return TMidVal(L,S,R)

def move(n,c,i):
    c=list(c);L=c[(i-1)%n];S=c[i];R=c[(i+1)%n];c[i]=output_val(n,i,L,S,R);return tuple(c)

def is_privileged(n,c,i):
    L=c[(i-1)%n];S=c[i];R=c[(i+1)%n];return output_val(n,i,L,S,R)!=S

def fc(n,c):
    return sum(1 for j in range(n) if c[j]!=c[(j+1)%n])

def exp2_bit(n,j,a,b):return 1 if 2<=j and j+2<n and a==2 and b!=2 else 0
def int21_bit(n,j,a,b):return 1 if 2<=j and j+2<n and a==2 and b==1 else 0

def tp_inv(n,c):
    e=sum(exp2_bit(n,j,c[j],c[(j+1)%n]) for j in range(n))
    i=sum(int21_bit(n,j,c[j],c[(j+1)%n]) for j in range(n))
    w=sum(j*exp2_bit(n,j,c[j],c[(j+1)%n]) for j in range(n))
    return(e,i,w)

def tp_reachable(n,c):
    tp=tp_inv(n,c);visited={c};q=[c]
    while q:
        d=q.pop(0)
        for i in range(n):
            if is_privileged(n,d,i):
                e=move(n,d,i)
                if tp_inv(n,e)==tp and e not in visited:
                    visited.add(e);q.append(e)
    return visited

def phi_full(n,c):
    return max(fc(n,d) for d in tp_reachable(n,c))

# Check sorry 6: c1=0
n = 9
print("=== Sorry 6: Pn1:(2,0,0) c1=0 ===")
print("Checking: PhiFull(c') = fc(c') for all configs")
all_destcap = True
for interior in itertools.product(range(3), repeat=5):
    c = (0, 0) + interior + (2, 0)
    if not is_privileged(n, c, 8): continue
    cp = move(n, c, 8)
    tpr = tp_reachable(n, cp)
    fc_cp = fc(n, cp)
    max_fc = max(fc(n, d) for d in tpr)
    if max_fc > fc_cp:
        print(f"  DESTCAP FAIL: c={c}, c'={cp}, fc(c')={fc_cp}, max_reachable_fc={max_fc}")
        all_destcap = False
print(f"Destination-cap holds: {all_destcap}")
print(f"Implication: PhiFull(c') = fc(c') always, so PhiFull(c') < PhiFull(c)")
print()

# Check sorry 7: c1=2
print("=== Sorry 7: Pn1:(2,0,0) c1=2 ===")
all_destcap7 = True
pf_eq_count = 0
for interior in itertools.product(range(3), repeat=5):
    c2, c3, c4, c5, c6 = interior
    # c1=2 means s.c1=2, which is c[1]=2
    # But wait - position 1 is "low" with 3 states, so c[1] ∈ {0,1,2}
    c = (0, 2, c2, c3, c4, c5, c6, 2, 0)
    # Position 1 has value 2 - check if this is valid
    # Actually we need to re-check: c1 is the boundary 6-tuple field c1,
    # which corresponds to c[1] in the config
    if not is_privileged(n, c, 8): continue
    cp = move(n, c, 8)
    fc_cp = fc(n, cp)
    fc_c = fc(n, c)
    if fc_cp != fc_c + 1: continue  # Need fc gain +1

    tp_c = tp_inv(n, c)
    tp_cp = tp_inv(n, cp)
    if tp_c != tp_cp: continue  # Need TP preserved

    tpr = tp_reachable(n, cp)
    max_fc = max(fc(n, d) for d in tpr)
    if max_fc > fc_cp:
        print(f"  DESTCAP FAIL: c={c}, c'={cp}, fc(c')={fc_cp}, max={max_fc}")
        all_destcap7 = False

    pf_c = phi_full(n, c)
    pf_cp = phi_full(n, cp)
    if pf_c == pf_cp:
        pf_eq_count += 1
        print(f"  PF EQ: c={c}, pf={pf_c}")

print(f"Sorry 7 destination-cap holds: {all_destcap7}")
print(f"Sorry 7 PhiFull equality count: {pf_eq_count}")
print()

# Key mechanism: WHY does PhiFull drop?
print("=== Mechanism: why PhiFull(c') < PhiFull(c) ===")
c = (0, 0, 0, 0, 0, 0, 0, 2, 0)
cp = move(n, c, 8)
print(f"c = {c}, fc={fc(n,c)}")
print(f"c' = {cp}, fc={fc(n,cp)}")

tpr_c = tp_reachable(n, c)
tpr_cp = tp_reachable(n, cp)
print(f"|TP-reachable(c)| = {len(tpr_c)}")
print(f"|TP-reachable(c')| = {len(tpr_cp)}")

# Show the maximizer of PhiFull(c) is NOT in tp_reachable(c')
pf_c = phi_full(n, c)
maximizers_c = [d for d in tpr_c if fc(n, d) == pf_c]
print(f"PhiFull(c) = {pf_c}, maximizers: {len(maximizers_c)}")
for m in maximizers_c:
    in_cp = m in tpr_cp
    print(f"  maximizer {m}: fc={fc(n,m)}, in TP-reachable(c'): {in_cp}")

# What IS the TP-reachable set from c'?
print(f"\nTP-reachable from c' (showing fc):")
for d in sorted(tpr_cp):
    print(f"  {d}: fc={fc(n,d)}")
