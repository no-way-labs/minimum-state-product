"""
Trace which fc-positive step types (B1-B5) occur in TP-reachable from c'
for the Pn1:(2,0,0) c1=0 case.
"""
import itertools

# Tables (compact)
def TBotVal(L,S,R):return{(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}.get((L,S,R),0)
def TLowVal(L,S,R):return{(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}.get((L,S,R),0)
def TMidVal(L,S,R):return{(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}.get((L,S,R),0)
def THighVal(L,S,R):return{(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}.get((L,S,R),0)
def TTopVal(L,S,R):return{(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}.get((L,S,R),0)

def outval(n,i,L,S,R):
    if i==0:return TBotVal(L,S,R)
    if i==1:return TLowVal(L,S,R)
    if i==n-1:return TTopVal(L,S,R)
    if i==n-2:return THighVal(L,S,R)
    return TMidVal(L,S,R)

def move(n,c,i):c=list(c);c[i]=outval(n,i,c[(i-1)%n],c[i],c[(i+1)%n]);return tuple(c)
def priv(n,c,i):return outval(n,i,c[(i-1)%n],c[i],c[(i+1)%n])!=c[i]
def fc(n,c):return sum(1 for j in range(n) if c[j]!=c[(j+1)%n])
def e2b(n,j,a,b):return 1 if 2<=j and j+2<n and a==2 and b!=2 else 0
def tpinv(n,c):
    e=sum(e2b(n,j,c[j],c[(j+1)%n]) for j in range(n))
    i21=sum(1 if 2<=j and j+2<n and c[j]==2 and c[(j+1)%n]==1 else 0 for j in range(n))
    w=sum(j*e2b(n,j,c[j],c[(j+1)%n]) for j in range(n))
    return(e,i21,w)

n = 9
print(f"=== Mechanism analysis at n={n} ===")

# Check ALL starting configs for sorry 6
all_fc_pos_types = set()
all_ok = True

for interior in itertools.product(range(3), repeat=5):
    c = (0, 0) + interior + (2, 0)
    cp = move(n, c, 8)
    tp0 = tpinv(n, cp)
    fc_cp = fc(n, cp)

    # BFS through TP-reachable from c'
    visited = {cp}
    queue = [cp]
    while queue:
        d = queue.pop(0)
        for i in range(n):
            if priv(n, d, i):
                e = move(n, d, i)
                if tpinv(n, e) == tp0 and e not in visited:
                    visited.add(e)
                    queue.append(e)
                    # Check if this step is fc-positive
                    if fc(n, e) > fc(n, d):
                        L, S, R = d[(i-1)%n], d[i], d[(i+1)%n]
                        # Classify
                        if i == 0 and L == 0 and S == 0 and R == 0:
                            typ = "B1"
                        elif i == 0 and L == 1 and S == 1 and R == 2:
                            typ = "B2"
                        elif i == n-2 and L == 1 and S == 1 and R == 1:
                            typ = "B3"
                        elif i == n-1 and L == 2 and S == 0 and R == 0:
                            typ = "B4"
                        elif 2 <= i and i+2 < n and L == 2 and S == 1 and R == 1:
                            typ = f"B5@{i}"
                        else:
                            typ = f"UNKNOWN@{i}(L={L},S={S},R={R})"
                        all_fc_pos_types.add(typ)
                        # Check if fc exceeds fc(c')
                        if fc(n, e) > fc_cp:
                            print(f"  BOUND VIOLATION: c={c}, d={d}, e={e}, fc(e)={fc(n,e)}, fc(c')={fc_cp}, type={typ}")
                            all_ok = False

    max_fc = max(fc(n, d) for d in visited)
    if max_fc > fc_cp:
        print(f"  DESTCAP FAIL: c={c}, max={max_fc}, fc(c')={fc_cp}")
        all_ok = False

print(f"\nFc-positive TP step types encountered: {sorted(all_fc_pos_types)}")
print(f"Destination-cap holds for all: {all_ok}")
print()

# Now check: what invariant holds for ALL TP-reachable configs?
print("=== Checking boundary invariants ===")
for interior in [(0,0,0,0,0), (1,0,1,0,1), (2,1,0,1,2), (0,1,2,1,0)]:
    c = (0, 0) + interior + (2, 0)
    cp = move(n, c, 8)
    tp0 = tpinv(n, cp)
    visited = {cp}
    queue = [cp]
    while queue:
        d = queue.pop(0)
        for i in range(n):
            if priv(n, d, i):
                e = move(n, d, i)
                if tpinv(n, e) == tp0 and e not in visited:
                    visited.add(e)
                    queue.append(e)

    print(f"\nc = {c}, c' = {cp}")
    print(f"  fc(c') = {fc(n, cp)}")
    print(f"  |TP-reach| = {len(visited)}")
    max_fc_reach = max(fc(n, d) for d in visited)
    print(f"  max fc in TP-reach = {max_fc_reach}")
    # Check d[0], d[1] values
    d0_vals = set(d[0] for d in visited)
    d1_vals = set(d[1] for d in visited)
    dn1_vals = set(d[n-1] for d in visited)
    dn2_vals = set(d[n-2] for d in visited)
    print(f"  d[0] values: {sorted(d0_vals)}")
    print(f"  d[1] values: {sorted(d1_vals)}")
    print(f"  d[n-2] values: {sorted(dn2_vals)}")
    print(f"  d[n-1] values: {sorted(dn1_vals)}")
    # When d[1]=2, what is d[2]?
    d2_when_d1_is_2 = set(d[2] for d in visited if d[1] == 2)
    if d2_when_d1_is_2:
        print(f"  When d[1]=2, d[2] ∈ {sorted(d2_when_d1_is_2)}")
    # Check B1/B3/B4 preconditions
    for d in visited:
        # B1: d[n-1]=0, d[0]=0, d[1]=0
        if d[n-1]==0 and d[0]==0 and d[1]==0 and priv(n,d,0):
            e = move(n,d,0)
            if tpinv(n,e)==tp0:
                print(f"  B1 possible: d={d}, fc={fc(n,d)}, fc(e)={fc(n,e)}")
        # B3: d[n-3]=1, d[n-2]=1, d[n-1]=1
        if d[n-3]==1 and d[n-2]==1 and d[n-1]==1 and priv(n,d,n-2):
            e = move(n,d,n-2)
            if tpinv(n,e)==tp0:
                print(f"  B3 possible: d={d}, fc={fc(n,d)}, fc(e)={fc(n,e)}")
        # B4: d[n-2]=2, d[n-1]=0, d[0]=0
        if d[n-2]==2 and d[n-1]==0 and d[0]==0 and priv(n,d,n-1):
            e = move(n,d,n-1)
            if tpinv(n,e)==tp0:
                print(f"  B4 possible: d={d}, fc={fc(n,d)}, fc(e)={fc(n,e)}")
