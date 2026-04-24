"""Generate Lean witness for ms=(2,2,2,3) product=24 n=4 (w4opt prefix)."""
from itertools import product as cartesian

n = 4
ms = [2, 2, 2, 3]
P = 24

# TF from verify_found_system.py
tf = {}
lines = """
f_0(0,0,0)=1 f_0(1,0,0)=0 f_0(2,0,0)=0 f_0(0,0,1)=0 f_0(1,0,1)=1 f_0(2,0,1)=0
f_0(0,1,0)=1 f_0(1,1,0)=0 f_0(2,1,0)=0 f_0(0,1,1)=1 f_0(1,1,1)=1 f_0(2,1,1)=0
f_1(0,0,0)=0 f_1(0,0,1)=0 f_1(0,1,0)=1 f_1(0,1,1)=0 f_1(1,0,0)=1 f_1(1,0,1)=0
f_1(1,1,0)=1 f_1(1,1,1)=1
f_2(0,0,0)=0 f_2(0,0,1)=1 f_2(0,0,2)=0 f_2(0,1,0)=1 f_2(0,1,1)=1 f_2(0,1,2)=0
f_2(1,0,0)=1 f_2(1,0,1)=0 f_2(1,0,2)=0 f_2(1,1,0)=1 f_2(1,1,1)=0 f_2(1,1,2)=0
f_3(0,0,0)=0 f_3(0,1,0)=0 f_3(0,2,0)=0 f_3(0,0,1)=0 f_3(0,1,1)=2 f_3(0,2,1)=2
f_3(1,0,0)=0 f_3(1,1,0)=2 f_3(1,2,0)=2 f_3(1,0,1)=1 f_3(1,1,1)=1 f_3(1,2,1)=0
""".strip().replace('\n', ' ').split()

for tok in lines:
    parts = tok.split('=')
    val = int(parts[1])
    lhs = parts[0]
    proc = int(lhs[2])
    args = lhs[lhs.index('(')+1:lhs.index(')')].split(',')
    L, S, R = int(args[0]), int(args[1]), int(args[2])
    tf[(proc, L, S, R)] = val

all_cfgs = list(cartesian(*(range(m) for m in ms)))

def priv(c):
    return [i for i in range(n) if tf[(i, c[(i-1)%n], c[i], c[(i+1)%n])] != c[i]]

def succ(c, p):
    r = list(c)
    r[p] = tf[(p, c[(p-1)%n], c[p], c[(p+1)%n])]
    return tuple(r)

# Good cycle
good = [c for c in all_cfgs if len(priv(c)) == 1]
good_set = set(good)
cur = good[0]
cycle = []
visited = set()
while cur not in visited:
    visited.add(cur)
    cycle.append(cur)
    ps = priv(cur)
    cur = succ(cur, ps[0])
assert len(cycle) == len(good) == 16

# Mixed-radix encoding: c0 + 2*c1 + 4*c2 + 8*c3 (but m3=3, so range is 0..23)
def encode(c):
    return c[0] + 2*c[1] + 4*c[2] + 8*c[3]

def decode(v):
    return (v%2, (v//2)%2, (v//4)%2, (v//8)%3)

cycle_codes = [encode(c) for c in cycle]
print(f"Good cycle codes: {cycle_codes}")
print(f"Good cycle length: {len(cycle_codes)}")

# Bad configs and rank
bad = [c for c in all_cfgs if c not in good_set]
bad_set = set(bad)

# Compute bad rank via iterative sink removal
remaining = set(bad)
rank = {}
r = 1
while remaining:
    sinks = set()
    for c in remaining:
        ps = priv(c)
        if all(succ(c, p) not in remaining for p in ps):
            sinks.add(c)
    assert sinks, f"Stuck with {len(remaining)} remaining"
    for c in sinks:
        rank[c] = r
    remaining -= sinks
    r += 1

# Verify rank decreases on every bad step
for c in bad:
    for p in priv(c):
        s = succ(c, p)
        if s in bad_set:
            assert rank[s] < rank[c], f"Rank doesn't decrease: {c}->{s}"

print(f"Bad configs: {len(bad)}, max rank: {max(rank.values())}")

# Build rank array indexed by code
rank_arr = [0] * P
for c in bad:
    rank_arr[encode(c)] = rank[c]
print(f"Rank array: {rank_arr}")

# --- Generate Lean code ---
print("\n\n--- LEAN CODE ---\n")

# w4optM
print("/-! ### Witness n=4 (optimal), ms=(2, 2, 2, 3), product=24 -/\n")
print("def w4optM (i : Fin 4) : Nat :=")
print("  match i.val with")
print("  | 0 => 2")
print("  | 1 => 2")
print("  | 2 => 2")
print("  | _ => 3\n")

print("def w4optSpec : RingSpec where")
print("  n := 4")
print("  n_ge_4 := by omega")
print("  m := w4optM")
print("  m_pos := by intro i; fin_cases i <;> simp [w4optM]\n")

# Transition tables per processor
for proc in range(n):
    left_m = ms[(proc-1)%n]
    self_m = ms[proc]
    right_m = ms[(proc+1)%n]
    print(f"private def w4optP{proc} (L S R : Nat) : Nat :=")
    print(f"  match L, S, R with")
    for L in range(left_m):
        for S in range(self_m):
            for R in range(right_m):
                val = tf[(proc, L, S, R)]
                print(f"  | {L}, {S}, {R} => {val}")
    print(f"  | _, _, _ => 0\n")

# w4optTrans
print("def w4optTrans : TransFn w4optSpec := fun i L S R =>")
print("  let v := match i.val with")
for proc in range(n):
    print(f"    | {proc} => w4optP{proc} L.val S.val R.val")
print(f"    | _ => 0")
print(f"  ⟨v % w4optSpec.m i, Nat.mod_lt _ (by fin_cases i <;> simp [w4optSpec, w4optM])⟩\n")

print("def w4optSystem : System := ⟨w4optSpec, w4optTrans⟩\n")

print(f"theorem w4opt_stateProduct : stateProduct w4optSpec = 24 := by")
print(f"  simp [stateProduct, w4optSpec, w4optM, Fin.prod_univ_succ]\n")

# Config encoding
print("def w4optCfg (x0 : Fin 2) (x1 : Fin 2) (x2 : Fin 2) (x3 : Fin 3) : Config w4optSpec")
print("  | ⟨0, _⟩ => x0")
print("  | ⟨1, _⟩ => x1")
print("  | ⟨2, _⟩ => x2")
print("  | ⟨3, _⟩ => x3\n")

print("def w4optCfgCode (c : Config w4optSpec) : Nat :=")
print("  (c ⟨0, by decide⟩).1 + 2 * ((c ⟨1, by decide⟩).1 + 2 * ((c ⟨2, by decide⟩).1 + 2 * ((c ⟨3, by decide⟩).1)))\n")

print("def w4optCfgOfCode (k : Nat) : Config w4optSpec :=")
print("  w4optCfg")
print("    ⟨k % 2, by omega⟩")
print("    ⟨(k / 2) % 2, by omega⟩")
print("    ⟨(k / 4) % 2, by omega⟩")
print("    ⟨(k / 8) % 3, by omega⟩\n")

# Good cycle
print(f"def w4optGoodCycleCodes : List Nat := {cycle_codes}\n")
print("def w4optGoodCycleConfigs : List (Config w4optSpec) :=")
print("  w4optGoodCycleCodes.map w4optCfgOfCode\n")

# GoodCycle proofs
print("theorem w4optGoodCycle_nonempty : w4optGoodCycleConfigs ≠ [] := by")
print("  simp [w4optGoodCycleConfigs, w4optGoodCycleCodes]\n")

print("theorem w4optGoodCycle_unique_privileged_aux :")
print("    ∀ c ∈ w4optGoodCycleConfigs,")
print("      (∃ i, privileged w4optSystem c i) ∧")
print("      (∀ i j, privileged w4optSystem c i → privileged w4optSystem c j → i = j) :=")
print("  by native_decide\n")

print("theorem w4optGoodCycle_unique_privileged :")
print("    ∀ c ∈ w4optGoodCycleConfigs, ∃! i, privileged w4optSystem c i := by")
print("  intro c hc")
print("  simpa [ExistsUnique] using w4optGoodCycle_unique_privileged_aux c hc\n")

print("theorem w4optGoodCycle_closed :")
print("    ∀ k : Fin w4optGoodCycleConfigs.length,")
print("      ∃ i,")
print("        privileged w4optSystem (w4optGoodCycleConfigs.get k) i ∧")
print("          w4optGoodCycleConfigs.get (nextIndex w4optGoodCycleConfigs k) =")
print("            move w4optSystem (w4optGoodCycleConfigs.get k) i := by")
print("  native_decide\n")

print("theorem w4optGoodCycle_distinct :")
print("    ∀ j₁ j₂ : Fin w4optGoodCycleConfigs.length,")
print("      w4optGoodCycleConfigs.get j₁ = w4optGoodCycleConfigs.get j₂ → j₁ = j₂ := by")
print("  native_decide\n")

print("def w4optGoodCycle : GoodCycle w4optSystem where")
print("  configs := w4optGoodCycleConfigs")
print("  nonempty := w4optGoodCycle_nonempty")
print("  unique_privileged := w4optGoodCycle_unique_privileged")
print("  closed := w4optGoodCycle_closed")
print("  distinct := w4optGoodCycle_distinct\n")

# Bad rank
print(f"def w4optBadRank (c : Config w4optSpec) : Nat :=")
print(f"  match w4optCfgCode c with")
for v in range(P):
    print(f"  | {v} => {rank_arr[v]}")
print(f"  | _ => 0\n")

print("theorem w4optBadRank_decreases (c c' : Config w4optSpec)")
print("    (hbad : c ∉ w4optGoodCycleConfigs)")
print("    (i : Fin w4optSpec.n)")
print("    (hpriv : privileged w4optSystem c i)")
print("    (hmove : c' = move w4optSystem c i)")
print("    (hnext : move w4optSystem c i ∉ w4optGoodCycleConfigs) :")
print("    w4optBadRank (move w4optSystem c i) < w4optBadRank c := by")
print("  native_decide +revert\n")

print("theorem w4optBadRank_decreases_step (c c' : Config w4optSpec) :")
print("    badStep w4optSystem w4optGoodCycle c' c → w4optBadRank c' < w4optBadRank c := by")
print("  intro ⟨hbad, hbad', ⟨i, hpriv, hmove⟩⟩")
print("  subst hmove")
print("  exact w4optBadRank_decreases c _ hbad i hpriv rfl hbad'\n")

print("theorem w4opt_converges : converges w4optSystem w4optGoodCycle := by")
print("  apply WellFounded.intro")
print("  intro c")
print("  apply (measure_wf w4optBadRank).wf.apply")
print("  intro c' hbad")
print("  exact w4optBadRank_decreases_step c c' hbad\n")

print("theorem w4opt_valid : valid w4optSystem := by")
print("  exact ⟨w4optGoodCycle, w4opt_converges⟩")
