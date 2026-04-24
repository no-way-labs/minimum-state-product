"""Generate Lean 4 witness for ms=(2,2,2,3) product=24 system at n=4.

Reads TF data from verify_found_system.py, computes good cycle and bad ranks,
outputs Lean code following the w4 pattern in SmallN/Defs.lean with w4opt prefix.
"""
from itertools import product as cartesian

n = 4
ms = [2, 2, 2, 3]
P = 1
for m in ms:
    P *= m
assert P == 24

# Build TF from the verified system
tf = {}
lines_raw = """
f_0(0,0,0)=1
f_0(1,0,0)=0
f_0(2,0,0)=0
f_0(0,0,1)=0
f_0(1,0,1)=1
f_0(2,0,1)=0
f_0(0,1,0)=1
f_0(1,1,0)=0
f_0(2,1,0)=0
f_0(0,1,1)=1
f_0(1,1,1)=1
f_0(2,1,1)=0
f_1(0,0,0)=0
f_1(0,0,1)=0
f_1(0,1,0)=1
f_1(0,1,1)=0
f_1(1,0,0)=1
f_1(1,0,1)=0
f_1(1,1,0)=1
f_1(1,1,1)=1
f_2(0,0,0)=0
f_2(0,0,1)=1
f_2(0,0,2)=0
f_2(0,1,0)=1
f_2(0,1,1)=1
f_2(0,1,2)=0
f_2(1,0,0)=1
f_2(1,0,1)=0
f_2(1,0,2)=0
f_2(1,1,0)=1
f_2(1,1,1)=0
f_2(1,1,2)=0
f_3(0,0,0)=0
f_3(0,1,0)=0
f_3(0,2,0)=0
f_3(0,0,1)=0
f_3(0,1,1)=2
f_3(0,2,1)=2
f_3(1,0,0)=0
f_3(1,1,0)=2
f_3(1,2,0)=2
f_3(1,0,1)=1
f_3(1,1,1)=1
f_3(1,2,1)=0
""".strip().split('\n')

for line in lines_raw:
    parts = line.split('=')
    val = int(parts[1])
    lhs = parts[0]
    proc = int(lhs[2])
    args = lhs[lhs.index('(')+1:lhs.index(')')].split(',')
    L, S, R = int(args[0]), int(args[1]), int(args[2])
    tf[(proc, L, S, R)] = val

# Enumerate all configs
all_cfgs = list(cartesian(*(range(m) for m in ms)))
assert len(all_cfgs) == P

def priv(c):
    return [i for i in range(n)
            if tf[(i, c[(i-1)%n], c[i], c[(i+1)%n])] != c[i]]

def succ(c, p):
    r = list(c)
    r[p] = tf[(p, c[(p-1)%n], c[p], c[(p+1)%n])]
    return tuple(r)

# Identify good and bad configs
good = [c for c in all_cfgs if len(priv(c)) == 1]
bad = [c for c in all_cfgs if len(priv(c)) >= 2]
print(f"Good: {len(good)}, Bad: {len(bad)}")

# Build good cycle
good_set = set(good)
visited = set()
cur = good[0]
cycle = []
while cur not in visited:
    visited.add(cur)
    cycle.append(cur)
    ps = priv(cur)
    cur = succ(cur, ps[0])
assert len(visited) == len(good), f"Cycle {len(visited)} != good {len(good)}"
print(f"Good cycle length: {len(cycle)}")
for i, c in enumerate(cycle):
    ps = priv(c)
    print(f"  {i}: {c} priv={ps}")

# Mixed-radix encoding for (2,2,2,3)
# code = x0 + 2*x1 + 4*x2 + 8*x3  (same as w4 but last digit is mod 3 not mod 4)
def encode(c):
    return c[0] + 2*c[1] + 4*c[2] + 8*c[3]

def decode(k):
    x0 = (k // 1) % 2
    x1 = (k // 2) % 2
    x2 = (k // 4) % 2
    x3 = (k // 8) % 3
    return (x0, x1, x2, x3)

# Verify encoding round-trips
for c in all_cfgs:
    assert decode(encode(c)) == c, f"Round-trip failed for {c}"

cycle_codes = [encode(c) for c in cycle]
print(f"Good cycle codes: {cycle_codes}")

# Build bad-rank function
# We need: for every bad config c, for every privileged proc p,
#   if succ(c,p) is also bad, then rank(succ(c,p)) < rank(c)
# Use iterative sink removal to assign ranks

bad_set = set(bad)
rank = {}
remaining = set(bad)
current_rank = 1

while remaining:
    # Find configs where ALL successors are either good or already ranked
    sinks = set()
    for c in remaining:
        ps = priv(c)
        all_resolved = True
        for p in ps:
            s = succ(c, p)
            if s in remaining:
                all_resolved = False
                break
        if all_resolved:
            sinks.add(c)
    assert sinks, f"No sinks found with {len(remaining)} remaining"
    for c in sinks:
        rank[c] = current_rank
    remaining -= sinks
    current_rank += 1

print(f"\nBad ranks (max {max(rank.values())}):")
for c in sorted(rank.keys()):
    print(f"  {c} code={encode(c)} rank={rank[c]}")

# Verify bad rank decreases
print("\nVerifying bad rank decreases...")
for c in bad:
    ps = priv(c)
    for p in ps:
        s = succ(c, p)
        if s in bad_set:
            assert rank[s] < rank[c], f"FAIL: {c} ->{p}-> {s}, rank {rank[c]} -> {rank[s]}"
print("PASS: all bad steps decrease rank")

# Also verify: bad configs that step to good get rank >= 1 (which they do since min rank = 1)
# And good configs get rank 0
print("PASS: all good configs will get rank 0")

# Build rank values list (indexed by code)
# max code = 8*2 + 4 + 2 + 1 = 23 for ms=(2,2,2,3)
max_code = 8 * (ms[3]-1) + 4 * (ms[2]-1) + 2 * (ms[1]-1) + (ms[0]-1)
print(f"Max code: {max_code}")
rank_vals = []
for k in range(max_code + 1):
    c = decode(k)
    # Check if valid config
    if all(c[i] < ms[i] for i in range(n)):
        if c in rank:
            rank_vals.append(rank[c])
        else:
            rank_vals.append(0)  # good config
    else:
        rank_vals.append(0)  # invalid code

print(f"Rank values: {rank_vals}")

# ---- Generate Lean code ----
print("\n" + "="*70)
print("LEAN CODE OUTPUT")
print("="*70)

lean = []

lean.append('/-! ### Witness n=4, ms=(2, 2, 2, 3), product=24 -/')
lean.append('')

# w4optM
lean.append('def w4optM (i : Fin 4) : Nat :=')
lean.append('  match i.val with')
lean.append('  | 0 => 2')
lean.append('  | 1 => 2')
lean.append('  | 2 => 2')
lean.append('  | _ => 3')
lean.append('')

# w4optSpec
lean.append('def w4optSpec : RingSpec where')
lean.append('  n := 4')
lean.append('  n_ge_4 := by omega')
lean.append('  m := w4optM')
lean.append('  m_pos := by intro i; fin_cases i <;> simp [w4optM]')
lean.append('')

# Generate processor tables
for proc in range(n):
    pname = f'w4optP{proc}'
    lean.append(f'private def {pname} (L S R : Nat) : Nat :=')
    lean.append(f'  match L, S, R with')

    # Get the domain for this processor
    m_left = ms[(proc - 1) % n]
    m_self = ms[proc]
    m_right = ms[(proc + 1) % n]

    for L_val in range(m_left):
        for S_val in range(m_self):
            for R_val in range(m_right):
                val = tf[(proc, L_val, S_val, R_val)]
                lean.append(f'  | {L_val}, {S_val}, {R_val} => {val}')

    lean.append(f'  | _, _, _ => 0')
    lean.append('')

# w4optOutVal
lean.append('def w4optOutVal (i L S R : Nat) : Nat :=')
lean.append('  match i with')
lean.append('  | 0 => w4optP0 L S R')
lean.append('  | 1 => w4optP1 L S R')
lean.append('  | 2 => w4optP2 L S R')
lean.append('  | _ => w4optP3 L S R')
lean.append('')

# w4optOutVal_lt
lean.append('private lemma w4optOutVal_lt (i : Fin 4)')
lean.append('    (L : Fin (w4optSpec.m (left i)))')
lean.append('    (S : Fin (w4optSpec.m i))')
lean.append('    (R : Fin (w4optSpec.m (right i))) :')
lean.append('    w4optOutVal i.val L.val S.val R.val < w4optSpec.m i := by')
lean.append('  fin_cases i <;> fin_cases L <;> fin_cases S <;> fin_cases R <;>')
lean.append('    simp_all [w4optOutVal, w4optP0, w4optP1, w4optP2, w4optP3, w4optSpec, w4optM]')
lean.append('')

# w4optTrans
lean.append('def w4optTrans : TransFn w4optSpec := by')
lean.append('  intro i L S R')
lean.append('  exact ⟨w4optOutVal i.val L.val S.val R.val, w4optOutVal_lt i L S R⟩')
lean.append('')

# w4optSystem
lean.append('def w4optSystem : System where')
lean.append('  rs := w4optSpec')
lean.append('  f := w4optTrans')
lean.append('')

# stateProduct proof
lean.append('theorem w4opt_stateProduct : stateProduct w4optSpec = 24 := by')
lean.append('  simp [stateProduct, w4optSpec, w4optM, Fin.prod_univ_succ]')
lean.append('')

# w4optCfg
lean.append('def w4optCfg (x0 : Fin 2) (x1 : Fin 2) (x2 : Fin 2) (x3 : Fin 3) : Config w4optSpec')
lean.append('  | ⟨0, _⟩ => x0')
lean.append('  | ⟨1, _⟩ => x1')
lean.append('  | ⟨2, _⟩ => x2')
lean.append('  | ⟨3, _⟩ => x3')
lean.append('')

# w4optCfgCode — mixed radix: x0 + 2*x1 + 4*x2 + 8*x3
lean.append('def w4optCfgCode (c : Config w4optSpec) : Nat :=')
lean.append('  (c ⟨0, by decide⟩).1 + 2 * ((c ⟨1, by decide⟩).1 + 2 * ((c ⟨2, by decide⟩).1 + 2 * ((c ⟨3, by decide⟩).1)))')
lean.append('')

# w4optCfgOfCode
lean.append('def w4optCfgOfCode (k : Nat) : Config w4optSpec :=')
lean.append('  w4optCfg')
lean.append('    ⟨(k / 1) % 2, by omega⟩')
lean.append('    ⟨(k / 2) % 2, by omega⟩')
lean.append('    ⟨(k / 4) % 2, by omega⟩')
lean.append('    ⟨(k / 8) % 3, by omega⟩')
lean.append('')

# Good cycle codes
lean.append(f'def w4optGoodCycleCodes : List Nat := {cycle_codes}')
lean.append('')

# Good cycle configs
lean.append('def w4optGoodCycleConfigs : List (Config w4optSpec) :=')
lean.append('  w4optGoodCycleCodes.map w4optCfgOfCode')
lean.append('')

# Rank values
lean.append(f'def w4optRankVals : List Nat := {rank_vals}')
lean.append('')

# Bad rank function
lean.append('def w4optBadRank (c : Config w4optSpec) : Nat :=')
lean.append('  w4optRankVals.getD (w4optCfgCode c) 0')
lean.append('')

# GoodCycle proofs
lean.append('theorem w4optGoodCycle_nonempty : w4optGoodCycleConfigs ≠ [] := by')
lean.append('  decide')
lean.append('')

lean.append('theorem w4optGoodCycle_unique_privileged_aux :')
lean.append('    ∀ c ∈ w4optGoodCycleConfigs,')
lean.append('      ∃ i, privileged w4optSystem c i ∧')
lean.append('        ∀ j, privileged w4optSystem c j → j = i := by')
lean.append('  native_decide')
lean.append('')

lean.append('theorem w4optGoodCycle_unique_privileged :')
lean.append('    ∀ c ∈ w4optGoodCycleConfigs, ∃! i, privileged w4optSystem c i := by')
lean.append('  intro c hc')
lean.append('  simpa [ExistsUnique] using w4optGoodCycle_unique_privileged_aux c hc')
lean.append('')

lean.append('theorem w4optGoodCycle_closed :')
lean.append('    ∀ k : Fin w4optGoodCycleConfigs.length,')
lean.append('      ∃ i,')
lean.append('        privileged w4optSystem (w4optGoodCycleConfigs.get k) i ∧')
lean.append('          w4optGoodCycleConfigs.get (nextIndex w4optGoodCycleConfigs k) =')
lean.append('            move w4optSystem (w4optGoodCycleConfigs.get k) i := by')
lean.append('  native_decide')
lean.append('')

lean.append('theorem w4optGoodCycle_distinct :')
lean.append('    ∀ j₁ j₂ : Fin w4optGoodCycleConfigs.length,')
lean.append('      w4optGoodCycleConfigs.get j₁ = w4optGoodCycleConfigs.get j₂ → j₁ = j₂ := by')
lean.append('  native_decide')
lean.append('')

lean.append('def w4optGoodCycle : GoodCycle w4optSystem where')
lean.append('  configs := w4optGoodCycleConfigs')
lean.append('  nonempty := w4optGoodCycle_nonempty')
lean.append('  unique_privileged := w4optGoodCycle_unique_privileged')
lean.append('  closed := w4optGoodCycle_closed')
lean.append('  distinct := w4optGoodCycle_distinct')
lean.append('')

# BadRank decreases proof
lean.append('theorem w4optBadRank_decreases_from')
lean.append('    (c : Config w4optSpec)')
lean.append('    (hbad : c ∉ w4optGoodCycleConfigs)')
lean.append('    (i : Fin 4)')
lean.append('    (hpriv : privileged w4optSystem c i)')
lean.append('    (hnext : move w4optSystem c i ∉ w4optGoodCycleConfigs) :')
lean.append('    w4optBadRank (move w4optSystem c i) < w4optBadRank c := by')
lean.append('  native_decide +revert')
lean.append('')

lean.append('theorem w4optBadRank_decreases :')
lean.append('    ∀ {c\' c : Config w4optSpec},')
lean.append('      badStep w4optSystem w4optGoodCycle c\' c → w4optBadRank c\' < w4optBadRank c := by')
lean.append('  intro c\' c hstep')
lean.append('  rcases hstep with ⟨hbad, hnext, ⟨i, hpriv, rfl⟩⟩')
lean.append('  exact w4optBadRank_decreases_from c hbad i hpriv hnext')
lean.append('')

lean.append('theorem w4opt_converges : converges w4optSystem w4optGoodCycle := by')
lean.append('  let f : Config w4optSpec → Nat := w4optBadRank')
lean.append('  let r : Config w4optSpec → Config w4optSpec → Prop := InvImage Nat.lt f')
lean.append('  have hwf : WellFounded r := by')
lean.append('    simpa [r] using (InvImage.wf f Nat.lt_wfRel.wf)')
lean.append('  refine Subrelation.wf (r := r) ?_ hwf')
lean.append('  intro c\' c hstep')
lean.append('  exact w4optBadRank_decreases hstep')
lean.append('')

lean.append('theorem w4opt_valid : valid w4optSystem := by')
lean.append('  exact ⟨w4optGoodCycle, w4opt_converges⟩')

# Print the output
output = '\n'.join(lean)
print()
print(output)
