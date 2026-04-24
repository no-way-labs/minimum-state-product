"""Summarize combined n=10 DFS + SMT sweep results for §6.5 paper text."""
import json
from collections import Counter

HERE = "docs/lean_docs/paper_upgrade_3"

dfs = json.load(open(f"{HERE}/axc_n10_sweep_results.json"))
smt = json.load(open(f"{HERE}/axc_n10_smt_sweep_results.json"))

# DFS side — count firing (ms, ord) pairs
dfs_eval_pairs = 0
dfs_fire_pairs = 0
dfs_with_cycle = 0
sk_fracs = []
Ls = []
for r in dfs["results"]:
    if r["n_cycles_found"] > 0:
        dfs_with_cycle += 1
    for po in r["per_ordering"]:
        if po.get("cycle_found"):
            dfs_eval_pairs += 1
            if po.get("axc_sk_nonempty"):
                dfs_fire_pairs += 1
                sk_fracs.append(po["axc_sk_frac"])
                Ls.append(po["L"])

# SMT side — one ordering per multiset
smt_found = 0
smt_no = 0
smt_unk = 0
for r in smt["results"]:
    if r["status"] == "found":
        smt_found += 1
        sk_fracs.append(r["axc"]["sk_frac"])
        Ls.append(r["L"])
    elif r["status"] == "no_cycle_all_L":
        smt_no += 1
    else:
        smt_unk += 1

print(f"DFS: {dfs_with_cycle} multisets with cycle, {dfs_eval_pairs} eval pairs, {dfs_fire_pairs} fire pairs")
print(f"SMT: {smt_found} found, {smt_no} no_cycle, {smt_unk} unknown (in progress: {smt.get('in_progress')})")
print()
print(f"Total multisets touched: {dfs_with_cycle + smt_found}")
print(f"Total eval pairs (DFS + SMT): {dfs_eval_pairs + smt_found}")
print(f"Fire / eval: {dfs_fire_pairs + smt_found} / {dfs_eval_pairs + smt_found}")
print()
print(f"sk_frac: min={min(sk_fracs):.3f} max={max(sk_fracs):.3f} "
      f"mean={sum(sk_fracs)/len(sk_fracs):.3f}")
print(f"L: min={min(Ls)} max={max(Ls)}")
print()
print("=" * 40, "§6.5 fill", "=" * 40)
print(f"  NDFS      = {dfs_with_cycle}")
print(f"  NSMT      = {smt_found}")
print(f"  NEVAL     = {dfs_eval_pairs + smt_found}")
print(f"  NFIRE     = {dfs_fire_pairs + smt_found}")
print(f"  SKFRAC_LO = {min(sk_fracs):.3f}")
print(f"  SKFRAC_HI = {max(sk_fracs):.3f}")
print(f"  SKFRAC_MEAN = {sum(sk_fracs)/len(sk_fracs):.3f}")
print(f"  L_LO      = {min(Ls)}")
print(f"  L_HI      = {max(Ls)}")
