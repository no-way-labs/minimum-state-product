#!/usr/bin/env python3
"""
Check whether the constant-FutureFc subgraph (on full configs at n=9) is a DAG.
If so, compute its rank and project to the 6-tuple.

Also compute Φ_full (max fc over TP-preserving paths) and compare with FutureFc.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system
from collections import deque, Counter, defaultdict

n = 9
ms, fs = build_system(n)
N = 1
for m in ms:
    N *= m

def idx_to_config(idx):
    c = []
    for m in reversed(ms):
        c.append(idx % m)
        idx //= m
    return tuple(reversed(c))

def config_to_idx(c):
    idx = 0
    for j in range(n):
        idx = idx * ms[j] + c[j]
    return idx

def move(c, pos):
    L = c[(pos - 1) % n]
    S = c[pos]
    R = c[(pos + 1) % n]
    new_val = fs[pos](L, S, R)
    c2 = list(c)
    c2[pos] = new_val
    return tuple(c2)

def fc(c):
    return sum(1 for j in range(n) if c[j] != c[(j+1)%n])

def exp2_count(c):
    return sum(1 for j in range(2, n-2) if c[j] == 2 and c[(j+1)%n] in (0,1))

def int_21(c):
    return sum(1 for j in range(2, n-2) if c[j] == 2 and c[(j+1)%n] == 1)

def exp2_weight(c):
    return sum(j for j in range(2, n-2) if c[j] == 2 and c[(j+1)%n] in (0,1))

def tp_triple(c):
    return (exp2_count(c), int_21(c), exp2_weight(c))

# Build bad config list
bad_configs = []
bad_set = set()
fc_cache = {}
tp_cache = {}
for i in range(N):
    c = idx_to_config(i)
    f = fc(c)
    if f > 0:
        bad_configs.append(i)
        bad_set.add(i)
        fc_cache[i] = f
        tp_cache[i] = tp_triple(c)

print(f"Bad configs: {len(bad_configs)}")

# Build bad-step graph
bad_adj = {i: [] for i in bad_configs}
for i in bad_configs:
    c = idx_to_config(i)
    for p in range(n):
        c2 = move(c, p)
        if c2 == c:
            continue
        j = config_to_idx(c2)
        if j in bad_set:
            bad_adj[i].append(j)

# Compute FutureFc
print("Computing FutureFc...")
future_fc = dict(fc_cache)  # copy
rev_adj = {i: [] for i in bad_configs}
for i in bad_configs:
    for j in bad_adj[i]:
        rev_adj[j].append(i)

changed = True
iters = 0
while changed:
    changed = False
    iters += 1
    for j in bad_configs:
        for i in rev_adj[j]:
            if future_fc[j] > future_fc[i]:
                future_fc[i] = future_fc[j]
                changed = True
    if iters > 100:
        break
print(f"FutureFc converged in {iters} iterations")

# Compute Φ_full (max fc over TP-preserving reachable)
print("Computing Φ_full (TP-preserving)...")
# Build TP-preserving subgraph
tp_adj = {i: [] for i in bad_configs}
for i in bad_configs:
    for j in bad_adj[i]:
        if tp_cache[j] == tp_cache[i]:
            tp_adj[i].append(j)

phi_full = dict(fc_cache)  # copy
tp_rev = {i: [] for i in bad_configs}
for i in bad_configs:
    for j in tp_adj[i]:
        tp_rev[j].append(i)

changed = True
iters = 0
while changed:
    changed = False
    iters += 1
    for j in bad_configs:
        for i in tp_rev[j]:
            if phi_full[j] > phi_full[i]:
                phi_full[i] = phi_full[j]
                changed = True
    if iters > 100:
        break
print(f"Φ_full converged in {iters} iterations")

# Compare
diffs = sum(1 for i in bad_configs if future_fc[i] != phi_full[i])
print(f"FutureFc != Φ_full: {diffs} / {len(bad_configs)}")
print(f"FutureFc range: {min(future_fc.values())}..{max(future_fc.values())}")
print(f"Φ_full range:   {min(phi_full.values())}..{max(phi_full.values())}")

# === Check CF DAG ===
print("\n=== Constant-FutureFc subgraph ===")
cf_adj = defaultdict(list)
cf_nodes = set()
cf_edge_count = 0
for i in bad_configs:
    for j in bad_adj[i]:
        if future_fc[j] == future_fc[i]:
            cf_adj[i].append(j)
            cf_nodes.add(i)
            cf_nodes.add(j)
            cf_edge_count += 1

print(f"CF nodes: {len(cf_nodes)}, CF edges: {cf_edge_count}")

# DAG check via DFS
WHITE, GRAY, BLACK = 0, 1, 2
color = {c: WHITE for c in cf_nodes}
is_dag = True
cycle_node = None
for start in cf_nodes:
    if color[start] != WHITE:
        continue
    stack = [(start, iter(cf_adj.get(start, [])))]
    color[start] = GRAY
    while stack:
        node, children = stack[-1]
        try:
            child = next(children)
            if child not in cf_nodes:
                continue
            if color[child] == GRAY:
                is_dag = False
                cycle_node = child
                break
            if color[child] == WHITE:
                color[child] = GRAY
                stack.append((child, iter(cf_adj.get(child, []))))
        except StopIteration:
            color[node] = BLACK
            stack.pop()
    if not is_dag:
        break

print(f"Is DAG: {is_dag}")

if not is_dag:
    print(f"Cycle detected at node {cycle_node}")
    c = idx_to_config(cycle_node)
    print(f"  config: {c}, fc={fc_cache[cycle_node]}, FutureFc={future_fc[cycle_node]}")
    # Find actual cycle
    # BFS from cycle_node to find cycle
    visited = {cycle_node}
    parent = {cycle_node: None}
    queue = deque([cycle_node])
    found_cycle = False
    while queue and not found_cycle:
        u = queue.popleft()
        for v in cf_adj.get(u, []):
            if v == cycle_node and u != cycle_node:
                print(f"  Cycle: ... -> {idx_to_config(u)} -> {idx_to_config(cycle_node)}")
                found_cycle = True
                break
            if v not in visited and v in cf_nodes:
                visited.add(v)
                parent[v] = u
                queue.append(v)

if is_dag:
    # Compute rank (longest path)
    out_deg = {c: len(cf_adj.get(c, [])) for c in cf_nodes}
    sinks = [c for c in cf_nodes if out_deg.get(c, 0) == 0]
    rank = {c: 0 for c in sinks}
    radj = defaultdict(list)
    for c in cf_nodes:
        for s in cf_adj.get(c, []):
            if s in cf_nodes:
                radj[s].append(c)
    q = deque(sinks)
    while q:
        s = q.popleft()
        for c in radj.get(s, []):
            new_r = rank[s] + 1
            if c not in rank or new_r > rank[c]:
                rank[c] = new_r
                q.append(c)
    max_rank = max(rank.values())
    print(f"Max rank (longest path): {max_rank}")

# === Check constant-Φ_full DAG ===
print("\n=== Constant-Φ_full subgraph ===")
cphi_adj = defaultdict(list)
cphi_nodes = set()
cphi_edge_count = 0
for i in bad_configs:
    for j in tp_adj[i]:  # TP-preserving steps only
        if phi_full[j] == phi_full[i]:
            cphi_adj[i].append(j)
            cphi_nodes.add(i)
            cphi_nodes.add(j)
            cphi_edge_count += 1

print(f"CΦ nodes: {len(cphi_nodes)}, CΦ edges: {cphi_edge_count}")

# DAG check
color2 = {c: WHITE for c in cphi_nodes}
is_dag2 = True
for start in cphi_nodes:
    if color2[start] != WHITE:
        continue
    stack = [(start, iter(cphi_adj.get(start, [])))]
    color2[start] = GRAY
    while stack:
        node, children = stack[-1]
        try:
            child = next(children)
            if child not in cphi_nodes:
                continue
            if color2[child] == GRAY:
                is_dag2 = False
                break
            if color2[child] == WHITE:
                color2[child] = GRAY
                stack.append((child, iter(cphi_adj.get(child, []))))
        except StopIteration:
            color2[node] = BLACK
            stack.pop()
    if not is_dag2:
        break

print(f"Is DAG: {is_dag2}")

if is_dag2:
    out_deg2 = {c: len(cphi_adj.get(c, [])) for c in cphi_nodes}
    sinks2 = [c for c in cphi_nodes if out_deg2.get(c, 0) == 0]
    rank2 = {c: 0 for c in sinks2}
    radj2 = defaultdict(list)
    for c in cphi_nodes:
        for s in cphi_adj.get(c, []):
            if s in cphi_nodes:
                radj2[s].append(c)
    q = deque(sinks2)
    while q:
        s = q.popleft()
        for c in radj2.get(s, []):
            new_r = rank2[s] + 1
            if c not in rank2 or new_r > rank2[c]:
                rank2[c] = new_r
                q.append(c)
    max_rank2 = max(rank2.values())
    print(f"Max rank (longest path): {max_rank2}")

    # Project to 6-tuple
    def boundary6(c):
        return ((((c[0]*3+c[1])*3+c[2])*3+c[n-3])*3+c[n-2])*2+c[n-1]

    cphi_6tuple = set()
    for i in cphi_nodes:
        c = idx_to_config(i)
        for j in cphi_adj[i]:
            c2 = idx_to_config(j)
            b1 = boundary6(c)
            b2 = boundary6(c2)
            if b1 != b2:
                cphi_6tuple.add((b1, b2))

    print(f"\nCΦ 6-tuple edges (boundary-changing): {len(cphi_6tuple)}")

    # Compare with 617-edge set
    dag_edges = set()
    dag_edge_list = [
        (0, 6), (0, 162), (1, 0), (1, 7), (2, 164), (3, 1), (3, 9), (4, 166), (6, 8), (6, 168), (7, 6), (7, 9), (8, 170), (9, 11), (10, 16), (10, 172), (11, 17), (12, 174), (13, 12), (14, 176),
        (16, 4), (16, 178), (17, 5), (18, 24), (18, 180), (19, 18), (19, 25), (20, 182), (21, 19), (21, 27), (22, 184), (24, 26), (24, 186), (25, 24), (25, 27), (26, 188), (27, 29), (28, 34), (28, 190), (29, 35),
        (30, 192), (31, 30), (32, 194), (34, 22), (34, 196), (35, 23), (36, 0), (36, 42), (36, 198), (37, 1), (37, 36), (37, 43), (38, 2), (38, 200), (39, 3), (39, 37), (39, 45), (40, 4), (40, 202), (41, 5),
        (42, 6), (42, 44), (42, 204), (43, 7), (43, 42), (43, 45), (44, 8), (44, 206), (45, 9), (45, 47), (46, 10), (46, 52), (46, 208), (47, 11), (47, 53), (48, 12), (48, 210), (49, 13), (49, 48), (50, 14),
        (50, 212), (51, 15), (52, 16), (52, 40), (52, 214), (53, 17), (53, 41), (54, 0), (54, 60), (54, 72), (54, 216), (55, 61), (55, 73), (56, 2), (56, 74), (56, 218), (57, 55), (57, 63), (57, 75), (58, 59),
        (58, 76), (59, 77), (60, 6), (60, 62), (60, 78), (60, 222), (61, 63), (61, 79), (62, 8), (62, 80), (62, 224), (63, 65), (63, 81), (64, 65), (64, 70), (64, 82), (65, 71), (65, 83), (66, 12), (66, 84),
        (66, 228), (67, 85), (68, 14), (68, 86), (68, 230), (69, 87), (70, 58), (70, 71), (70, 88), (71, 59), (71, 89), (72, 78), (72, 90), (72, 234), (73, 79), (73, 91), (74, 92), (74, 236), (75, 73), (75, 81),
        (75, 93), (76, 77), (76, 94), (77, 95), (78, 80), (78, 96), (78, 240), (79, 81), (79, 97), (80, 98), (80, 242), (81, 83), (81, 99), (82, 83), (82, 88), (82, 100), (83, 89), (83, 101), (84, 102), (84, 246),
        (85, 103), (86, 104), (86, 248), (87, 105), (88, 76), (88, 89), (88, 106), (89, 77), (89, 107), (90, 36), (90, 96), (90, 252), (91, 97), (92, 38), (93, 91), (93, 99), (94, 40), (94, 95), (96, 42), (96, 98),
        (96, 258), (97, 99), (98, 44), (98, 260), (99, 101), (100, 46), (100, 101), (100, 106), (101, 107), (102, 48), (104, 50), (106, 52), (106, 94), (106, 107), (107, 95), (108, 0), (108, 114), (108, 144), (109, 115), (110, 2),
        (110, 146), (111, 109), (111, 117), (112, 113), (114, 6), (114, 116), (114, 150), (115, 117), (116, 8), (116, 152), (117, 119), (118, 119), (118, 124), (119, 125), (120, 12), (120, 156), (122, 14), (122, 158), (124, 112), (124, 125),
        (125, 113), (126, 108), (126, 132), (126, 144), (127, 109), (127, 133), (128, 110), (128, 146), (129, 111), (129, 127), (129, 135), (130, 112), (130, 131), (131, 113), (132, 114), (132, 134), (132, 150), (133, 115), (133, 135), (134, 116),
        (134, 152), (135, 117), (135, 137), (136, 118), (136, 137), (136, 142), (137, 119), (137, 143), (138, 120), (138, 156), (139, 121), (140, 122), (140, 158), (141, 123), (142, 124), (142, 130), (142, 143), (142, 160), (143, 125), (143, 131),
        (144, 36), (144, 150), (145, 37), (145, 144), (145, 151), (146, 38), (147, 39), (147, 145), (147, 153), (148, 40), (149, 41), (150, 42), (150, 152), (151, 43), (151, 150), (151, 153), (152, 44), (153, 45), (153, 155), (154, 46),
        (154, 160), (155, 47), (155, 161), (156, 48), (157, 49), (157, 156), (158, 50), (159, 51), (160, 52), (160, 148), (161, 53), (161, 149), (162, 168), (162, 216), (163, 1), (163, 162), (163, 169), (163, 217), (164, 218), (165, 3),
        (165, 163), (165, 171), (165, 219), (166, 220), (167, 5), (167, 221), (168, 170), (168, 222), (169, 7), (169, 168), (169, 171), (169, 223), (170, 171), (170, 224), (171, 9), (171, 173), (171, 225), (172, 178), (172, 226), (173, 11),
        (173, 179), (173, 227), (174, 228), (175, 13), (175, 174), (175, 229), (176, 230), (177, 15), (177, 231), (178, 166), (178, 232), (179, 17), (179, 167), (179, 233), (180, 186), (181, 19), (181, 180), (181, 187), (183, 21), (183, 181),
        (183, 189), (185, 23), (186, 188), (187, 25), (187, 186), (187, 189), (188, 189), (189, 27), (189, 191), (190, 196), (191, 29), (191, 197), (193, 31), (193, 192), (195, 33), (196, 184), (197, 35), (197, 185), (198, 162), (198, 204),
        (198, 252), (199, 37), (199, 163), (199, 198), (199, 205), (199, 253), (200, 164), (201, 39), (201, 165), (201, 199), (201, 207), (201, 255), (202, 166), (203, 41), (203, 167), (203, 257), (204, 168), (204, 206), (204, 258), (205, 43),
        (205, 169), (205, 204), (205, 207), (205, 259), (206, 170), (206, 207), (206, 260), (207, 45), (207, 171), (207, 209), (207, 261), (208, 172), (208, 214), (209, 47), (209, 173), (209, 215), (209, 263), (210, 174), (211, 49), (211, 175),
        (211, 210), (211, 265), (212, 176), (213, 51), (213, 177), (213, 267), (214, 178), (214, 202), (215, 53), (215, 179), (215, 203), (215, 269), (216, 222), (216, 234), (217, 216), (217, 223), (217, 235), (218, 236), (219, 217), (219, 225),
        (219, 237), (220, 238), (221, 239), (222, 224), (222, 240), (223, 222), (223, 225), (223, 241), (224, 225), (224, 242), (225, 227), (225, 243), (226, 232), (226, 244), (227, 233), (227, 245), (228, 246), (229, 228), (229, 247), (230, 248),
        (231, 249), (232, 220), (232, 250), (233, 221), (233, 251), (234, 240), (234, 252), (235, 234), (235, 241), (235, 253), (236, 254), (237, 235), (237, 243), (237, 255), (238, 239), (238, 256), (239, 257), (240, 242), (240, 258), (241, 240),
        (241, 243), (241, 259), (242, 243), (242, 260), (243, 245), (243, 261), (244, 240), (244, 245), (244, 250), (244, 262), (245, 251), (245, 263), (246, 264), (247, 246), (247, 265), (248, 266), (249, 267), (250, 238), (250, 251), (250, 268),
        (251, 239), (251, 269), (252, 258), (252, 306), (253, 252), (253, 259), (253, 307), (254, 308), (255, 253), (255, 261), (255, 309), (256, 257), (256, 310), (257, 311), (258, 260), (258, 312), (259, 258), (259, 261), (259, 313), (260, 261),
        (260, 314), (261, 263), (261, 315), (262, 258), (262, 263), (262, 268), (262, 316), (263, 269), (263, 317), (264, 318), (265, 319), (266, 320), (267, 321), (268, 256), (268, 269), (268, 322), (269, 257), (269, 323), (270, 276), (271, 109),
        (271, 270), (271, 277), (273, 111), (273, 271), (273, 279), (274, 275), (275, 113), (276, 278), (277, 115), (277, 276), (277, 279), (278, 279), (279, 117), (279, 281), (280, 276), (280, 281), (280, 286), (281, 119), (281, 287), (283, 121),
        (285, 123), (286, 274), (286, 287), (287, 125), (287, 275), (288, 270), (288, 294), (289, 127), (289, 271), (289, 288), (289, 295), (290, 272), (291, 129), (291, 273), (291, 289), (291, 297), (292, 274), (292, 293), (293, 131), (293, 275),
        (294, 276), (294, 296), (295, 133), (295, 277), (295, 294), (295, 297), (296, 278), (296, 297), (297, 135), (297, 279), (297, 299), (298, 280), (298, 294), (298, 299), (298, 304), (299, 137), (299, 281), (299, 305), (300, 282), (301, 139),
        (301, 283), (302, 284), (303, 141), (303, 285), (304, 286), (304, 292), (304, 305), (305, 143), (305, 287), (305, 293), (306, 312), (307, 145), (307, 306), (307, 313), (309, 147), (309, 307), (309, 315), (310, 311), (311, 149), (312, 314),
        (313, 151), (313, 312), (313, 315), (314, 315), (315, 153), (315, 317), (316, 312), (316, 317), (316, 322), (317, 155), (317, 323), (319, 157), (321, 159), (322, 310), (322, 323), (323, 161), (323, 311),
    ]
    for (a, b) in dag_edge_list:
        dag_edges.add((a, b))

    in_dag = cphi_6tuple & dag_edges
    not_in_dag = cphi_6tuple - dag_edges
    dag_not_cphi = dag_edges - cphi_6tuple
    print(f"  In 617-edge DAG:     {len(in_dag)}")
    print(f"  NOT in DAG:          {len(not_in_dag)}")
    print(f"  DAG but not in CΦ:   {len(dag_not_cphi)}")

# Also: check CF 6-tuple projection
print("\n=== CF (constant-FutureFc) 6-tuple projection ===")
cf_6tuple = set()
for i in cf_nodes:
    c = idx_to_config(i)
    for j in cf_adj[i]:
        c2 = idx_to_config(j)
        b1 = ((((c[0]*3+c[1])*3+c[2])*3+c[n-3])*3+c[n-2])*2+c[n-1]
        b2 = ((((c2[0]*3+c2[1])*3+c2[2])*3+c2[n-3])*3+c2[n-2])*2+c2[n-1]
        if b1 != b2:
            cf_6tuple.add((b1, b2))
print(f"CF 6-tuple edges: {len(cf_6tuple)}")

# Is CF 6-tuple a DAG?
cf6_adj = defaultdict(set)
cf6_nodes = set()
for (a, b) in cf_6tuple:
    cf6_adj[a].add(b)
    cf6_nodes.add(a)
    cf6_nodes.add(b)

color3 = {c: WHITE for c in cf6_nodes}
is_dag3 = True
for start in cf6_nodes:
    if color3[start] != WHITE:
        continue
    stack = [(start, iter(cf6_adj.get(start, set())))]
    color3[start] = GRAY
    while stack:
        node, children = stack[-1]
        try:
            child = next(children)
            if child not in cf6_nodes:
                continue
            if color3[child] == GRAY:
                is_dag3 = False
                break
            if color3[child] == WHITE:
                color3[child] = GRAY
                stack.append((child, iter(cf6_adj.get(child, set()))))
        except StopIteration:
            color3[node] = BLACK
            stack.pop()
    if not is_dag3:
        break

print(f"CF 6-tuple DAG: {is_dag3}")

print("\nDONE")
