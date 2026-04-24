#!/usr/bin/env python3
"""Check if TP-preserving boundary transitions form a DAG.

Key argument: In any CF cycle, TP must be constant (non-increasing + returns to start).
TP-preserved interior steps are fc-constant + decrease hop budget → can't cycle.
So all steps in a CF cycle must be boundary-changing AND TP-preserving.

If TP-preserving boundary transitions form a DAG → no CF cycle → CF is WF.
This avoids needing the 617-edge completeness entirely!"""

def TBotVal(L,S,R):
    t = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    return t.get((L,S,R), 0)
def TLowVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    return t.get((L,S,R), 0)
def TMidVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R), 0)
def THighVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    return t.get((L,S,R), 0)
def TTopVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    return t.get((L,S,R), 0)

def frontierBitVal(a, b):
    return 1 if a != b else 0

def encode(c0, c1, c2, cN3, cN2, cN1):
    return ((((c0 * 3 + c1) * 3 + c2) * 3 + cN3) * 3 + cN2) * 2 + cN1

def decode(s):
    cN1 = s % 2; s //= 2
    cN2 = s % 3; s //= 3
    cN3 = s % 3; s //= 3
    c2 = s % 3; s //= 3
    c1 = s % 3; s //= 3
    c0 = s
    return (c0, c1, c2, cN3, cN2, cN1)

# exp2 bit: 1 iff both values are 2
def exp2Bit(a, b):
    return 1 if a == 2 and b == 2 else 0

# int21 bit: 1 iff one is 2 and other is 1 (or vice versa)
def int21Bit(a, b):
    return 1 if (a == 2 and b == 1) or (a == 1 and b == 2) else 0

# exp2 weight contribution at edge (j, j+1) for position j:
# This depends on the position. For simplicity, check if boundary-local
# TP components are preserved.

# For a step at position p, the affected edges are (p-1, p) and (p, p+1).
# TP preservation means: for each of exp2, int21, exp2_weight,
# the sum of contributions at edges (p-1,p) and (p,p+1) is the same before and after.

# For boundary positions, the relevant local values are in the 6-tuple (+ extras).

# Check TP preservation for a transition at each boundary position.
def check_tp_preserved_bot(cN1, c0, c1, new_c0):
    """Position 0. Edges: (n-1, 0) and (0, 1). L=cN1, S=c0, R=c1."""
    # Edge (n-1, 0): cN1, c0 → cN1, new_c0
    # Edge (0, 1): c0, c1 → new_c0, c1
    e2_before = exp2Bit(cN1, c0) + exp2Bit(c0, c1)
    e2_after = exp2Bit(cN1, new_c0) + exp2Bit(new_c0, c1)
    i21_before = int21Bit(cN1, c0) + int21Bit(c0, c1)
    i21_after = int21Bit(cN1, new_c0) + int21Bit(new_c0, c1)
    # exp2_weight depends on position — at positions n-1 and 0,
    # these are endpoint/near-endpoint positions with specific weights.
    # For a complete check, we'd need the weight formula.
    # But exp2 involves values = 2, and c0 ∈ {0,1}, cN1 ∈ {0,1}.
    # So exp2Bit(cN1, c0) = 0 always (neither can be 2).
    # And exp2Bit(c0, c1) = 0 since c0 ∈ {0,1}.
    # Similarly for new_c0 ∈ {0,1}.
    # So exp2 is always preserved at Bot.
    # Similarly int21: int21Bit(cN1, c0) depends on {cN1, c0} ⊂ {0,1}.
    # int21(0,0)=0, int21(0,1)=0, int21(1,0)=0, int21(1,1)=0. Always 0.
    # int21Bit(c0, c1): c0 ∈ {0,1}, c1 ∈ {0,1,2}.
    # int21(0,1)=0, int21(0,2)=0, int21(1,0)=0, int21(1,1)=0, int21(1,2)=1.
    # After: int21(new_c0, c1): same domain.
    # So for Bot position, check int21 at edge (0,1).
    return e2_before == e2_after and i21_before == i21_after

def check_tp_preserved_general(L, S, R, S_new, pos_type, n_val=9):
    """General TP preservation check. Returns True if all local TP quantities preserved.
    For simplicity, just check exp2 and int21 (exp2_weight is harder without position info).
    This is a conservative check — if even exp2+int21 aren't preserved, TP definitely isn't."""
    e2_before = exp2Bit(L, S) + exp2Bit(S, R)
    e2_after = exp2Bit(L, S_new) + exp2Bit(S_new, R)
    i21_before = int21Bit(L, S) + int21Bit(S, R)
    i21_after = int21Bit(L, S_new) + int21Bit(S_new, R)
    fb_before = frontierBitVal(L, S) + frontierBitVal(S, R)
    fb_after = frontierBitVal(L, S_new) + frontierBitVal(S_new, R)
    return e2_before == e2_after and i21_before == i21_after

# Build the TP-preserving boundary transition graph
tp_adj = {i: set() for i in range(324)}
all_adj = {i: set() for i in range(324)}
tp_total = 0
all_total = 0

for c0 in range(2):
  for c1 in range(3):
    for c2 in range(3):
      for cN3 in range(3):
        for cN2 in range(3):
          for cN1 in range(2):
            s = encode(c0, c1, c2, cN3, cN2, cN1)

            # P0: L=cN1, S=c0, R=c1
            new_c0 = TBotVal(cN1, c0, c1)
            if new_c0 != c0 and new_c0 < 2:
              t = encode(new_c0, c1, c2, cN3, cN2, cN1)
              all_adj[s].add(t)
              all_total += 1
              if check_tp_preserved_general(cN1, c0, c1, new_c0, 'bot'):
                tp_adj[s].add(t)
                tp_total += 1

            # P1: L=c0, S=c1, R=c2
            new_c1 = TLowVal(c0, c1, c2)
            if new_c1 != c1 and new_c1 < 3:
              t = encode(c0, new_c1, c2, cN3, cN2, cN1)
              all_adj[s].add(t)
              all_total += 1
              if check_tp_preserved_general(c0, c1, c2, new_c1, 'low'):
                tp_adj[s].add(t)
                tp_total += 1

            # P2: L=c1, S=c2, R=c3 for c3 in range(3)
            for c3 in range(3):
              new_c2 = TMidVal(c1, c2, c3)
              if new_c2 != c2 and new_c2 < 3:
                t = encode(c0, c1, new_c2, cN3, cN2, cN1)
                all_adj[s].add(t)
                all_total += 1
                if check_tp_preserved_general(c1, c2, c3, new_c2, 'mid'):
                  tp_adj[s].add(t)
                  tp_total += 1

            # PN3: L=cn4, S=cN3, R=cN2 for cn4 in range(3)
            for cn4 in range(3):
              new_cN3 = TMidVal(cn4, cN3, cN2)
              if new_cN3 != cN3 and new_cN3 < 3:
                t = encode(c0, c1, c2, new_cN3, cN2, cN1)
                all_adj[s].add(t)
                all_total += 1
                if check_tp_preserved_general(cn4, cN3, cN2, new_cN3, 'mid'):
                  tp_adj[s].add(t)
                  tp_total += 1

            # PN2: L=cN3, S=cN2, R=cN1
            new_cN2 = THighVal(cN3, cN2, cN1)
            if new_cN2 != cN2 and new_cN2 < 3:
              t = encode(c0, c1, c2, cN3, new_cN2, cN1)
              all_adj[s].add(t)
              all_total += 1
              if check_tp_preserved_general(cN3, cN2, cN1, new_cN2, 'high'):
                tp_adj[s].add(t)
                tp_total += 1

            # PN1: L=cN2, S=cN1, R=c0
            new_cN1 = TTopVal(cN2, cN1, c0)
            if new_cN1 != cN1 and new_cN1 < 2:
              t = encode(c0, c1, c2, cN3, cN2, new_cN1)
              all_adj[s].add(t)
              all_total += 1
              if check_tp_preserved_general(cN2, cN1, c0, new_cN1, 'top'):
                tp_adj[s].add(t)
                tp_total += 1

tp_edges = sum(len(v) for v in tp_adj.values())
print(f"All boundary transitions: {all_total} (unique edges: {sum(len(v) for v in all_adj.values())})")
print(f"TP-preserving boundary transitions: {tp_total} (unique edges: {tp_edges})")

# Check for cycles in TP-preserving graph
import sys
sys.setrecursionlimit(10000)

idx_counter = [0]
stack = []
lowlink = {}
index = {}
on_stack = set()
sccs = []

def strongconnect(v):
    index[v] = lowlink[v] = idx_counter[0]
    idx_counter[0] += 1
    stack.append(v)
    on_stack.add(v)
    for w in tp_adj[v]:
        if w not in index:
            strongconnect(w)
            lowlink[v] = min(lowlink[v], lowlink[w])
        elif w in on_stack:
            lowlink[v] = min(lowlink[v], index[w])
    if lowlink[v] == index[v]:
        scc = []
        while True:
            w = stack.pop()
            on_stack.discard(w)
            scc.append(w)
            if w == v:
                break
        sccs.append(scc)

for v in range(324):
    if v not in index:
        strongconnect(v)

non_trivial = [s for s in sccs if len(s) > 1]
self_loops = sum(1 for v in range(324) if v in tp_adj[v])

print(f"\nTP-preserving boundary graph:")
print(f"  Non-trivial SCCs: {len(non_trivial)}")
print(f"  Self-loops: {self_loops}")

if not non_trivial and self_loops == 0:
    print("  *** TP-PRESERVING BOUNDARY TRANSITIONS FORM A DAG! ***")

    # Compute rank
    topo_order = []
    for scc in sccs:
        topo_order.extend(scc)
    topo_order.reverse()
    rank = {v: 0 for v in range(324)}
    for v in reversed(topo_order):
        for w in tp_adj[v]:
            rank[v] = max(rank[v], rank[w] + 1)
    max_rank = max(rank.values())
    print(f"  Max rank: {max_rank}")

    # Verify rank
    violations = 0
    for v in range(324):
        for w in tp_adj[v]:
            if rank[w] >= rank[v]:
                violations += 1
    print(f"  Rank violations: {violations}")

    # Print rank values for Lean
    rank_list = [rank[i] for i in range(324)]
    print(f"\n  Rank values: {rank_list}")
else:
    print(f"  TP-preserving boundary graph has CYCLES")
    for i, scc in enumerate(non_trivial[:5]):
        print(f"  SCC {i}: size {len(scc)}, sample: {[decode(v) for v in scc[:3]]}")

# Also check: is the TP-preserving set a superset of the 617 CF edges?
sixTupleEdgeSet = set([(0, 6), (0, 162), (1, 0), (1, 7), (2, 164), (3, 1), (3, 9), (4, 166), (6, 8), (6, 168), (7, 6), (7, 9), (8, 170), (9, 11), (10, 16), (10, 172), (11, 17), (12, 174), (13, 12), (14, 176), (16, 4), (16, 178), (17, 5), (18, 24), (18, 180), (19, 18), (19, 25), (20, 182), (21, 19), (21, 27), (22, 184), (24, 26), (24, 186), (25, 24), (25, 27), (26, 188), (27, 29), (28, 34), (28, 190), (29, 35), (30, 192), (31, 30), (32, 194), (34, 22), (34, 196), (35, 23), (36, 0), (36, 42), (36, 198), (37, 1), (37, 36), (37, 43), (38, 2), (38, 200), (39, 3), (39, 37), (39, 45), (40, 4), (40, 202), (41, 5), (42, 6), (42, 44), (42, 204), (43, 7), (43, 42), (43, 45), (44, 8), (44, 206), (45, 9), (45, 47), (46, 10), (46, 52), (46, 208), (47, 11), (47, 53), (48, 12), (48, 210), (49, 13), (49, 48), (50, 14), (50, 212), (51, 15), (52, 16), (52, 40), (52, 214), (53, 17), (53, 41), (54, 0), (54, 60), (54, 72), (54, 216), (55, 61), (55, 73), (56, 2), (56, 74), (56, 218), (57, 55), (57, 63), (57, 75), (58, 59), (58, 76), (59, 77), (60, 6), (60, 62), (60, 78), (60, 222), (61, 63), (61, 79), (62, 8), (62, 80), (62, 224), (63, 65), (63, 81), (64, 65), (64, 70), (64, 82), (65, 71), (65, 83), (66, 12), (66, 84), (66, 228), (67, 85), (68, 14), (68, 86), (68, 230), (69, 87), (70, 58), (70, 71), (70, 88), (71, 59), (71, 89), (72, 78), (72, 90), (72, 234), (73, 79), (73, 91), (74, 92), (74, 236), (75, 73), (75, 81), (75, 93), (76, 77), (76, 94), (77, 95), (78, 80), (78, 96), (78, 240), (79, 81), (79, 97), (80, 98), (80, 242), (81, 83), (81, 99), (82, 83), (82, 88), (82, 100), (83, 89), (83, 101), (84, 102), (84, 246), (85, 103), (86, 104), (86, 248), (87, 105), (88, 76), (88, 89), (88, 106), (89, 77), (89, 107), (90, 36), (90, 96), (90, 252), (91, 97), (92, 38), (93, 91), (93, 99), (94, 40), (94, 95), (96, 42), (96, 98), (96, 258), (97, 99), (98, 44), (98, 260), (99, 101), (100, 46), (100, 101), (100, 106), (101, 107), (102, 48), (104, 50), (106, 52), (106, 94), (106, 107), (107, 95), (108, 0), (108, 114), (108, 144), (109, 115), (110, 2), (110, 146), (111, 109), (111, 117), (112, 113), (114, 6), (114, 116), (114, 150), (115, 117), (116, 8), (116, 152), (117, 119), (118, 119), (118, 124), (119, 125), (120, 12), (120, 156), (122, 14), (122, 158), (124, 112), (124, 125), (125, 113), (126, 108), (126, 132), (126, 144), (127, 109), (127, 133), (128, 110), (128, 146), (129, 111), (129, 127), (129, 135), (130, 112), (130, 131), (131, 113), (132, 114), (132, 134), (132, 150), (133, 115), (133, 135), (134, 116), (134, 152), (135, 117), (135, 137), (136, 118), (136, 137), (136, 142), (137, 119), (137, 143), (138, 120), (138, 156), (139, 121), (140, 122), (140, 158), (141, 123), (142, 124), (142, 130), (142, 143), (142, 160), (143, 125), (143, 131), (144, 36), (144, 150), (145, 37), (145, 144), (145, 151), (146, 38), (147, 39), (147, 145), (147, 153), (148, 40), (149, 41), (150, 42), (150, 152), (151, 43), (151, 150), (151, 153), (152, 44), (153, 45), (153, 155), (154, 46), (154, 160), (155, 47), (155, 161), (156, 48), (157, 49), (157, 156), (158, 50), (159, 51), (160, 52), (160, 148), (161, 53), (161, 149), (162, 168), (162, 216), (163, 1), (163, 162), (163, 169), (163, 217), (164, 218), (165, 3), (165, 163), (165, 171), (165, 219), (166, 220), (167, 5), (167, 221), (168, 170), (168, 222), (169, 7), (169, 168), (169, 171), (169, 223), (170, 171), (170, 224), (171, 9), (171, 173), (171, 225), (172, 178), (172, 226), (173, 11), (173, 179), (173, 227), (174, 228), (175, 13), (175, 174), (175, 229), (176, 230), (177, 15), (177, 231), (178, 166), (178, 232), (179, 17), (179, 167), (179, 233), (180, 186), (181, 19), (181, 180), (181, 187), (183, 21), (183, 181), (183, 189), (185, 23), (186, 188), (187, 25), (187, 186), (187, 189), (188, 189), (189, 27), (189, 191), (190, 196), (191, 29), (191, 197), (193, 31), (193, 192), (195, 33), (196, 184), (197, 35), (197, 185), (198, 162), (198, 204), (198, 252), (199, 37), (199, 163), (199, 198), (199, 205), (199, 253), (200, 164), (201, 39), (201, 165), (201, 199), (201, 207), (201, 255), (202, 166), (203, 41), (203, 167), (203, 257), (204, 168), (204, 206), (204, 258), (205, 43), (205, 169), (205, 204), (205, 207), (205, 259), (206, 170), (206, 207), (206, 260), (207, 45), (207, 171), (207, 209), (207, 261), (208, 172), (208, 214), (209, 47), (209, 173), (209, 215), (209, 263), (210, 174), (211, 49), (211, 175), (211, 210), (211, 265), (212, 176), (213, 51), (213, 177), (213, 267), (214, 178), (214, 202), (215, 53), (215, 179), (215, 203), (215, 269), (216, 222), (216, 234), (217, 216), (217, 223), (217, 235), (218, 236), (219, 217), (219, 225), (219, 237), (220, 238), (221, 239), (222, 224), (222, 240), (223, 222), (223, 225), (223, 241), (224, 225), (224, 242), (225, 227), (225, 243), (226, 232), (226, 244), (227, 233), (227, 245), (228, 246), (229, 228), (229, 247), (230, 248), (231, 249), (232, 220), (232, 250), (233, 221), (233, 251), (234, 240), (234, 252), (235, 234), (235, 241), (235, 253), (236, 254), (237, 235), (237, 243), (237, 255), (238, 239), (238, 256), (239, 257), (240, 242), (240, 258), (241, 240), (241, 243), (241, 259), (242, 243), (242, 260), (243, 245), (243, 261), (244, 240), (244, 245), (244, 250), (244, 262), (245, 251), (245, 263), (246, 264), (247, 246), (247, 265), (248, 266), (249, 267), (250, 238), (250, 251), (250, 268), (251, 239), (251, 269), (252, 258), (252, 306), (253, 252), (253, 259), (253, 307), (254, 308), (255, 253), (255, 261), (255, 309), (256, 257), (256, 310), (257, 311), (258, 260), (258, 312), (259, 258), (259, 261), (259, 313), (260, 261), (260, 314), (261, 263), (261, 315), (262, 258), (262, 263), (262, 268), (262, 316), (263, 269), (263, 317), (264, 318), (265, 319), (266, 320), (267, 321), (268, 256), (268, 269), (268, 322), (269, 257), (269, 323), (270, 276), (271, 109), (271, 270), (271, 277), (273, 111), (273, 271), (273, 279), (274, 275), (275, 113), (276, 278), (277, 115), (277, 276), (277, 279), (278, 279), (279, 117), (279, 281), (280, 276), (280, 281), (280, 286), (281, 119), (281, 287), (283, 121), (285, 123), (286, 274), (286, 287), (287, 125), (287, 275), (288, 270), (288, 294), (289, 127), (289, 271), (289, 288), (289, 295), (290, 272), (291, 129), (291, 273), (291, 289), (291, 297), (292, 274), (292, 293), (293, 131), (293, 275), (294, 276), (294, 296), (295, 133), (295, 277), (295, 294), (295, 297), (296, 278), (296, 297), (297, 135), (297, 279), (297, 299), (298, 280), (298, 294), (298, 299), (298, 304), (299, 137), (299, 281), (299, 305), (300, 282), (301, 139), (301, 283), (302, 284), (303, 141), (303, 285), (304, 286), (304, 292), (304, 305), (305, 143), (305, 287), (305, 293), (306, 312), (307, 145), (307, 306), (307, 313), (309, 147), (309, 307), (309, 315), (310, 311), (311, 149), (312, 314), (313, 151), (313, 312), (313, 315), (314, 315), (315, 153), (315, 317), (316, 312), (316, 317), (316, 322), (317, 155), (317, 323), (319, 157), (321, 159), (322, 310), (322, 323), (323, 161), (323, 311)])

tp_edge_set = set()
for v in range(324):
    for w in tp_adj[v]:
        tp_edge_set.add((v, w))

cf_not_tp = sixTupleEdgeSet - tp_edge_set
tp_not_cf = tp_edge_set - sixTupleEdgeSet

print(f"\n617 CF edges NOT in TP-preserving set: {len(cf_not_tp)}")
print(f"TP-preserving edges NOT in 617 CF set: {len(tp_not_cf)}")
if cf_not_tp:
    print(f"  First few CF-only edges: {list(cf_not_tp)[:5]}")
    for e in list(cf_not_tp)[:3]:
        s, t = decode(e[0]), decode(e[1])
        print(f"    {e[0]}={s} -> {e[1]}={t}")
