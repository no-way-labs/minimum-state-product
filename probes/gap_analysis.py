#!/usr/bin/env python3
"""
Analyze the gap between ALL possible boundary transitions in the CUP-2
6-tuple system and the 617 certified edges in sixTupleEdgeVals.
"""

# === Transition tables from Tables.lean ===

def TBotVal(L, S, R):
    t = {
        (0,0,0):1, (0,0,1):1, (0,0,2):0,
        (0,1,0):1, (0,1,1):1, (0,1,2):1,
        (1,0,0):0, (1,0,1):1, (1,0,2):0,
        (1,1,0):0, (1,1,1):1, (1,1,2):0,
    }
    return t.get((L,S,R), 0)

def TLowVal(L, S, R):
    t = {
        (0,0,0):0, (0,0,1):0, (0,0,2):0,
        (0,1,0):0, (0,1,1):1, (0,1,2):0,
        (0,2,0):0, (0,2,1):2, (0,2,2):0,
        (1,0,0):1, (1,0,1):1, (1,0,2):1,
        (1,1,0):1, (1,1,1):1, (1,1,2):2,
        (1,2,0):0, (1,2,1):1, (1,2,2):2,
    }
    return t.get((L,S,R), 0)

def TMidVal(L, S, R):
    t = {
        (0,0,0):0, (0,0,1):0, (0,0,2):0,
        (0,1,0):0, (0,1,1):1, (0,1,2):0,
        (0,2,0):0, (0,2,1):2, (0,2,2):0,
        (1,0,0):1, (1,0,1):1, (1,0,2):1,
        (1,1,0):1, (1,1,1):1, (1,1,2):2,
        (1,2,0):0, (1,2,1):1, (1,2,2):2,
        (2,0,0):0, (2,0,1):0, (2,0,2):2,
        (2,1,0):1, (2,1,1):0, (2,1,2):2,  # (2,1,1) liveness fix: was 2
        (2,2,0):0, (2,2,1):2, (2,2,2):2,
    }
    return t.get((L,S,R), 0)

def THighVal(L, S, R):
    t = {
        (0,0,0):0, (0,0,1):0,
        (0,1,0):0, (0,1,1):0,
        (0,2,0):0, (0,2,1):0,
        (1,0,0):1, (1,0,1):1,
        (1,1,0):1, (1,1,1):2,
        (1,2,0):0, (1,2,1):2,
        (2,0,0):0, (2,0,1):2,
        (2,1,0):0, (2,1,1):2,
        (2,2,0):2, (2,2,1):2,
    }
    return t.get((L,S,R), 0)

def TTopVal(L, S, R):
    t = {
        (0,0,0):0, (0,0,1):0,
        (0,1,0):0, (0,1,1):0,
        (1,0,0):0, (1,0,1):1,
        (1,1,0):1, (1,1,1):1,
        (2,0,0):1, (2,0,1):1,
        (2,1,0):1, (2,1,1):1,
    }
    return t.get((L,S,R), 0)

# === Encoding ===

def encode(c0, c1, c2, cN3, cN2, cN1):
    return ((((c0*3 + c1)*3 + c2)*3 + cN3)*3 + cN2)*2 + cN1

def decode(v):
    cN1 = v % 2; v //= 2
    cN2 = v % 3; v //= 3
    cN3 = v % 3; v //= 3
    c2  = v % 3; v //= 3
    c1  = v % 3; v //= 3
    c0  = v
    return (c0, c1, c2, cN3, cN2, cN1)

# === Parse the 617 certified edges ===

certified_edges = set()
edge_list_raw = [
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

# Note: in Lean, sixTupleEdge c' c checks (c.1, c'.1) in the list
# So edge (a, b) in the list means: source=a, successor=b, i.e. a -> b
# And sixTupleEdge c' c = (c, c') in list means c -> c'
# Let's re-read: sixTupleEdge c' c := sixTupleEdgeVals.contains (c.1, c'.1)
# So (c, c') means from state c we go to c'. The pair (source, dest) = (c, c').
# Wait: (c.1, c'.1) means first element is c (the "from"), second is c' (the "to").
# So edge list entries are (from, to).

for (a, b) in edge_list_raw:
    certified_edges.add((a, b))

assert len(certified_edges) == 617, f"Expected 617 edges, got {len(certified_edges)}"

# === Enumerate all boundary states ===

all_states = []
for c0 in range(2):
    for c1 in range(3):
        for c2 in range(3):
            for cN3 in range(3):
                for cN2 in range(3):
                    for cN1 in range(2):
                        all_states.append((c0, c1, c2, cN3, cN2, cN1))

assert len(all_states) == 324

# === Generate all boundary transitions ===

pos_names = ["P0 (bot)", "P1 (low)", "P2 (mid)", "P(n-3) (mid)", "P(n-2) (high)", "P(n-1) (top)"]

all_transitions = []  # (pos_name, src_enc, dst_enc, src_tuple, dst_tuple, detail)
actual_moves = []     # only where src != dst

for (c0, c1, c2, cN3, cN2, cN1) in all_states:
    src = encode(c0, c1, c2, cN3, cN2, cN1)

    # Position 0: TBotVal(cN1, c0, c1) -> new c0
    new_c0 = TBotVal(cN1, c0, c1)
    dst = encode(new_c0, c1, c2, cN3, cN2, cN1)
    detail = f"TBot({cN1},{c0},{c1})={new_c0}"
    all_transitions.append(("P0 (bot)", src, dst, (c0,c1,c2,cN3,cN2,cN1), (new_c0,c1,c2,cN3,cN2,cN1), detail))

    # Position 1: TLowVal(c0, c1, c2) -> new c1
    new_c1 = TLowVal(c0, c1, c2)
    dst = encode(c0, new_c1, c2, cN3, cN2, cN1)
    detail = f"TLow({c0},{c1},{c2})={new_c1}"
    all_transitions.append(("P1 (low)", src, dst, (c0,c1,c2,cN3,cN2,cN1), (c0,new_c1,c2,cN3,cN2,cN1), detail))

    # Position 2: TMidVal(c1, c2, c3) for each c3 -> new c2
    for c3 in range(3):
        new_c2 = TMidVal(c1, c2, c3)
        dst = encode(c0, c1, new_c2, cN3, cN2, cN1)
        detail = f"TMid({c1},{c2},{c3})={new_c2}, c3={c3}"
        all_transitions.append(("P2 (mid)", src, dst, (c0,c1,c2,cN3,cN2,cN1), (c0,c1,new_c2,cN3,cN2,cN1), detail))

    # Position n-3: TMidVal(cn4, cN3, cN2) for each cn4 -> new cN3
    for cn4 in range(3):
        new_cN3 = TMidVal(cn4, cN3, cN2)
        dst = encode(c0, c1, c2, new_cN3, cN2, cN1)
        detail = f"TMid({cn4},{cN3},{cN2})={new_cN3}, cn4={cn4}"
        all_transitions.append(("P(n-3) (mid)", src, dst, (c0,c1,c2,cN3,cN2,cN1), (c0,c1,c2,new_cN3,cN2,cN1), detail))

    # Position n-2: THighVal(cN3, cN2, cN1) -> new cN2
    new_cN2 = THighVal(cN3, cN2, cN1)
    dst = encode(c0, c1, c2, cN3, new_cN2, cN1)
    detail = f"THigh({cN3},{cN2},{cN1})={new_cN2}"
    all_transitions.append(("P(n-2) (high)", src, dst, (c0,c1,c2,cN3,cN2,cN1), (c0,c1,c2,cN3,new_cN2,cN1), detail))

    # Position n-1: TTopVal(cN2, cN1, c0) -> new cN1
    new_cN1 = TTopVal(cN2, cN1, c0)
    dst = encode(c0, c1, c2, cN3, cN2, new_cN1)
    detail = f"TTop({cN2},{cN1},{c0})={new_cN1}"
    all_transitions.append(("P(n-1) (top)", src, dst, (c0,c1,c2,cN3,cN2,cN1), (c0,c1,c2,cN3,cN2,new_cN1), detail))

# Filter to actual moves (src != dst)
for t in all_transitions:
    pos, src, dst, src_t, dst_t, detail = t
    if src != dst:
        actual_moves.append(t)

# Deduplicate: same (src, dst) can appear from different c3/cn4 values
# but they're the same edge in the 6-tuple graph
unique_edges = {}
for t in actual_moves:
    pos, src, dst, src_t, dst_t, detail = t
    key = (src, dst)
    if key not in unique_edges:
        unique_edges[key] = []
    unique_edges[key].append(t)

in_certified = {}
not_in_certified = {}
for key in unique_edges:
    if key in certified_edges:
        in_certified[key] = unique_edges[key]
    else:
        not_in_certified[key] = unique_edges[key]

print("=" * 70)
print("CUP-2 Six-Tuple Boundary Transition Gap Analysis")
print("=" * 70)
print()
print(f"Total boundary states: 324")
print(f"Total transition instances (incl. c3/cn4 variants): {len(all_transitions)}")
print(f"  of which are actual moves (src != dst): {len(actual_moves)}")
print(f"Unique (src, dst) edges from actual moves: {len(unique_edges)}")
print(f"  In certified 617-edge set:     {len(in_certified)}")
print(f"  NOT in certified set (GAP):    {len(not_in_certified)}")
print()

# Break down by position
print("--- Breakdown by position ---")
for pos_name in pos_names:
    pos_edges = set()
    pos_moves = 0
    pos_total = 0
    for t in all_transitions:
        if t[0] == pos_name:
            pos_total += 1
            if t[1] != t[2]:
                pos_moves += 1
                pos_edges.add((t[1], t[2]))
    in_c = sum(1 for e in pos_edges if e in certified_edges)
    not_c = sum(1 for e in pos_edges if e not in certified_edges)
    print(f"  {pos_name}: {pos_total} instances, {pos_moves} moves, {len(pos_edges)} unique edges, {in_c} certified, {not_c} gap")
print()

# Check: are there certified edges NOT produced by any boundary transition?
boundary_edge_set = set(unique_edges.keys())
certified_not_boundary = certified_edges - boundary_edge_set
print(f"Certified edges NOT from boundary transitions: {len(certified_not_boundary)}")
if certified_not_boundary:
    print("  (These come from interior transitions, which are handled separately)")
print()

# List gap transitions
if not_in_certified:
    print("=" * 70)
    print(f"GAP TRANSITIONS ({len(not_in_certified)} unique edges)")
    print("=" * 70)
    # Sort by source for readability
    for key in sorted(not_in_certified.keys()):
        src, dst = key
        src_t = decode(src)
        dst_t = decode(dst)
        examples = not_in_certified[key]
        positions = sorted(set(t[0] for t in examples))
        details = [t[5] for t in examples[:3]]  # show up to 3
        print(f"  {src:3d} -> {dst:3d}  src={src_t} dst={dst_t}  pos={positions}  {details[0]}")
        for d in details[1:]:
            print(f"              {d}")
else:
    print("NO GAP — all boundary transitions are in the certified edge set!")

# Also check: which certified edges come from boundary moves?
print()
print("=" * 70)
print("SUMMARY")
print("=" * 70)
print(f"  Certified edges (DAG):              617")
print(f"  Unique boundary move edges:         {len(unique_edges)}")
print(f"  Boundary edges in certified set:    {len(in_certified)}")
print(f"  Boundary edges NOT certified (gap): {len(not_in_certified)}")
print(f"  Certified edges from interior only: {len(certified_not_boundary)}")
print()
print("These gap transitions must be proved to be FutureFc-dropping")
print("(i.e., they decrease the maximum reachable fc) to close the")
print("completeness claim for the 6-tuple DAG convergence proof.")
