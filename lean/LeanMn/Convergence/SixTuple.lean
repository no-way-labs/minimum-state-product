import LeanMn.Convergence.Anomalous

namespace LeanMn

abbrev SixState := Fin 324

structure SixBoundary where
  c0 : Fin 2
  c1 : Fin 3
  c2 : Fin 3
  cN3 : Fin 3
  cN2 : Fin 3
  cN1 : Fin 2
deriving DecidableEq, Fintype, Repr

@[ext] theorem SixBoundary.ext {s t : SixBoundary}
    (h0 : s.c0 = t.c0) (h1 : s.c1 = t.c1) (h2 : s.c2 = t.c2)
    (hN3 : s.cN3 = t.cN3) (hN2 : s.cN2 = t.cN2) (hN1 : s.cN1 = t.cN1) :
    s = t := by
  cases s
  cases t
  cases h0
  cases h1
  cases h2
  cases hN3
  cases hN2
  cases hN1
  rfl

def SixBoundary.encode (s : SixBoundary) : SixState :=
  ⟨((((s.c0.1 * 3 + s.c1.1) * 3 + s.c2.1) * 3 + s.cN3.1) * 3 + s.cN2.1) * 2 + s.cN1.1, by
    omega⟩

/-- Condensation rank of the 617-edge CΦ 6-tuple graph (1 SCC {239,245,251}, max rank 26). -/
def condensationRankVals : List Nat :=
  [16, 17, 5, 18, 11, 0, 15, 16, 14, 3, 14, 2, 5, 6, 5, 0, 12, 1, 8, 9, 1, 10, 1, 0, 7, 8, 6, 3, 3, 2, 1, 2, 1, 0, 2, 1, 17, 18, 6, 19, 12, 1, 16, 17, 15, 4, 15, 3, 6, 7, 6, 1, 13, 2, 20, 7, 9, 8, 15, 2, 19, 6, 18, 5, 18, 4, 9, 2, 9, 2, 16, 3, 19, 6, 8, 7, 14, 1, 18, 5, 17, 4, 17, 3, 8, 1, 8, 1, 15, 2, 18, 5, 7, 6, 13, 0, 17, 4, 16, 3, 16, 2, 7, 0, 7, 0, 14, 1, 19, 5, 8, 6, 1, 0, 18, 4, 17, 3, 3, 2, 8, 0, 8, 0, 2, 1, 20, 6, 9, 7, 2, 1, 19, 5, 18, 4, 4, 3, 9, 1, 9, 1, 3, 2, 18, 19, 7, 20, 13, 2, 17, 18, 16, 5, 16, 4, 7, 8, 7, 2, 14, 3, 15, 24, 4, 25, 10, 9, 14, 23, 13, 12, 13, 11, 4, 13, 4, 7, 11, 10, 7, 10, 0, 11, 0, 1, 6, 9, 5, 4, 2, 3, 0, 3, 0, 1, 1, 2, 16, 25, 5, 26, 11, 10, 15, 24, 14, 13, 14, 12, 5, 14, 5, 8, 12, 11, 14, 23, 3, 24, 9, 8, 13, 22, 12, 11, 12, 10, 3, 12, 3, 6, 10, 9, 11, 22, 2, 23, 8, 7, 10, 21, 9, 8, 11, 7, 2, 11, 2, 5, 9, 7, 10, 21, 1, 22, 5, 4, 9, 20, 8, 7, 10, 6, 1, 10, 1, 4, 6, 5, 7, 8, 0, 9, 2, 1, 6, 7, 5, 4, 7, 3, 0, 1, 0, 1, 3, 2, 8, 9, 1, 10, 3, 2, 7, 8, 6, 5, 8, 4, 1, 2, 1, 2, 4, 3, 9, 20, 0, 21, 4, 3, 8, 19, 7, 6, 9, 5, 0, 9, 0, 3, 5, 4]

theorem condensationRankVals_length : condensationRankVals.length = 324 := by native_decide

def condensationRank (s : SixState) : Nat :=
  condensationRankVals.getD s.1 0

/-- SCC sub-rank for the 3-node SCC {239,245,251}. Within the SCC:
    245→251 and 251→239 have sccSubRank dropping; 239→245 has fc dropping (analytical). -/
def sccSubRankVals : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem sccSubRankVals_length : sccSubRankVals.length = 324 := by native_decide

def sccSubRank (s : SixState) : Nat :=
  sccSubRankVals.getD s.1 0

/-- Legacy alias for backwards compatibility. -/
def sixStateRank (s : SixState) : Nat :=
  condensationRank s

def sixTupleEdgeVals : List (Nat × Nat) :=
  [
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
    (134, 152), (135, 117), (135, 137), (136, 118), (136, 137), (136, 142), (137, 119), (137, 143), (138, 120), (138, 156), (139, 121), (140, 122), (140, 158), (141, 123), (142, 124), (142, 130), (142, 143), (143, 125), (143, 131),
    (144, 36), (144, 150), (145, 37), (145, 144), (145, 151), (146, 38), (147, 39), (147, 145), (147, 153), (148, 40), (149, 41), (150, 42), (150, 152), (151, 43), (151, 150), (151, 153), (152, 44), (153, 45), (153, 155), (154, 46),
    (154, 160), (155, 47), (155, 161), (156, 48), (157, 49), (157, 156), (158, 50), (159, 51), (160, 52), (160, 148), (161, 53), (161, 149), (162, 168), (162, 216), (163, 1), (163, 162), (163, 169), (163, 217), (164, 218), (165, 3),
    (165, 163), (165, 171), (165, 219), (166, 220), (167, 5), (167, 221), (168, 170), (168, 222), (169, 7), (169, 168), (169, 171), (169, 223), (170, 171), (170, 224), (171, 9), (171, 173), (171, 225), (172, 178), (172, 226), (173, 11),
    (173, 179), (173, 227), (174, 228), (175, 13), (175, 174), (175, 229), (176, 230), (177, 15), (177, 231), (178, 166), (178, 232), (179, 17), (179, 167), (179, 233), (180, 186), (181, 19), (181, 180), (181, 187), (183, 21), (183, 181),
    (183, 189), (185, 23), (186, 188), (187, 25), (187, 186), (187, 189), (188, 189), (189, 27), (189, 191), (190, 196), (191, 29), (191, 197), (193, 31), (193, 192), (195, 33), (196, 184), (197, 35), (197, 185), (198, 162), (198, 204),
    (198, 252), (199, 37), (199, 163), (199, 198), (199, 205), (199, 253), (200, 164), (201, 39), (201, 165), (201, 199), (201, 207), (201, 255), (202, 166), (203, 41), (203, 167), (203, 257), (204, 168), (204, 206), (204, 258), (205, 43),
    (205, 169), (205, 204), (205, 207), (205, 259), (206, 170), (206, 207), (206, 260), (207, 45), (207, 171), (207, 209), (207, 261), (208, 172), (208, 214), (209, 47), (209, 173), (209, 215), (209, 263), (210, 174), (211, 49), (211, 175),
    (211, 210), (211, 265), (212, 176), (213, 51), (213, 177), (213, 267), (214, 178), (214, 202), (215, 53), (215, 179), (215, 203), (215, 269), (216, 222), (216, 234), (217, 216), (217, 223), (217, 235), (218, 236), (219, 217), (219, 225),
    (219, 237), (220, 238), (221, 239), (222, 224), (222, 240), (223, 222), (223, 225), (223, 241), (224, 225), (224, 242), (225, 227), (225, 243), (226, 232), (226, 244), (227, 233), (227, 245), (228, 246), (229, 228), (229, 247), (230, 248),
    (231, 249), (232, 220), (232, 250), (233, 221), (233, 251), (234, 240), (234, 252), (235, 234), (235, 241), (235, 253), (236, 254), (237, 235), (237, 243), (237, 255), (238, 239), (238, 256), (239, 245), (239, 257), (240, 242), (240, 258), (241, 240),
    (241, 243), (241, 259), (242, 243), (242, 260), (243, 245), (243, 261), (244, 240), (244, 245), (244, 250), (244, 262), (245, 251), (245, 263), (246, 264), (247, 246), (247, 265), (248, 266), (249, 267), (250, 238), (250, 251), (250, 268),
    (251, 239), (251, 269), (252, 258), (252, 306), (253, 252), (253, 259), (253, 307), (254, 308), (255, 253), (255, 261), (255, 309), (256, 257), (256, 310), (257, 311), (258, 260), (258, 312), (259, 258), (259, 261), (259, 313), (260, 261),
    (260, 314), (261, 263), (261, 315), (262, 258), (262, 263), (262, 268), (262, 316), (263, 269), (263, 317), (264, 318), (265, 319), (266, 320), (267, 321), (268, 256), (268, 269), (268, 322), (269, 257), (269, 323), (270, 276), (271, 109),
    (271, 270), (271, 277), (273, 111), (273, 271), (273, 279), (274, 275), (275, 113), (276, 278), (277, 115), (277, 276), (277, 279), (278, 279), (279, 117), (279, 281), (280, 276), (280, 281), (280, 286), (281, 119), (281, 287), (283, 121),
    (285, 123), (286, 274), (286, 287), (287, 125), (287, 275), (288, 270), (288, 294), (289, 127), (289, 271), (289, 288), (289, 295), (290, 272), (291, 129), (291, 273), (291, 289), (291, 297), (292, 274), (292, 293), (293, 131), (293, 275),
    (294, 276), (294, 296), (295, 133), (295, 277), (295, 294), (295, 297), (296, 278), (296, 297), (297, 135), (297, 279), (297, 299), (298, 280), (298, 294), (298, 299), (298, 304), (299, 137), (299, 281), (299, 305), (300, 282), (301, 139),
    (301, 283), (302, 284), (303, 141), (303, 285), (304, 286), (304, 292), (304, 305), (305, 143), (305, 287), (305, 293), (306, 312), (307, 145), (307, 306), (307, 313), (309, 147), (309, 307), (309, 315), (310, 311), (311, 149), (312, 314),
    (313, 151), (313, 312), (313, 315), (314, 315), (315, 153), (315, 317), (316, 312), (316, 317), (316, 322), (317, 155), (317, 323), (319, 157), (321, 159), (322, 310), (322, 323), (323, 161), (323, 311)
  ]

def sixTupleEdge (c' c : SixState) : Prop :=
  sixTupleEdgeVals.contains (c.1, c'.1) = true

instance (c' c : SixState) : Decidable (sixTupleEdge c' c) := by
  unfold sixTupleEdge
  infer_instance

theorem sixTupleEdgeVals_length : sixTupleEdgeVals.length = 617 := by native_decide

/-- For every sixTupleEdge, either condensation rank drops, SCC sub-rank drops,
    or the edge is the SCC fc-edge (239→245) handled analytically. -/
theorem sixTuple_edge_lex_decrease {c' c : SixState} (h : sixTupleEdge c' c) :
    (condensationRank c' < condensationRank c) ∨
    (condensationRank c' = condensationRank c ∧ sccSubRank c' < sccSubRank c) ∨
    (c.1 = 239 ∧ c'.1 = 245) := by
  have hclosed : ∀ (c' c : SixState), sixTupleEdge c' c →
      (condensationRank c' < condensationRank c) ∨
      (condensationRank c' = condensationRank c ∧ sccSubRank c' < sccSubRank c) ∨
      (c.1 = 239 ∧ c'.1 = 245) := by native_decide
  exact hclosed c' c h

def sixBoundaryEdge (s' s : SixBoundary) : Prop :=
  sixTupleEdge s'.encode s.encode

instance (s' s : SixBoundary) : Decidable (sixBoundaryEdge s' s) := by
  unfold sixBoundaryEdge
  infer_instance

-- sixBoundaryEdge_wf is unused; the WF proof now goes through ConstLayerDAG's 4-component lex.

def IsB1Boundary (s : SixBoundary) : Prop :=
  s.cN1.1 = 0 ∧ s.c0.1 = 0 ∧ s.c1.1 = 0

def IsB2Boundary (s : SixBoundary) : Prop :=
  s.cN1.1 = 1 ∧ s.c0.1 = 1 ∧ s.c1.1 = 2

def IsB3Boundary (s : SixBoundary) : Prop :=
  s.cN3.1 = 1 ∧ s.cN2.1 = 1 ∧ s.cN1.1 = 1

def IsB4Boundary (s : SixBoundary) : Prop :=
  s.cN2.1 = 2 ∧ s.cN1.1 = 0 ∧ s.c0.1 = 0

def b1BoundarySucc (s : SixBoundary) : SixBoundary :=
  { s with c0 := 1 }

def b2BoundarySucc (s : SixBoundary) : SixBoundary :=
  { s with c0 := 0 }

def b3BoundarySucc (s : SixBoundary) : SixBoundary :=
  { s with cN2 := 2 }

def b4BoundarySucc (s : SixBoundary) : SixBoundary :=
  { s with cN1 := 1 }

def cup2BoundaryIdx0 (n : Nat) (hn : 9 ≤ n) : Fin n :=
  ⟨0, by omega⟩

def cup2BoundaryIdx1 (n : Nat) (hn : 9 ≤ n) : Fin n :=
  ⟨1, by omega⟩

def cup2BoundaryIdx2 (n : Nat) (hn : 9 ≤ n) : Fin n :=
  ⟨2, by omega⟩

def cup2BoundaryIdxN3 (n : Nat) (hn : 9 ≤ n) : Fin n :=
  ⟨n - 3, by omega⟩

def cup2BoundaryIdxN2 (n : Nat) (hn : 9 ≤ n) : Fin n :=
  ⟨n - 2, by omega⟩

def cup2BoundaryIdxN1 (n : Nat) (hn : 9 ≤ n) : Fin n :=
  ⟨n - 1, by omega⟩

@[simp] theorem left_cup2BoundaryIdx0 (n : Nat) (hn : 9 ≤ n) :
    left (cup2BoundaryIdx0 n hn) = cup2BoundaryIdxN1 n hn := by
  apply Fin.ext
  simp [left_val, cup2BoundaryIdx0, cup2BoundaryIdxN1]

@[simp] theorem right_cup2BoundaryIdx0 (n : Nat) (hn : 9 ≤ n) :
    right (cup2BoundaryIdx0 n hn) = cup2BoundaryIdx1 n hn := by
  apply Fin.ext
  have hlt : 1 < n := by omega
  simp [right_val, cup2BoundaryIdx0, cup2BoundaryIdx1, Nat.mod_eq_of_lt hlt]

@[simp] theorem left_cup2BoundaryIdx1 (n : Nat) (hn : 9 ≤ n) :
    left (cup2BoundaryIdx1 n hn) = cup2BoundaryIdx0 n hn := by
  apply Fin.ext
  simp [left_val, cup2BoundaryIdx0, cup2BoundaryIdx1]

@[simp] theorem right_cup2BoundaryIdx1 (n : Nat) (hn : 9 ≤ n) :
    right (cup2BoundaryIdx1 n hn) = cup2BoundaryIdx2 n hn := by
  apply Fin.ext
  have hlt : 2 < n := by omega
  simp [right_val, cup2BoundaryIdx1, cup2BoundaryIdx2, Nat.mod_eq_of_lt hlt]

@[simp] theorem left_cup2BoundaryIdx2 (n : Nat) (hn : 9 ≤ n) :
    left (cup2BoundaryIdx2 n hn) = cup2BoundaryIdx1 n hn := by
  apply Fin.ext
  have hge : 2 + n - 1 ≥ n := by omega
  have hlt : 1 < n := by omega
  rw [left_val, cup2BoundaryIdx2, cup2BoundaryIdx1, Nat.mod_eq_sub_mod hge]
  simp [Nat.mod_eq_of_lt hlt]

@[simp] theorem right_cup2BoundaryIdxN3 (n : Nat) (hn : 9 ≤ n) :
    right (cup2BoundaryIdxN3 n hn) = cup2BoundaryIdxN2 n hn := by
  apply Fin.ext
  have hsum : n - 3 + 1 = n - 2 := by omega
  have hlt : n - 2 < n := by omega
  rw [right_val, cup2BoundaryIdxN3, cup2BoundaryIdxN2, hsum]
  exact Nat.mod_eq_of_lt hlt

@[simp] theorem left_cup2BoundaryIdxN2 (n : Nat) (hn : 9 ≤ n) :
    left (cup2BoundaryIdxN2 n hn) = cup2BoundaryIdxN3 n hn := by
  apply Fin.ext
  have hge : n - 2 + n - 1 ≥ n := by omega
  have hsub : n - 2 + n - 1 - n = n - 3 := by omega
  have hlt : n - 3 < n := by omega
  rw [left_val, cup2BoundaryIdxN2, cup2BoundaryIdxN3, Nat.mod_eq_sub_mod hge]
  rw [hsub]
  exact Nat.mod_eq_of_lt hlt

@[simp] theorem right_cup2BoundaryIdxN2 (n : Nat) (hn : 9 ≤ n) :
    right (cup2BoundaryIdxN2 n hn) = cup2BoundaryIdxN1 n hn := by
  apply Fin.ext
  have hsum : n - 2 + 1 = n - 1 := by omega
  have hlt : n - 1 < n := by omega
  rw [right_val, cup2BoundaryIdxN2, cup2BoundaryIdxN1, hsum]
  exact Nat.mod_eq_of_lt hlt

@[simp] theorem left_cup2BoundaryIdxN1 (n : Nat) (hn : 9 ≤ n) :
    left (cup2BoundaryIdxN1 n hn) = cup2BoundaryIdxN2 n hn := by
  apply Fin.ext
  have hge : n - 1 + n - 1 ≥ n := by omega
  have hsub : n - 1 + n - 1 - n = n - 2 := by omega
  have hlt : n - 2 < n := by omega
  rw [left_val, cup2BoundaryIdxN1, cup2BoundaryIdxN2, Nat.mod_eq_sub_mod hge]
  rw [hsub]
  exact Nat.mod_eq_of_lt hlt

@[simp] theorem right_cup2BoundaryIdxN1 (n : Nat) (hn : 9 ≤ n) :
    right (cup2BoundaryIdxN1 n hn) = cup2BoundaryIdx0 n hn := by
  apply Fin.ext
  have hsum : n - 1 + 1 = n := by omega
  rw [right_val, cup2BoundaryIdxN1, cup2BoundaryIdx0, hsum]
  simp

@[simp] theorem cup2OutVal_boundaryIdx0 (n : Nat) (hn : 9 ≤ n) (L S R : Nat) :
    cup2OutVal n (cup2BoundaryIdx0 n hn) L S R = TBotVal L S R := by
  simp [cup2OutVal, cup2BoundaryIdx0]

@[simp] theorem cup2OutVal_boundaryIdx1 (n : Nat) (hn : 9 ≤ n) (L S R : Nat) :
    cup2OutVal n (cup2BoundaryIdx1 n hn) L S R = TLowVal L S R := by
  simp [cup2OutVal, cup2BoundaryIdx1]

@[simp] theorem cup2OutVal_boundaryIdx2 (n : Nat) (hn : 9 ≤ n) (L S R : Nat) :
    cup2OutVal n (cup2BoundaryIdx2 n hn) L S R = TMidVal L S R := by
  have h3 : ¬ 3 = n := by omega
  have h4 : ¬ 4 = n := by omega
  simp [cup2OutVal, cup2BoundaryIdx2, h3, h4]

@[simp] theorem cup2OutVal_boundaryIdxN3 (n : Nat) (hn : 9 ≤ n) (L S R : Nat) :
    cup2OutVal n (cup2BoundaryIdxN3 n hn) L S R = TMidVal L S R := by
  have h0 : ¬ (n - 3 = 0) := by omega
  have h1 : ¬ (n - 3 = 1) := by omega
  have hsum1 : n - 3 + 1 = n - 2 := by omega
  have hsum2 : n - 3 + 2 = n - 1 := by omega
  have htop : ¬ (n - 2 = n) := by omega
  have hhigh : ¬ (n - 1 = n) := by omega
  simp [cup2OutVal, cup2BoundaryIdxN3, h0, h1, hsum1, hsum2, htop, hhigh]

@[simp] theorem cup2OutVal_boundaryIdxN2 (n : Nat) (hn : 9 ≤ n) (L S R : Nat) :
    cup2OutVal n (cup2BoundaryIdxN2 n hn) L S R = THighVal L S R := by
  have h0 : ¬ (n - 2 = 0) := by omega
  have h1 : ¬ (n - 2 = 1) := by omega
  have htop : ¬ (n - 2 + 1 = n) := by omega
  have hhigh : n - 2 + 2 = n := by omega
  simp [cup2OutVal, cup2BoundaryIdxN2, h0, h1, htop, hhigh]

@[simp] theorem cup2OutVal_boundaryIdxN1 (n : Nat) (hn : 9 ≤ n) (L S R : Nat) :
    cup2OutVal n (cup2BoundaryIdxN1 n hn) L S R = TTopVal L S R := by
  have h0 : ¬ (n - 1 = 0) := by omega
  have h1 : ¬ (n - 1 = 1) := by omega
  have htop : n - 1 + 1 = n := by omega
  simp [cup2OutVal, cup2BoundaryIdxN1, h0, h1, htop]

def cup2Boundary6 (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) : SixBoundary where
  c0 := Fin.cast (by
    exact cup2M_eq_two_of_endpoint
      (n := n) (i := cup2BoundaryIdx0 n hn9) (Or.inl rfl)) (c (cup2BoundaryIdx0 n hn9))
  c1 := Fin.cast (by
    exact cup2M_self_low hn4 (i := cup2BoundaryIdx1 n hn9) rfl) (c (cup2BoundaryIdx1 n hn9))
  c2 := Fin.cast (by
    have h0 : (cup2BoundaryIdx2 n hn9).1 ≠ 0 := by
      simp [cup2BoundaryIdx2]
    have htop : (cup2BoundaryIdx2 n hn9).1 + 1 ≠ n := by
      simp [cup2BoundaryIdx2]
      omega
    exact cup2M_self_mid hn4 (i := cup2BoundaryIdx2 n hn9) h0 htop) (c (cup2BoundaryIdx2 n hn9))
  cN3 := Fin.cast (by
    have h0 : (cup2BoundaryIdxN3 n hn9).1 ≠ 0 := by
      simp [cup2BoundaryIdxN3]
      omega
    have htop : (cup2BoundaryIdxN3 n hn9).1 + 1 ≠ n := by
      simp [cup2BoundaryIdxN3]
      omega
    exact cup2M_self_mid hn4 (i := cup2BoundaryIdxN3 n hn9) h0 htop) (c (cup2BoundaryIdxN3 n hn9))
  cN2 := Fin.cast (by
    have hhigh : (cup2BoundaryIdxN2 n hn9).1 + 2 = n := by
      simp [cup2BoundaryIdxN2]
      omega
    exact cup2M_self_high hn4 (i := cup2BoundaryIdxN2 n hn9) hhigh) (c (cup2BoundaryIdxN2 n hn9))
  cN1 := Fin.cast (by
    have htop : (cup2BoundaryIdxN1 n hn9).1 + 1 = n := by
      simp [cup2BoundaryIdxN1]
      omega
    exact cup2M_eq_two_of_endpoint
      (n := n) (i := cup2BoundaryIdxN1 n hn9) (Or.inr htop)) (c (cup2BoundaryIdxN1 n hn9))

def cup2BoundaryState (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) : SixState :=
  (cup2Boundary6 n hn4 hn9 c).encode

theorem cup2Boundary6_move_eq_of_deep (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hleft : 2 < i.1) (hright : i.1 + 3 < n) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c i) = cup2Boundary6 n hn4 hn9 c := by
  have hneq0 : cup2BoundaryIdx0 n hn9 ≠ i := by
    intro h
    have hval : 0 = i.1 := by simpa [cup2BoundaryIdx0] using congrArg Fin.val h
    omega
  have hneq1 : cup2BoundaryIdx1 n hn9 ≠ i := by
    intro h
    have hval : 1 = i.1 := by simpa [cup2BoundaryIdx1] using congrArg Fin.val h
    omega
  have hneq2 : cup2BoundaryIdx2 n hn9 ≠ i := by
    intro h
    have hval : 2 = i.1 := by simpa [cup2BoundaryIdx2] using congrArg Fin.val h
    omega
  have hneqN3 : cup2BoundaryIdxN3 n hn9 ≠ i := by
    intro h
    have hval : n - 3 = i.1 := by simpa [cup2BoundaryIdxN3] using congrArg Fin.val h
    omega
  have hneqN2 : cup2BoundaryIdxN2 n hn9 ≠ i := by
    intro h
    have hval : n - 2 = i.1 := by simpa [cup2BoundaryIdxN2] using congrArg Fin.val h
    omega
  have hneqN1 : cup2BoundaryIdxN1 n hn9 ≠ i := by
    intro h
    have hval : n - 1 = i.1 := by simpa [cup2BoundaryIdxN1] using congrArg Fin.val h
    omega
  ext <;>
    simp [cup2Boundary6, move, hneq0, hneq1, hneq2, hneqN3, hneqN2, hneqN1]

theorem cup2BoundaryState_move_eq_of_deep (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hleft : 2 < i.1) (hright : i.1 + 3 < n) :
    cup2BoundaryState n hn4 hn9 (move (cup2System n hn4) c i) =
      cup2BoundaryState n hn4 hn9 c := by
  simp [cup2BoundaryState, cup2Boundary6_move_eq_of_deep n hn4 hn9 c i hleft hright]

theorem cup2BoundaryState_changed_implies_boundary_index (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hchange : cup2BoundaryState n hn4 hn9 (move (cup2System n hn4) c i) ≠
      cup2BoundaryState n hn4 hn9 c) :
    i.1 ≤ 2 ∨ n - 3 ≤ i.1 := by
  by_cases hle : i.1 ≤ 2
  · exact Or.inl hle
  · right
    by_contra hlt
    have hleft : 2 < i.1 := lt_of_not_ge hle
    have hright : i.1 + 3 < n := by omega
    exact hchange (cup2BoundaryState_move_eq_of_deep n hn4 hn9 c i hleft hright)

theorem cup2Boundary6_changed_implies_boundary_index (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hchange : cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c i) ≠
      cup2Boundary6 n hn4 hn9 c) :
    i.1 ≤ 2 ∨ n - 3 ≤ i.1 := by
  by_cases hle : i.1 ≤ 2
  · exact Or.inl hle
  · right
    by_contra hlt
    have hleft : 2 < i.1 := lt_of_not_ge hle
    have hright : i.1 + 3 < n := by omega
    exact hchange (cup2Boundary6_move_eq_of_deep n hn4 hn9 c i hleft hright)

theorem cup2Boundary6_changed_of_boundary_move (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hpriv : privileged (cup2System n hn4) c i)
    (hboundary : i.1 ≤ 2 ∨ n - 3 ≤ i.1) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c i) ≠
      cup2Boundary6 n hn4 hn9 c := by
  have hpriv_val :
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 ≠ (c i).1 := by
    simpa [privileged, cup2System, cup2Trans_val, Fin.ne_iff_vne] using hpriv
  intro heq
  rcases hboundary with hleft | hright
  · by_cases hi0 : i.1 = 0
    · have hi : i = cup2BoundaryIdx0 n hn9 := by
        apply Fin.ext
        simp [cup2BoundaryIdx0, hi0]
      subst i
      have hfield := congrArg SixBoundary.c0 heq
      have hval : cup2OutVal n (cup2BoundaryIdx0 n hn9)
          (c (left (cup2BoundaryIdx0 n hn9))).1 (c (cup2BoundaryIdx0 n hn9)).1
          (c (right (cup2BoundaryIdx0 n hn9))).1 = (c (cup2BoundaryIdx0 n hn9)).1 := by
        have hfield' : (cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9))).c0 =
            (cup2Boundary6 n hn4 hn9 c).c0 := hfield
        have hval' := congrArg Fin.val hfield'
        simpa [cup2Boundary6, cup2BoundaryIdx0, move_apply_self_val] using hval'
      exact hpriv_val hval
    · by_cases hi1 : i.1 = 1
      · have hi : i = cup2BoundaryIdx1 n hn9 := by
          apply Fin.ext
          simp [cup2BoundaryIdx1, hi1]
        subst i
        have hfield := congrArg SixBoundary.c1 heq
        have hval : cup2OutVal n (cup2BoundaryIdx1 n hn9)
            (c (left (cup2BoundaryIdx1 n hn9))).1 (c (cup2BoundaryIdx1 n hn9)).1
            (c (right (cup2BoundaryIdx1 n hn9))).1 = (c (cup2BoundaryIdx1 n hn9)).1 := by
          have hfield' : (cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))).c1 =
              (cup2Boundary6 n hn4 hn9 c).c1 := hfield
          have hval' := congrArg Fin.val hfield'
          simpa [cup2Boundary6, cup2BoundaryIdx1, move_apply_self_val] using hval'
        exact hpriv_val hval
      · have hi2 : i.1 = 2 := by omega
        have hi : i = cup2BoundaryIdx2 n hn9 := by
          apply Fin.ext
          simp [cup2BoundaryIdx2, hi2]
        subst i
        have hfield := congrArg SixBoundary.c2 heq
        have hval : cup2OutVal n (cup2BoundaryIdx2 n hn9)
            (c (left (cup2BoundaryIdx2 n hn9))).1 (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1 = (c (cup2BoundaryIdx2 n hn9)).1 := by
          have hfield' : (cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))).c2 =
              (cup2Boundary6 n hn4 hn9 c).c2 := hfield
          have hval' := congrArg Fin.val hfield'
          simpa [cup2Boundary6, cup2BoundaryIdx2, move_apply_self_val] using hval'
        exact hpriv_val hval
  · by_cases hiN3 : i.1 = n - 3
    · have hi : i = cup2BoundaryIdxN3 n hn9 := by
        apply Fin.ext
        simp [cup2BoundaryIdxN3, hiN3]
      subst i
      have hfield := congrArg SixBoundary.cN3 heq
      have hval : cup2OutVal n (cup2BoundaryIdxN3 n hn9)
          (c (left (cup2BoundaryIdxN3 n hn9))).1 (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1 = (c (cup2BoundaryIdxN3 n hn9)).1 := by
        have hfield' : (cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9))).cN3 =
            (cup2Boundary6 n hn4 hn9 c).cN3 := hfield
        have hval' := congrArg Fin.val hfield'
        simpa [cup2Boundary6, cup2BoundaryIdxN3, move_apply_self_val] using hval'
      exact hpriv_val hval
    · by_cases hiN2 : i.1 = n - 2
      · have hi : i = cup2BoundaryIdxN2 n hn9 := by
          apply Fin.ext
          simp [cup2BoundaryIdxN2, hiN2]
        subst i
        have hfield := congrArg SixBoundary.cN2 heq
        have hval : cup2OutVal n (cup2BoundaryIdxN2 n hn9)
            (c (left (cup2BoundaryIdxN2 n hn9))).1 (c (cup2BoundaryIdxN2 n hn9)).1
            (c (right (cup2BoundaryIdxN2 n hn9))).1 = (c (cup2BoundaryIdxN2 n hn9)).1 := by
          have hfield' : (cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9))).cN2 =
              (cup2Boundary6 n hn4 hn9 c).cN2 := hfield
          have hval' := congrArg Fin.val hfield'
          simpa [cup2Boundary6, cup2BoundaryIdxN2, move_apply_self_val] using hval'
        exact hpriv_val hval
      · have hiN1 : i.1 = n - 1 := by omega
        have hi : i = cup2BoundaryIdxN1 n hn9 := by
          apply Fin.ext
          simp [cup2BoundaryIdxN1, hiN1]
        subst i
        have hfield := congrArg SixBoundary.cN1 heq
        have hval : cup2OutVal n (cup2BoundaryIdxN1 n hn9)
            (c (left (cup2BoundaryIdxN1 n hn9))).1 (c (cup2BoundaryIdxN1 n hn9)).1
            (c (right (cup2BoundaryIdxN1 n hn9))).1 = (c (cup2BoundaryIdxN1 n hn9)).1 := by
          have hfield' : (cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))).cN1 =
              (cup2Boundary6 n hn4 hn9 c).cN1 := hfield
          have hval' := congrArg Fin.val hfield'
          simpa [cup2Boundary6, cup2BoundaryIdxN1, move_apply_self_val] using hval'
        exact hpriv_val hval

theorem cup2Boundary6_move_idx0 (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
      { cup2Boundary6 n hn4 hn9 c with
          c0 := Fin.cast (by
            exact cup2M_eq_two_of_endpoint
              (n := n) (i := cup2BoundaryIdx0 n hn9) (Or.inl rfl))
            ((move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) (cup2BoundaryIdx0 n hn9)) } := by
  have hneq1 : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
  have hneq2 : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx0, cup2BoundaryIdx2] at hval
  have hneqN3 : cup2BoundaryIdxN3 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx0, cup2BoundaryIdxN3] at hval
    omega
  have hneqN2 : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx0, cup2BoundaryIdxN2] at hval
    omega
  have hneqN1 : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at hval
    omega
  ext
  · simp [cup2Boundary6, cup2BoundaryIdx0]
  · simp [cup2Boundary6, cup2BoundaryIdx0]
    simpa [cup2BoundaryIdx0] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hneq1)
  · simp [cup2Boundary6, cup2BoundaryIdx0]
    simpa [cup2BoundaryIdx0] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hneq2)
  · simp [cup2Boundary6, cup2BoundaryIdx0]
    simpa [cup2BoundaryIdx0] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN3 n hn9) hneqN3)
  · simp [cup2Boundary6, cup2BoundaryIdx0]
    simpa [cup2BoundaryIdx0] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9) hneqN2)
  · simp [cup2Boundary6, cup2BoundaryIdx0]
    simpa [cup2BoundaryIdx0] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hneqN1)

theorem cup2Boundary6_move_idx1 (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
      { cup2Boundary6 n hn4 hn9 c with
          c1 := Fin.cast (by
            exact cup2M_self_low hn4 (i := cup2BoundaryIdx1 n hn9) rfl)
            ((move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) (cup2BoundaryIdx1 n hn9)) } := by
  have hneq0 : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
  have hneq2 : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx1, cup2BoundaryIdx2] at hval
  have hneqN3 : cup2BoundaryIdxN3 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx1, cup2BoundaryIdxN3] at hval
    omega
  have hneqN2 : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx1, cup2BoundaryIdxN2] at hval
    omega
  have hneqN1 : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx1, cup2BoundaryIdxN1] at hval
    omega
  ext
  · simp [cup2Boundary6, cup2BoundaryIdx1]
    simpa [cup2BoundaryIdx1] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hneq0)
  · simp [cup2Boundary6, cup2BoundaryIdx1]
  · simp [cup2Boundary6, cup2BoundaryIdx1]
    simpa [cup2BoundaryIdx1] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx2 n hn9) hneq2)
  · simp [cup2Boundary6, cup2BoundaryIdx1]
    simpa [cup2BoundaryIdx1] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN3 n hn9) hneqN3)
  · simp [cup2Boundary6, cup2BoundaryIdx1]
    simpa [cup2BoundaryIdx1] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9) hneqN2)
  · simp [cup2Boundary6, cup2BoundaryIdx1]
    simpa [cup2BoundaryIdx1] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hneqN1)

theorem cup2Boundary6_move_idx2 (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) =
      { cup2Boundary6 n hn4 hn9 c with
          c2 := Fin.cast (by
            have h0 : (cup2BoundaryIdx2 n hn9).1 ≠ 0 := by
              simp [cup2BoundaryIdx2]
            have htop : (cup2BoundaryIdx2 n hn9).1 + 1 ≠ n := by
              simp [cup2BoundaryIdx2]
              omega
            exact cup2M_self_mid hn4 (i := cup2BoundaryIdx2 n hn9) h0 htop)
            ((move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) (cup2BoundaryIdx2 n hn9)) } := by
  have hneq0 : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx0, cup2BoundaryIdx2] at hval
  have hneq1 : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx1, cup2BoundaryIdx2] at hval
  have hneqN3 : cup2BoundaryIdxN3 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx2, cup2BoundaryIdxN3] at hval
    omega
  have hneqN2 : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx2, cup2BoundaryIdxN2] at hval
    omega
  have hneqN1 : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at hval
    omega
  ext
  · simp [cup2Boundary6, cup2BoundaryIdx2]
    simpa [cup2BoundaryIdx2] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx0 n hn9) hneq0)
  · simp [cup2Boundary6, cup2BoundaryIdx2]
    simpa [cup2BoundaryIdx2] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx1 n hn9) hneq1)
  · simp [cup2Boundary6, cup2BoundaryIdx2]
  · simp [cup2Boundary6, cup2BoundaryIdx2]
    simpa [cup2BoundaryIdx2] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN3 n hn9) hneqN3)
  · simp [cup2Boundary6, cup2BoundaryIdx2]
    simpa [cup2BoundaryIdx2] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN2 n hn9) hneqN2)
  · simp [cup2Boundary6, cup2BoundaryIdx2]
    simpa [cup2BoundaryIdx2] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN1 n hn9) hneqN1)

theorem cup2Boundary6_move_idxN3 (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) =
      { cup2Boundary6 n hn4 hn9 c with
          cN3 := Fin.cast (by
            have h0 : (cup2BoundaryIdxN3 n hn9).1 ≠ 0 := by
              simp [cup2BoundaryIdxN3]
              omega
            have htop : (cup2BoundaryIdxN3 n hn9).1 + 1 ≠ n := by
              simp [cup2BoundaryIdxN3]
              omega
            exact cup2M_self_mid hn4 (i := cup2BoundaryIdxN3 n hn9) h0 htop)
            ((move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) (cup2BoundaryIdxN3 n hn9)) } := by
  have hneq0 : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdxN3 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx0, cup2BoundaryIdxN3] at hval
    omega
  have hneq1 : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdxN3 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx1, cup2BoundaryIdxN3] at hval
    omega
  have hneq2 : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdxN3 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx2, cup2BoundaryIdxN3] at hval
    omega
  have hneqN2 : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdxN3 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdxN2, cup2BoundaryIdxN3] at hval
    omega
  have hneqN1 : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdxN3 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdxN1, cup2BoundaryIdxN3] at hval
    omega
  ext
  · simp [cup2Boundary6, cup2BoundaryIdxN3]
    simpa [cup2BoundaryIdxN3] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdxN3 n hn9) (cup2BoundaryIdx0 n hn9) hneq0)
  · simp [cup2Boundary6, cup2BoundaryIdxN3]
    simpa [cup2BoundaryIdxN3] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdxN3 n hn9) (cup2BoundaryIdx1 n hn9) hneq1)
  · simp [cup2Boundary6, cup2BoundaryIdxN3]
    simpa [cup2BoundaryIdxN3] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdxN3 n hn9) (cup2BoundaryIdx2 n hn9) hneq2)
  · simp [cup2Boundary6, cup2BoundaryIdxN3]
  · simp [cup2Boundary6, cup2BoundaryIdxN3]
    simpa [cup2BoundaryIdxN3] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdxN3 n hn9) (cup2BoundaryIdxN2 n hn9) hneqN2)
  · simp [cup2Boundary6, cup2BoundaryIdxN3]
    simpa [cup2BoundaryIdxN3] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdxN3 n hn9) (cup2BoundaryIdxN1 n hn9) hneqN1)

theorem cup2Boundary6_move_idxN2 (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)) =
      { cup2Boundary6 n hn4 hn9 c with
          cN2 := Fin.cast (by
            have hhigh : (cup2BoundaryIdxN2 n hn9).1 + 2 = n := by
              simp [cup2BoundaryIdxN2]
              omega
            exact cup2M_self_high hn4 (i := cup2BoundaryIdxN2 n hn9) hhigh)
            ((move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)) (cup2BoundaryIdxN2 n hn9)) } := by
  have hneq0 : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdxN2 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx0, cup2BoundaryIdxN2] at hval
    omega
  have hneq1 : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdxN2 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx1, cup2BoundaryIdxN2] at hval
    omega
  have hneq2 : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdxN2 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx2, cup2BoundaryIdxN2] at hval
    omega
  have hneqN3 : cup2BoundaryIdxN3 n hn9 ≠ cup2BoundaryIdxN2 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdxN3, cup2BoundaryIdxN2] at hval
    omega
  have hneqN1 : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdxN2 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdxN1, cup2BoundaryIdxN2] at hval
    omega
  ext
  · simp [cup2Boundary6, cup2BoundaryIdxN2]
    simpa [cup2BoundaryIdxN2] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2BoundaryIdx0 n hn9) hneq0)
  · simp [cup2Boundary6, cup2BoundaryIdxN2]
    simpa [cup2BoundaryIdxN2] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2BoundaryIdx1 n hn9) hneq1)
  · simp [cup2Boundary6, cup2BoundaryIdxN2]
    simpa [cup2BoundaryIdxN2] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2BoundaryIdx2 n hn9) hneq2)
  · simp [cup2Boundary6, cup2BoundaryIdxN2]
    simpa [cup2BoundaryIdxN2] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2BoundaryIdxN3 n hn9) hneqN3)
  · simp [cup2Boundary6, cup2BoundaryIdxN2]
  · simp [cup2Boundary6, cup2BoundaryIdxN2]
    simpa [cup2BoundaryIdxN2] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdxN2 n hn9) (cup2BoundaryIdxN1 n hn9) hneqN1)

theorem cup2Boundary6_move_idxN1 (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
      { cup2Boundary6 n hn4 hn9 c with
          cN1 := Fin.cast (by
            have htop : (cup2BoundaryIdxN1 n hn9).1 + 1 = n := by
              simp [cup2BoundaryIdxN1]
              omega
            exact cup2M_eq_two_of_endpoint
              (n := n) (i := cup2BoundaryIdxN1 n hn9) (Or.inr htop))
            ((move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) (cup2BoundaryIdxN1 n hn9)) } := by
  have hneq0 : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at hval
    omega
  have hneq1 : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx1, cup2BoundaryIdxN1] at hval
    omega
  have hneq2 : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at hval
    omega
  have hneqN3 : cup2BoundaryIdxN3 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdxN3, cup2BoundaryIdxN1] at hval
    omega
  have hneqN2 : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
    intro h
    have hval := congrArg Fin.val h
    simp [cup2BoundaryIdxN2, cup2BoundaryIdxN1] at hval
    omega
  ext
  · simp [cup2Boundary6, cup2BoundaryIdxN1]
    simpa [cup2BoundaryIdxN1] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx0 n hn9) hneq0)
  · simp [cup2Boundary6, cup2BoundaryIdxN1]
    simpa [cup2BoundaryIdxN1] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx1 n hn9) hneq1)
  · simp [cup2Boundary6, cup2BoundaryIdxN1]
    simpa [cup2BoundaryIdxN1] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx2 n hn9) hneq2)
  · simp [cup2Boundary6, cup2BoundaryIdxN1]
    simpa [cup2BoundaryIdxN1] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdxN3 n hn9) hneqN3)
  · simp [cup2Boundary6, cup2BoundaryIdxN1]
    simpa [cup2BoundaryIdxN1] using
      congrArg Fin.val (move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdxN2 n hn9) hneqN2)
  · simp [cup2Boundary6, cup2BoundaryIdxN1]

/-! ### Boundary successor functions for CUP-2 boundary moves -/

/-- Boundary successor at position 0 (bot): fires c[0] with L=c[n-1], S=c[0], R=c[1]. -/
def boundarySuccP0 (s : SixBoundary) : SixBoundary :=
  { s with c0 := ⟨TBotVal s.cN1.1 s.c0.1 s.c1.1,
      TBotVal_lt s.cN1.2 s.c0.2 (by have := s.c1.2; omega)⟩ }

/-- Boundary successor at position 1 (low): fires c[1] with L=c[0], S=c[1], R=c[2]. -/
def boundarySuccP1 (s : SixBoundary) : SixBoundary :=
  { s with c1 := ⟨TLowVal s.c0.1 s.c1.1 s.c2.1,
      TLowVal_lt (by have := s.c0.2; omega) s.c1.2 s.c2.2⟩ }

/-- Boundary successor at position 2 (mid): fires c[2] with L=c[1], S=c[2], R=c[3].
    The right neighbor c[3] is not in the 6-tuple, so we take it as a parameter. -/
def boundarySuccP2 (s : SixBoundary) (c3 : Fin 3) : SixBoundary :=
  { s with c2 := ⟨TMidVal s.c1.1 s.c2.1 c3.1, TMidVal_lt s.c1.2 s.c2.2 c3.2⟩ }

/-- Boundary successor at position n-3 (mid): fires c[n-3] with L=c[n-4], S=c[n-3], R=c[n-2].
    The left neighbor c[n-4] is not in the 6-tuple, so we take it as a parameter. -/
def boundarySuccPN3 (s : SixBoundary) (cn4 : Fin 3) : SixBoundary :=
  { s with cN3 := ⟨TMidVal cn4.1 s.cN3.1 s.cN2.1, TMidVal_lt cn4.2 s.cN3.2 s.cN2.2⟩ }

/-- Boundary successor at position n-2 (high): fires c[n-2] with L=c[n-3], S=c[n-2], R=c[n-1]. -/
def boundarySuccPN2 (s : SixBoundary) : SixBoundary :=
  { s with cN2 := ⟨THighVal s.cN3.1 s.cN2.1 s.cN1.1,
      THighVal_lt s.cN3.2 s.cN2.2 (by have := s.cN1.2; omega)⟩ }

/-- Boundary successor at position n-1 (top): fires c[n-1] with L=c[n-2], S=c[n-1], R=c[0]. -/
def boundarySuccPN1 (s : SixBoundary) : SixBoundary :=
  { s with cN1 := ⟨TTopVal s.cN2.1 s.cN1.1 s.c0.1,
      TTopVal_lt s.cN2.2 (by have := s.cN1.2; omega) (by have := s.c0.2; omega)⟩ }

/-! ### Boundary rank for fc-nondecreasing transitions -/

/-- Rank function for the fc-nondecreasing boundary DAG (max rank 13).
    Covers all privileged boundary transitions that don't decrease fc. -/
def fcNondecRankVals : List Nat :=
  [9, 1, 6, 2, 6, 0, 8, 0, 7, 3, 8, 2, 10, 2, 6, 2, 7, 1, 4, 1, 1, 2, 1, 0,
   3, 0, 2, 3, 3, 2, 5, 2, 1, 2, 2, 1, 10, 2, 7, 3, 7, 1, 9, 1, 8, 4, 9, 3,
   11, 3, 7, 3, 8, 2, 8, 3, 5, 4, 5, 2, 7, 2, 6, 5, 7, 4, 9, 4, 5, 4, 6, 3,
   7, 2, 4, 3, 4, 1, 6, 1, 5, 4, 6, 3, 8, 3, 4, 3, 5, 2, 6, 1, 3, 2, 3, 0,
   5, 0, 4, 3, 5, 2, 7, 2, 3, 2, 4, 1, 3, 1, 0, 2, 1, 0, 2, 0, 1, 3, 3, 2,
   4, 2, 0, 2, 2, 1, 12, 4, 9, 5, 9, 3, 11, 3, 10, 6, 11, 5, 13, 5, 9, 5,
   10, 4, 11, 3, 8, 4, 8, 2, 10, 2, 9, 5, 10, 4, 12, 4, 8, 4, 9, 3, 8, 9,
   5, 10, 5, 7, 7, 8, 6, 10, 7, 9, 9, 10, 5, 9, 6, 8, 3, 4, 0, 5, 0, 1,
   2, 3, 1, 4, 2, 3, 4, 5, 0, 3, 1, 2, 9, 10, 6, 11, 6, 8, 8, 9, 7, 11,
   8, 10, 10, 11, 6, 10, 7, 9, 7, 8, 4, 9, 4, 6, 6, 7, 5, 9, 6, 8, 8, 9,
   4, 8, 5, 7, 6, 7, 3, 8, 3, 5, 5, 6, 4, 8, 5, 7, 7, 8, 3, 7, 4, 6,
   5, 6, 2, 7, 2, 4, 4, 5, 3, 7, 4, 6, 6, 7, 2, 6, 3, 5, 3, 4, 0, 5,
   0, 1, 2, 3, 1, 4, 2, 3, 4, 5, 0, 3, 1, 2, 5, 6, 2, 7, 2, 4, 4, 5,
   3, 7, 4, 6, 6, 7, 2, 6, 3, 5, 4, 5, 1, 6, 1, 3, 3, 4, 2, 6, 3, 5,
   5, 6, 1, 5, 2, 4]

def fcNondecRank (s : SixBoundary) : Nat :=
  match fcNondecRankVals[s.encode.1]? with
  | some r => r
  | none => 0

/-- Local fc contribution: number of frontier edges touching position i.
    delta_fc = localFcAfter - localFcBefore for the two edges adjacent to i. -/
def localFcDelta (L S R S_new : Nat) : Int :=
  ((if L != S_new then 1 else 0) - (if L != S then 1 else 0) +
   (if S_new != R then 1 else 0) - (if S != R then 1 else 0) : Int)

/-- Whether a boundary move at position 0 is fc-nondecreasing. -/
def fcNondecP0 (s : SixBoundary) : Bool :=
  localFcDelta s.cN1.1 s.c0.1 s.c1.1 (TBotVal s.cN1.1 s.c0.1 s.c1.1) ≥ 0

/-- Whether a boundary move at position 1 is fc-nondecreasing. -/
def fcNondecP1 (s : SixBoundary) : Bool :=
  localFcDelta s.c0.1 s.c1.1 s.c2.1 (TLowVal s.c0.1 s.c1.1 s.c2.1) ≥ 0

/-- Whether a boundary move at position 2 is fc-nondecreasing. -/
def fcNondecP2 (s : SixBoundary) (c3 : Fin 3) : Bool :=
  localFcDelta s.c1.1 s.c2.1 c3.1 (TMidVal s.c1.1 s.c2.1 c3.1) ≥ 0

/-- Whether a boundary move at position n-3 is fc-nondecreasing. -/
def fcNondecPN3 (s : SixBoundary) (cn4 : Fin 3) : Bool :=
  localFcDelta cn4.1 s.cN3.1 s.cN2.1 (TMidVal cn4.1 s.cN3.1 s.cN2.1) ≥ 0

/-- Whether a boundary move at position n-2 is fc-nondecreasing. -/
def fcNondecPN2 (s : SixBoundary) : Bool :=
  localFcDelta s.cN3.1 s.cN2.1 s.cN1.1 (THighVal s.cN3.1 s.cN2.1 s.cN1.1) ≥ 0

/-- Whether a boundary move at position n-1 is fc-nondecreasing. -/
def fcNondecPN1 (s : SixBoundary) : Bool :=
  localFcDelta s.cN2.1 s.cN1.1 s.c0.1 (TTopVal s.cN2.1 s.cN1.1 s.c0.1) ≥ 0

/-! ### Decode utility for SixBoundary -/

/-- Decode a SixState index back to a SixBoundary (inverse of encode). -/
def decodeSixBoundary (idx : Nat) : SixBoundary :=
  let cN1 := idx % 2
  let rest := idx / 2
  let cN2 := rest % 3
  let rest := rest / 3
  let cN3 := rest % 3
  let rest := rest / 3
  let c2 := rest % 3
  let rest := rest / 3
  let c1 := rest % 3
  let c0 := rest / 3
  { c0 := ⟨c0 % 2, Nat.mod_lt _ (by omega)⟩,
    c1 := ⟨c1 % 3, Nat.mod_lt _ (by omega)⟩,
    c2 := ⟨c2 % 3, Nat.mod_lt _ (by omega)⟩,
    cN3 := ⟨cN3 % 3, Nat.mod_lt _ (by omega)⟩,
    cN2 := ⟨cN2 % 3, Nat.mod_lt _ (by omega)⟩,
    cN1 := ⟨cN1 % 2, Nat.mod_lt _ (by omega)⟩ }

/-- Decode is a left inverse of encode for all SixBoundary values. -/
theorem decodeSixBoundary_encode :
    ∀ s : SixBoundary, decodeSixBoundary s.encode.1 = s := by
  native_decide

/-! ### SCC shared-field lemmas: all states in {239,245,251} share boundary fields except cN3 -/

/-- All SCC states share the same c0, c1, c2, cN2, cN1 values. -/
theorem scc_shared_fields (s s' : SixBoundary)
    (hs : s.encode.1 ∈ ({239, 245, 251} : Finset Nat))
    (hs' : s'.encode.1 ∈ ({239, 245, 251} : Finset Nat)) :
    s.c0 = s'.c0 ∧ s.c1 = s'.c1 ∧ s.c2 = s'.c2 ∧ s.cN2 = s'.cN2 ∧ s.cN1 = s'.cN1 := by
  have := fun (s s' : SixBoundary) =>
    fun (hs : s.encode.1 ∈ ({239, 245, 251} : Finset Nat)) =>
    fun (hs' : s'.encode.1 ∈ ({239, 245, 251} : Finset Nat)) =>
    (s.c0 = s'.c0 ∧ s.c1 = s'.c1 ∧ s.c2 = s'.c2 ∧ s.cN2 = s'.cN2 ∧ s.cN1 = s'.cN1)
  -- Use native_decide on the decidable proposition
  have hclosed : ∀ (s s' : SixBoundary),
      s.encode.1 ∈ ({239, 245, 251} : Finset Nat) →
      s'.encode.1 ∈ ({239, 245, 251} : Finset Nat) →
      s.c0 = s'.c0 ∧ s.c1 = s'.c1 ∧ s.c2 = s'.c2 ∧ s.cN2 = s'.cN2 ∧ s.cN1 = s'.cN1 := by
    native_decide
  exact hclosed s s' hs hs'

/-- SCC membership from sixTupleEdge with condensationRank equal and sccSubRank dropping. -/
theorem scc_membership_of_edge_cond_eq_scc_drop (s' s : SixState)
    (hedge : sixTupleEdge s' s)
    (hcond : condensationRank s' = condensationRank s)
    (hscc : sccSubRank s' < sccSubRank s) :
    s.1 ∈ ({239, 245, 251} : Finset Nat) ∧ s'.1 ∈ ({239, 245, 251} : Finset Nat) := by
  have hclosed : ∀ (s' s : SixState), sixTupleEdge s' s → condensationRank s' = condensationRank s →
      sccSubRank s' < sccSubRank s →
      s.1 ∈ ({239, 245, 251} : Finset Nat) ∧ s'.1 ∈ ({239, 245, 251} : Finset Nat) := by
    native_decide
  exact hclosed s' s hedge hcond hscc

/-! ### Native-decide: fc-nondecreasing privileged boundary transitions decrease fcNondecRank -/

theorem fcNondecRank_drop_P0 :
    ∀ s : SixBoundary, (boundarySuccP0 s).c0 ≠ s.c0 → fcNondecP0 s = true →
      fcNondecRank (boundarySuccP0 s) < fcNondecRank s := by
  native_decide

theorem fcNondecRank_drop_P1 :
    ∀ s : SixBoundary, (boundarySuccP1 s).c1 ≠ s.c1 → fcNondecP1 s = true →
      fcNondecRank (boundarySuccP1 s) < fcNondecRank s := by
  native_decide

theorem fcNondecRank_drop_P2 :
    ∀ (s : SixBoundary) (c3 : Fin 3),
      (boundarySuccP2 s c3).c2 ≠ s.c2 → fcNondecP2 s c3 = true →
        fcNondecRank (boundarySuccP2 s c3) < fcNondecRank s := by
  native_decide

-- fcNondecRank_drop_PN3 removed: dead code (old approach, not imported anywhere).

theorem fcNondecRank_drop_PN2 :
    ∀ s : SixBoundary, (boundarySuccPN2 s).cN2 ≠ s.cN2 → fcNondecPN2 s = true →
      fcNondecRank (boundarySuccPN2 s) < fcNondecRank s := by
  native_decide

theorem fcNondecRank_drop_PN1 :
    ∀ s : SixBoundary, (boundarySuccPN1 s).cN1 ≠ s.cN1 → fcNondecPN1 s = true →
      fcNondecRank (boundarySuccPN1 s) < fcNondecRank s := by
  native_decide

end LeanMn
