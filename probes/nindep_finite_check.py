"""Finite 8-tuple check for period3_noCopy_nIndep.

Key insight: boundary-changing step has mover in {0,1,2,n-3,n-2,n-1}.
The boundary transition depends ONLY on the 8-tuple:
  (c[0], c[1], c[2], c[3], c[n-4], c[n-3], c[n-2], c[n-1])
and this is n-independent for n >= 10.

Check: for ALL valid 8-tuples and ALL boundary movers,
if the step is privileged and boundary-changing,
is the boundary transition in isNoCopyEdge?

If YES: period3_noCopy_nIndep follows from the finite check alone,
WITHOUT needing TP-preserving or no-drop hypotheses.
"""

# Transition tables from CUP-2
TLow = {(0,0):1,(0,1):0,(0,2):0,(1,0):1,(1,1):0,(1,2):2,(2,0):0,(2,1):2,(2,2):1}
THigh = {(0,0,0):1,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):1,
         (1,0,0):1,(1,0,1):1,(1,1,0):0,(1,1,1):2,(1,2,0):1,(1,2,1):1,
         (2,0,0):2,(2,0,1):2,(2,1,0):2,(2,1,1):0,(2,2,0):0,(2,2,1):2}
TMid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,
        (0,2,0):0,(0,2,1):0,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
        (1,1,0):1,(1,1,1):1,(1,1,2):1,(1,2,0):1,(1,2,1):1,(1,2,2):1,
        (2,0,0):2,(2,0,1):2,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,
        (2,2,0):0,(2,2,1):2,(2,2,2):2}

# SixBoundary encoding: encode(c0,c1,c2,cn3,cn2,cn1) =
#   ((((c0*3+c1)*3+c2)*3+cn3)*3+cn2)*2+cn1
def encode6(c0, c1, c2, cn3, cn2, cn1):
    return ((((c0*3+c1)*3+c2)*3+cn3)*3+cn2)*2+cn1

# noCopyEdgeCodes from CPhiDelete.lean (335 entries)
noCopyEdgeCodes = [
  973, 1952, 2277, 2927, 3256, 3581, 6823, 7802, 8127, 8777, 9106, 9431, 11664, 11989, 12314,
  12639, 12673, 12964, 13289, 13614, 13652, 13939, 13977, 14264, 14589, 14627, 14914, 14956, 15239, 15281,
  15564, 15889, 16214, 16539, 16864, 17189, 17568, 17893, 18218, 18523, 18543, 18851, 18868, 19193, 19502,
  19518, 19827, 19843, 20168, 20477, 20493, 20801, 20806, 20818, 21131, 21143, 21468, 21793, 22118, 22443,
  22751, 22768, 23093, 23418, 23743, 24068, 24373, 24393, 24701, 24718, 25043, 25352, 25368, 25677, 25693,
  26018, 26327, 26343, 26651, 26656, 26668, 26981, 26993, 27318, 27643, 27968, 28293, 28601, 28618, 28943,
  30223, 30551, 31202, 31527, 32177, 32501, 32506, 32831, 34451, 36073, 36401, 37052, 37377, 38027, 38351,
  38356, 38681, 40301, 40932, 41257, 41582, 41907, 41923, 42232, 42251, 42557, 42882, 42902, 43207, 43227,
  43532, 43857, 43877, 44182, 44201, 44206, 44507, 44531, 44832, 45157, 45482, 45807, 46132, 46151, 46457,
  46692, 47017, 47342, 47667, 47773, 47992, 48317, 48642, 48752, 48967, 49077, 49292, 49617, 49727, 49942,
  50056, 50267, 50381, 50592, 50917, 51242, 51567, 51892, 52217, 52974, 53623, 54602, 54924, 54927, 55251,
  55577, 55906, 56231, 56874, 58824, 59473, 60452, 60774, 60777, 61101, 61427, 61756, 62081, 62724, 64314,
  64639, 64674, 64964, 65289, 65323, 65614, 65939, 66264, 66302, 66589, 66624, 66627, 66914, 66951, 67239,
  67277, 67564, 67606, 67889, 67931, 68214, 68539, 68574, 68864, 69189, 69514, 69839, 70218, 70524, 70543,
  70868, 71173, 71193, 71518, 71843, 72152, 72168, 72474, 72477, 72493, 72801, 72818, 73127, 73143, 73456,
  73468, 73781, 73793, 74118, 74424, 74443, 74768, 75093, 75418, 75743, 76068, 76374, 76393, 76718, 77023,
  77043, 77368, 77693, 78002, 78018, 78324, 78327, 78343, 78651, 78668, 78977, 78993, 79306, 79318, 79631,
  79643, 79968, 80274, 80293, 80618, 80943, 81268, 81593, 81954, 82224, 82279, 82604, 82873, 82929, 83254,
  83579, 83852, 83904, 84174, 84177, 84229, 84501, 84554, 84827, 84879, 85156, 85204, 85481, 85529, 85854,
  86179, 86504, 86829, 87154, 87479, 88074, 88723, 89702, 90024, 90027, 90351, 90677, 91006, 91331, 93582,
  93907, 93924, 94232, 94557, 94573, 94882, 95207, 95532, 95552, 95857, 95874, 95877, 96182, 96201, 96507,
  96527, 96832, 96856, 97157, 97181, 97482, 97807, 98132, 98457, 98782, 99107, 99774, 100423, 101402, 101724,
  101727, 102051, 102377, 102706, 103031]
noCopyEdgeSet = set(noCopyEdgeCodes)

def isNoCopyEdge(dst_enc, src_enc):
    return (src_enc * 324 + dst_enc) in noCopyEdgeSet

# For each "mover type" (which boundary position fires),
# compute the transition output and new boundary6.
# Mover types: 0, 1, 2, "n-3", "n-2", "n-1"
# 8-tuple: (v0, v1, v2, v3, vn4, vn3, vn2, vn1)
# boundary6_src: (v0, v1, v2, vn3, vn2, vn1)

def check_mover(v0, v1, v2, v3, vn4, vn3, vn2, vn1, mover):
    """Returns (privileged, bdry_changes, in_noCopyEdge, src_enc, dst_enc) or None."""
    src_bdry = (v0, v1, v2, vn3, vn2, vn1)
    src_enc = encode6(*src_bdry)

    if mover == 0:
        # TBot: output = (v0+1)%2. Neighbors: left=vn1 (wrap), right=v1
        out = (v0 + 1) % 2
        if out == v0: return None  # not privileged
        dst_bdry = (out, v1, v2, vn3, vn2, vn1)
    elif mover == 1:
        # TLow: output = TLow[(v1, v2)]. Neighbors: left=v0, right=v2
        out = TLow.get((v1, v2), v1)
        if out == v1: return None
        dst_bdry = (v0, out, v2, vn3, vn2, vn1)
    elif mover == 2:
        # TMid: output = TMid[(v1, v2, v3)]. Neighbors: left=v1, right=v3
        out = TMid.get((v1, v2, v3), v2)
        if out == v2: return None
        dst_bdry = (v0, v1, out, vn3, vn2, vn1)
    elif mover == 'n-3':
        # TMid: output = TMid[(vn4, vn3, vn2)]. Neighbors: left=vn4, right=vn2
        out = TMid.get((vn4, vn3, vn2), vn3)
        if out == vn3: return None
        dst_bdry = (v0, v1, v2, out, vn2, vn1)
    elif mover == 'n-2':
        # THigh: output = THigh[(vn3, vn2, vn1)]. Neighbors: left=vn3, right=vn1
        out = THigh.get((vn3, vn2, vn1), vn2)
        if out == vn2: return None
        dst_bdry = (v0, v1, v2, vn3, out, vn1)
    elif mover == 'n-1':
        # TTop: output = (vn1+1)%2. Neighbors: left=vn2, right=v0 (wrap)
        out = (vn1 + 1) % 2
        if out == vn1: return None
        dst_bdry = (v0, v1, v2, vn3, vn2, out)
    else:
        return None

    dst_enc = encode6(*dst_bdry)
    if dst_enc == src_enc:
        return None  # boundary didn't change (encoded same)

    return (True, True, isNoCopyEdge(dst_enc, src_enc), src_enc, dst_enc)

# Enumerate ALL valid 8-tuples
# Constraints: v0 in {0,1}, vn1 in {0,1}, others in {0,1,2}
# From no-copy: vn4 != vn3
movers = [0, 1, 2, 'n-3', 'n-2', 'n-1']

total_privileged_bdry_changing = 0
total_in_noCopyEdge = 0
total_NOT_in_noCopyEdge = 0
failures = []

# Also check WITHOUT the vn4 != vn3 constraint (to see if no-copy matters)
total_no_constraint = 0
fail_no_constraint = 0

for v0 in range(2):
  for v1 in range(3):
    for v2 in range(3):
      for v3 in range(3):
        for vn4 in range(3):
          for vn3 in range(3):
            for vn2 in range(3):
              for vn1 in range(2):
                for mover in movers:
                    result = check_mover(v0, v1, v2, v3, vn4, vn3, vn2, vn1, mover)
                    if result is None:
                        continue
                    _, _, in_nce, src_enc, dst_enc = result

                    # Track with and without no-copy constraint
                    total_no_constraint += 1
                    if not in_nce:
                        fail_no_constraint += 1

                    if vn4 == vn3:
                        continue  # skip non-no-copy

                    total_privileged_bdry_changing += 1
                    if in_nce:
                        total_in_noCopyEdge += 1
                    else:
                        total_NOT_in_noCopyEdge += 1
                        if len(failures) < 10:
                            failures.append((v0,v1,v2,v3,vn4,vn3,vn2,vn1,mover,src_enc,dst_enc))

print(f"=== With no-copy constraint (vn4 != vn3) ===")
print(f"Total privileged + boundary-changing: {total_privileged_bdry_changing}")
print(f"In isNoCopyEdge: {total_in_noCopyEdge}")
print(f"NOT in isNoCopyEdge: {total_NOT_in_noCopyEdge}")

if failures:
    print(f"\nFirst failures:")
    for f in failures:
        v0,v1,v2,v3,vn4,vn3,vn2,vn1,mover,se,de = f
        print(f"  8-tuple=({v0},{v1},{v2},{v3},{vn4},{vn3},{vn2},{vn1}), mover={mover}, "
              f"src_enc={se}, dst_enc={de}")
else:
    print("\n*** ALL boundary transitions are in isNoCopyEdge! ***")
    print("*** period3_noCopy_nIndep follows from finite check alone! ***")

print(f"\n=== Without no-copy constraint ===")
print(f"Total privileged + boundary-changing: {total_no_constraint}")
print(f"NOT in isNoCopyEdge: {fail_no_constraint}")
if fail_no_constraint == 0:
    print("*** Even without no-copy, ALL transitions are in isNoCopyEdge! ***")
