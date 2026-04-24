#!/usr/bin/env python3
"""Debug: check the first failing example in detail."""

n = 11
ms = [2,3,3,3,3,3,3,3,3,3,2]

TLow = {(0,0):1,(0,1):0,(0,2):0,(1,0):1,(1,1):0,(1,2):2,(2,0):0,(2,1):2,(2,2):1}
THigh = {(0,0,0):1,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):1,
         (1,0,0):1,(1,0,1):1,(1,1,0):0,(1,1,1):2,(1,2,0):1,(1,2,1):1,
         (2,0,0):2,(2,0,1):2,(2,1,0):2,(2,1,1):0,(2,2,0):0,(2,2,1):2}
TMid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,
        (0,2,0):0,(0,2,1):0,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
        (1,1,0):1,(1,1,1):1,(1,1,2):1,(1,2,0):1,(1,2,1):1,(1,2,2):1,
        (2,0,0):2,(2,0,1):2,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,
        (2,2,0):0,(2,2,1):2,(2,2,2):2}

src = [0,0,0,0,1,0,1,0,1,0,0]
p = 0
L = src[(p-1)%n]  # src[10] = 0
S = src[p]         # src[0] = 0
R = src[(p+1)%n]   # src[1] = 0
out = (S+1)%2      # = 1
print(f"Position {p}: L={L}, S={S}, R={R}, out={out}")
assert out != S, "Should be privileged"

dst = src.copy()
dst[p] = out
print(f"src = {src}")
print(f"dst = {dst}")

# Check no deep copy
print("\nDeep copy check:")
for k in range(4, n-4+1):
    print(f"  k={k}: dst[k]={dst[k]}, dst[k-1]={dst[k-1]}, dst[k+1]={dst[k+1]}, copy_left={dst[k]==dst[k-1]}, copy_right={dst[k]==dst[k+1]}")

# Check boundary encoding
def benc(c):
    return ((((c[0]*3+c[1])*3+c[2])*3+c[n-3])*3+c[n-2])*2+c[n-1]

enc_s = benc(src)
enc_d = benc(dst)
print(f"\nbenc(src) = {enc_s}")
print(f"benc(dst) = {enc_d}")
print(f"boundary changed: {enc_s != enc_d}")

# Check TP
def tp(c):
    count2 = sum(1 for j in range(n) if c[j]==2)
    count2then1 = sum(1 for j in range(1,n-1) if c[j]==2 and c[j+1]==1)
    sum2pos = sum(j for j in range(n) if c[j]==2)
    return (count2, count2then1, sum2pos)

print(f"\ntp(src) = {tp(src)}")
print(f"tp(dst) = {tp(dst)}")
print(f"TP preserved: {tp(src) == tp(dst)}")

# fc
def fc(c):
    return sum(1 for j in range(n) if c[j] != c[(j+1)%n])

print(f"\nfc(src) = {fc(src)}")
print(f"fc(dst) = {fc(dst)}")

# Edge code
ec = enc_s * 324 + enc_d
print(f"\nEdge code: {ec}")
print(f"In noCopyEdgeCodes: {ec in {2112}}")  # We know it's not

# Now check: does this edge have a "copy" in the interior?
# The "no-copy" concept might mean: in the dst config, for ALL interior positions k (say 3..n-4),
# dst[k] != dst[k-1] and dst[k] != dst[k+1]
print("\nFull adjacency check on dst:")
for k in range(n):
    left_copy = dst[k] == dst[(k-1)%n]
    right_copy = dst[k] == dst[(k+1)%n]
    print(f"  k={k}: val={dst[k]}, left_copy={left_copy}, right_copy={right_copy}")

# Count how many qualifying edges have edge codes NOT in the set
# Let's also see what edge codes the qualifying edges produce
print("\n\nLet's check what the actual noCopyEdgeCodes represent...")
noCopyEdgeCodes = set([973,1952,2277,2927,3256,3581,6823,7802,8127,8777,9106,9431,11664,11989,12314,12639,12673,12964,13289,13614,13652,13939,13977,14264,14589,14627,14914,14956,15239,15281,15564,15889,16214,16539,16864,17189,17568,17893,18218,18523,18543,18851,18868,19193,19502,19518,19827,19843,20168,20477,20493,20801,20806,20818,21131,21143,21468,21793,22118,22443,22751,22768,23093,23418,23743,24068,24373,24393,24701,24718,25043,25352,25368,25677,25693,26018,26327,26343,26651,26656,26668,26981,26993,27318,27643,27968,28293,28601,28618,28943,30223,30551,31202,31527,32177,32501,32506,32831,34451,36073,36401,37052,37377,38027,38351,38356,38681,40301,40932,41257,41582,41907,41923,42232,42251,42557,42882,42902,43207,43227,43532,43857,43877,44182,44201,44206,44507,44531,44832,45157,45482,45807,46132,46151,46457,46692,47017,47342,47667,47773,47992,48317,48642,48752,48967,49077,49292,49617,49727,49942,50056,50267,50381,50592,50917,51242,51567,51892,52217,52974,53623,54602,54924,54927,55251,55577,55906,56231,56874,58824,59473,60452,60774,60777,61101,61427,61756,62081,62724,64314,64639,64674,64964,65289,65323,65614,65939,66264,66302,66589,66624,66627,66914,66951,67239,67277,67564,67606,67889,67931,68214,68539,68574,68864,69189,69514,69839,70218,70524,70543,70868,71173,71193,71518,71843,72152,72168,72474,72477,72493,72801,72818,73127,73143,73456,73468,73781,73793,74118,74424,74443,74768,75093,75418,75743,76068,76374,76393,76718,77023,77043,77368,77693,78002,78018,78324,78327,78343,78651,78668,78977,78993,79306,79318,79631,79643,79968,80274,80293,80618,80943,81268,81593,81954,82224,82279,82604,82873,82929,83254,83579,83852,83904,84174,84177,84229,84501,84554,84827,84879,85156,85204,85481,85529,85854,86179,86504,86829,87154,87479,88074,88723,89702,90024,90027,90351,90677,91006,91331,93582,93907,93924,94232,94557,94573,94882,95207,95532,95552,95857,95874,95877,96182,96201,96507,96527,96832,96856,97157,97181,97482,97807,98132,98457,98782,99107,99774,100423,101402,101724,101727,102051,102377,102706,103031])

# The max edge code in the set
print(f"Max edge code in set: {max(noCopyEdgeCodes)}")
print(f"Max possible edge code: {323*324+323} = {323*324+323}")
print(f"Number of codes in set: {len(noCopyEdgeCodes)}")

# Let's decode a few edge codes from the set to understand the pattern
def decode_edge(ec):
    src_bnd = ec // 324
    dst_bnd = ec % 324
    return src_bnd, dst_bnd

def decode_bnd(b):
    c10 = b % 2; b //= 2
    c9 = b % 3; b //= 3
    c8 = b % 3; b //= 3
    c2 = b % 3; b //= 3
    c1 = b % 3; b //= 3
    c0 = b
    return (c0, c1, c2, c8, c9, c10)

print("\nFirst 5 edge codes in set:")
for ec in sorted(noCopyEdgeCodes)[:5]:
    sb, db = decode_edge(ec)
    print(f"  ec={ec}: src_bnd={decode_bnd(sb)}, dst_bnd={decode_bnd(db)}")

print("\nFailing example edge:")
sb, db = decode_edge(2112)
print(f"  ec=2112: src_bnd={decode_bnd(sb)}, dst_bnd={decode_bnd(db)}")
