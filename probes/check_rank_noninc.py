#!/usr/bin/env python3
"""Check if fc-non-increasing boundary transitions always decrease rank."""

def TBotVal(L,S,R):
    t={(0,0,0):1,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):0,(0,1,2):1,(1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):0,(1,1,1):0,(1,1,2):0}
    return t.get((L,S,R),S)
def TLowVal(L,S,R):
    t={(0,0,0):0,(0,0,1):2,(0,0,2):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):2,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0,(1,2,0):0,(1,2,1):0,(1,2,2):2}
    return t.get((L,S,R),S)
def TMidVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,0,2):2,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):1,(0,2,1):2,(0,2,2):2,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):2,(1,2,0):1,(1,2,1):2,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):0,(2,1,1):1,(2,1,2):0,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R),S)
def THighVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):0,(0,2,2):2,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):2,(1,1,2):0,(1,2,0):1,(1,2,1):0,(1,2,2):2,(2,0,0):0,(2,0,1):1,(2,0,2):0,(2,1,0):2,(2,1,1):2,(2,1,2):0,(2,2,0):1,(2,2,1):0,(2,2,2):2}
    return t.get((L,S,R),S)
def TTopVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):0,(1,1,1):0,(2,0,0):1,(2,0,1):1,(2,1,0):0,(2,1,1):0}
    return t.get((L,S,R),S)

def frontierBit(a, b):
    return 0 if a == b else 1

def enc(c0,c1,c2,cN3,cN2,cN1):
    return ((((c0*3+c1)*3+c2)*3+cN3)*3+cN2)*2+cN1

def localFcBefore(L,S,R):
    return frontierBit(L,S) + frontierBit(S,R)

def localFcAfter(L,S,R,out):
    return frontierBit(L,out) + frontierBit(out,R)

rank_vals=[14,15,5,16,9,0,13,14,12,3,14,2,5,6,5,0,10,1,8,9,1,10,1,0,7,8,6,3,3,2,1,2,1,0,2,1,15,16,6,17,10,1,14,15,13,4,15,3,6,7,6,1,11,2,18,7,9,8,13,2,17,6,16,5,18,4,9,2,9,2,14,3,17,6,8,7,12,1,16,5,15,4,17,3,8,1,8,1,13,2,16,5,7,6,11,0,15,4,14,3,16,2,7,0,7,0,12,1,17,5,8,6,1,0,16,4,15,3,3,2,8,0,8,0,2,1,18,6,9,7,2,1,17,5,16,4,14,3,9,1,9,1,13,2,16,17,7,18,11,2,15,16,14,5,16,4,7,8,7,2,12,3,13,22,4,23,8,7,12,21,11,10,13,9,4,13,4,7,9,8,7,10,0,11,0,1,6,9,5,4,2,3,0,3,0,1,1,2,14,23,5,24,9,8,13,22,12,11,14,10,5,14,5,8,10,9,12,21,3,22,7,6,11,20,10,9,12,8,3,12,3,6,8,7,11,20,2,21,6,5,10,19,9,8,11,7,2,11,2,5,7,6,10,19,1,20,5,4,9,18,8,7,10,6,1,10,1,4,6,5,7,8,0,9,2,1,6,7,5,4,7,3,0,1,0,1,3,2,8,9,1,10,3,2,7,8,6,5,8,4,1,2,1,2,4,3,9,18,0,19,4,3,8,17,7,6,9,5,0,9,0,3,5,4]

# Collect fc-non-increasing AND fc-strict-decrease boundary transitions
fc_strict_drop_rank_increase = []
fc_nonincrease_rank_increase = []

for c0 in range(2):
 for c1 in range(3):
  for c2 in range(3):
   for cN3 in range(3):
    for cN2 in range(3):
     for cN1 in range(2):
      src = enc(c0,c1,c2,cN3,cN2,cN1)

      transitions = []
      # Pos 0
      v = TBotVal(cN1, c0, c1)
      if v != c0 and v < 2:
          dst = enc(v,c1,c2,cN3,cN2,cN1)
          d = localFcAfter(cN1,c0,c1,v) - localFcBefore(cN1,c0,c1)
          transitions.append((src, dst, d))

      # Pos 1
      v = TLowVal(c0, c1, c2)
      if v != c1 and v < 3:
          dst = enc(c0,v,c2,cN3,cN2,cN1)
          d = localFcAfter(c0,c1,c2,v) - localFcBefore(c0,c1,c2)
          transitions.append((src, dst, d))

      # Pos 2 (R interior)
      for R in range(3):
          v = TMidVal(c1, c2, R)
          if v != c2 and v < 3:
              dst = enc(c0,c1,v,cN3,cN2,cN1)
              d = localFcAfter(c1,c2,R,v) - localFcBefore(c1,c2,R)
              transitions.append((src, dst, d))

      # Pos N-3 (L interior)
      for L in range(3):
          v = TMidVal(L, cN3, cN2)
          if v != cN3 and v < 3:
              dst = enc(c0,c1,c2,v,cN2,cN1)
              d = localFcAfter(L,cN3,cN2,v) - localFcBefore(L,cN3,cN2)
              transitions.append((src, dst, d))

      # Pos N-2
      v = THighVal(cN3, cN2, cN1)
      if v != cN2 and v < 3:
          dst = enc(c0,c1,c2,cN3,v,cN1)
          d = localFcAfter(cN3,cN2,cN1,v) - localFcBefore(cN3,cN2,cN1)
          transitions.append((src, dst, d))

      # Pos N-1
      v = TTopVal(cN2, cN1, c0)
      if v != cN1 and v < 2:
          dst = enc(c0,c1,c2,cN3,cN2,v)
          d = localFcAfter(cN2,cN1,c0,v) - localFcBefore(cN2,cN1,c0)
          transitions.append((src, dst, d))

      for src2, dst2, delta in transitions:
          if delta < 0 and rank_vals[dst2] >= rank_vals[src2]:
              fc_strict_drop_rank_increase.append((src2, dst2, delta, rank_vals[src2], rank_vals[dst2]))
          if delta <= 0 and rank_vals[dst2] >= rank_vals[src2]:
              fc_nonincrease_rank_increase.append((src2, dst2, delta, rank_vals[src2], rank_vals[dst2]))

print(f"fc-strictly-decreasing + rank non-decreasing: {len(fc_strict_drop_rank_increase)}")
for t in fc_strict_drop_rank_increase[:10]:
    print(f"  src={t[0]} dst={t[1]} delta_fc={t[2]} rank_src={t[3]} rank_dst={t[4]}")

print(f"\nfc-non-increasing + rank non-decreasing: {len(fc_nonincrease_rank_increase)}")
