#!/usr/bin/env python3
"""
Research Agent: WHY do 617 of 1098 TP-preserving boundary transitions preserve PhiFull?

Investigation plan:
1. Enumerate ALL TP-preserving boundary transitions (6 positions)
2. Classify each as PhiFull-preserving (in 617) or PhiFull-changing (the 481)
3. Compute boundary fc change (delta_bfc) for each
4. Check if delta_bfc <= 0 characterizes the 617 set
5. Check position distribution of the 481
6. Check if PhiFull is a pure boundary function
7. Test at n=9,10,11 for n-independence

Key insight to test: PhiFull = fc + g where g = max additional fc reachable via TP chain.
When boundary changes, BOTH fc and g can change. The 617 are those where PhiFull doesn't change.
"""

import sys, os, time
from itertools import product as cartesian
from collections import defaultdict, Counter

# ================================================================
# CUP-2 Lean tables (NOT the Python cup2_theorem.py tables — these
# match the Lean formalization's TBotVal, TLowVal, TMidVal, THighVal, TTopVal)
# ================================================================

def TBotVal(L, S, R):
    """P0: binary, (L=c[n-1], S=c[0], R=c[1])"""
    t = {(0,0,0):1,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):0,(0,1,2):1,
         (1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):0,(1,1,1):0,(1,1,2):0}
    return t.get((L, S, R), S)

def TLowVal(L, S, R):
    """P1: ternary, (L=c[0], S=c[1], R=c[2])"""
    t = {(0,0,0):0,(0,0,1):2,(0,0,2):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,
         (0,2,0):0,(0,2,1):2,(0,2,2):2,
         (1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0,
         (1,2,0):0,(1,2,1):0,(1,2,2):2}
    return t.get((L, S, R), S)

def TMidVal(L, S, R):
    """Interior ternary, (L=c[j-1], S=c[j], R=c[j+1])"""
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):2,(0,1,0):0,(0,1,1):1,(0,1,2):0,
         (0,2,0):1,(0,2,1):2,(0,2,2):2,
         (1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):2,
         (1,2,0):1,(1,2,1):2,(1,2,2):2,
         (2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):0,(2,1,1):1,(2,1,2):0,
         (2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L, S, R), S)

def THighVal(L, S, R):
    """P(n-2): ternary, (L=c[n-3], S=c[n-2], R=c[n-1])"""
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,
         (0,2,0):0,(0,2,1):0,(0,2,2):2,
         (1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):2,(1,1,2):0,
         (1,2,0):1,(1,2,1):0,(1,2,2):2,
         (2,0,0):0,(2,0,1):1,(2,0,2):0,(2,1,0):2,(2,1,1):2,(2,1,2):0,
         (2,2,0):1,(2,2,1):0,(2,2,2):2}
    return t.get((L, S, R), S)

def TTopVal(L, S, R):
    """P(n-1): binary, (L=c[n-2], S=c[n-1], R=c[0])"""
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,
         (1,0,0):0,(1,0,1):1,(1,1,0):0,(1,1,1):0,
         (2,0,0):1,(2,0,1):1,(2,1,0):0,(2,1,1):0}
    return t.get((L, S, R), S)


def build_system(n):
    """Build CUP-2 system matching Lean formalization tables."""
    ms = [2] + [3] * (n - 2) + [2]
    tables = [TBotVal, TLowVal] + [TMidVal] * (n - 4) + [THighVal, TTopVal]
    fs = []
    for t in tables:
        def make_f(table):
            def f(L, S, R): return table(L, S, R)
            return f
        fs.append(make_f(t))
    return ms, fs


def fc(c, n):
    """Number of frontier bits (c[j] != c[j+1])."""
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def tp_invariant(c, n):
    """TpInvariant: (exp2_count, int_21_count, exp2_weight)"""
    e2 = 0; i21 = 0; ew = 0
    for j in range(2, n - 2):
        if c[j] == 2:
            r = c[(j + 1) % n]
            if r == 0:
                e2 += 1; ew += j
            elif r == 1:
                e2 += 1; i21 += 1; ew += j
    return (e2, i21, ew)


def enc6(c0, c1, c2, cN3, cN2, cN1):
    return ((((c0 * 3 + c1) * 3 + c2) * 3 + cN3) * 3 + cN2) * 2 + cN1


def dec6(code):
    cN1 = code % 2; code //= 2
    cN2 = code % 3; code //= 3
    cN3 = code % 3; code //= 3
    c2 = code % 3; code //= 3
    c1 = code % 3; code //= 3
    c0 = code % 2
    return (c0, c1, c2, cN3, cN2, cN1)


def bfc(c0, c1, c2, cN3, cN2, cN1):
    """Boundary fc contribution: frontier bits among the 6 boundary positions.
    Note: this counts transitions between c[n-1]↔c[0], c[0]↔c[1], c[1]↔c[2],
    and cN3↔cN2, cN2↔cN1. The c[2]↔c[3] and c[n-4]↔cN3 transitions
    depend on interior values."""
    fb = lambda a, b: 0 if a == b else 1
    return (fb(cN1, c0) + fb(c0, c1) + fb(c1, c2) +
            fb(cN3, cN2) + fb(cN2, cN1))
    # NOTE: c2↔cN3 boundary is WRONG for general n — there's interior between them


# The 617 edges from the Lean code
edge_617_list = [(0,6),(0,162),(1,0),(1,7),(2,164),(3,1),(3,9),(4,166),(6,8),(6,168),(7,6),(7,9),(8,170),(9,11),(10,16),(10,172),(11,17),(12,174),(13,12),(14,176),(16,4),(16,178),(17,5),(18,24),(18,180),(19,18),(19,25),(20,182),(21,19),(21,27),(22,184),(24,26),(24,186),(25,24),(25,27),(26,188),(27,29),(28,34),(28,190),(29,35),(30,192),(31,30),(32,194),(34,22),(34,196),(35,23),(36,0),(36,42),(36,198),(37,1),(37,36),(37,43),(38,2),(38,200),(39,3),(39,37),(39,45),(40,4),(40,202),(41,5),(42,6),(42,44),(42,204),(43,7),(43,42),(43,45),(44,8),(44,206),(45,9),(45,47),(46,10),(46,52),(46,208),(47,11),(47,53),(48,12),(48,210),(49,13),(49,48),(50,14),(50,212),(51,15),(52,16),(52,40),(52,214),(53,17),(53,41),(54,0),(54,60),(54,72),(54,216),(55,61),(55,73),(56,2),(56,74),(56,218),(57,55),(57,63),(57,75),(58,59),(58,76),(59,77),(60,6),(60,62),(60,78),(60,222),(61,63),(61,79),(62,8),(62,80),(62,224),(63,65),(63,81),(64,65),(64,70),(64,82),(65,71),(65,83),(66,12),(66,84),(66,228),(67,85),(68,14),(68,86),(68,230),(69,87),(70,58),(70,71),(70,88),(71,59),(71,89),(72,78),(72,90),(72,234),(73,79),(73,91),(74,92),(74,236),(75,73),(75,81),(75,93),(76,77),(76,94),(77,95),(78,80),(78,96),(78,240),(79,81),(79,97),(80,98),(80,242),(81,83),(81,99),(82,83),(82,88),(82,100),(83,89),(83,101),(84,102),(84,246),(85,103),(86,104),(86,248),(87,105),(88,76),(88,89),(88,106),(89,77),(89,107),(90,36),(90,96),(90,252),(91,97),(92,38),(93,91),(93,99),(94,40),(94,95),(96,42),(96,98),(96,258),(97,99),(98,44),(98,260),(99,101),(100,46),(100,101),(100,106),(101,107),(102,48),(104,50),(106,52),(106,94),(106,107),(107,95),(108,0),(108,114),(108,144),(109,115),(110,2),(110,146),(111,109),(111,117),(112,113),(114,6),(114,116),(114,150),(115,117),(116,8),(116,152),(117,119),(118,119),(118,124),(119,125),(120,12),(120,156),(122,14),(122,158),(124,112),(124,125),(125,113),(126,108),(126,132),(126,144),(127,109),(127,133),(128,110),(128,146),(129,111),(129,127),(129,135),(130,112),(130,131),(131,113),(132,114),(132,134),(132,150),(133,115),(133,135),(134,116),(134,152),(135,117),(135,137),(136,118),(136,137),(136,142),(137,119),(137,143),(138,120),(138,156),(139,121),(140,122),(140,158),(141,123),(142,124),(142,130),(142,143),(143,125),(143,131),(144,36),(144,150),(145,37),(145,144),(145,151),(146,38),(147,39),(147,145),(147,153),(148,40),(149,41),(150,42),(150,152),(151,43),(151,150),(151,153),(152,44),(153,45),(153,155),(154,46),(154,160),(155,47),(155,161),(156,48),(157,49),(157,156),(158,50),(159,51),(160,52),(160,148),(161,53),(161,149),(162,168),(162,216),(163,1),(163,162),(163,169),(163,217),(164,218),(165,3),(165,163),(165,171),(165,219),(166,220),(167,5),(167,221),(168,170),(168,222),(169,7),(169,168),(169,171),(169,223),(170,171),(170,224),(171,9),(171,173),(171,225),(172,178),(172,226),(173,11),(173,179),(173,227),(174,228),(175,13),(175,174),(175,229),(176,230),(177,15),(177,231),(178,166),(178,232),(179,17),(179,167),(179,233),(180,186),(181,19),(181,180),(181,187),(183,21),(183,181),(183,189),(185,23),(186,188),(187,25),(187,186),(187,189),(188,189),(189,27),(189,191),(190,196),(191,29),(191,197),(193,31),(193,192),(195,33),(196,184),(197,35),(197,185),(198,162),(198,204),(198,252),(199,37),(199,163),(199,198),(199,205),(199,253),(200,164),(201,39),(201,165),(201,199),(201,207),(201,255),(202,166),(203,41),(203,167),(203,257),(204,168),(204,206),(204,258),(205,43),(205,169),(205,204),(205,207),(205,259),(206,170),(206,207),(206,260),(207,45),(207,171),(207,209),(207,261),(208,172),(208,214),(209,47),(209,173),(209,215),(209,263),(210,174),(211,49),(211,175),(211,210),(211,265),(212,176),(213,51),(213,177),(213,267),(214,178),(214,202),(215,53),(215,179),(215,203),(215,269),(216,222),(216,234),(217,216),(217,223),(217,235),(218,236),(219,217),(219,225),(219,237),(220,238),(221,239),(222,224),(222,240),(223,222),(223,225),(223,241),(224,225),(224,242),(225,227),(225,243),(226,232),(226,244),(227,233),(227,245),(228,246),(229,228),(229,247),(230,248),(231,249),(232,220),(232,250),(233,221),(233,251),(234,240),(234,252),(235,234),(235,241),(235,253),(236,254),(237,235),(237,243),(237,255),(238,239),(238,256),(239,245),(239,257),(240,242),(240,258),(241,240),(241,243),(241,259),(242,243),(242,260),(243,245),(243,261),(244,240),(244,245),(244,250),(244,262),(245,251),(245,263),(246,264),(247,246),(247,265),(248,266),(249,267),(250,238),(250,251),(250,268),(251,239),(251,269),(252,258),(252,306),(253,252),(253,259),(253,307),(254,308),(255,253),(255,261),(255,309),(256,257),(256,310),(257,311),(258,260),(258,312),(259,258),(259,261),(259,313),(260,261),(260,314),(261,263),(261,315),(262,258),(262,263),(262,268),(262,316),(263,269),(263,317),(264,318),(265,319),(266,320),(267,321),(268,256),(268,269),(268,322),(269,257),(269,323),(270,276),(271,109),(271,270),(271,277),(273,111),(273,271),(273,279),(274,275),(275,113),(276,278),(277,115),(277,276),(277,279),(278,279),(279,117),(279,281),(280,276),(280,281),(280,286),(281,119),(281,287),(283,121),(285,123),(286,274),(286,287),(287,125),(287,275),(288,270),(288,294),(289,127),(289,271),(289,288),(289,295),(290,272),(291,129),(291,273),(291,289),(291,297),(292,274),(292,293),(293,131),(293,275),(294,276),(294,296),(295,133),(295,277),(295,294),(295,297),(296,278),(296,297),(297,135),(297,279),(297,299),(298,280),(298,294),(298,299),(298,304),(299,137),(299,281),(299,305),(300,282),(301,139),(301,283),(302,284),(303,141),(303,285),(304,286),(304,292),(304,305),(305,143),(305,287),(305,293),(306,312),(307,145),(307,306),(307,313),(309,147),(309,307),(309,315),(310,311),(311,149),(312,314),(313,151),(313,312),(313,315),(314,315),(315,153),(315,317),(316,312),(316,317),(316,322),(317,155),(317,323),(319,157),(321,159),(322,310),(322,323),(323,161),(323,311)]
edge_617 = set(edge_617_list)

# B4 edges (the 12 special fc-drop edges handled by the BFL framework, not in the 617)
b4_edges = set([(4,5),(10,11),(16,17),(22,23),(28,29),(34,35),(40,41),(46,47),(52,53),(148,149),(154,155),(160,161)])


def main():
    sys.stdout.reconfigure(line_buffering=True)

    print("=" * 70)
    print("INVESTIGATION: PhiFull-preserving vs PhiFull-changing boundary transitions")
    print("=" * 70)

    # ================================================================
    # STEP 1: Enumerate ALL TP-preserving boundary transitions
    # ================================================================
    # A boundary transition changes one of positions {0, 1, 2, n-3, n-2, n-1}.
    # For positions 0, 1, n-2, n-1: output is fully determined by boundary 6-tuple.
    # For positions 2 and n-3: output depends on one interior neighbor (c[3] or c[n-4]).

    all_trans = []  # (src_enc, dst_enc, pos_label, bfc_delta, interior_val_or_None)

    for c0 in range(2):
      for c1 in range(3):
        for c2 in range(3):
          for cN3 in range(3):
            for cN2 in range(3):
              for cN1 in range(2):
                src = enc6(c0, c1, c2, cN3, cN2, cN1)
                src_bfc = bfc(c0, c1, c2, cN3, cN2, cN1)

                # Pos 0: TBot(L=cN1, S=c0, R=c1)
                v = TBotVal(cN1, c0, c1)
                if v != c0 and v < 2:
                    dst = enc6(v, c1, c2, cN3, cN2, cN1)
                    dst_bfc = bfc(v, c1, c2, cN3, cN2, cN1)
                    all_trans.append((src, dst, 'P0', dst_bfc - src_bfc, None))

                # Pos 1: TLow(L=c0, S=c1, R=c2)
                v = TLowVal(c0, c1, c2)
                if v != c1 and v < 3:
                    dst = enc6(c0, v, c2, cN3, cN2, cN1)
                    dst_bfc = bfc(c0, v, c2, cN3, cN2, cN1)
                    all_trans.append((src, dst, 'P1', dst_bfc - src_bfc, None))

                # Pos 2: TMid(L=c1, S=c2, R=c3) — c3 is interior
                for c3 in range(3):
                    v = TMidVal(c1, c2, c3)
                    if v != c2 and v < 3:
                        dst = enc6(c0, c1, v, cN3, cN2, cN1)
                        dst_bfc = bfc(c0, c1, v, cN3, cN2, cN1)
                        all_trans.append((src, dst, 'P2', dst_bfc - src_bfc, c3))

                # Pos n-3: TMid(L=cN4, S=cN3, R=cN2) — cN4 is interior
                for cN4 in range(3):
                    v = TMidVal(cN4, cN3, cN2)
                    if v != cN3 and v < 3:
                        dst = enc6(c0, c1, c2, v, cN2, cN1)
                        dst_bfc = bfc(c0, c1, c2, v, cN2, cN1)
                        all_trans.append((src, dst, 'PN3', dst_bfc - src_bfc, cN4))

                # Pos n-2: THigh(L=cN3, S=cN2, R=cN1)
                v = THighVal(cN3, cN2, cN1)
                if v != cN2 and v < 3:
                    dst = enc6(c0, c1, c2, cN3, v, cN1)
                    dst_bfc = bfc(c0, c1, c2, cN3, v, cN1)
                    all_trans.append((src, dst, 'PN2', dst_bfc - src_bfc, None))

                # Pos n-1: TTop(L=cN2, S=cN1, R=c0)
                v = TTopVal(cN2, cN1, c0)
                if v != cN1 and v < 2:
                    dst = enc6(c0, c1, c2, cN3, cN2, v)
                    dst_bfc = bfc(c0, c1, c2, cN3, cN2, v)
                    all_trans.append((src, dst, 'PN1', dst_bfc - src_bfc, None))

    # Deduplicate by (src, dst) — same pair can arise from P2/PN3 with different interior values
    by_pair = defaultdict(list)
    for src, dst, pos, delta, interior in all_trans:
        by_pair[(src, dst)].append((pos, delta, interior))

    total_unique_pairs = len(by_pair)
    in_617_count = sum(1 for p in by_pair if p in edge_617)
    in_b4_count = sum(1 for p in by_pair if p in b4_edges)
    not_in_either = sum(1 for p in by_pair if p not in edge_617 and p not in b4_edges)

    print(f"\nTotal unique (src,dst) boundary transitions: {total_unique_pairs}")
    print(f"  In 617 set: {in_617_count}")
    print(f"  In B4 set: {in_b4_count}")
    print(f"  Not in either: {not_in_either}")

    # ================================================================
    # STEP 2: Position distribution
    # ================================================================
    print(f"\n{'='*70}")
    print("POSITION DISTRIBUTION")
    print(f"{'='*70}")

    pos_in_617 = Counter()
    pos_not_in = Counter()
    for (src, dst), infos in by_pair.items():
        positions = set(info[0] for info in infos)
        if (src, dst) in edge_617:
            for p in positions:
                pos_in_617[p] += 1
        elif (src, dst) not in b4_edges:
            for p in positions:
                pos_not_in[p] += 1

    print("\nPositions of PhiFull-PRESERVING (617) edges:")
    for p in ['P0', 'P1', 'P2', 'PN3', 'PN2', 'PN1']:
        print(f"  {p}: {pos_in_617.get(p, 0)}")

    print("\nPositions of PhiFull-CHANGING (not-617, not-B4) edges:")
    for p in ['P0', 'P1', 'P2', 'PN3', 'PN2', 'PN1']:
        print(f"  {p}: {pos_not_in.get(p, 0)}")

    # ================================================================
    # STEP 3: Boundary fc delta distribution
    # ================================================================
    print(f"\n{'='*70}")
    print("BOUNDARY FC DELTA DISTRIBUTION")
    print(f"{'='*70}")

    delta_in_617 = Counter()
    delta_not_in = Counter()
    for (src, dst), infos in by_pair.items():
        # Take first delta (they should all be the same for same src,dst)
        delta = infos[0][1]
        if (src, dst) in edge_617:
            delta_in_617[delta] += 1
        elif (src, dst) not in b4_edges:
            delta_not_in[delta] += 1

    print("\nBfc delta for PhiFull-PRESERVING (617):")
    for d in sorted(delta_in_617.keys()):
        print(f"  delta={d:+d}: {delta_in_617[d]}")

    print("\nBfc delta for PhiFull-CHANGING (not-617):")
    for d in sorted(delta_not_in.keys()):
        print(f"  delta={d:+d}: {delta_not_in[d]}")

    # ================================================================
    # STEP 4: Is delta_bfc <= 0 sufficient? Necessary?
    # ================================================================
    print(f"\n{'='*70}")
    print("TEST: delta_bfc <= 0 as characterization")
    print(f"{'='*70}")

    # In 617 but delta > 0?
    in_617_positive = []
    for (src, dst), infos in by_pair.items():
        delta = infos[0][1]
        if (src, dst) in edge_617 and delta > 0:
            in_617_positive.append((src, dst, delta, infos))

    # Not in 617 but delta <= 0?
    not_617_nonpositive = []
    for (src, dst), infos in by_pair.items():
        delta = infos[0][1]
        if (src, dst) not in edge_617 and (src, dst) not in b4_edges and delta <= 0:
            not_617_nonpositive.append((src, dst, delta, infos))

    print(f"\nIn 617 with delta_bfc > 0: {len(in_617_positive)}")
    for x in in_617_positive[:10]:
        s6 = dec6(x[0]); d6 = dec6(x[1])
        print(f"  {x[0]}->{x[1]} delta={x[2]} src={s6} dst={d6} pos={x[3][0][0]}")

    print(f"\nNot in 617 with delta_bfc <= 0: {len(not_617_nonpositive)}")
    for x in not_617_nonpositive[:10]:
        s6 = dec6(x[0]); d6 = dec6(x[1])
        print(f"  {x[0]}->{x[1]} delta={x[2]} src={s6} dst={d6} pos={x[3][0][0]}")

    # ================================================================
    # STEP 5: For P2 and PN3, check interior-value dependence
    # ================================================================
    print(f"\n{'='*70}")
    print("INTERIOR VALUE DEPENDENCE (P2 and PN3)")
    print(f"{'='*70}")

    # For the same (src_enc, dst_enc) pair at P2 or PN3,
    # does it appear in 617 for some interior values but not others?
    p2_pairs = defaultdict(set)  # (src, dst) -> set of interior values
    pn3_pairs = defaultdict(set)
    for src, dst, pos, delta, interior in all_trans:
        if pos == 'P2' and interior is not None:
            p2_pairs[(src, dst)].add(interior)
        if pos == 'PN3' and interior is not None:
            pn3_pairs[(src, dst)].add(interior)

    print(f"\nP2 unique (src,dst) pairs: {len(p2_pairs)}")
    print(f"PN3 unique (src,dst) pairs: {len(pn3_pairs)}")

    # Check: for P2, same (src,dst) can be triggered by multiple c3 values.
    # The boundary change is the same regardless of c3 (since c3 is not in the 6-tuple).
    # So the question is: is the 617 membership a property of the BOUNDARY CHANGE alone?
    multi_c3 = sum(1 for v in p2_pairs.values() if len(v) > 1)
    multi_cn4 = sum(1 for v in pn3_pairs.values() if len(v) > 1)
    print(f"P2 pairs with multiple interior values: {multi_c3}")
    print(f"PN3 pairs with multiple interior values: {multi_cn4}")

    # ================================================================
    # STEP 6: Position-by-position analysis for positions 0,1,n-2,n-1
    #         (fully determined by boundary — no interior ambiguity)
    # ================================================================
    print(f"\n{'='*70}")
    print("FULLY-DETERMINED POSITIONS: DETAILED ANALYSIS")
    print(f"{'='*70}")

    for pos_label in ['P0', 'P1', 'PN2', 'PN1']:
        in_set = []
        out_set = []
        for (src, dst), infos in by_pair.items():
            positions = set(info[0] for info in infos)
            if pos_label not in positions:
                continue
            delta = [info[1] for info in infos if info[0] == pos_label][0]
            if (src, dst) in edge_617:
                in_set.append((src, dst, delta))
            elif (src, dst) not in b4_edges:
                out_set.append((src, dst, delta))

        print(f"\n{pos_label}: {len(in_set)} in 617, {len(out_set)} not-in-617")
        if out_set:
            print(f"  Not-in-617 deltas: {Counter(x[2] for x in out_set)}")
            print(f"  In-617 deltas: {Counter(x[2] for x in in_set)}")
            for x in out_set[:5]:
                s6 = dec6(x[0]); d6 = dec6(x[1])
                print(f"    {x[0]}->{x[1]} delta={x[2]} src={s6} dst={d6}")

    # ================================================================
    # STEP 7: Full computational check at n=9,10,11
    #         Compute PhiFull exactly and verify the 617 characterization
    # ================================================================
    print(f"\n{'='*70}")
    print("FULL COMPUTATIONAL VERIFICATION at n=9,10,11")
    print(f"{'='*70}")

    for n_val in [9, 10, 11]:
        t0 = time.time()
        ms, fs = build_system(n_val)
        n = n_val
        all_configs = list(cartesian(*(range(m) for m in ms)))

        # Find good configs
        good_set = set()
        for c in all_configs:
            priv = [j for j in range(n) if fs[j](c[(j-1)%n], c[j], c[(j+1)%n]) != c[j]]
            if len(priv) == 1:
                good_set.add(c)

        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        fc_cache = {c: fc(c, n) for c in bad_list}

        # Build TP graph on bad configs
        tp_fwd = defaultdict(list)
        tp_edge_list = []
        for c in bad_list:
            tp_c = tp_invariant(c, n)
            for i in range(n):
                L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                out = fs[i](L, S, R)
                if out != S:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        tp_s = tp_invariant(succ, n)
                        if tp_c == tp_s:
                            dfc = fc_cache[succ] - fc_cache[c]
                            tp_fwd[c].append((succ, dfc))
                            tp_edge_list.append((c, succ, i, dfc))

        # Compute g (max future fc gain) via Bellman-Ford
        g = {c: 0 for c in bad_list}
        for _ in range(2 * n + 10):
            changed = False
            for c in bad_list:
                for s, dfc in tp_fwd.get(c, []):
                    new_g = dfc + g[s]
                    if new_g > g[c]:
                        g[c] = new_g
                        changed = True
            if not changed:
                break

        phi = {c: fc_cache[c] + g[c] for c in bad_list}

        # Now classify boundary transitions
        boundary_trans_in = set()    # PhiFull-preserving
        boundary_trans_out = set()   # PhiFull-changing

        for c, s, pos, dfc in tp_edge_list:
            if pos not in [0, 1, 2, n-3, n-2, n-1]:
                continue
            s6c = (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])
            s6s = (s[0], s[1], s[2], s[n-3], s[n-2], s[n-1])
            if s6c == s6s:
                continue  # Interior change only
            enc_c = enc6(*s6c)
            enc_s = enc6(*s6s)
            if phi[s] == phi[c]:
                boundary_trans_in.add((enc_c, enc_s))
            else:
                boundary_trans_out.add((enc_c, enc_s))

        # Compare with the 617 set
        match_617 = boundary_trans_in == edge_617
        elapsed = time.time() - t0
        print(f"\nn={n_val}: PhiFull-preserving boundary: {len(boundary_trans_in)}, "
              f"PhiFull-changing: {len(boundary_trans_out)}, "
              f"matches 617: {match_617}, time={elapsed:.1f}s")

        if not match_617:
            only_computed = boundary_trans_in - edge_617
            only_617 = edge_617 - boundary_trans_in
            print(f"  Only in computed: {len(only_computed)} — {sorted(only_computed)[:5]}")
            print(f"  Only in 617 set: {len(only_617)} — {sorted(only_617)[:5]}")

        # ============================================================
        # KEY ANALYSIS: For PhiFull-changing transitions,
        # what is phi[s] - phi[c]?
        # ============================================================
        phi_delta_dist = Counter()
        phi_delta_by_pos = defaultdict(Counter)
        fc_delta_by_phi = defaultdict(Counter)   # phi_change -> fc_delta distribution
        g_delta_by_phi = defaultdict(Counter)

        for c, s, pos, dfc in tp_edge_list:
            if pos not in [0, 1, 2, n-3, n-2, n-1]:
                continue
            s6c = (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])
            s6s = (s[0], s[1], s[2], s[n-3], s[n-2], s[n-1])
            if s6c == s6s:
                continue
            dphi = phi[s] - phi[c]
            if dphi != 0:
                pos_label = {0:'P0', 1:'P1', 2:'P2', n-3:'PN3', n-2:'PN2', n-1:'PN1'}[pos]
                phi_delta_dist[dphi] += 1
                phi_delta_by_pos[pos_label][dphi] += 1
                fc_delta_by_phi[dphi][dfc] += 1
                g_delta_by_phi[dphi][g[s] - g[c]] += 1

        print(f"\n  PhiFull change distribution (delta_phi):")
        for d in sorted(phi_delta_dist.keys()):
            print(f"    delta_phi={d:+d}: {phi_delta_dist[d]}")

        print(f"\n  PhiFull change by position:")
        for p in ['P0', 'P1', 'P2', 'PN3', 'PN2', 'PN1']:
            if phi_delta_by_pos[p]:
                print(f"    {p}: {dict(phi_delta_by_pos[p])}")

        print(f"\n  For PhiFull-changing transitions:")
        print(f"    fc change distribution: {dict(Counter(dfc for c, s, pos, dfc in tp_edge_list if pos in [0,1,2,n-3,n-2,n-1] and (c[0],c[1],c[2],c[n-3],c[n-2],c[n-1]) != (s[0],s[1],s[2],s[n-3],s[n-2],s[n-1]) and phi[s] != phi[c]))}")
        print(f"    g change distribution: {dict(Counter(g[s]-g[c] for c, s, pos, dfc in tp_edge_list if pos in [0,1,2,n-3,n-2,n-1] and (c[0],c[1],c[2],c[n-3],c[n-2],c[n-1]) != (s[0],s[1],s[2],s[n-3],s[n-2],s[n-1]) and phi[s] != phi[c]))}")

        # ============================================================
        # KEY QUESTION: Is PhiFull a function of boundary alone?
        # ============================================================
        phi_by_boundary = defaultdict(set)
        for c in bad_list:
            b = (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])
            tp = tp_invariant(c, n)
            phi_by_boundary[(b, tp)].add(phi[c])

        multi_phi = sum(1 for v in phi_by_boundary.values() if len(v) > 1)
        print(f"\n  Boundary+TP states with multiple PhiFull values: {multi_phi}")
        if multi_phi > 0:
            for (b, tp), phis in sorted(phi_by_boundary.items()):
                if len(phis) > 1:
                    print(f"    boundary={b} tp={tp} PhiFull values: {sorted(phis)}")
                    break

        # Check: is PhiFull a function of boundary alone (ignoring TP)?
        phi_by_boundary_only = defaultdict(set)
        for c in bad_list:
            b = (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])
            phi_by_boundary_only[b].add(phi[c])
        multi_phi_no_tp = sum(1 for v in phi_by_boundary_only.values() if len(v) > 1)
        print(f"  Boundary-only states with multiple PhiFull values: {multi_phi_no_tp}")

    # ================================================================
    # STEP 8: Check the fc-nondecreasing hypothesis more carefully
    # For each PhiFull-CHANGING transition, compute:
    #   - local fc change at the boundary
    #   - whether fc INCREASED at this boundary move
    #   - the g-value change
    # ================================================================
    print(f"\n{'='*70}")
    print("DETAILED MECHANISM ANALYSIS at n=9")
    print(f"{'='*70}")

    n_val = 9
    ms, fs = build_system(n_val)
    n = n_val
    all_configs = list(cartesian(*(range(m) for m in ms)))
    good_set = set()
    for c in all_configs:
        priv = [j for j in range(n) if fs[j](c[(j-1)%n], c[j], c[(j+1)%n]) != c[j]]
        if len(priv) == 1:
            good_set.add(c)
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)
    fc_cache = {c: fc(c, n) for c in bad_list}

    tp_fwd = defaultdict(list)
    tp_edge_list = []
    for c in bad_list:
        tp_c = tp_invariant(c, n)
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    tp_s = tp_invariant(succ, n)
                    if tp_c == tp_s:
                        dfc = fc_cache[succ] - fc_cache[c]
                        tp_fwd[c].append((succ, dfc))
                        tp_edge_list.append((c, succ, i, dfc))

    g = {c: 0 for c in bad_list}
    for _ in range(30):
        changed = False
        for c in bad_list:
            for s, dfc in tp_fwd.get(c, []):
                new_g = dfc + g[s]
                if new_g > g[c]:
                    g[c] = new_g
                    changed = True
        if not changed:
            break

    phi = {c: fc_cache[c] + g[c] for c in bad_list}

    # For EVERY PhiFull-changing boundary transition, trace WHY phi changes
    print("\nPhiFull-changing boundary transitions: decomposition into fc + g")
    print("Format: src_bdry -> dst_bdry | pos | delta_fc | delta_g | delta_phi")

    change_decomp = Counter()  # (delta_fc, delta_g) -> count
    for c, s, pos, dfc in tp_edge_list:
        if pos not in [0, 1, 2, n-3, n-2, n-1]:
            continue
        s6c = (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])
        s6s = (s[0], s[1], s[2], s[n-3], s[n-2], s[n-1])
        if s6c == s6s:
            continue
        dphi = phi[s] - phi[c]
        if dphi != 0:
            dg = g[s] - g[c]
            change_decomp[(dfc, dg)] += 1

    print("\n(delta_fc, delta_g) -> count for PhiFull-CHANGING transitions:")
    for k in sorted(change_decomp.keys()):
        print(f"  dfc={k[0]:+d}, dg={k[1]:+d} => dphi={k[0]+k[1]:+d}: {change_decomp[k]}")

    # Same for PhiFull-preserving
    preserve_decomp = Counter()
    for c, s, pos, dfc in tp_edge_list:
        if pos not in [0, 1, 2, n-3, n-2, n-1]:
            continue
        s6c = (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])
        s6s = (s[0], s[1], s[2], s[n-3], s[n-2], s[n-1])
        if s6c == s6s:
            continue
        dphi = phi[s] - phi[c]
        if dphi == 0:
            dg = g[s] - g[c]
            preserve_decomp[(dfc, dg)] += 1

    print("\n(delta_fc, delta_g) -> count for PhiFull-PRESERVING transitions:")
    for k in sorted(preserve_decomp.keys()):
        print(f"  dfc={k[0]:+d}, dg={k[1]:+d}: {preserve_decomp[k]}")

    # ================================================================
    # STEP 9: The critical test — is "delta_phi <= 0" equivalent to "in 617"?
    # Or is it "delta_phi = 0"? Check the direction of phi change.
    # ================================================================
    print(f"\n{'='*70}")
    print("DIRECTION OF PhiFull CHANGE for not-617 transitions")
    print(f"{'='*70}")

    increases = 0
    decreases = 0
    for c, s, pos, dfc in tp_edge_list:
        if pos not in [0, 1, 2, n-3, n-2, n-1]:
            continue
        s6c = (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])
        s6s = (s[0], s[1], s[2], s[n-3], s[n-2], s[n-1])
        if s6c == s6s:
            continue
        dphi = phi[s] - phi[c]
        if dphi > 0:
            increases += 1
        elif dphi < 0:
            decreases += 1

    print(f"PhiFull increases: {increases}")
    print(f"PhiFull decreases: {decreases}")
    print(f"PhiFull unchanged: (the 617 set)")


if __name__ == '__main__':
    main()
