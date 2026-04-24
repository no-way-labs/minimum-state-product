"""Check at n=7 whether walks with all binary fc >= 4 exist."""
import sys

n = 7
binary = {0, 2, 4}
# Minimum L for all binary fc >= 4: 4*3 + 2*4 = 20

for L in [15, 16, 17, 18]:
    count = 0
    found_ge4 = 0
    found_fc2 = 0

    def gen(word):
        global count, found_ge4, found_fc2
        if len(word) == L:
            disp = 0; cw = 0
            for i in range(L):
                d = (word[(i+1)%L] - word[i]) % n
                if d == 1: cw += 1; disp += 1
                elif d == n-1: disp -= 1
            if disp != 0 or cw == 0: return
            fc = [0]*n
            for m in word: fc[m] += 1
            if any(f < 2 for f in fc): return
            if max(fc) < 3: return
            t = set()
            for m in word: t.add(m); t.add((m-1)%n); t.add((m+1)%n)
            if len(t) < n: return
            count += 1
            if all(fc[b] >= 4 for b in binary):
                found_ge4 += 1
            if any(fc[b] == 2 for b in binary):
                found_fc2 += 1
            return
        last = word[-1]
        for nxt in [(last-1)%n, last, (last+1)%n]:
            word.append(nxt); gen(word); word.pop()

    gen([0])  # Only start from 0
    print(f'n={n}, L={L}: {count} valid (start=0), {found_fc2} have binary-fc2, {found_ge4} all-binary-ge4')
