#!/usr/bin/env python3
"""Check which generated words have valid +-1 wrap-around."""
import time
from itertools import combinations


def gen_words(n, fc_target, max_results=500, timeout_s=15):
    target_cl = sum(fc_target)
    results = []
    t0 = time.time()
    def dfs(word, fc):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == fc_target[p] for p in range(n)):
                results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, fc_target[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in [(last + 1) % n, (last - 1) % n]:
            if fc[nxt] < fc_target[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for start in range(n):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            break
        fc = [0] * n
        fc[start] = 1
        if fc[start] <= fc_target[start]:
            dfs([start], fc)
    return results


def total_displacement(word, n):
    W = 0
    L = len(word)
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            pass
        elif diff <= n // 2:
            W += diff
        else:
            W -= (n - diff)
    return W


def step_directions(word, n):
    L = len(word)
    dirs = []
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            dirs.append(0)
        elif diff == 1:
            dirs.append(1)
        elif diff == n - 1:
            dirs.append(-1)
        else:
            dirs.append(diff if diff <= n // 2 else diff - n)
    return dirs


n = 5
ms = [2, 2, 3, 2, 3]
words = gen_words(n, list(ms), max_results=500, timeout_s=10)
valid_wrap = 0
invalid_wrap = 0
for w in words:
    diff = (w[0] - w[-1]) % n
    if diff == 1 or diff == n - 1:
        valid_wrap += 1
    else:
        invalid_wrap += 1
print(f'Total words: {len(words)}')
print(f'Valid wrap-around (+-1): {valid_wrap}')
print(f'Invalid wrap-around: {invalid_wrap}')

# Now check: among OW-NU words with invalid wrap, can they actually occur?
# In a REAL good cycle, the mover word IS a cyclic +-1 walk.
# So the wrap-around MUST be +-1.
# Words with invalid wrap are NOT valid mover words for good cycles.
print("\nAmong OW-NU words:")
ow_nu_valid = 0
ow_nu_invalid = 0
for w in words:
    wl = list(w)
    W = total_displacement(wl, n)
    if abs(W) != n:
        continue
    dirs = step_directions(wl, n)
    ns_d = [d for d in dirs if d != 0]
    if not ns_d or all(d == ns_d[0] for d in ns_d):
        continue
    diff = (w[0] - w[-1]) % n
    if diff == 1 or diff == n - 1:
        ow_nu_valid += 1
    else:
        ow_nu_invalid += 1
        if ow_nu_invalid <= 3:
            print(f"  Invalid wrap: word={wl}, W={W}, dirs={dirs}")
            print(f"    last={wl[-1]}, first={wl[0]}, diff={(wl[0]-wl[-1])%n}")

print(f"OW-NU valid wrap: {ow_nu_valid}")
print(f"OW-NU invalid wrap: {ow_nu_invalid}")

# CRITICAL: If ALL OW-NU words have invalid wrap-around,
# then there are NO valid OW-NU good cycles, and the theorem is vacuously true!
# But that would mean the RA13 verification is testing words that can't actually occur.

# Let's also check: are there ANY valid-wrap OW-NU words?
print("\nChecking valid-wrap OW-NU words:")
count = 0
for w in words:
    wl = list(w)
    diff = (wl[0] - wl[-1]) % n
    if diff != 1 and diff != n - 1:
        continue
    W = total_displacement(wl, n)
    if abs(W) != n:
        continue
    dirs = step_directions(wl, n)
    ns_d = [d for d in dirs if d != 0]
    if not ns_d or all(d == ns_d[0] for d in ns_d):
        continue
    count += 1
    if count <= 5:
        print(f"  word={wl}, W={W}")
        print(f"    dirs={dirs}, all +-1: {all(abs(d)<=1 for d in dirs)}")
print(f"Total valid-wrap OW-NU: {count}")
