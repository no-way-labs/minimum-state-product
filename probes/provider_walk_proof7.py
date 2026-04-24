"""
Check whether CE mover words can be realized as actual good cycles.

A mover word [w_0, ..., w_{L-1}] can be a good cycle only if there
exists a starting config and transition functions such that:
1. Each config is distinct (good cycle = Hamiltonian cycle on good configs)
2. At each step, exactly w_i is privileged
3. The cycle returns to the starting config

Actually, the question is whether there exist transition functions
f_i(L, S, R) such that:
- Applying f_{w_i} to config c_i gives c_{i+1}
- Each c_i is distinct
- w_i is the unique privileged proc at c_i
- c_L = c_0

This is equivalent to: is the mover word realizable?

Let me check a specific CE: word = [1, 0, 1, 0, 1, 2, 3, 4, 3, 4, 3, 2]
n=5, ms=[2, 3, 2, 3, 2]

For this to be a good cycle, we need 12 distinct configs from a state space
of size 2*3*2*3*2 = 72. And at each config, exactly one proc is privileged.

Let me try to construct such a system or prove it's impossible.

Actually, a cleaner approach: use the VERIFIER to check if any valid system
with ms=[2,3,2,3,2] has a good cycle with this mover word.
"""
import sys
sys.path.insert(0, './claude')
from verifier import all_configs, privileged_set, apply_move, verify_system
import itertools


def find_good_cycle_mover_word(ms, fs):
    """Find the mover word of the good cycle (if valid system)."""
    n = len(ms)
    result = verify_system(ms, fs)
    if not result['valid']:
        return None

    good = result['good_configs']
    if not good:
        return None

    # Build the cycle
    priv_map = {}
    for c in good:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 1:
            priv_map[c] = priv[0]
        else:
            return None

    start = next(iter(good))
    word = []
    visited = set()
    current = start
    while True:
        if current in visited:
            break
        visited.add(current)
        p = priv_map[current]
        word.append(p)
        current = apply_move(current, p, fs, ms)

    if current != start:
        return None

    return word


def check_ce_realizability():
    """Check if the CE mover word can be realized.

    Strategy: enumerate ALL valid systems with ms=[2,3,2,3,2]
    and check their mover words.
    """
    n = 5
    ms = [2, 3, 2, 3, 2]
    target_word = [1, 0, 1, 0, 1, 2, 3, 4, 3, 4, 3, 2]

    # Too many transition functions to enumerate all. Instead, let's
    # check whether valid systems with this ms exist and what their
    # mover words look like.

    # Use the known M_5=96 witness to check: ms=[2,2,2,3,4] has product 96.
    # Our ms=[2,3,2,3,2] has product 72 < 96. So any valid system would
    # have product 72 < 4*27 = 108 (sub-threshold for n=5).

    # Actually, let me search for valid systems with ms=[2,3,2,3,2].
    print(f"Searching for valid systems with ms={ms}, product={72}")

    # Generate transition functions via systematic enumeration
    # This is huge (2^8 * 3^27 * ...), so let's try random sampling instead.
    import random
    random.seed(42)

    found_valid = 0
    found_ce_word = 0
    total_checked = 0
    all_words_found = set()

    for trial in range(100000):
        # Random transition functions
        fs = []
        for i in range(n):
            m_i = ms[i]
            m_left = ms[(i-1)%n]
            m_right = ms[(i+1)%n]
            table = {}
            for L in range(m_left):
                for S in range(m_i):
                    for R in range(m_right):
                        table[(L, S, R)] = random.randint(0, m_i - 1)

            def make_f(tbl, mi):
                def f(L, S, R):
                    return tbl[(L, S, R)]
                return f
            fs.append(make_f(table, m_i))

        result = verify_system(ms, fs)
        total_checked += 1
        if result['valid']:
            found_valid += 1
            word = find_good_cycle_mover_word(ms, fs)
            if word:
                wt = tuple(word)
                all_words_found.add(wt)
                if word == target_word:
                    found_ce_word += 1
                    print(f"  FOUND CE WORD at trial {trial}!")

        if trial % 10000 == 9999:
            print(f"  Checked {trial+1}: {found_valid} valid, {len(all_words_found)} unique words")

    print(f"\nTotal checked: {total_checked}")
    print(f"Valid systems: {found_valid}")
    print(f"Unique mover words: {len(all_words_found)}")
    print(f"CE word found: {found_ce_word}")

    # Print some sample words
    print("\nSample mover words from valid systems:")
    for w in list(all_words_found)[:20]:
        fc = [0]*n
        for m in w:
            fc[m] += 1
        disp = 0
        cw = 0
        for i in range(len(w)):
            nxt = w[(i+1)%len(w)]
            diff = (nxt - w[i]) % n
            if diff == 1:
                cw += 1
                disp += 1
            elif diff == n-1:
                disp -= 1
        zw = "ZW" if disp == 0 else f"wind={disp}"
        print(f"  L={len(w)}: {list(w)[:20]}{'...' if len(w)>20 else ''} fc={fc} {zw} cw={cw}")


def check_ce_with_known_systems():
    """Check CEs against KNOWN valid systems at n=5.

    From memory: M_5 = 96, achieved by ms=(2,2,2,3,4).
    Our ms=(2,3,2,3,2) has product 72, so valid systems may or may not exist.

    Let's check: are there valid systems with product < 96?
    """
    n = 5
    print("\n=== Valid system search for sub-threshold ms at n=5 ===\n")

    # Check several sub-threshold ms vectors
    test_ms = [
        [2, 3, 2, 3, 2],  # product 72
        [2, 3, 2, 3, 3],  # product 108 = 4*27 = threshold
        [2, 3, 2, 2, 3],  # product 72
    ]

    import random
    random.seed(42)

    for ms in test_ms:
        prod = 1
        for m in ms:
            prod *= m
        thresh = 4 * (3 ** (n-2))
        st = "SUB" if prod < thresh else "AT/ABOVE"
        print(f"ms={ms}, product={prod}, threshold={thresh}, {st}-threshold")

        found = 0
        for trial in range(50000):
            fs = []
            for i in range(n):
                m_i = ms[i]
                m_left = ms[(i-1)%n]
                m_right = ms[(i+1)%n]
                table = {}
                for L in range(m_left):
                    for S in range(m_i):
                        for R in range(m_right):
                            table[(L, S, R)] = random.randint(0, m_i - 1)
                def make_f(tbl):
                    def f(L, S, R):
                        return tbl[(L, S, R)]
                    return f
                fs.append(make_f(table))

            result = verify_system(ms, fs)
            if result['valid']:
                found += 1
                word = find_good_cycle_mover_word(ms, fs)
                if word:
                    fc = [0]*n
                    for m in word:
                        fc[m] += 1
                    print(f"  VALID! trial={trial}, cycle len={len(word)}, fc={fc}")
                    if found >= 3:
                        break

        if found == 0:
            print(f"  No valid system found in 50000 trials")
        print()


if __name__ == "__main__":
    check_ce_with_known_systems()
