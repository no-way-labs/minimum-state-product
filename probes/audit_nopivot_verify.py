"""Use the official verifier to test valid systems in the no-pivot n=9 family.

If verify_system returns a valid RuleSystem for ms=(2,3,3,2,3,3,2,3,3) or any
nearby no-pivot multiset with product < 8748, we have a real counterexample
and the non-consec theorem must be stated differently.
"""
import sys
sys.path.insert(0, './claude')
from verifier import verify_system, search_optimal

N = 9
MS = (2, 3, 3, 2, 3, 3, 2, 3, 3)

# Exhaustively search for a valid rule system with this ms
print(f"Searching for valid rule system in ms={MS}, product={2*3*3*2*3*3*2*3*3}")
print(f"M_9 bound = 4*3^7 = 8748")
print()

# search_optimal signature check
import inspect
print("search_optimal signature:", inspect.signature(search_optimal))
print("verify_system signature:", inspect.signature(verify_system))
