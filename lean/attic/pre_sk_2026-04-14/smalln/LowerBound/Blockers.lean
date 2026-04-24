import LeanMn.SmallN.LowerBound.Core

namespace LeanMn.SmallN.LowerBound

/-- Bitmask with the lowest `size` bits set. -/
def fullMask (size : Nat) : Nat :=
  (1 <<< size) - 1

/-- Iterative sink deletion on a finite digraph encoded by successor masks. -/
def sinkKernelMask (size : Nat) (succMasks : Array Nat) : Nat :=
  let rec go : Nat → Nat → Nat
    | 0, remaining => remaining
    | fuel + 1, remaining =>
        let sinks :=
          (List.range size).foldl
            (fun mask v =>
              if ((remaining >>> v) &&& 1) == 0 then
                mask
              else if (succMasks[v]! &&& remaining) == 0 then
                mask ||| (1 <<< v)
              else
                mask)
            0
        if sinks == 0 then
          remaining
        else
          go fuel (remaining &&& (fullMask size ^^^ sinks))
  go size (fullMask size)

/-- Boolean version of “the sink-deletion kernel is nonempty”. -/
def hasNonemptySinkKernel (size : Nat) (succMasks : Array Nat) : Bool :=
  sinkKernelMask size succMasks != 0

end LeanMn.SmallN.LowerBound
