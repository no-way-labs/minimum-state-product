import LeanMn.SmallN.LowerBound.N5Data
import LeanMn.SmallN.LowerBound.Blockers
import LeanMn.SmallN.LowerBound.N5Types

namespace LeanMn.SmallN.LowerBound

structure N5CandidateCycle where
  profile : List Nat
  configs : List (List Nat)
  movers : List Nat
deriving DecidableEq, Repr

structure N5TailCandidate where
  profile : N5ProfileTag
  configs : Array (Array Nat)
  movers : Array Nat
deriving Repr

def N5CandidateCycle.fullProcessorSupport (c : N5CandidateCycle) : Bool :=
  (List.range 5).all fun p => p ∈ c.movers

def N5CandidateCycle.canonicalStart (c : N5CandidateCycle) : Bool :=
  match c.configs with
  | [] => false
  | start :: rest => rest.all fun cfg => start ≤ cfg

private def moverAdjacent5 (a b : Nat) : Bool :=
  let diff := Nat.dist a b
  diff ≤ 1 || 5 - diff ≤ 1

def N5CandidateCycle.adjacentMoverWord (c : N5CandidateCycle) : Bool :=
  match c.movers with
  | [] => true
  | _ :: [] => true
  | a :: b :: rest =>
      ((a :: b :: rest).zip (b :: rest)).all fun ab => moverAdjacent5 ab.1 ab.2

def N5CandidateCycle.stepShapeOk (c : N5CandidateCycle) : Bool :=
  c.configs.length = c.movers.length

def N5TailCandidate.toCandidateCycle (c : N5TailCandidate) : N5CandidateCycle :=
  {
    profile := N5ProfileTag.representative c.profile
    configs := c.configs.toList.map Array.toList
    movers := c.movers.toList
  }

abbrev N5EntryKey := Nat × Nat × Nat × Nat
abbrev N5Entry := N5EntryKey × Nat

private def cfgGet? (cfg : List Nat) (i : Nat) : Option Nat :=
  cfg.toArray[i]?

private def leftIx5 (i : Nat) : Nat :=
  (i + 4) % 5

private def rightIx5 (i : Nat) : Nat :=
  (i + 1) % 5

private def entryLookup (entries : List N5Entry) (key : N5EntryKey) : Option Nat :=
  match entries.find? (fun e => e.1 = key) with
  | some e => some e.2
  | none => none

private def entryInsertConsistent (entries : List N5Entry) (key : N5EntryKey) (value : Nat) :
    Option (List N5Entry) :=
  match entryLookup entries key with
  | some value' =>
      if value' = value then
        some entries
      else
        none
  | none =>
      some ((key, value) :: entries)

private def allConfigsOfProfile : List Nat → List (List Nat)
  | [] => [[]]
  | m :: ms =>
      ((List.range m).map fun v =>
        (allConfigsOfProfile ms).map fun rest => v :: rest).foldr List.append []

private def stepEntryData? (cfg nextCfg : List Nat) (proc : Nat) :
    Option (N5EntryKey × Nat) := do
  let leftVal ← cfgGet? cfg (leftIx5 proc)
  let selfVal ← cfgGet? cfg proc
  let rightVal ← cfgGet? cfg (rightIx5 proc)
  let nextVal ← cfgGet? nextCfg proc
  pure ((proc, leftVal, selfVal, rightVal), nextVal)

private def privilegeSetFromEntries (entries : List N5Entry) (cfg : List Nat) : List Nat :=
  (List.range 5).filter fun proc =>
    match stepEntryData? cfg cfg proc with
    | some (key, current) =>
        match entryLookup entries key with
        | some out => out != current
        | none => false
    | none => false

private def reconstructDeterminedEntries (c : N5CandidateCycle) : Option (List N5Entry) := do
  if !c.stepShapeOk then
    none
  else
    let cfgs := c.configs.toArray
    let movers := c.movers.toArray
    let len := cfgs.size
    let mut entries : List N5Entry := []
    for idx in [:len] do
      let cfg := cfgs[idx]!
      let nextCfg := cfgs[(idx + 1) % len]!
      let proc := movers[idx]!
      let some (key, outVal) := stepEntryData? cfg nextCfg proc
        | none
      let some entries' := entryInsertConsistent entries key outVal
        | none
      entries := entries'
      for other in List.range 5 do
        if other != proc then
          let some (otherKey, selfVal) := stepEntryData? cfg cfg other
            | none
          let some entries'' := entryInsertConsistent entries otherKey selfVal
            | none
          entries := entries''
    if (cfgs.toList.all fun cfg => (privilegeSetFromEntries entries cfg).length = 1) then
      some entries
    else
      none

private def succMaskFromEntries (entries : List N5Entry) (goodSet : List (List Nat))
    (nonGoodIndex : List (List Nat)) (cfg : List Nat) : Nat :=
  (List.range 5).foldl
    (fun mask proc =>
      match stepEntryData? cfg cfg proc with
      | some (key, current) =>
          match entryLookup entries key with
          | some out =>
              if out = current then
                mask
              else
                let nextCfg := (cfg.toArray.set! proc out).toList
                if nextCfg ∈ goodSet then
                  mask
                else
                  match nonGoodIndex.idxOf? nextCfg with
                  | some idx => mask ||| (1 <<< idx)
                  | none => mask
          | none => mask
      | none => mask)
    0

private def profileLooksN5Tail (profile : List Nat) : Bool :=
  n5ProfileTag? profile = some .tailA || n5ProfileTag? profile = some .tailB

def candidateBlocked5 (c : N5CandidateCycle) : Bool :=
  if !c.stepShapeOk then
    true
  else if !c.fullProcessorSupport then
    true
  else if !c.adjacentMoverWord then
    true
  else if !profileLooksN5Tail c.profile then
    false
  else
    match reconstructDeterminedEntries c with
    | none => true
    | some entries =>
        let allCfgs := allConfigsOfProfile c.profile
        let nonGood := allCfgs.filter fun cfg => cfg ∉ c.configs
        let succMasks := nonGood.map (succMaskFromEntries entries c.configs nonGood)
        hasNonemptySinkKernel nonGood.length succMasks.toArray

def easyCandidateBlocked5 : N5CandidateCycle → Bool :=
  candidateBlocked5

def candidateBlockedTail5 (c : N5TailCandidate) : Bool :=
  candidateBlocked5 c.toCandidateCycle

end LeanMn.SmallN.LowerBound
