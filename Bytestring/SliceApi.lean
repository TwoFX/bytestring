import Bytestring.Basic
import Bytestring.HenrikWants

namespace ByteString
namespace Slice

@[inline]
def isEmpty (s : Slice) : Bool := s.utf8Size == 0

inductive SearchStep (s : Slice) where
  | rejected (startPos endPos : s.Pos)
  | matched (startPos endPos : s.Pos)
  deriving Inhabited

class ToForwardSearcher (ρ : Type) (σ : outParam (Slice → Type)) where
  toSearcher : (s : Slice) → ρ → Std.Iter (α := σ s) (SearchStep s)

class ForwardPattern (ρ : Type) (σ : outParam (Slice → Type)) extends ToForwardSearcher ρ σ where
  startsWith : Slice → ρ → Bool
  dropPrefix? : Slice → ρ → Option Slice

namespace Internal

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]

@[inline]
def nextMatch (searcher : Std.Iter (α := σ s) (SearchStep s)) :
    Option (Std.Iter (α := σ s) (SearchStep s) × s.Pos × s.Pos) :=
  go searcher
where
  go [∀ s, Std.Iterators.Finite (σ s) Id] (searcher : Std.Iter (α := σ s) (SearchStep s)) :
      Option (Std.Iter (α := σ s) (SearchStep s) × s.Pos × s.Pos) :=
    match searcher.step with
    | .yield it (.matched startPos endPos) _ => some (it, startPos, endPos)
    | .yield it (.rejected ..) _ | .skip it .. => go it
    | .done .. => none
  termination_by Std.Iterators.Iter.finitelyManySteps searcher

@[inline]
def nextReject (searcher : Std.Iter (α := σ s) (SearchStep s)) :
    Option (Std.Iter (α := σ s) (SearchStep s) × s.Pos × s.Pos) :=
  go searcher
where
  go [∀ s, Std.Iterators.Finite (σ s) Id] (searcher : Std.Iter (α := σ s) (SearchStep s)) :
      Option (Std.Iter (α := σ s) (SearchStep s) × s.Pos × s.Pos) :=
    match searcher.step with
    | .yield it (.rejected startPos endPos) _ => some (it, startPos, endPos)
    | .yield it (.matched ..) _ | .skip it .. => go it
    | .done .. => none
  termination_by Std.Iterators.Iter.finitelyManySteps searcher

end Internal

namespace ForwardPattern

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [ToForwardSearcher ρ σ]

@[specialize pat]
def defaultStartsWith (s : Slice) (pat : ρ) : Bool :=
  let searcher := ToForwardSearcher.toSearcher s pat
  match searcher.step with
  | .yield _ (.matched start ..) _ => s.startPos = start
  | _ => false

@[specialize pat]
def defaultDropPrefix? (s : Slice) (pat : ρ) : Option Slice :=
  let searcher := ToForwardSearcher.toSearcher s pat
  match searcher.step with
  | .yield _ (.matched _ endPos) _ => some (s.replaceStart endPos)
  | _ => none

@[always_inline, inline]
def defaultImplementation : ForwardPattern ρ σ where
  startsWith := defaultStartsWith
  dropPrefix? := defaultDropPrefix?

end ForwardPattern

section ForwardPatternSearchers

@[unbox]
structure ForwardCharSearcher (s : Slice) where
  currPos : s.Pos
  needle : Char
  deriving Inhabited

namespace ForwardCharSearcher

@[inline]
def iter (s : Slice) (c : Char) : Std.Iter (α := ForwardCharSearcher s) (SearchStep s) :=
  { internalState := { currPos := s.startPos, needle := c }}

instance (s : Slice) : Std.Iterators.Iterator (ForwardCharSearcher s) Id (SearchStep s) where
  IsPlausibleStep it
    | .yield it' out =>
      it.internalState.needle = it'.internalState.needle ∧
      ∃ h1 : it.internalState.currPos ≠ s.endPos,
        it'.internalState.currPos = it.internalState.currPos.next h1 ∧
        match out with
        | .matched startPos endPos =>
          it.internalState.currPos = startPos ∧
          it'.internalState.currPos = endPos ∧
          it.internalState.currPos.get h1 = it.internalState.needle
        | .rejected startPos endPos =>
          it.internalState.currPos = startPos ∧
          it'.internalState.currPos = endPos ∧
          it.internalState.currPos.get h1 ≠ it.internalState.needle
    | .skip _ => False
    | .done => it.internalState.currPos = s.endPos
  step := fun ⟨currPos, needle⟩ =>
    if h1 : currPos = s.endPos then
      pure ⟨.done, by simp [h1]⟩
    else
      let nextPos := currPos.next h1
      let nextIt := ⟨nextPos, needle⟩
      if h2 : currPos.get h1 = needle then
        pure ⟨.yield nextIt (.matched currPos nextPos), by simp [h1, h2, nextIt, nextPos]⟩
      else
        pure ⟨.yield nextIt (.rejected currPos nextPos), by simp [h1, h2, nextIt, nextPos]⟩

private def finitenessRelation : Std.Iterators.FinitenessRelation (ForwardCharSearcher s) Id where
  rel := sorry
  wf := sorry
  subrelation := sorry

instance : Std.Iterators.Finite (ForwardCharSearcher s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.Iterators.IteratorLoop (ForwardCharSearcher s) Id Id :=
  .defaultImplementation

instance : ToForwardSearcher Char ForwardCharSearcher where
  toSearcher := iter

instance : ForwardPattern Char ForwardCharSearcher := .defaultImplementation

end ForwardCharSearcher

@[unbox]
structure ForwardCharPredSearcher (s : Slice) where
  currPos : s.Pos
  needle : Char → Bool
  deriving Inhabited

namespace ForwardCharPredSearcher

@[inline]
def iter (s : Slice) (p : Char → Bool) : Std.Iter (α := ForwardCharPredSearcher s) (SearchStep s) :=
  { internalState := { currPos := s.startPos, needle := p }}

instance (s : Slice) : Std.Iterators.Iterator (ForwardCharPredSearcher s) Id (SearchStep s) where
  IsPlausibleStep it
    | .yield it' out =>
      it.internalState.needle = it'.internalState.needle ∧
      ∃ h1 : it.internalState.currPos ≠ s.endPos,
        it'.internalState.currPos = it.internalState.currPos.next h1 ∧
        match out with
        | .matched startPos endPos =>
          it.internalState.currPos = startPos ∧
          it'.internalState.currPos = endPos ∧
          it.internalState.needle (it.internalState.currPos.get h1)
        | .rejected startPos endPos =>
          it.internalState.currPos = startPos ∧
          it'.internalState.currPos = endPos ∧
          ¬ it.internalState.needle (it.internalState.currPos.get h1)
    | .skip _ => False
    | .done => it.internalState.currPos = s.endPos
  step := fun ⟨currPos, needle⟩ =>
    if h1 : currPos = s.endPos then
      pure ⟨.done, by simp [h1]⟩
    else
      let nextPos := currPos.next h1
      let nextIt := ⟨nextPos, needle⟩
      if h2 : needle <| currPos.get h1 then
        pure ⟨.yield nextIt (.matched currPos nextPos), by simp [h1, h2, nextPos, nextIt]⟩
      else
        pure ⟨.yield nextIt (.rejected currPos nextPos), by simp [h1, h2, nextPos, nextIt]⟩


private def finitenessRelation : Std.Iterators.FinitenessRelation (ForwardCharPredSearcher s) Id where
  rel := sorry
  wf := sorry
  subrelation := sorry

instance : Std.Iterators.Finite (ForwardCharPredSearcher s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.Iterators.IteratorLoop (ForwardCharPredSearcher s) Id Id :=
  .defaultImplementation

instance : ToForwardSearcher (Char → Bool) ForwardCharPredSearcher where
  toSearcher := iter

instance : ForwardPattern (Char → Bool) ForwardCharPredSearcher := .defaultImplementation

end ForwardCharPredSearcher

@[unbox]
structure ForwardSliceSearcher (s : Slice) where
  -- TODO: likely needs to be nonempty
  needle : Slice
  -- TODO: This needs to be a vector
  table : Array Nat
  stackPos : s.Pos
  needlePos : needle.Pos
  --deriving Inhabited

namespace ForwardSliceSearcher

def buildTable (pat : Slice) : Array Nat :=
  sorry

@[inline]
def iter (s : Slice) (pat : Slice) : Std.Iter (α := ForwardSliceSearcher s) (SearchStep s) :=
  { internalState := {
      needle := pat,
      table := buildTable pat,
      stackPos := s.startPos,
      needlePos := pat.startPos
    }
  }

instance (s : Slice) : Std.Iterators.Iterator (ForwardSliceSearcher s) Id (SearchStep s) where
  IsPlausibleStep := sorry
  step := fun ⟨needle, table, stackPos, needlePos⟩ => do
    sorry

private def finitenessRelation : Std.Iterators.FinitenessRelation (ForwardSliceSearcher s) Id where
  rel := sorry
  wf := sorry
  subrelation := sorry

instance : Std.Iterators.Finite (ForwardSliceSearcher s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.Iterators.IteratorLoop (ForwardSliceSearcher s) Id Id :=
  .defaultImplementation

instance : ToForwardSearcher Slice ForwardSliceSearcher where
  toSearcher := iter

@[inline]
def startsWith (s : Slice) (pat : Slice) : Bool :=
  go s s.startPos.offset pat pat.startPos.offset
where
  go (s : Slice) (sCurr : ByteOffset) (pat : Slice) (patCurr : ByteOffset) : Bool :=
    if h : sCurr < s.utf8Size ∧ patCurr < pat.utf8Size then
      if s.utf8ByteAt sCurr h.left == pat.utf8ByteAt patCurr h.right then
        go s sCurr.inc pat patCurr.inc
      else
        false
    else
      sCurr == s.utf8Size && patCurr == pat.utf8Size
  termination_by s.utf8Size - sCurr
  decreasing_by sorry

@[inline]
def dropPrefix? (s : Slice) (pat : Slice) : Option Slice :=
  go s s.startPos.offset pat pat.startPos.offset
where
  go (s : Slice) (sCurr : ByteOffset) (pat : Slice) (patCurr : ByteOffset) : Option Slice :=
    if h1 : patCurr < pat.utf8Size then
      if h2 : sCurr < s.utf8Size then
        if s.utf8ByteAt sCurr h2 == pat.utf8ByteAt patCurr h1 then
          go s sCurr.inc pat patCurr.inc
        else
          none
      else
        none
    else
      /-
      SAFETY: This pos! works because `s` has the prefix `pat` starting from the initial value of
      `sCurr` so `sCurr` is at the end of the `pat` prefix in `s` and thus at a valid unicode offset
      right now
      -/
      some <| s.replaceStart (s.pos! sCurr)
  termination_by s.endPos.offset - sCurr
  decreasing_by sorry

instance : ForwardPattern Slice ForwardSliceSearcher where
  startsWith := startsWith
  dropPrefix? := dropPrefix?

instance : ToForwardSearcher ByteString ForwardSliceSearcher where
  toSearcher slice pat := iter slice pat.toSlice

instance : ForwardPattern ByteString ForwardSliceSearcher where
  startsWith s pat := startsWith s pat.toSlice
  dropPrefix? s pat := dropPrefix? s pat.toSlice

end ForwardSliceSearcher

end ForwardPatternSearchers

section ForwardPatternUsers

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]
variable [∀ s, Std.Iterators.IteratorLoop (σ s) Id Id]
variable [ForwardPattern ρ σ]

@[inline]
def startsWith (s : Slice) (pat : ρ) : Bool :=
  ForwardPattern.startsWith s pat

structure SplitIterator (ρ : Type) [ForwardPattern ρ σ] where
  s : Slice
  currPos : s.Pos
  searcher : Std.Iter (α := σ s) (SearchStep s)
  --deriving Inhabited

namespace SplitIterator

instance [Pure m] : Std.Iterators.Iterator (SplitIterator ρ) m Slice where
  IsPlausibleStep := sorry
  step := fun ⟨s, currPos, searcher⟩ =>
    match Internal.nextMatch searcher with
    | some (searcher, startPos, endPos) =>
      -- TODO: This is difficult, we want to put `endPos` here but our abstract notion of pattern
      -- might return something that is in fact not `currPos ≤` and as such invalid to be used here.
      -- we might require some lawfulness annotations on the pattern (or more precisely its searcher
      -- iterator) to make this work out. I'll wait on this for a talk with Markus.
      let slice := s.replaceStart currPos |>.replaceEnd sorry
      let nextIt := ⟨s, endPos, searcher⟩
      pure ⟨.yield nextIt slice, sorry⟩
    | none => pure ⟨.done, sorry⟩

private def finitenessRelation [Pure m] : Std.Iterators.FinitenessRelation (SplitIterator ρ) m where
  rel := sorry
  wf := sorry
  subrelation := sorry

instance [Pure m] : Std.Iterators.Finite (SplitIterator ρ) m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect (SplitIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial (SplitIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop (SplitIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial (SplitIterator ρ) m n :=
  .defaultImplementation

end SplitIterator

@[specialize pat]
def split (s : Slice) (pat : ρ) : Std.Iter (α := SplitIterator ρ) Slice :=
  { internalState := { s, currPos := s.startPos, searcher := ToForwardSearcher.toSearcher s pat } }

@[specialize pat]
def trimStartMatches (s : Slice) (pat : ρ) : Slice :=
  let searcher := ToForwardSearcher.toSearcher s pat
  match Internal.nextReject searcher with
  | some (_, startPos, _) => s.replaceStart startPos
  | none => s.replaceStart s.endPos

-- If we want to optimize this can be pushed further by specialising for ASCII
@[inline]
def trimAsciiStart (s : Slice) : Slice :=
  trimStartMatches s Char.isWhitespace

@[inline]
def dropPrefix? (s : Slice) (pat : ρ) : Option Slice :=
  ForwardPattern.dropPrefix? s pat

@[specialize pat]
def trimPrefix (s : Slice) (pat : ρ) : Slice :=
  dropPrefix? s pat |>.getD s

@[specialize pat]
def find (s : Slice) (pat : ρ) : Option s.Pos :=
  let searcher := ToForwardSearcher.toSearcher s pat
  match Internal.nextMatch searcher with
  | some (_, startPos, _) => some startPos
  | none => none

@[specialize pat]
def contains (s : Slice) (pat : ρ) : Bool :=
  let searcher := ToForwardSearcher.toSearcher s pat
  Internal.nextMatch searcher |>.isSome

@[specialize pat]
def all (s : Slice) (pat : ρ) : Bool :=
  let searcher := ToForwardSearcher.toSearcher s pat
  Internal.nextReject searcher |>.isNone

end ForwardPatternUsers

-- For reverse search we implement a different type class hierarchy as we only want to verify one
-- string searching algorithm this quarter, once we have the reverse one we can unify.

class ToBackwardSearcher (ρ : Type) (σ : outParam (Slice → Type)) where
  toSearcher : (s : Slice) → ρ → Std.Iter (α := σ s) (SearchStep s)

class SuffixPattern (ρ : Type) where
  endsWith : Slice → ρ → Bool
  dropSuffix? : Slice → ρ → Option Slice

namespace ToBackwardSearcher

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [ToBackwardSearcher ρ σ]

@[specialize pat]
def defaultEndsWith (s : Slice) (pat : ρ) : Bool :=
  let searcher := ToBackwardSearcher.toSearcher s pat
  match searcher.step with
  | .yield _ (.matched _ endPos) _ => s.endPos = endPos
  | _ => false

@[specialize pat]
def defaultDropSuffix? (s : Slice) (pat : ρ) : Option Slice :=
  let searcher := ToBackwardSearcher.toSearcher s pat
  match searcher.step with
  | .yield _ (.matched startPos _) _ => some (s.replaceEnd startPos)
  | _ => none

@[always_inline, inline]
def defaultImplementation : SuffixPattern ρ where
  endsWith := defaultEndsWith
  dropSuffix? := defaultDropSuffix?

end ToBackwardSearcher

section BackwardPatternSearchers

@[unbox]
structure BackwardCharSearcher (s : Slice) where
  currPos : s.Pos
  needle : Char
  deriving Inhabited

namespace BackwardCharSearcher

@[inline]
def iter (s : Slice) (c : Char) : Std.Iter (α := BackwardCharSearcher s) (SearchStep s) :=
  { internalState := { currPos := s.startPos, needle := c }}

instance (s : Slice) : Std.Iterators.Iterator (BackwardCharSearcher s) Id (SearchStep s) where
  IsPlausibleStep it
    | .yield it' out =>
      it.internalState.needle = it'.internalState.needle ∧
      ∃ h1 : it.internalState.currPos ≠ s.startPos,
        it'.internalState.currPos = it.internalState.currPos.prev h1 ∧
        match out with
        | .matched startPos endPos =>
          it.internalState.currPos = endPos ∧
          it'.internalState.currPos = startPos ∧
          (it.internalState.currPos.prev h1).get (prev_ne_endPos h1) = it.internalState.needle
        | .rejected startPos endPos =>
          it.internalState.currPos = endPos ∧
          it'.internalState.currPos = startPos ∧
          (it.internalState.currPos.prev h1).get (prev_ne_endPos h1) ≠ it.internalState.needle
    | .skip _ => False
    | .done => it.internalState.currPos = s.startPos
  step := fun ⟨currPos, needle⟩ =>
    if h1 : currPos = s.startPos then
      pure ⟨.done, by simp [h1]⟩
    else
      let nextPos := currPos.prev h1
      let nextIt := ⟨nextPos, needle⟩
      if h2 : nextPos.get (prev_ne_endPos h1) = needle then
        pure ⟨.yield nextIt (.matched nextPos currPos), by simp [h1, h2, nextIt, nextPos]⟩
      else
        pure ⟨.yield nextIt (.rejected nextPos currPos), by simp [h1, h2, nextIt, nextPos]⟩

private def finitenessRelation : Std.Iterators.FinitenessRelation (BackwardCharSearcher s) Id where
  rel := sorry
  wf := sorry
  subrelation := sorry

instance : Std.Iterators.Finite (BackwardCharSearcher s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.Iterators.IteratorLoop (BackwardCharSearcher s) Id Id :=
  .defaultImplementation

instance : ToBackwardSearcher Char BackwardCharSearcher where
  toSearcher := iter

instance : SuffixPattern Char := ToBackwardSearcher.defaultImplementation

end BackwardCharSearcher

@[unbox]
structure BackwardCharPredSearcher (s : Slice) where
  currPos : s.Pos
  needle : Char → Bool
  deriving Inhabited

namespace BackwardCharPredSearcher

@[inline]
def iter (s : Slice) (c : Char → Bool) : Std.Iter (α := BackwardCharPredSearcher s) (SearchStep s) :=
  { internalState := { currPos := s.startPos, needle := c }}

instance (s : Slice) : Std.Iterators.Iterator (BackwardCharPredSearcher s) Id (SearchStep s) where
  IsPlausibleStep it
    | .yield it' out =>
      it.internalState.needle = it'.internalState.needle ∧
      ∃ h1 : it.internalState.currPos ≠ s.startPos,
        it'.internalState.currPos = it.internalState.currPos.prev h1 ∧
        match out with
        | .matched startPos endPos =>
          it.internalState.currPos = endPos ∧
          it'.internalState.currPos = startPos ∧
          it.internalState.needle ((it.internalState.currPos.prev h1).get (prev_ne_endPos h1))
        | .rejected startPos endPos =>
          it.internalState.currPos = endPos ∧
          it'.internalState.currPos = startPos ∧
          ¬ it.internalState.needle ((it.internalState.currPos.prev h1).get (prev_ne_endPos h1))
    | .skip _ => False
    | .done => it.internalState.currPos = s.startPos
  step := fun ⟨currPos, needle⟩ =>
    if h1 : currPos = s.startPos then
      pure ⟨.done, by simp [h1]⟩
    else
      let nextPos := currPos.prev h1
      let nextIt := ⟨nextPos, needle⟩
      if h2 : needle <| nextPos.get (prev_ne_endPos h1) then
        pure ⟨.yield nextIt (.matched nextPos currPos), by simp [h1, h2, nextIt, nextPos]⟩
      else
        pure ⟨.yield nextIt (.rejected nextPos currPos), by simp [h1, h2, nextIt, nextPos]⟩

private def finitenessRelation : Std.Iterators.FinitenessRelation (BackwardCharPredSearcher s) Id where
  rel := sorry
  wf := sorry
  subrelation := sorry

instance : Std.Iterators.Finite (BackwardCharPredSearcher s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.Iterators.IteratorLoop (BackwardCharPredSearcher s) Id Id :=
  .defaultImplementation

instance : ToBackwardSearcher (Char → Bool) BackwardCharPredSearcher where
  toSearcher := iter

instance : SuffixPattern Char := ToBackwardSearcher.defaultImplementation

end BackwardCharPredSearcher

end BackwardPatternSearchers

namespace SuffixPattern.Slice

@[inline]
def endsWith (s : Slice) (pat : Slice) : Bool :=
  go s s.endPos.offset pat pat.endPos.offset
where
  go (s : Slice) (sCurr : ByteOffset) (pat : Slice) (patCurr : ByteOffset) : Bool :=
    if h : sCurr ≠ 0 ∧ patCurr ≠ 0 then
      let sPrev := sCurr.dec
      let patPrev := patCurr.dec
      -- These sorries are simple Nat arguments if we pull through additional invariants
      if s.utf8ByteAt sPrev sorry == pat.utf8ByteAt patPrev sorry then
        go s sPrev pat patPrev
      else
        false
    else
      sCurr == 0 && patCurr == 0
  termination_by sCurr
  decreasing_by sorry

@[inline]
def dropSuffix? (s : Slice) (pat : Slice) : Option Slice :=
  go s s.endPos.offset pat pat.endPos.offset
where
  go (s : Slice) (sCurr : ByteOffset) (pat : Slice) (patCurr : ByteOffset) : Option Slice :=
    if h1 : patCurr ≠ 0 then
      if h2 : sCurr ≠ 0 then
        let sPrev := sCurr.dec
        let patPrev := patCurr.dec
        if s.utf8ByteAt sPrev sorry == pat.utf8ByteAt patPrev sorry then
          go s sPrev pat patPrev
        else
          none
      else
        none
    else
      /-
      SAFETY: Same reason as `dropPrefix`.
      -/
      some <| s.replaceStart (Slice.pos! s sCurr)
  termination_by sCurr
  decreasing_by sorry

instance : SuffixPattern Slice where
  endsWith := endsWith
  dropSuffix? := dropSuffix?

instance : SuffixPattern ByteString where
  endsWith s pat := endsWith s pat.toSlice
  dropSuffix? s pat := dropSuffix? s pat.toSlice

end SuffixPattern.Slice

section SuffixPatternUsers

variable {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]
variable [∀ s, Std.Iterators.IteratorLoop (σ s) Id Id]

@[inline]
def endsWith [SuffixPattern ρ] (s : Slice) (pat : ρ) : Bool :=
  SuffixPattern.endsWith s pat

-- TODO: Wait for forward splitting with this one
structure RevSplitIterator where
  s : Slice
  currPos : s.Pos
  --deriving Inhabited

instance : Std.Iterators.Iterator RevSplitIterator Id Slice where
  IsPlausibleStep := sorry
  step := sorry

@[specialize pat]
def revSplit [ToBackwardSearcher ρ σ] (s : Slice) (pat : ρ) : RevSplitIterator := sorry

@[specialize pat]
def trimEndMatches [ToBackwardSearcher ρ σ] (s : Slice) (pat : ρ) : Slice :=
  let searcher := ToBackwardSearcher.toSearcher s pat
  match Internal.nextReject searcher with
  | some (_, _, endPos) => s.replaceEnd endPos
  | none => s.replaceEnd s.startPos

-- If we want to optimize this can be pushed further by specialising for ASCII
@[inline]
def trimAsciiEnd (s : Slice) : Slice :=
  trimEndMatches s Char.isWhitespace

@[inline]
def dropSuffix? [SuffixPattern ρ] (s : Slice) (pat : ρ) : Option Slice :=
  SuffixPattern.dropSuffix? s pat

@[specialize pat]
def trimSuffix [SuffixPattern ρ] (s : Slice) (pat : ρ) : Slice :=
  dropSuffix? s pat |>.getD s

@[specialize pat]
def revFind [ToBackwardSearcher ρ σ] (s : Slice) (pat : ρ) : Option s.Pos :=
  let searcher := ToBackwardSearcher.toSearcher s pat
  match Internal.nextMatch searcher with
  | some (_, startPos, _) => some startPos
  | none => none

end SuffixPatternUsers

def trimAscii (s : Slice) : Slice :=
  s.trimAsciiStart.trimAsciiEnd

def eqIgnoreAsciiCase (s1 s2 : Slice) : Bool :=
    s1.utf8Size == s2.utf8Size && go s1 s1.startPos.offset s2 s2.startPos.offset
where
  go (s1 : Slice) (s1Curr : ByteOffset) (s2 : Slice) (s2Curr : ByteOffset) : Bool :=
    if h : s1Curr < s1.utf8Size ∧ s2Curr < s2.utf8Size then
      if (s1.utf8ByteAt s1Curr h.left).toAsciiLower == (s2.utf8ByteAt s2Curr h.right).toAsciiLower then
        go s1 s1Curr.inc s2 s2Curr.inc
      else
        false
    else
      s1Curr == s1.utf8Size && s2Curr == s2.utf8Size
  termination_by s1.endPos.offset - s1Curr
  decreasing_by sorry

instance : DecidableEq Slice := sorry
instance : Ord Slice := sorry
instance : Hashable Slice := sorry

structure CharIterator where
  s : Slice
  currPos : s.Pos
  --deriving Inhabited

namespace CharIterator
-- TODO: API to create iterator

instance [Pure m] : Std.Iterators.Iterator CharIterator m Char where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h1 : it.internalState.s = it'.internalState.s,
      ∃ h2 : it.internalState.currPos ≠ it.internalState.s.endPos,
        it'.internalState.currPos = h1 ▸ (it.internalState.currPos.next h2) ∧
        it.internalState.currPos.get h2 = out
    | .skip _ => False
    | .done => it.internalState.currPos = it.internalState.s.endPos
  step := fun ⟨s, currPos⟩ =>
    if h : currPos = s.endPos then
      pure ⟨.done, by simp [h]⟩
    else
      pure ⟨.yield ⟨s, currPos.next h⟩ (currPos.get h), by simp [h]⟩

private def finitenessRelation [Pure m] : Std.Iterators.FinitenessRelation CharIterator m where
  rel := sorry
  wf := sorry
  subrelation := sorry

instance [Pure m] : Std.Iterators.Finite CharIterator m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect CharIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial CharIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop CharIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial CharIterator m n :=
  .defaultImplementation

end CharIterator

structure CharIndexIterator (s : Slice) where
  currPos : s.Pos
  deriving Inhabited

namespace CharIndexIterator
-- TODO: API to create iterator

instance [Pure m] : Std.Iterators.Iterator (CharIndexIterator s) m s.Pos where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h : it.internalState.currPos ≠ s.endPos,
        it'.internalState.currPos = it.internalState.currPos.next h ∧
        it.internalState.currPos = out
    | .skip _ => False
    | .done => it.internalState.currPos = s.endPos
  step := fun ⟨⟨currPos⟩⟩ =>
    if h : currPos = s.endPos then
      pure ⟨.done, by simp [h]⟩
    else
      pure ⟨.yield ⟨⟨currPos.next h⟩⟩ currPos, by simp [h]⟩

private def finitenessRelation [Pure m] : Std.Iterators.FinitenessRelation (CharIndexIterator s) m where
  rel := sorry
  wf := sorry
  subrelation := sorry

instance [Pure m] : Std.Iterators.Finite (CharIndexIterator s) m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect (CharIndexIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial (CharIndexIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop (CharIndexIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial (CharIndexIterator s) m n :=
  .defaultImplementation

end CharIndexIterator

-- TODO: wait with this one until split is resolved, will run into the same issue
structure LineIterator where
  s : Slice
  currPos : s.Pos
  --deriving Inhabited

namespace LineIterator
-- TODO: API to create iterator

instance [Pure m] : Std.Iterators.Iterator LineIterator m Slice where
  IsPlausibleStep it := sorry
  step := sorry

private def finitenessRelation [Pure m] : Std.Iterators.FinitenessRelation (LineIterator) m where
  rel := sorry
  wf := sorry
  subrelation := sorry

instance [Pure m] : Std.Iterators.Finite LineIterator m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect LineIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial LineIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop LineIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial LineIterator m n :=
  .defaultImplementation

end LineIterator

-- TODO: wait with this one until markus has decided whether ByteOffset is a good idea
structure ByteIterator where
  s : Slice
  offset : ByteOffset
  --deriving Inhabited

namespace ByteIterator
-- TODO: API to create iterator

instance [Pure m] : Std.Iterators.Iterator ByteIterator m UInt8 where
  IsPlausibleStep it := sorry
  step := sorry

private def finitenessRelation [Pure m] : Std.Iterators.FinitenessRelation (ByteIterator) m where
  rel := sorry
  wf := sorry
  subrelation := sorry

instance [Pure m] : Std.Iterators.Finite ByteIterator m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect ByteIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial ByteIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop ByteIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial ByteIterator m n :=
  .defaultImplementation

end ByteIterator

section Ranges

instance {s : Slice} : Std.PRange.UpwardEnumerable s.Pos where
  succ? p := p.next?

instance {s : Slice} : Std.PRange.Least? s.Pos where
  least? := some s.startPos

/-
- LawfulUpwardEnumerable is not doable without LT instance
- InfinitelyUpwardEnumerable is false
- RangeSize is doable but not in O(1) so we skip it as its a footgun
- LawfulRangeSize not applicable because of that
-/

/-
We want this to work at least:
#check fun (s : Slice) => Id.run do
  for x in s.startPos...s.endPos do
    continue
  return 0
-/

end Ranges

end Slice
end ByteString
