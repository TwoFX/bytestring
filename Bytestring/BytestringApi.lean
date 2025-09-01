import Bytestring.SliceApi

namespace ByteString

@[inline]
def isEmpty (s : ByteString) : Bool := s.utf8Size == 0

section ForwardPatternUsers

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (Slice.SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]
variable [∀ s, Std.Iterators.IteratorLoop (σ s) Id Id]

@[inline]
def startsWith [Slice.ForwardPattern ρ] (s : ByteString) (pat : ρ) : Bool :=
  s.toSlice.startsWith pat

@[inline]
def split [Slice.ToForwardSearcher ρ σ] (s : ByteString) (pat : ρ) : Std.Iter (α := Slice.SplitIterator ρ) Slice :=
  s.toSlice.split pat

@[inline]
def splitInclusive [Slice.ToForwardSearcher ρ σ] (s : ByteString) (pat : ρ) : Std.Iter (α := Slice.SplitInclusiveIterator ρ) Slice :=
  s.toSlice.splitInclusive pat

@[inline]
def drop (s : ByteString) (n : Nat) : Slice :=
  s.toSlice.drop n

@[inline]
def dropWhile [Slice.ToForwardSearcher ρ σ] (s : ByteString) (pat : ρ) : Slice :=
  s.toSlice.dropWhile pat

@[inline]
def trimAsciiStart (s : ByteString) : Slice :=
  s.toSlice.trimAsciiStart

@[inline]
def take (s : ByteString) (n : Nat) : Slice :=
  s.toSlice.take n

@[inline]
def takeWhile [Slice.ToForwardSearcher ρ σ] (s : ByteString) (pat : ρ) : Slice :=
  s.toSlice.takeWhile pat

@[inline]
def dropPrefix? [Slice.ForwardPattern ρ] (s : ByteString) (pat : ρ) : Option Slice :=
  s.toSlice.dropPrefix? pat

@[inline]
def trimPrefix [Slice.ForwardPattern ρ] (s : ByteString) (pat : ρ) : Slice :=
  s.toSlice.trimPrefix pat

@[inline]
def find? [Slice.ToForwardSearcher ρ σ] (s : ByteString) (pat : ρ) : Option s.Pos :=
  s.toSlice.find? pat |>.map Slice.Pos.up

@[inline]
def contains [Slice.ToForwardSearcher ρ σ] (s : ByteString) (pat : ρ) : Bool :=
  s.toSlice.contains pat

@[inline]
def all [Slice.ToForwardSearcher ρ σ] (s : ByteString) (pat : ρ) : Bool :=
  s.toSlice.all pat

end ForwardPatternUsers

section SuffixPatternUsers

variable {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (Slice.SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]
variable [∀ s, Std.Iterators.IteratorLoop (σ s) Id Id]

@[inline]
def endsWith [Slice.SuffixPattern ρ] (s : ByteString) (pat : ρ) : Bool :=
  s.toSlice.endsWith pat

@[inline]
def revSplit [Slice.ToBackwardSearcher ρ σ] (s : ByteString) (pat : ρ) :
    Std.Iter (α := Slice.RevSplitIterator ρ) Slice :=
  s.toSlice.revSplit pat

@[inline]
def dropEnd (s : ByteString) (n : Nat) : Slice :=
  s.toSlice.dropEnd n

@[inline]
def dropEndWhile [Slice.ToBackwardSearcher ρ σ] (s : ByteString) (pat : ρ) : Slice :=
  s.toSlice.dropEndWhile pat

@[inline]
def trimAsciiEnd (s : ByteString) : Slice :=
  s.toSlice.trimAsciiEnd

@[inline]
def takeEnd (s : ByteString) (n : Nat) : Slice :=
  s.toSlice.takeEnd n

@[inline]
def takeEndWhile [Slice.ToBackwardSearcher ρ σ] (s : ByteString) (pat : ρ) : Slice :=
  s.toSlice.takeEndWhile pat

@[inline]
def dropSuffix? [Slice.SuffixPattern ρ] (s : ByteString) (pat : ρ) : Option Slice :=
  s.toSlice.dropSuffix? pat

@[inline]
def trimSuffix [Slice.SuffixPattern ρ] (s : ByteString) (pat : ρ) : Slice :=
  s.toSlice.trimSuffix pat

@[inline]
def revFind? [Slice.ToBackwardSearcher ρ σ] (s : ByteString) (pat : ρ) : Option s.Pos :=
  s.toSlice.revFind? pat |>.map Slice.Pos.up

end SuffixPatternUsers

@[inline]
def trimAscii (s : ByteString) : Slice :=
  s.toSlice.trimAscii

@[inline]
def eqIgnoreAsciiCase (s1 s2 : ByteString) : Bool :=
  s1.toSlice.eqIgnoreAsciiCase s2.toSlice

instance : DecidableEq ByteString := sorry
instance : Ord ByteString := sorry
instance : Hashable ByteString := sorry

def chars (s : ByteString) : Std.Iter (α := Slice.CharIterator) Char :=
  s.toSlice.chars

def revChars (s : ByteString) : Std.Iter (α := Slice.RevCharIterator) Char :=
  s.toSlice.revChars

structure PosIterator (s : ByteString) where
  currPos : s.Pos
  --deriving Inhabited

-- we want to duplicate this to return `String.Pos` instead of `Slice.Pos`
def positions (s : ByteString) : Std.Iter (α := PosIterator s) s.Pos :=
  { internalState := { currPos := s.startPos }}

namespace PosIterator

instance [Pure m] : Std.Iterators.Iterator (PosIterator s) m s.Pos where
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

private def finitenessRelation [Pure m] : Std.Iterators.FinitenessRelation (PosIterator s) m where
  rel := InvImage WellFoundedRelation.rel
      (fun it => s.utf8Size.numBytes - it.internalState.currPos.offset.numBytes)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation := sorry

instance [Pure m] : Std.Iterators.Finite (PosIterator s) m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect (PosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial (PosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop (PosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial (PosIterator s) m n :=
  .defaultImplementation

end PosIterator

structure RevPosIterator (s : ByteString) where
  currPos : s.Pos
  --deriving Inhabited

def revPositions (s : ByteString) : Std.Iter (α := RevPosIterator s) s.Pos :=
  { internalState := { currPos := s.endPos }}

namespace RevPosIterator

instance [Pure m] : Std.Iterators.Iterator (RevPosIterator s) m s.Pos where
  IsPlausibleStep it := sorry
  step := fun ⟨⟨currPos⟩⟩ =>
    if h : currPos = s.startPos then
      pure ⟨.done, sorry⟩
    else
      let prevPos := currPos.prev h
      pure ⟨.yield ⟨⟨prevPos⟩⟩ prevPos, sorry⟩

private def finitenessRelation [Pure m] : Std.Iterators.FinitenessRelation (RevPosIterator s) m where
  rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.currPos.offset.numBytes)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation := sorry

instance [Pure m] : Std.Iterators.Finite (RevPosIterator s) m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect (RevPosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial (RevPosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop (RevPosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial (RevPosIterator s) m n :=
  .defaultImplementation

end RevPosIterator

-- TODO: naming
def bytes' (s : ByteString) : Std.Iter (α := Slice.ByteIterator) UInt8 :=
  s.toSlice.bytes

def revBytes (s : ByteString) : Std.Iter (α := Slice.RevByteIterator) UInt8 :=
  s.toSlice.revBytes

def lines (s : ByteString) :=
  s.toSlice.lines

end ByteString
