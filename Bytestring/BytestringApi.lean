import Bytestring.SliceApi

namespace ByteString

@[inline]
def isEmpty (s : ByteString) : Bool := s.utf8Size == 0

section ForwardPatternUsers

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (Slice.SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]
variable [∀ s, Std.Iterators.IteratorLoop (σ s) Id Id]
variable [Slice.ForwardPattern ρ σ]

@[inline]
def startsWith (s : ByteString) (pat : ρ) : Bool :=
  s.toSlice.startsWith pat

@[inline]
def split (s : ByteString) (pat : ρ) : Std.Iter (α := Slice.SplitIterator ρ) Slice :=
  s.toSlice.split pat

@[inline]
def trimStartMatches (s : ByteString) (pat : ρ) : Slice :=
  s.toSlice.trimStartMatches pat

@[inline]
def trimAsciiStart (s : ByteString) : Slice :=
  s.toSlice.trimAsciiStart

@[inline]
def dropPrefix? (s : ByteString) (pat : ρ) : Option Slice :=
  s.toSlice.dropPrefix? pat

@[inline]
def trimPrefix (s : ByteString) (pat : ρ) : Slice :=
  s.toSlice.trimPrefix pat

@[inline]
def find (s : ByteString) (pat : ρ) : Option s.Pos :=
  s.toSlice.find pat |>.map Slice.Pos.up

@[inline]
def contains (s : ByteString) (pat : ρ) : Bool :=
  s.toSlice.contains pat

@[inline]
def all (s : ByteString) (pat : ρ) : Bool :=
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
def revSplit [Slice.ToBackwardSearcher ρ σ] (s : ByteString) (pat : ρ) : Slice.RevSplitIterator :=
  s.toSlice.revSplit pat

@[inline]
def trimEndMatches [Slice.ToBackwardSearcher ρ σ] (s : ByteString) (pat : ρ) : Slice :=
  s.toSlice.trimEndMatches pat

@[inline]
def trimAsciiEnd (s : ByteString) : Slice :=
  s.toSlice.trimAsciiEnd

@[inline]
def dropSuffix? [Slice.SuffixPattern ρ] (s : ByteString) (pat : ρ) : Option Slice :=
  s.toSlice.dropSuffix? pat

@[inline]
def trimSuffix [Slice.SuffixPattern ρ] (s : ByteString) (pat : ρ) : Slice :=
  s.toSlice.trimSuffix pat

@[inline]
def revFind [Slice.ToBackwardSearcher ρ σ] (s : ByteString) (pat : ρ) : Option s.Pos :=
  s.toSlice.revFind pat |>.map Slice.Pos.up

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

-- TODO: iterator API

end ByteString
