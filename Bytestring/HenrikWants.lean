import Bytestring.Basic

namespace ByteString
namespace Slice

theorem prev_ne_endPos {s : Slice} {p : s.Pos} (h : p ≠ s.startPos) : p.prev h ≠ s.endPos := sorry

end Slice
end ByteString
