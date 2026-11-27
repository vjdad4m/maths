import TinyFourOrder14OneRow111Part0
import TinyFourOrder14OneRow111Part1
import TinyFourOrder14OneRow111Part2

namespace FourOrder14One
theorem tbl111 : Table 1 11 (by decide) (by decide) := by
  intro a b c d
  fin_cases a
  · exact tbl111_part0 b c d
  · exact tbl111_part1 b c d
  · exact tbl111_part2 b c d

#print axioms tbl111
end FourOrder14One
