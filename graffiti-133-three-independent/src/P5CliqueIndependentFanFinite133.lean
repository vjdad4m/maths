import P5CliqueOnePortAmbientBudget133
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Graffiti133P5CliqueArms.IndependentFanFinite
set_option maxRecDepth 140000
set_option maxHeartbeats 25000000

def masks : Fin 35 → Nat := ![0,1,2,4,8,16,20,24,32,34,40,64,66,68,128,132,136,160,168,192,196,256,258,264,272,280,320,322,512,514,516,528,532,544,546]
def clauses : List (Nat×Nat) := [(0,1049600),(0,8200),(0,65600),(0,8388736),(0,67109120),(0,134348800),(0,268697600),(0,536871424),(0,524800),(0,537395200),(109,0),(111616,0),(433,0),(721,0),(443392,0),(454033408,0),(738304,0),(756023296,0),(91,0),(93184,0),(95420416,0),(9969794,0),(135399944,0),(269779520,0),(68748577,0),(37753862,0),(18891824,0),(136447616,0),(604046432,0),(302253824,0),(50337797,0),(671098889,0),(6340625,0),(11141249,0),(805404737,0),(101449985,0),(545326144,16),(68690176,4),(38012160,128),(269520960,8),(269746696,4096),(68223012,8192),(738224236,16842752),(318905100,134479872),(4228160,268435472),(34607360,262148),(813805594,4194368),(817991706,8256),(105656454,8388864),(114040966,4352)]
def pack (a b c : Nat) : Nat := a+1024*b+1048576*c
def pass (m : Nat) (c : Nat×Nat) : Bool := m &&& c.1 != 0 || m &&& c.2 != c.2
def check (a b c : Fin 35) : Bool := clauses.all (pass (pack (masks a) (masks b) (masks c)))
def rowEval (a : Fin 35) : Bool := (List.finRange 35).any (fun b=>(List.finRange 35).any (fun c=>check a b c))
private theorem row0 : rowEval 0=false := by decide
private theorem row1 : rowEval 1=false := by decide
private theorem row2 : rowEval 2=false := by decide
private theorem row3 : rowEval 3=false := by decide
private theorem row4 : rowEval 4=false := by decide
private theorem row5 : rowEval 5=false := by decide
private theorem row6 : rowEval 6=false := by decide
private theorem row7 : rowEval 7=false := by decide
private theorem row8 : rowEval 8=false := by decide
private theorem row9 : rowEval 9=false := by decide
private theorem row10 : rowEval 10=false := by decide
private theorem row11 : rowEval 11=false := by decide
private theorem row12 : rowEval 12=false := by decide
private theorem row13 : rowEval 13=false := by decide
private theorem row14 : rowEval 14=false := by decide
private theorem row15 : rowEval 15=false := by decide
private theorem row16 : rowEval 16=false := by decide
private theorem row17 : rowEval 17=false := by decide
private theorem row18 : rowEval 18=false := by decide
private theorem row19 : rowEval 19=false := by decide
private theorem row20 : rowEval 20=false := by decide
private theorem row21 : rowEval 21=false := by decide
private theorem row22 : rowEval 22=false := by decide
private theorem row23 : rowEval 23=false := by decide
private theorem row24 : rowEval 24=false := by decide
private theorem row25 : rowEval 25=false := by decide
private theorem row26 : rowEval 26=false := by decide
private theorem row27 : rowEval 27=false := by decide
private theorem row28 : rowEval 28=false := by decide
private theorem row29 : rowEval 29=false := by decide
private theorem row30 : rowEval 30=false := by decide
private theorem row31 : rowEval 31=false := by decide
private theorem row32 : rowEval 32=false := by decide
private theorem row33 : rowEval 33=false := by decide
private theorem row34 : rowEval 34=false := by decide
theorem no_passing_masks (a b c : Fin 35) : check a b c=false := by
  have zero : rowEval a=false := by
    fin_cases a
    · exact row0
    · exact row1
    · exact row2
    · exact row3
    · exact row4
    · exact row5
    · exact row6
    · exact row7
    · exact row8
    · exact row9
    · exact row10
    · exact row11
    · exact row12
    · exact row13
    · exact row14
    · exact row15
    · exact row16
    · exact row17
    · exact row18
    · exact row19
    · exact row20
    · exact row21
    · exact row22
    · exact row23
    · exact row24
    · exact row25
    · exact row26
    · exact row27
    · exact row28
    · exact row29
    · exact row30
    · exact row31
    · exact row32
    · exact row33
    · exact row34
  cases e : check a b c with
  | false => rfl
  | true =>
    have yes : rowEval a=true := List.any_eq_true.mpr ⟨b,List.mem_finRange b,
      List.any_eq_true.mpr ⟨c,List.mem_finRange c,e⟩⟩
    rw [zero] at yes
    contradiction

#print axioms no_passing_masks
end Graffiti133P5CliqueArms.IndependentFanFinite
