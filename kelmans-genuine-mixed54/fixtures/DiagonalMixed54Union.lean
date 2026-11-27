import DiagonalMixed54Ranks
import RemotePortCapacity
import Mathlib.Data.List.Chain

open Finset SimpleGraph
open scoped BigOperators
set_option maxHeartbeats 0
namespace KelmansCactus.AtomicBridge.DiagonalMixed54
open SquareCap (HasFactor)
open RemoteSpacedPrismHandle (Port)
open RemotePortCapacity (Behind residue_capacity)

private def zones : List (Fin 7) := [6,0,0,0,0,0,0,0,0,6,1,1,1,1,1,1,1,1,6,2,2,2,2,2,2,2,2,6,3,3,3,3,3,3,3,3,4,0,0,0,0,1,1,1,2,2,3,3,5,4,2,3,0,0]
private def portIndex : Port → Nat
  | .inl (.inl false) => 48
  | .inl (.inl true) => 49
  | .inl (.inr false) => 50
  | .inl (.inr true) => 51
  | .inr false => 52
  | .inr true => 53
def home : Board → Fin 7
  | .inl v => zones[v.val]!
  | .inr p => zones[portIndex p]!

def ports : Finset Board := univ.filter (fun x => home x=6)
def group (i : Fin 6) : Finset Board := univ.filter (fun x => home x=i.castSucc)
def good (x y : Board) : Prop := home x=6 ∨ home y=6 ∨ home x=home y
instance (x y : Board) : Decidable (good x y) := by unfold good; infer_instance
theorem good_symm {x y : Board} (h : good x y) : good y x := by
  rcases h with h|h|h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h.symm)

set_option maxRecDepth 15000 in
private theorem certified_old_edges :
    ∀ e ∈ edgeTable.edges.toFinset,
    (mate false e.1=e.2 ∧ mate true e.1=e.2) ∨ good (.inl e.1) (.inl e.2) := by
  have check : edgeTable.edges.all
      (fun e=>decide ((mate false e.1=e.2 ∧ mate true e.1=e.2) ∨ good (.inl e.1) (.inl e.2))) = true := by decide
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp check e (List.mem_toFinset.mp he))
private theorem certified_slots : ∀ i : Port, good (.inr i) (.inl (a i)) ∧ good (.inr i) (.inl (b i)) :=
  by decide

theorem adjacency_respects_seal {x y : Board} (e : pairUnion.Adj x y) : good x y := by
  rcases x with (u|i) <;> rcases y with (v|j)
  · change (rank false).Adj (.inl u) (.inl v) ∨ (rank true).Adj (.inl u) (.inl v) at e
    have forward (u v : Core) (ad : (u,v)∈edgeTable.edges)
        (bad : ¬(mate false u=v ∧ mate true u=v)) : good (.inl u) (.inl v) :=
      (certified_old_edges (u,v) (List.mem_toFinset.mpr ad)).resolve_left bad
    have adj : core.Adj u v := e.elim (fun h=>h.1.1) (fun h=>h.1.1)
    have bad : ¬(mate false u=v ∧ mate true u=v) :=
      fun ⟨p,q⟩=>e.elim (fun h=>h.2 p) (fun h=>h.2 q)
    rcases adj with f|f
    · exact forward u v f bad
    · have rev : ¬(mate false v=u ∧ mate true v=u) := by
        rintro ⟨p,q⟩
        apply bad
        exact ⟨by rw [←p,mate_involutive],by rw [←q,mate_involutive]⟩
      exact good_symm (forward v u f rev)
  · obtain rfl|rfl := pair_le e
    · exact good_symm (certified_slots j).1
    · exact good_symm (certified_slots j).2
  · obtain rfl|rfl := pair_le e
    · exact (certified_slots i).1
    · exact (certified_slots i).2
  · exact (pair_le e : False).elim

theorem groups_disjoint (i j : Fin 6) (ne : i≠j) : Disjoint (group i) (group j) := by
  apply disjoint_left.mpr
  intro x mx my
  have ex : home x=i.castSucc := (mem_filter.mp mx).2
  have ey : home x=j.castSucc := (mem_filter.mp my).2
  exact ne (Fin.ext (congrArg (fun f : Fin 7 => f.val) (ex.symm.trans ey)))

theorem groups_off_ports (i : Fin 6) : Disjoint (group i) ports := by
  apply disjoint_left.mpr
  intro x mx my
  have ex : home x=i.castSucc := (mem_filter.mp mx).2
  have ey : home x=6 := (mem_filter.mp my).2
  have val : i.val=6 := congrArg Fin.val (ex.symm.trans ey)
  omega

theorem groups_sealed (i : Fin 6) : Behind pairUnion ports (group i) := by
  intro x hx y ad
  rcases adjacency_respects_seal ad with p|p|p
  · exact (disjoint_left.mp (groups_off_ports i) hx (mem_filter.mpr ⟨mem_univ _,p⟩)).elim
  · exact Or.inr (mem_filter.mpr ⟨mem_univ _,p⟩)
  · exact Or.inl (mem_filter.mpr ⟨mem_univ _,p.symm.trans (mem_filter.mp hx).2⟩)

theorem ports_exact : ports=(route [0,9,18,27]).toFinset := by decide
theorem sealed_orders (i : Fin 6) :
    (group i).card = ([14,11,11,11,2,1] : List Nat)[i.val]! := by
  fin_cases i <;> decide

theorem pair_union_no_factor : ¬HasFactor pairUnion := by
  intro f
  have b := residue_capacity pairUnion ports group groups_off_ports groups_disjoint groups_sealed f
  have exact : ¬(∑ i : Fin 6,(group i).card%3) ≤ 2*ports.card := by decide
  exact exact b

theorem rank_no_factor (k : Bool) : ¬HasFactor (rank k) := by
  rintro ⟨P,legal,apart,cover⟩
  apply pair_union_no_factor
  refine ⟨P,?_,apart,cover⟩
  intro T tm
  obtain ⟨size,c,cm,edges⟩ := legal T tm
  refine ⟨size,c,cm,?_⟩
  intro x m ne
  cases k
  · exact Or.inl (edges x m ne)
  · exact Or.inr (edges x m ne)

def diagA : List Board := route [2,3,4,5,6,7]
def diagB : List Board := route [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,0,1]
def cyclicOrder (flip : Bool) : List Board := diagA ++ (if flip then diagB.reverse else diagB)
def shortEar : List Board := route [0,48,9]
def longEar : List Board := route [18,49,36,27]
def positions (i j : Nat) := ((j+36-i-1)%36,(i+36-j-1)%36)

set_option maxRecDepth 14000 in
theorem locked_phases (flip : Bool) :
    (cyclicOrder flip).Nodup ∧ (cyclicOrder flip).length=36 ∧
    ((cyclicOrder flip).getLast?.getD (decode 0)::cyclicOrder flip).Chain' pairUnion.Adj ∧
    shortEar.Chain' pairUnion.Adj ∧ longEar.Chain' pairUnion.Adj ∧
    (∀ i : Fin 36,(cyclicOrder flip)[i.val]! ∈ ports ↔ i.val%9=7) := by
  have cycle : (cyclicOrder flip).Nodup ∧ (cyclicOrder flip).length=36 ∧
      ((cyclicOrder flip).getLast?.getD (decode 0)::cyclicOrder flip).Chain' pairUnion.Adj ∧
      shortEar.Chain' pairUnion.Adj ∧ longEar.Chain' pairUnion.Adj := by
    cases flip <;> decide
  have position (i : Fin 36) : (cyclicOrder flip)[i.val]!∈ports ↔ i.val%9=7 := by
    cases flip <;> fin_cases i <;> decide
  exact ⟨cycle.1,cycle.2.1,cycle.2.2.1,cycle.2.2.2.1,cycle.2.2.2.2,position⟩

theorem two_bad_residues (flip : Bool) {i j : Fin 36} (hi : (cyclicOrder flip)[i.val]!∈ports)
    (hj : (cyclicOrder flip)[j.val]!∈ports) :
    (positions i.val j.val).1%3=2 ∧ (positions i.val j.val).2%3=2 := by
  have a := (locked_phases flip).2.2.2.2.2 i |>.mp hi
  have b := (locked_phases flip).2.2.2.2.2 j |>.mp hj
  have hi := i.isLt
  have hj := j.isLt
  unfold positions
  omega

#print axioms adjacency_respects_seal
#print axioms sealed_orders
#print axioms pair_union_no_factor
#print axioms rank_no_factor
#print axioms locked_phases
#print axioms two_bad_residues
end KelmansCactus.AtomicBridge.DiagonalMixed54
