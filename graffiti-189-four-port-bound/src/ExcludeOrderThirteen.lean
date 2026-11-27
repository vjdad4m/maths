import PortNumerics
import SingletonOrderThirteen189

namespace Graffiti189SingletonCage
open Finset SimpleGraph
open Graffiti189LongestPath.FourCut.Three
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {r a b : V}
variable (S : SingleRoot G r a b)

theorem order_le_twelve (four : S.ports.card=4)
    (high : ∀ v, v≠r → 4≤G.degree v) : Fintype.card V≤12 := by
  classical
  obtain ⟨_,hi,hA,hB,common,ends⟩ :=
    classes_cap S four (high a S.left.ne.symm) (high b S.right.ne.symm)
  by_contra large
  have order : Fintype.card V=13 := by omega
  have posA : 0<(exclusiveA S).card := by
    by_contra n
    have z := common (Or.inl (by omega))
    omega
  have posB : 0<(exclusiveB S).card := by
    by_contra n
    have z := common (Or.inr (by omega))
    omega
  have ones : (exclusiveA S).card=1 ∧ (exclusiveB S).card=1 := by
    by_cases edge : G.Adj a b
    · have hh := ends edge
      omega
    · simp only [edge,if_false,Nat.add_zero] at hA hB
      omega
  obtain ⟨p,pA⟩ := card_eq_one.mp ones.1
  obtain ⟨q,qB⟩ := card_eq_one.mp ones.2
  have pp : p∈exclusiveA S := by rw [pA]; exact mem_singleton_self p
  have qq : q∈exclusiveB S := by rw [qB]; exact mem_singleton_self q
  have ap : G.Adj a p := (mem_filter.mp pp).2.1
  have nbp : ¬G.Adj b p := (mem_filter.mp pp).2.2
  have bq : G.Adj b q := (mem_filter.mp qq).2.1
  have naq : ¬G.Adj a q := (mem_filter.mp qq).2.2
  have pq : p≠q := fun e => naq (e ▸ ap)
  have up : p∈S.ports := (mem_filter.mp pp).1
  have uq : q∈S.ports := (mem_filter.mp qq).1
  have qmem : q∈S.ports.erase p := mem_erase.mpr ⟨pq.symm,uq⟩
  let T := (S.ports.erase p).erase q
  have two : T.card=2 := by
    dsimp [T]
    rw [card_erase_of_mem qmem, card_erase_of_mem up,four]
  obtain ⟨c,d,_,cd⟩ := card_eq_two.mp two
  have cT : c∈T := by rw [cd]; exact mem_insert_self c _
  have dT : d∈T := by rw [cd]; exact mem_insert_of_mem (mem_singleton_self d)
  have both (v : V) (h : v∈T) : G.Adj a v ∧ G.Adj b v := by
    have vp := (mem_erase.mp (mem_erase.mp h).2).2
    constructor
    · by_cases av : G.Adj a v
      · exact av
      have ex : v∈exclusiveB S := by
        rw [exclusiveB_eq S]; exact mem_filter.mpr ⟨vp,av⟩
      rw [qB] at ex
      exact ((mem_erase.mp h).1 (mem_singleton.mp ex)).elim
    · by_cases bv : G.Adj b v
      · exact bv
      have ex : v∈exclusiveA S := by
        rw [exclusiveA_eq S]; exact mem_filter.mpr ⟨vp,bv⟩
      rw [pA] at ex
      exact ((mem_erase.mp (mem_erase.mp h).2).1 (mem_singleton.mp ex)).elim
  have ports : S.ports={p,q,c,d} := by
    rw [←show insert p (insert q T) = ({p,q,c,d}:Finset V) from by rw [cd]]
    dsimp [T]
    rw [insert_erase qmem, insert_erase up]
  exact no_order_thirteen_explicit S four order ports pq
    (mem_erase.mp (mem_erase.mp cT).2).1.symm (mem_erase.mp cT).1.symm
    ap nbp bq naq (both c cT).1 (both c cT).2 (both d dT).1 (both d dT).2
    (high c (S.mem_off3.mp (mem_filter.mp (mem_erase.mp (mem_erase.mp cT).2).2).1).1)

#print axioms order_le_twelve
end Graffiti189SingletonCage
