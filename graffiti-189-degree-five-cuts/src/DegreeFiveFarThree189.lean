import CutExtraction189
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fin.VecNotation
namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
/-- Three nonintersecting connected shores of deletion of a two vertices. -/
structure FarThreeShores (G : SimpleGraph V) (a b : V) where
  H : Fin 3 → Finset V
  dis : ∀ i j, i≠j → Disjoint (H i) (H j)
  off : ∀ i,a∉H i ∧ b∉H i
  closed : ∀ i,∀ x∈H i,∀ y,G.Adj x y → y=a ∨ y=b ∨ y∈H i
  joined : ∀ i,(G.induce (↑(H i) : Set V)).Connected
  hitA : ∀ i,∃ x∈H i,G.Adj a x
  hitB : ∀ i,∃ x∈H i,G.Adj b x

namespace FarThreeShores
variable {a b : V} (S : FarThreeShores G a b)
def ports (i : Fin 3) := (S.H i).filter (G.Adj a)
noncomputable def innerTwo (i : Fin 3) := (S.H i) ∩ DistanceTwo G a

private theorem d2 {x y z : V} (hc : G.Connected) (xz : x≠z)
    (non : ¬G.Adj x z) (xy : G.Adj x y) (yz : G.Adj y z) :
    z∈DistanceTwo G x := by
  classical
  have h := hc.one_lt_dist_of_ne_of_not_adj xz non
  have le := G.dist_le (Walk.cons xy (Walk.cons yz .nil))
  simp at le
  simp [DistanceTwo, show G.dist x z=2 by omega]

private theorem cross_dis {i j : Fin 3} (ne : i≠j) {x y : V}
    (xi : x∈S.H i) (yj : y∈S.H j) : x≠y ∧ ¬G.Adj x y := by
  have yn : y∉S.H i := fun h=>disjoint_left.mp (S.dis i j ne) h yj
  exact ⟨fun h=>yn (h ▸ xi),fun h=>(S.closed i x xi y h).elim
    (fun e=>(S.off j).1 (e ▸ yj)) (fun p=>p.elim (fun e=>(S.off j).2 (e ▸ yj)) yn)⟩

private theorem across_port_subset (hc : G.Connected) {i j : Fin 3} (ne : i≠j)
    {x : V} (xi : x∈S.ports i) : S.ports j ⊆ DistanceTwo G x := by
  intro y yj
  obtain ⟨xi,cx⟩ := mem_filter.mp xi
  obtain ⟨yj,cy⟩ := mem_filter.mp yj
  have h := cross_dis S ne xi yj
  exact d2 hc h.1 h.2 cx.symm cy

private theorem across_cap (hc : G.Connected) (d : ∀ x, (DistanceTwo G x).card≤5)
    (i j k : Fin 3) (ij : i≠j) (ik : i≠k) (jk : j≠k) :
    (S.ports j).card+(S.ports k).card≤5 := by
  obtain ⟨x,xi,cx⟩ := S.hitA i
  have port : x∈S.ports i := mem_filter.mpr ⟨xi,cx⟩
  have sub := union_subset (across_port_subset S hc ij port) (across_port_subset S hc ik port)
  have n := card_le_card sub
  have djk : Disjoint (S.ports j) (S.ports k) := (S.dis j k jk).mono (filter_subset (G.Adj a) (S.H j)) (filter_subset (G.Adj a) (S.H k))
  rw [card_union_of_disjoint djk] at n
  exact n.trans (d x)

private theorem internal_cap (d : ∀ x, (DistanceTwo G x).card≤5)
    (i j k : Fin 3) (ij : i≠j) (ik : i≠k) (jk : j≠k) :
    (S.innerTwo i).card+(S.innerTwo j).card+(S.innerTwo k).card≤5 := by
  have pair (p q : Fin 3) (pq : p≠q) : Disjoint (S.innerTwo p) (S.innerTwo q) :=
    (S.dis _ _ pq).mono inter_subset_left inter_subset_left
  have sub (p : Fin 3) : S.innerTwo p ⊆ DistanceTwo G a := inter_subset_right
  have cnt := card_le_card (union_subset (union_subset (sub i) (sub j)) (sub k))
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨pair i k ik,pair j k jk⟩),
    card_union_of_disjoint (pair i j ij)] at cnt
  exact cnt.trans (d a)

private theorem high_port_cost (hc : G.Connected) (far : 3≤G.dist a b) {i : Fin 3} {x : V}
    (xp : x∈S.ports i) (high : 5≤G.degree x) :
    5≤(S.ports i).card+(S.innerTwo i).card := by
  classical
  obtain ⟨xi,ax⟩ := mem_filter.mp xp
  have inc : G.neighborFinset x ⊆ insert a (((S.ports i).erase x) ∪ S.innerTwo i) := by
    intro y hy
    have xy := (mem_neighborFinset G x y).mp hy
    rcases S.closed i x xi y xy with rfl|rfl|yi
    · simp
    · have q := G.dist_le (Walk.cons ax (Walk.cons xy .nil))
      simp at q
      omega
    apply mem_insert_of_mem
    by_cases cy : G.Adj a y
    · exact mem_union_left _ (mem_erase.mpr ⟨xy.ne.symm,mem_filter.mpr ⟨yi,cy⟩⟩)
    exact mem_union_right _ (mem_inter.mpr ⟨yi,d2 hc (fun e=>(S.off i).1 (e.symm ▸ yi)) cy ax xy⟩)
  have deg := card_le_card inc
  rw [card_neighborFinset_eq_degree] at deg
  have c1 := card_insert_le a ((S.ports i).erase x ∪ S.innerTwo i)
  have c2 := card_union_le ((S.ports i).erase x) (S.innerTwo i)
  rw [card_erase_of_mem xp] at c2
  have pos := card_pos.mpr ⟨x,xp⟩
  omega


private theorem inner_positive (hc : G.Connected) (far : 3≤G.dist a b) (i : Fin 3) :
    1≤(S.innerTwo i).card := by
  classical
  obtain ⟨x,xi,ax⟩ := S.hitA i
  obtain ⟨y,yi,by'⟩ := S.hitB i
  apply Nat.succ_le_of_lt
  by_contra bad
  let W : Set V := ↑(S.H i)
  obtain ⟨p⟩ := (S.joined i).preconnected (⟨x,xi⟩ : W) ⟨y,yi⟩
  have prop {u v : W} (q : (G.induce W).Walk u v) : G.Adj a u.val → G.Adj a v.val := by
    induction q with
    | nil => exact id
    | @cons u w v uw q ih =>
      intro au
      apply ih
      apply Classical.byContradiction
      intro no
      have wh : w.val∈S.H i := w.property
      have ne : a≠w.val := fun e=>(S.off i).1 ((congrArg (fun v=>v∈S.H i) e.symm).mp wh)
      have two := d2 hc ne no au (show G.Adj u.val w.val from uw)
      have cnt : 0<(S.innerTwo i).card := card_pos.mpr ⟨_,mem_inter.mpr ⟨wh,two⟩⟩
      omega
  have ay := prop p ax
  have h := G.dist_le (Walk.cons ay (Walk.cons by'.symm .nil))
  simp at h
  omega

private theorem no_low_shore (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x, (EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (i j k : Fin 3) (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (low : ¬ ∃ x∈S.ports i, 5≤G.degree x) : False := by
  classical
  have d (x : V) := distanceTwo_le_of_even 5 x (even x)
  obtain ⟨x,xi,ax⟩ := S.hitA i
  have xp : x∈S.ports i := mem_filter.mpr ⟨xi,ax⟩
  have lx : ¬5≤G.degree x := fun h=>low ⟨x,xp,h⟩
  have hport (l : Fin 3) (il : i≠l) : 5≤(S.ports l).card+(S.innerTwo l).card := by
    obtain ⟨y,yl,ay⟩ := S.hitA l
    have ne := (cross_dis S il xi yl).1
    exact high_port_cost S hc far (mem_filter.mpr ⟨yl,ay⟩) ((degree x y ne).resolve_left lx)
  have jh := hport j ij
  have kh := hport k ik
  have ac := across_cap S hc d i j k ij ik jk
  have dc := internal_cap S d i j k ij ik jk
  have pos := inner_positive S hc far i
  omega

include S in
theorem impossible (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x, (EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v) : False := by
  classical
  by_cases low : ∃ i, ¬∃ x∈S.ports i, 5≤G.degree x
  · obtain ⟨i,il⟩ := low
    fin_cases i
    · exact no_low_shore S hc far even degree 0 1 2 (by decide) (by decide) (by decide) il
    · exact no_low_shore S hc far even degree 1 0 2 (by decide) (by decide) (by decide) il
    · exact no_low_shore S hc far even degree 2 0 1 (by decide) (by decide) (by decide) il
  push_neg at low
  have high (i : Fin 3) : 5≤(S.ports i).card+(S.innerTwo i).card := by
    obtain ⟨x,px,dx⟩ := low i
    exact high_port_cost S hc far px dx
  have d (x : V) := distanceTwo_le_of_even 5 x (even x)
  have c0 := across_cap S hc d 0 1 2 (by decide) (by decide) (by decide)
  have c1 := across_cap S hc d 1 0 2 (by decide) (by decide) (by decide)
  have c2 := across_cap S hc d 2 0 1 (by decide) (by decide) (by decide)
  have cd := internal_cap S d 0 1 2 (by decide) (by decide) (by decide)
  have h0 := high 0
  have h1 := high 1
  have h2 := high 2
  omega

#print axioms impossible
end FarThreeShores
end Graffiti189LongestPath.CrossSaturation
