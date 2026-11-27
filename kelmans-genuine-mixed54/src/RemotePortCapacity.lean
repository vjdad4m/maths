import SquareCapFactor
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace KelmansCactus.AtomicBridge.RemotePortCapacity
open SimpleGraph Finset
open scoped BigOperators
open SquareCap (HasFactor)
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

/-- Every vertex in a piece can leave it only through a port. The pieces
 need not be connected, and neither need they exhaust the non-port vertices. -/
def Behind (G : SimpleGraph V) (ports pieces : Finset V) : Prop :=
  ∀ x∈pieces,∀ y,G.Adj x y → y∈pieces ∨ y∈ports

/-- Each sealed piece must export at least its order modulo three in vertices
 assigned to port-touching tiles, and every port supplies at most two such
 non-port slots. This is a necessary (not sufficient) factor condition. -/
theorem residue_capacity (G : SimpleGraph V) (ports : Finset V) (grp : I→Finset V)
    (noPort : ∀ i,Disjoint (grp i) ports)
    (apart : ∀ i j,i≠j → Disjoint (grp i) (grp j))
    (sealed : ∀ i,Behind G ports (grp i))
    (factor : HasFactor G) : (∑ i,(grp i).card % 3) ≤ 2*ports.card := by
  classical
  obtain ⟨P,tiles,disj,cover⟩:=factor
  let X := P.filter (fun T=>¬Disjoint T ports)
  let B := X.biUnion id
  have x_mem {T : Finset V} : T∈X ↔ T∈P ∧ ¬Disjoint T ports := by simp [X]
  have port_inside : ports⊆B := by
    intro v hp
    have whole : v∈P.biUnion id := by rw [cover]; exact mem_univ _
    obtain ⟨T,tP,tv⟩:=mem_biUnion.mp whole
    exact mem_biUnion.mpr ⟨T,x_mem.mpr ⟨tP,fun e=>disjoint_left.mp e tv hp⟩,tv⟩
  have count_tiles (Q : Finset (Finset V)) (sub : Q⊆P) :
      (Q.biUnion id).card=3*Q.card := by
    rw [card_biUnion]
    · have hu :
        (∑ T∈Q,(id T).card) = ∑ _T∈Q,(3:ℕ) :=
        sum_congr rfl (fun T h=>(tiles T (sub h)).1)
      rw [hu]
      simp [Nat.mul_comm]
    · intro A hA D hD ne
      exact disj A (sub hA) D (sub hD) ne
  have p_cover : X.biUnion (fun T=>T∩ports)=ports := by
    ext v
    constructor
    · intro h
      obtain ⟨T,_,hv⟩:=mem_biUnion.mp h
      exact (mem_inter.mp hv).2
    · intro h
      obtain ⟨T,tX,hv⟩:=mem_biUnion.mp (port_inside h)
      exact mem_biUnion.mpr ⟨T,tX,mem_inter.mpr ⟨hv,h⟩⟩
  have x_card : X.card≤ports.card := by
    have c : (X.biUnion (fun T=>T∩ports)).card=∑ T∈X,(T∩ports).card := by
      apply card_biUnion
      intro A hA D hD ne
      exact (disj A (x_mem.mp hA).1 D (x_mem.mp hD).1 ne).mono inter_subset_left inter_subset_left
    rw [p_cover] at c
    rw [c]
    calc
      X.card = ∑ _T∈X,(1:ℕ) := by simp
      _ ≤ ∑ T∈X,(T∩ports).card := by
        apply sum_le_sum
        intro T h
        have ne : (T∩ports).Nonempty := by
          by_contra! empty
          have dj : Disjoint T ports := by
            apply disjoint_left.mpr
            intro v vt vp
            exact empty ⟨v,mem_inter.mpr ⟨vt,vp⟩⟩
          exact (x_mem.mp h).2 dj
        exact card_pos.mpr ne
  have b_count : B.card=3*X.card := count_tiles X (fun _ h=>(x_mem.mp h).1)
  have lim : (B \ ports).card≤2*ports.card := by
    have e := card_sdiff_add_card_eq_card port_inside
    omega
  have lower (i : I) : (grp i).card % 3 ≤ ((grp i)∩B).card := by
    let Y := P.filter (fun T=>Disjoint T ports ∧ ¬Disjoint T (grp i))
    have y_mem {T : Finset V} : T∈Y ↔ T∈P ∧ Disjoint T ports ∧ ¬Disjoint T (grp i) := by simp [Y]
    have contained (T : Finset V) (h : T∈Y) : T ⊆ grp i := by
      obtain ⟨tP,avoid,meet⟩:=y_mem.mp h
      obtain ⟨_,c,cT,star⟩:=tiles T tP
      have w : ∃ v∈T,v∈grp i := by
        by_cases ex : ∃ v∈T,v∈grp i
        · exact ex
        · exact (meet (disjoint_left.mpr (fun v vt vg=>ex ⟨v,vt,vg⟩))).elim
      obtain ⟨v,vT,vg⟩:=w
      have cg : c∈grp i := by
        by_cases e : v=c
        · exact e ▸ vg
        · exact (sealed i v vg c (star v vT e).symm).resolve_right (disjoint_left.mp avoid cT)
      intro y yt
      by_cases e : y=c
      · exact e.symm ▸ cg
      · exact (sealed i c cg y (star y yt e)).resolve_right (disjoint_left.mp avoid yt)
    have peel : Y.biUnion id = grp i \ B := by
      ext v
      constructor
      · intro h
        obtain ⟨T,tY,vT⟩:=mem_biUnion.mp h
        refine mem_sdiff.mpr ⟨contained T tY vT,?_⟩
        intro vb
        obtain ⟨U,uX,vU⟩:=mem_biUnion.mp vb
        have ne : T≠U := by
          intro e
          exact (x_mem.mp uX).2 (e ▸ (y_mem.mp tY).2.1)
        exact disjoint_left.mp (disj T (y_mem.mp tY).1 U (x_mem.mp uX).1 ne) vT vU
      · intro h
        obtain ⟨g,nb⟩:=mem_sdiff.mp h
        have whole : v∈P.biUnion id := by rw [cover]; exact mem_univ _
        obtain ⟨T,tP,vT⟩:=mem_biUnion.mp whole
        have avoid : Disjoint T ports := by
          by_cases yes : Disjoint T ports
          · exact yes
          · exact (nb (mem_biUnion.mpr ⟨T,x_mem.mpr ⟨tP,yes⟩,vT⟩)).elim
        exact mem_biUnion.mpr ⟨T,y_mem.mpr ⟨tP,avoid,fun d=>disjoint_left.mp d vT g⟩,vT⟩
    have part := card_sdiff_add_card_inter (grp i) B
    have yy := count_tiles Y (fun _ h=>(y_mem.mp h).1)
    rw [peel] at yy
    omega
  have summed : (∑ i,((grp i)∩B).card) ≤ (B\ports).card := by
    let U := univ.biUnion (fun i=>grp i∩B)
    have c : U.card=∑ i,((grp i)∩B).card := by
      apply card_biUnion
      intro i _ j _ n
      exact (apart i j n).mono inter_subset_left inter_subset_left
    rw [←c]
    apply card_le_card
    intro v vm
    obtain ⟨i,_,vi⟩:=mem_biUnion.mp vm
    obtain ⟨vg,vb⟩:=mem_inter.mp vi
    exact mem_sdiff.mpr ⟨vb,disjoint_left.mp (noPort i) vg⟩
  exact (sum_le_sum (fun i _=>lower i)).trans (summed.trans lim)

#print axioms residue_capacity
end KelmansCactus.AtomicBridge.RemotePortCapacity
