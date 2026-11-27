import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteAvoid3OneWire
open SquareCap (FactorOn HasFactor IsTile)
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem dvd_sum {T : Finset (Finset V)} (f : Finset V→ℕ)
    (d : ∀ A∈T,3∣f A) : 3∣∑ A∈T,f A := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [sum_insert ha]
      exact Nat.dvd_add (d a (mem_insert_self _ _))
        (ih (fun b hb=>d b (mem_insert_of_mem hb)))

/-- If one shore has order divisible by three and there is at most one
wire across the cut, no P3-factor can use the wire. A tile crossing
the cut must use both its endpoints, so at most one tile crosses;
it would contribute one or two vertices to a multiple-of-three shore. -/
theorem outside_factors_of_one_wire (H : SimpleGraph V)
    (B : Finset V) (m : 3∣B.card) {l r : V}
    (seam : ∀ a : V,a∉B → ∀ b∈B,H.Adj a b → a=l∧b=r)
    (f : HasFactor H) : FactorOn H (univ \ B) := by
  classical
  obtain ⟨P,tiles,apart,cover⟩ := f
  have crossing (A : Finset V) (a : A∈P) (p : ∃ z∈A,z∈B) (q : ∃ z∈A,z∉B) : l∈A∧r∈A := by
    obtain ⟨u,ua,ub⟩ := q
    obtain ⟨v,va,vb⟩ := p
    obtain ⟨_,c,ca,inc⟩ := tiles A a
    by_cases cB : c∈B
    · have uc : u≠c := fun h=>ub (h.symm ▸ cB)
      obtain ⟨rfl,rfl⟩ := seam u ub c cB (inc u ua uc).symm
      exact ⟨ua,ca⟩
    · have vc : v≠c := fun h=>cB (h ▸ vb)
      obtain ⟨rfl,rfl⟩ := seam c cB v vb (inc v va vc)
      exact ⟨ca,va⟩
  have overlap : P.biUnion (fun A=>A∩B)=B := by
    ext z
    constructor
    · intro h
      obtain ⟨A,_,hz⟩ := mem_biUnion.mp h
      exact (mem_inter.mp hz).2
    · intro hz
      have s : z∈P.biUnion id := cover.symm ▸ mem_univ z
      obtain ⟨A,a,za⟩ := mem_biUnion.mp s
      exact mem_biUnion.mpr ⟨A,a,mem_inter.mpr ⟨za,hz⟩⟩
  have pairwise : (↑P : Set (Finset V)).PairwiseDisjoint (fun A=>A∩B) := by
    intro A a J j ne
    apply Disjoint.mono
      (show A∩B ⊆ A from inter_subset_left)
      (show J∩B ⊆ J from inter_subset_left)
    exact apart A a J j ne
  have count : B.card=∑ A∈P,(A∩B).card := by
    exact (congrArg Finset.card overlap).symm.trans (Finset.card_biUnion pairwise)
  have noncross (A : Finset V) (a : A∈P) : (A∩B).card=0 ∨ (A∩B).card=3 := by
    by_cases empty : A∩B=∅
    · exact Or.inl (card_eq_zero.mpr empty)
    · by_cases full : A∩B=A
      · exact Or.inr ((congrArg Finset.card full).trans (tiles A a).1)
      · exfalso
        have pr : ∃ z∈A,z∈B := by
          obtain ⟨p,hp⟩ := nonempty_iff_ne_empty.mpr empty
          exact ⟨p,(mem_inter.mp hp).1,(mem_inter.mp hp).2⟩
        have cr : ∃ z∈A,z∉B := by
          apply Classical.byContradiction
          intro no
          push_neg at no
          apply full
          ext z
          simp only [mem_inter]
          exact ⟨And.left,fun h=>⟨h,no z h⟩⟩
        have ports := crossing A a pr cr
        have dv : 3 ∣ ∑ J∈P.erase A,(J∩B).card := by
          apply dvd_sum
          intro J jm
          obtain ⟨ja,jp⟩ := mem_erase.mp jm
          by_cases n : J∩B=∅
          · rw [n,card_empty]; omega
          · by_cases y : J∩B=J
            · rw [y,(tiles J jp).1]
            · exfalso
              have pp : ∃ z∈J,z∈B := by
                obtain ⟨q,hq⟩ := nonempty_iff_ne_empty.mpr n
                exact ⟨q,(mem_inter.mp hq).1,(mem_inter.mp hq).2⟩
              have qq : ∃ z∈J,z∉B := by
                apply Classical.byContradiction
                intro no
                push_neg at no
                apply y
                ext z
                simp only [mem_inter]
                exact ⟨And.left,fun h=>⟨h,no z h⟩⟩
              exact disjoint_left.mp (apart A a J jp ja.symm) ports.1 (crossing J jp pp qq).1
        obtain ⟨z,za,zb⟩ := cr
        have greater : 0<(A∩B).card := card_pos.mpr (nonempty_iff_ne_empty.mpr empty)
        have less : (A∩B).card≤2 := by
          have sub : A∩B⊆A.erase z :=
            fun b m=>mem_erase.mpr ⟨fun e=>zb (e ▸ (mem_inter.mp m).2),(mem_inter.mp m).1⟩
          have k := card_le_card sub
          rw [card_erase_of_mem za,(tiles A a).1] at k
          exact k
        have dc := Finset.sum_erase_add P (fun J=>(J∩B).card) a
        change (∑ J∈P.erase A,(J∩B).card)+(A∩B).card = ∑ J∈P,(J∩B).card at dc
        rw [←dc] at count
        omega
  let Q := P.filter (fun A=>Disjoint A B)
  refine ⟨Q,fun A a=>tiles A (mem_filter.mp a).1,
    fun A a J j n=>apart A (mem_filter.mp a).1 J (mem_filter.mp j).1 n,?_⟩
  ext z
  constructor
  · intro h
    obtain ⟨A,a,za⟩ := mem_biUnion.mp h
    exact mem_sdiff.mpr ⟨mem_univ _,fun zb=>disjoint_left.mp (mem_filter.mp a).2 za zb⟩
  · intro h
    have zb := (mem_sdiff.mp h).2
    have hz : z∈P.biUnion id := cover.symm ▸ mem_univ z
    obtain ⟨A,a,za⟩ := mem_biUnion.mp hz
    change z∈A at za
    have hd : Disjoint A B := by
      apply disjoint_left.mpr
      intro t ta tb
      rcases noncross A a with zero|all
      · have m : t∈A∩B := mem_inter.mpr ⟨ta,tb⟩
        simp [card_eq_zero.mp zero] at m
      · have sub : A∩B ⊆ A.erase z :=
          fun b m=>mem_erase.mpr ⟨fun e=>zb (e ▸ (mem_inter.mp m).2),(mem_inter.mp m).1⟩
        have h := card_le_card sub
        rw [all,card_erase_of_mem za,(tiles A a).1] at h
        omega
    exact mem_biUnion.mpr ⟨A,mem_filter.mpr ⟨a,hd⟩,za⟩

#print axioms outside_factors_of_one_wire
end KelmansCactus.AtomicBridge.RemoteAvoid3OneWire
