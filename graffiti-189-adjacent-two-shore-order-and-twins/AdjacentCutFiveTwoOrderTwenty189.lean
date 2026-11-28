import AdjacentCutFiveTwoTwinGeometry189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore mem_shore shore_off shore_disjoint shore_closed shore_hit_a
  shore_hit_b from AdjacentCutFiveActual189
open private positive_cap foreign_pos_even from AdjacentCutFiveComponents189
open private mem_positive cross_dist_of_equal odd_equal d2
  odd_dist_to_even_next from AdjacentCutFiveBound189
open private complete_from_no_local_even from AdjacentCutFiveTwoTwinGeometry189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem actual_two_shores (two : Nat.card (Cmp G a b) = 2) :
    ∃ C D : Cmp G a b, C≠D ∧ ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D := by
  classical
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change Nat.card J.ConnectedComponent = 2 at two
  rw [Nat.card_eq_fintype_card] at two
  let F := Fintype.equivFinOfCardEq two
  let C := F.symm (0 : Fin 2)
  let D := F.symm (1 : Fin 2)
  have cd : C ≠ D := fun h => (by decide : (0 : Fin 2) ≠ 1) (F.symm.injective h)
  have cover {z : V} (za : z≠a) (zb : z≠b) : z∈Shore C ∨ z∈Shore D := by
    let Z := J.connectedComponentMk ⟨z,za,zb⟩
    have zz : F Z = 0 ∨ F Z = 1 := by
      exact (by decide : ∀ i : Fin 2, i=0 ∨ i=1) (F Z)
    rcases zz with h|h
    · exact .inl (mem_shore.mpr ⟨⟨za,zb⟩,F.injective (by simpa [C] using h)⟩)
    · exact .inr (mem_shore.mpr ⟨⟨za,zb⟩,F.injective (by simpa [D] using h)⟩)
  exact ⟨C,D,cd,fun {z} => cover (z:=z)⟩

private theorem order_twenty_of_asym
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (two : Nat.card (Cmp G a b) = 2)
    {z : V} (zb : z ≠ b) (az : G.Adj a z) (bz : ¬ G.Adj b z) :
    Fintype.card V ≤ 20 := by
  classical
  obtain ⟨C,D,cd,cover⟩ := actual_two_shores two
  have dis := shore_disjoint cd
  obtain ⟨x,xc,ax⟩ := shore_hit_a ab.ne conn C
  obtain ⟨y,yd,ay⟩ := shore_hit_a ab.ne conn D
  let L := (Shore C).filter (fun v => v∈PositiveEven G y)
  let R := (Shore D).filter (fun v => v∈PositiveEven G x)
  let A := PositiveEven G a
  let B := PositiveEven G b
  let U := A ∪ B
  let W := L ∪ R
  have sub : (univ.erase a |>.erase b : Finset V) ⊆ U ∪ W := by
    intro v hv
    have vb := (mem_erase.mp hv).1
    have va := (mem_erase.mp (mem_erase.mp hv).2).1
    by_cases ea : Even (G.dist a v)
    · exact mem_union.mpr (.inl (mem_union.mpr (.inl (mem_positive.mpr ⟨va,ea⟩))))
    by_cases eb : Even (G.dist b v)
    · exact mem_union.mpr (.inl (mem_union.mpr (.inr (mem_positive.mpr ⟨vb,eb⟩))))
    have same := odd_equal hc ab ea eb
    rcases cover va vb with vc|vd
    · have no : v∉Shore D := fun h=>disjoint_left.mp dis vc h
      have dk := cross_dist_of_equal (Shore D) hc yd no (shore_closed D) (.inl ay) same
      have e := mem_positive.mpr ⟨(show v≠y from fun h=>no (by simpa only [h] using yd)),odd_dist_to_even_next dk ea⟩
      exact mem_union.mpr (.inr (mem_union.mpr (.inl (mem_filter.mpr ⟨vc,e⟩))))
    · have no : v∉Shore C := fun h=>disjoint_left.mp dis h vd
      have dk := cross_dist_of_equal (Shore C) hc xc no (shore_closed C) (.inl ax) same
      have e := mem_positive.mpr ⟨(show v≠x from fun h=>no (by simpa only [h] using xc)),odd_dist_to_even_next dk ea⟩
      exact mem_union.mpr (.inr (mem_union.mpr (.inr (mem_filter.mpr ⟨vd,e⟩))))
  have za : z≠a := az.ne.symm
  have zB : z∈B := by
    have hh := d2 hc zb.symm bz ab.symm az
    exact mem_positive.mpr ⟨zb,by simp [(mem_filter.mp hh).2]⟩
  have zW : z∈W := by
    rcases cover za zb with zc|zd
    · exact mem_union.mpr (.inl (mem_filter.mpr ⟨zc,foreign_pos_even hc cd.symm yd zc ay az⟩))
    · exact mem_union.mpr (.inr (mem_filter.mpr ⟨zd,foreign_pos_even hc cd xc zd ax az⟩))
  have zU : z∈U := mem_union.mpr (.inr zB)
  have unionErase : U∪W = U∪(W.erase z) := by
    ext u
    by_cases h : u=z
    · subst u; simp [zU]
    · simp [h]
  have rem_size := card_le_card sub
  rw [card_erase_of_mem (by simp [ab.ne.symm]),card_erase_of_mem (mem_univ _),card_univ,
    unionErase] at rem_size
  have ucard := card_union_le A B
  have wcard := card_union_le L R
  have uv := card_union_le U (W.erase z)
  rw [card_erase_of_mem zW] at uv
  have acard := positive_cap a even
  have bcard := positive_cap b even
  have lcard : L.card ≤ 5 :=
    (card_le_card (show L ⊆ PositiveEven G y from fun _ h=>(mem_filter.mp h).2)).trans
      (positive_cap y even)
  have rcard : R.card ≤ 5 :=
    (card_le_card (show R ⊆ PositiveEven G x from fun _ h=>(mem_filter.mp h).2)).trans
      (positive_cap x even)
  by_cases small : Fintype.card V ≤ 20
  · exact small
  have big : 21 ≤ Fintype.card V := Nat.lt_of_not_ge small
  exfalso
  have l5 : L.card = 5 := by
    change U.card ≤ A.card + B.card at ucard
    change W.card ≤ L.card + R.card at wcard
    change A.card ≤ 5 at acard
    change B.card ≤ 5 at bcard
    omega
  have r5 : R.card = 5 := by
    change U.card ≤ A.card + B.card at ucard
    change W.card ≤ L.card + R.card at wcard
    change A.card ≤ 5 at acard
    change B.card ≤ 5 at bcard
    omega
  have ban {K P : Cmp G a b} (kp : K≠P)
      {v : V} (vc : v∈Shore K) (quota : ((Shore P).filter (fun u=>u∈PositiveEven G v)).card = 5) :
      ∀ u∈Shore K,u∉PositiveEven G v := by
    intro u uc ue
    let X := (Shore P).filter (fun w=>w∈PositiveEven G v)
    have un : u∉X := fun m => disjoint_left.mp (shore_disjoint kp) uc (mem_filter.mp m).1
    have s : insert u X ⊆ PositiveEven G v := by
      intro t tm
      rcases mem_insert.mp tm with rfl|tm
      · exact ue
      · exact (mem_filter.mp tm).2
    have c := card_le_card s
    rw [card_insert_of_not_mem un] at c
    change X.card = 5 at quota
    have q := positive_cap v even
    omega
  have ux := complete_from_no_local_even hc xc (ban cd xc r5)
  have uy := complete_from_no_local_even hc yd (ban cd.symm yd l5)
  let Cport := (Shore C).filter (G.Adj a)
  let Dport := (Shore D).filter (G.Adj a)
  have cp := card_le_card (show Cport ⊆ PositiveEven G y from
    fun _ q=>foreign_pos_even hc cd.symm yd (mem_filter.mp q).1 ay (mem_filter.mp q).2)
  have dp := card_le_card (show Dport ⊆ PositiveEven G x from
    fun _ q=>foreign_pos_even hc cd xc (mem_filter.mp q).1 ax (mem_filter.mp q).2)
  have rest : (univ.erase a |>.erase b : Finset V) ⊆ A ∪ (Cport∪Dport) := by
    intro v hv
    have vb := (mem_erase.mp hv).1
    have va := (mem_erase.mp (mem_erase.mp hv).2).1
    by_cases av : G.Adj a v
    · rcases cover va vb with vc|vd
      · exact mem_union.mpr (.inr (mem_union.mpr (.inl (mem_filter.mpr ⟨vc,av⟩))))
      · exact mem_union.mpr (.inr (mem_union.mpr (.inr (mem_filter.mpr ⟨vd,av⟩))))
    have w : ∃ c, G.Adj a c ∧ G.Adj c v := by
      rcases cover va vb with vc|vd
      · exact ⟨x,ax,(ux v vc).resolve_left (fun h=>av (h.symm ▸ ax))⟩
      · exact ⟨y,ay,(uy v vd).resolve_left (fun h=>av (h.symm ▸ ay))⟩
    obtain ⟨c,ac,cv⟩ := w
    have dd := d2 hc va.symm av ac cv
    exact mem_union.mpr (.inl (mem_positive.mpr ⟨va,by simp [(mem_filter.mp dd).2]⟩))
  have rem := card_le_card rest
  rw [card_erase_of_mem (by simp [ab.ne.symm]),card_erase_of_mem (mem_univ _),card_univ] at rem
  have p12 := card_union_le Cport Dport
  have p123 := card_union_le A (Cport ∪ Dport)
  have e1 := positive_cap x even
  have e2 := positive_cap y even
  change A.card ≤ 5 at acard
  omega


theorem order_le_twenty_of_actual_adjacent_two_shores
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (two : Nat.card (Cmp G a b) = 2) :
    Fintype.card V ≤ 20 := by
  classical
  by_cases twin : ∀ z, z ≠ a → z ≠ b → (G.Adj a z ↔ G.Adj b z)
  · exact (order_le_seventeen_of_actual_adjacent_twin_cut hc ab even conn (two.symm ▸ Nat.le_refl 2) twin).trans (by decide)
  push_neg at twin
  obtain ⟨z,za,zb,h⟩ := twin
  by_cases az : G.Adj a z
  · exact order_twenty_of_asym hc ab even conn two zb az ((h.resolve_right (fun q=>q.1 az)).2)
  have bz : G.Adj b z := (h.resolve_left (fun q=>az q.1)).2
  have sw : {z : V | z≠a ∧ z≠b} = {z : V | z≠b ∧ z≠a} := Set.ext (fun _=>and_comm)
  have twos : Nat.card (Cmp G b a) = 2 := by
    change Nat.card (G.induce {z : V | z≠b ∧ z≠a}).ConnectedComponent = 2
    rw [←sw]
    exact two
  exact order_twenty_of_asym hc ab.symm even conn twos za bz az

#print axioms order_le_twenty_of_actual_adjacent_two_shores
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
