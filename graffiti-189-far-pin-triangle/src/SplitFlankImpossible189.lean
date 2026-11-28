import FlankShore189
import ExactStarOpposite189
import TruncatedHall189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath Graffiti189LongestPath.Rigidity
open Graffiti189LongestPath.OneSlack Graffiti189LongestPath.SingleStar Graffiti189LongestPath.FlankShore
open Graffiti189LongestPath.ForeignPorts Graffiti189LongestPath.TruncatedHall
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.mem_omittedStar Graffiti189LongestPath.Rigidity.mem_external from Rigidity189
open private Graffiti189LongestPath.OneSlack.cardinal_flankVertices
  Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem
  Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
set_option warningAsError true
set_option maxHeartbeats 2000000
namespace Graffiti189LongestPath.SplitFlankImpossible
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Two large complementary shores are impossible: the full distance-two
budgets of the pin and a high flank charge each other in opposite directions. -/
theorem no_split_flanks (hc : G.Connected) (k : Nat) (hk : 4≤k)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (one : (Pins p x).card=1) (far : (Shell G x 4).Nonempty) (xd : k+2≤G.degree x)
    {i : Nat} (hi : i∈Pins p x)
    (C D : Finset V) (sep : Disjoint C D)
    (ca : Disjoint C (OmittedStar p x)) (cb : Disjoint C (External G (OmittedStar p x)))
    (da : Disjoint D (OmittedStar p x)) (db : Disjoint D (External G (OmittedStar p x)))
    (cc : ∀ u∈C,∀ v∉C,G.Adj u v → v∈External G (OmittedStar p x))
    (dc : ∀ u∈D,∀ v∉D,G.Adj u v → v∈External G (OmittedStar p x))
    (dg : ∀ g∈D, ∃ u∈D, G.Adj g u) (dn : D.Nonempty) (dlarge : k+2<2*D.card)
    {f : V} (fc : f∈C) (ft : G.Adj (p.getVert i) f) (fd : k+2≤G.degree f) :
    False := by
  classical
  let d := k+2
  let t := p.getVert i
  let A := OmittedStar p x
  let B := External G A
  let F := FlankVertices p x
  let L := A.filter (G.Adj t)
  let T := A.filter (fun z => ¬G.Adj t z)
  let S := B.filter (G.Adj f)
  have cap₂ (z : V) : (DistanceTwo G z).card≤d := distanceTwo_le_of_even d z (cap z)
  have fb : f∉B := fun h => disjoint_left.mp cb fc h
  have fa : f∉A := fun h => disjoint_left.mp ca fc h
  have fD : f∉D := fun h => disjoint_left.mp sep fc h
  have bt : t∈B := Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary hx
    (mem_image.mpr ⟨i,hi,rfl⟩)
  have ta : t∉A := (Graffiti189LongestPath.Rigidity.mem_external.mp bt).1
  have tx : G.Adj t x := (Graffiti189LongestPath.pin_data hi).2.symm
  have sing : Pins p x={i} := by
    apply (eq_of_subset_of_card_le _ _).symm
    · intro z hz
      exact (mem_singleton.mp hz).symm ▸ hi
    · rw [card_singleton,one]
  have flim : F.card≤2 := by
    change (FlankVertices p x).card≤2
    rw [Graffiti189LongestPath.OneSlack.cardinal_flankVertices hp]
    simp only [FlankIndices,sing,image_singleton]
    exact (card_union_le _ _).trans (by simp)
  have hC := pins_meet_complement_in_flanks hc k cap conn hp hx one far hi C ⟨f,fc⟩ ca cb cc
  have hD := pins_meet_complement_in_flanks hc k cap conn hp hx one far hi D dn da db dc
  obtain ⟨g,hg⟩ := hD.1
  have gd := (mem_filter.mp hg).1
  have gt := (mem_filter.mp hg).2
  have fF : f∈F := (mem_inter.mp (hC.2 ▸ mem_filter.mpr ⟨fc,ft⟩)).2
  have gF : g∈F := (mem_inter.mp (hD.2 ▸ hg)).2
  have unique {z : V} (zc : z∈C) (tz : G.Adj t z) : z=f := by
    have zz : z∈F := (mem_inter.mp (hC.2 ▸ mem_filter.mpr ⟨zc,tz⟩)).2
    apply Classical.byContradiction
    intro zf
    have zg : z≠g := fun e => disjoint_left.mp sep zc (e.symm ▸ gd)
    have fg : f≠g := fun e => disjoint_left.mp sep fc (e.symm ▸ gd)
    have c := two_lt_card.mpr ⟨z,zz,f,fF,g,gF,zf,zg,fg⟩
    omega
  have uniqueD {z : V} (zd : z∈D) (tz : G.Adj t z) : z=g := by
    have zz : z∈F := (mem_inter.mp (hD.2 ▸ mem_filter.mpr ⟨zd,tz⟩)).2
    apply Classical.byContradiction
    intro zg
    have zf : z≠f := fun e => disjoint_left.mp sep (e ▸ fc) zd
    have gf : g≠f := fun e => disjoint_left.mp sep (e ▸ fc) gd
    have c := two_lt_card.mpr ⟨z,zz,g,gF,f,fF,zg,zf,gf⟩
    omega
  have xa : x∈A := Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have xl : d≤A.card := by
    have sub : G.neighborFinset x ⊆ PinVertices p x ∪ A.erase x := by
      intro z hz
      have e := (G.mem_neighborFinset x z).mp hz
      by_cases pos : z∈p.support
      · obtain ⟨j,hj,eq⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp hx pos e
        exact mem_union.mpr (Or.inl (mem_image.mpr ⟨j,hj,eq⟩))
      · exact mem_union.mpr (Or.inr (mem_erase.mpr ⟨e.ne.symm,
          Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨pos,Or.inr e⟩⟩))
    have s := card_le_card sub
    rw [G.card_neighborFinset_eq_degree] at s
    have c := card_union_le (PinVertices p x) (A.erase x)
    rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp,one,card_erase_of_mem xa] at c
    dsimp [d]
    omega
  have coverT : T⊆DistanceTwo G t := by
    intro z hz
    obtain ⟨za,ntz⟩ := mem_filter.mp hz
    rcases (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp za).2 with e|e
    · exact (ntz (e.symm ▸ tx)).elim
    · exact Graffiti189LongestPath.mem_distanceTwo.mpr
        (Graffiti189LongestPath.dist_two hc (fun h => ta (h.symm ▸ za)) ntz tx e)
  let N := C.filter (G.Adj f)
  have coverN : N⊆DistanceTwo G t := by
    intro z hz
    obtain ⟨zc,ed⟩ := mem_filter.mp hz
    have no : ¬G.Adj t z := fun e => ed.ne (unique zc e).symm
    have ne : t≠z := fun e => disjoint_left.mp cb zc (e ▸ bt)
    exact Graffiti189LongestPath.mem_distanceTwo.mpr (Graffiti189LongestPath.dist_two hc ne no ft ed)
  have dis : Disjoint T N := disjoint_left.mpr (fun _ ht hn =>
    disjoint_left.mp ca (mem_filter.mp hn).1 (mem_filter.mp ht).1)
  have c := card_le_card (union_subset coverT coverN)
  rw [card_union_of_disjoint dis] at c
  let P := D.filter (G.Adj g)
  have coverP : P⊆DistanceTwo G t := by
    intro z hz
    obtain ⟨zd,ed⟩ := mem_filter.mp hz
    have no : ¬G.Adj t z := fun e => ed.ne (uniqueD zd e).symm
    have ne : t≠z := fun e => disjoint_left.mp db zd (e ▸ bt)
    exact Graffiti189LongestPath.mem_distanceTwo.mpr (Graffiti189LongestPath.dist_two hc ne no gt ed)
  have disP : Disjoint (T∪N) P := disjoint_left.mpr (by
    intro u h hu
    exact (mem_union.mp h).elim
      (fun e => disjoint_left.mp da (mem_filter.mp hu).1 (mem_filter.mp e).1)
      (fun e => disjoint_left.mp sep (mem_filter.mp e).1 (mem_filter.mp hu).1))
  have all := card_le_card (union_subset (union_subset coverT coverN) coverP)
  rw [card_union_of_disjoint disP,card_union_of_disjoint dis] at all
  have pp : 0<P.card := by
    obtain ⟨u,ud,e⟩ := dg g gd
    exact card_pos.mpr ⟨u,mem_filter.mpr ⟨ud,e⟩⟩
  have up := cap₂ t
  have neighbors : G.neighborFinset f⊆N∪S := by
    intro z hz
    have ed := (G.mem_neighborFinset f z).mp hz
    by_cases h : z∈C
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨h,ed⟩))
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨cc f fc z h ed,ed⟩))
  have nc := card_le_card neighbors
  rw [G.card_neighborFinset_eq_degree] at nc
  have ncu := card_union_le N S
  have ts : T.card+P.card≤S.card := by dsimp [d] at up; omega
  have sB := singleton_star_budget hc k conn hp hx one (cap x)
  have bk : B.card=k := (sB.2.2.2.2.1 far).1
  let Q := shoreNeighbors G D S
  have hall := truncated_hall k D B S conn db bk (filter_subset _ _) fD fb dc
  change min D.card S.card≤Q.card at hall
  have coverQ : Q⊆DistanceTwo G f := by
    intro z hz
    obtain ⟨zd,v,vs,vz⟩ := mem_filter.mp hz
    have ne : f≠z := fun e => fD (e.symm ▸ zd)
    have no : ¬G.Adj f z := fun e => fb (dc z zd f fD e.symm)
    exact Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.dist_two hc ne no (mem_filter.mp vs).2 vz)
  have coverL : L⊆DistanceTwo G f := by
    intro z hz
    obtain ⟨za,tz⟩ := mem_filter.mp hz
    have ne : f≠z := fun e => fa (e.symm ▸ za)
    have no : ¬G.Adj f z := fun e => fb
      (Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨fa,z,za,e.symm⟩)
    exact Graffiti189LongestPath.mem_distanceTwo.mpr (Graffiti189LongestPath.dist_two hc ne no ft.symm tz)
  have lq : Disjoint L Q := disjoint_left.mpr (fun _ hl hq =>
    disjoint_left.mp da (mem_filter.mp hq).1 (mem_filter.mp hl).1)
  have use := card_le_card (union_subset coverL coverQ)
  rw [card_union_of_disjoint lq] at use
  have use' := cap₂ f
  have union : A⊆L∪T := by
    intro z hz
    by_cases h : G.Adj t z
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hz,h⟩))
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hz,h⟩))
  have size := (card_le_card union).trans (card_union_le L T)
  have half : 2*S.card≤d := by
    apply Nat.le_of_not_gt
    intro many
    have ab : Disjoint A B := disjoint_left.mpr (fun _ h b =>
      (Graffiti189LongestPath.Rigidity.mem_external.mp b).1 h)
    have cl : ∀ z∈A,∀ y∉A,G.Adj z y → y∈B := fun z hz y hy e =>
      Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨hy,z,hz,e⟩
    have ct := across_two_shores_budget hc d k A D B conn ab db da.symm bk
      (by dsimp [d] at xl; omega) fa fD fb cl dc (cap f) many
    change D.card+S.card≤d at ct
    dsimp [d] at ct many
    omega
  rw [min_eq_right (by dsimp [d] at half; omega : S.card≤D.card)] at hall
  omega
#print axioms no_split_flanks

/-- A far singleton with two complementary components is traceable.
In a counterexample its complementary shore must therefore be connected. -/
theorem traceable_of_split_complement (hc : G.Connected) (k : Nat) (hk : 4≤k)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (one : (Pins p x).card=1) (far : (Shell G x 4).Nonempty) (xd : k+2≤G.degree x)
    {i : Nat} (hi : i∈Pins p x)
    (C D : Finset V) (sep : Disjoint C D)
    (ca : Disjoint C (OmittedStar p x)) (cb : Disjoint C (External G (OmittedStar p x)))
    (da : Disjoint D (OmittedStar p x)) (db : Disjoint D (External G (OmittedStar p x)))
    (cc : ∀ u∈C,∀ v∉C,G.Adj u v → v∈External G (OmittedStar p x))
    (dc : ∀ u∈D,∀ v∉D,G.Adj u v → v∈External G (OmittedStar p x))
    (ccon : (G.induce (C : Set V)).Connected)
    (dcon : (G.induce (D : Set V)).Connected) :
    ∃ (u v : V) (q : G.Walk u v), q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  apply Classical.byContradiction
  intro fail
  obtain ⟨u⟩ := ccon.nonempty
  obtain ⟨v⟩ := dcon.nonempty
  have cn : C.Nonempty := ⟨u.val,u.property⟩
  have dn : D.Nonempty := ⟨v.val,v.property⟩
  have sB := singleton_star_budget hc k conn hp hx one (cap x)
  have bk : (External G (OmittedStar p x)).card=k := (sB.2.2.2.2.1 far).1
  have act : 0<(Pins p x).card := card_pos.mpr ⟨i,hi⟩
  have few : (Pins p x).card≤2 := by omega
  have large (T : Finset V) (tn : T.Nonempty) (ta : Disjoint T (OmittedStar p x))
      (tb : Disjoint T (External G (OmittedStar p x)))
      (tc : ∀ u∈T,∀ v∉T,G.Adj u v → v∈External G (OmittedStar p x)) :
      k+3<2*T.card := by
    apply Nat.lt_of_not_ge
    intro sm
    exact fail (Graffiti189LongestPath.ExactStarOpposite.traceable_of_small_opposite hc k hk conn cap
      deg hp hx xd act few bk T tn sm ta tb tc)
  have cl := large C cn ca cb cc
  have dl := large D dn da db dc
  have internal (T : Finset V) (tc : (G.induce (T : Set V)).Connected) (tl : k+3<2*T.card)
      (w : V) (hw : w∈T) : ∃ z∈T,G.Adj w z := by
    have hs : 1<T.card := by omega
    obtain ⟨z,hz,ne⟩ := exists_ne_of_one_lt_card hs w
    let A : ↥(T : Set V) := ⟨w,hw⟩
    let B : ↥(T : Set V) := ⟨z,hz⟩
    obtain ⟨q⟩ := tc A B
    have step {a b : ↥(T : Set V)} (p : (G.induce (T : Set V)).Walk a b) (n : a≠b) :
        ∃ z : ↥(T : Set V), (G.induce (T : Set V)).Adj a z := by
      cases p with
      | nil => exact (n rfl).elim
      | @cons a y b e q => exact ⟨y,e⟩
    have neq : A≠B := fun e => ne (congrArg Subtype.val e).symm
    obtain ⟨y,e⟩ := step q neq
    exact ⟨y.val,y.property,e⟩
  obtain ⟨f,hf⟩ := (pins_meet_complement_in_flanks hc k cap conn hp hx one far hi C cn ca cb cc).1
  obtain ⟨g,hg⟩ := (pins_meet_complement_in_flanks hc k cap conn hp hx one far hi D dn da db dc).1
  obtain ⟨fc,ft⟩ := mem_filter.mp hf
  obtain ⟨gd,gt⟩ := mem_filter.mp hg
  have ne : f≠g := fun e => disjoint_left.mp sep fc (e.symm ▸ gd)
  rcases deg f g ne with fd|gd'
  · exact no_split_flanks hc k hk cap conn hp hx one far xd hi C D sep ca cb da db cc dc
      (internal D dcon dl) dn (by omega) fc ft fd
  · exact no_split_flanks hc k hk cap conn hp hx one far xd hi D C sep.symm da db ca cb dc cc
      (internal C ccon cl) cn (by omega) gd gt gd'
#print axioms traceable_of_split_complement
end Graffiti189LongestPath.SplitFlankImpossible
