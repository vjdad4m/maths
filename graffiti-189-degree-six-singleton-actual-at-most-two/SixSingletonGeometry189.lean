import SixSingletonCommon189
import AdjacentCutFiveFourteenLabel189
import AdjacentCutFiveSixteenSingletonDepth189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore mem_shore shore_off shore_closed shore_disjoint shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private Cmp DeletionConnected aPorts bPorts two_local_counts from SixCutFar189
open private Vis vis_sub from AdjacentCutFiveComponents189
open private singleton_distance from SixCutLowSingleton189
open private positive_even_cap from TwoCutOrderCenters189
open private in_positive_even_of_dist_two from TwoCutDistanceCaps189
open private depth_predecessor_on_shore from AdjacentCutFiveSixteenSingletonDepth189
open private d2 from CrossSaturation189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (depth shore_swapCut)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private noncomputable def Dark (C : Cmp G a b) : Finset V := Shore C\Vis C
private noncomputable def Common (C : Cmp G a b) : Finset V := aPorts C∩bPorts C
private noncomputable def strictA (C : Cmp G a b) : Finset V :=
  (Dark C).filter (fun z=>G.dist a z<G.dist b z)
private noncomputable def strictB (C : Cmp G a b) : Finset V :=
  (Dark C).filter (fun z=>G.dist b z<G.dist a z)
private noncomputable def bal (C : Cmp G a b) : Finset V :=
  (Dark C).filter (fun z=>G.dist a z=G.dist b z)

private theorem port_union_vis (C : Cmp G a b) : aPorts C∪bPorts C=Vis C := by
  ext z
  simp [aPorts,bPorts,Vis,and_or_left]

private theorem singleton_neighborhood_exact
    {S : Cmp G a b} {s : V} (sS : Shore S={s}) (as' : G.Adj a s) (bs' : G.Adj b s) :
    G.neighborFinset s={a,b} := by
  apply Subset.antisymm
  · intro z h
    have e := (mem_neighborFinset _ _ _).mp h
    rcases shore_closed S s (by simp [sS]) z e with p|p|p
    · simp [p]
    · simp [p]
    have same : z=s := by simpa only [sS,mem_singleton] using p
    exact (e.ne same.symm).elim
  exact insert_subset ((mem_neighborFinset _ _ _).mpr as'.symm)
    (singleton_subset_iff.mpr ((mem_neighborFinset _ _ _).mpr bs'.symm))

private theorem a_port_lower_singleton_dist_two {S D : Cmp G a b} (_sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    {s : V} (sS : Shore S={s}) (aa : 6≤G.degree a) (ab : ¬G.Adj a b) :
    5≤(aPorts D).card := by
  have sub : G.neighborFinset a⊆insert s (aPorts D) := by
    intro z h
    have az := (mem_neighborFinset _ _ _).mp h
    have nz : z≠b := fun e=>ab (e ▸ az)
    rcases cover az.ne.symm nz with sz|dz
    · exact mem_insert.mpr (.inl (by simpa only [sS,mem_singleton] using sz))
    exact mem_insert_of_mem (mem_filter.mpr ⟨dz,az⟩)
  have c := card_le_card sub
  rw [card_neighborFinset_eq_degree] at c
  have k := card_insert_le s (aPorts D)
  omega

private theorem visible_subset_singleton_even {S D : Cmp G a b} (sd : S≠D)
    (hc : G.Connected) {s : V} (ss : s∈Shore S) (as' : G.Adj a s) (bs' : G.Adj b s) :
    Vis D⊆PositiveEven G s := by
  intro z zp
  have ⟨zd,port⟩ := mem_filter.mp zp
  have zs : z∉Shore S := fun h=>disjoint_left.mp (shore_disjoint sd) h zd
  have ne : s≠z := fun h=>zs (h ▸ ss)
  have sz : ¬G.Adj s z := by
    intro e
    rcases shore_closed S s ss z e with p|p|p
    · exact (shore_off D).1 (p ▸ zd)
    · exact (shore_off D).2 (p ▸ zd)
    exact zs p
  rcases port with az|bz
  · exact in_positive_even_of_dist_two (mem_filter.mp (d2 hc ne sz as'.symm az)).2
  exact in_positive_even_of_dist_two (mem_filter.mp (d2 hc ne sz bs'.symm bz)).2

private theorem nonadjacent_twin_dist_eq (hc : G.Connected)
    (tw : ∀ w,G.Adj a w↔G.Adj b w) {z : V} (za : z≠a) (zb : z≠b) :
    G.dist a z=G.dist b z := by
  have go {u v z : V} (no : u≠z) (h : ∀ x,G.Adj u x → G.Adj v x) : G.dist v z≤G.dist u z := by
    obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist u z
    cases p with
    | nil => exact (no rfl).elim
    | cons e p =>
      have q := G.dist_le (Walk.cons (h _ e) p)
      simp only [Walk.length_cons] at pl q
      omega
  exact le_antisymm (go zb.symm (fun w=> (tw w).mpr)) (go za.symm (fun w=>(tw w).mp))

private theorem vis_six_of_nonadjacent_singleton (hc : G.Connected)
    (even : ∀ z,(EvenFrom G z).card≤7) (_ab : a≠b) (non : ¬G.Adj a b)
    {S D : Cmp G a b} (sd : S≠D) (d13 : (Shore D).card=13)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    {s : V} (sS : Shore S={s}) (as' : G.Adj a s) (bs' : G.Adj b s)
    (aa : 5≤(aPorts D).card) (bb : 5≤(bPorts D).card) :
    (Vis D).card=6 := by
  classical
  have ss : s∈Shore S := by simp [sS]
  have sub := visible_subset_singleton_even sd hc ss as' bs'
  have cap := positive_even_cap (d:=6) (even s)
  have t := card_le_card sub
  have av : aPorts D⊆Vis D := by rw [←port_union_vis]; exact subset_union_left
  have bv : bPorts D⊆Vis D := by rw [←port_union_vis]; exact subset_union_right
  have al := card_le_card av
  have bl := card_le_card bv
  by_contra h
  have v5 : (Vis D).card=5 := by omega
  have ae : aPorts D=Vis D := eq_of_subset_of_card_le av (by omega)
  have be : bPorts D=Vis D := eq_of_subset_of_card_le bv (by omega)
  have eqP : aPorts D=bPorts D := ae.trans be.symm
  have tw (z : V) : G.Adj a z↔G.Adj b z := by
    by_cases za : z=a
    · subst z
      simp [G.loopless,show ¬G.Adj b a from fun h=>non h.symm]
    by_cases zb : z=b
    · subst z
      simp [G.loopless,non]
    rcases cover za zb with zs|zd
    · have e : z=s := by simpa only [sS,mem_singleton] using zs
      simp [e,as',bs']
    have eq : z∈aPorts D↔z∈bPorts D := by rw [eqP]
    simpa only [aPorts,bPorts,mem_filter,zd,true_and] using eq
  have all : Shore D⊆PositiveEven G a∪PositiveEven G s := by
    intro z zd
    have zs : z≠s := fun e=>disjoint_left.mp (shore_disjoint sd) ss (e ▸ zd)
    have ⟨za,zb⟩ := (mem_shore.mp zd).choose
    have eq := nonadjacent_twin_dist_eq hc tw za zb
    by_cases ev : Even (G.dist a z)
    · exact mem_union_left _ (mem_erase.mpr ⟨za,mem_filter.mpr ⟨mem_univ _,ev⟩⟩)
    have d := singleton_distance sS hc as' bs' zs
    rw [←eq,min_self] at d
    have sev : Even (G.dist s z) := by simp only [Nat.even_iff] at ev ⊢; omega
    exact mem_union_right _ (mem_erase.mpr ⟨zs,mem_filter.mpr ⟨mem_univ _,sev⟩⟩)
  have c := card_le_card all
  have u := card_union_le (PositiveEven G a) (PositiveEven G s)
  have p := positive_even_cap (d:=6) (even a)
  omega

private theorem all_dark_depth_two_of_visible_six (hc : G.Connected)
    (even : ∀ z,(EvenFrom G z).card≤7) {S D : Cmp G a b} (sd : S≠D)
    {s : V} (sS : Shore S={s}) (as' : G.Adj a s) (bs' : G.Adj b s)
    (v6 : (Vis D).card=6) :
    ∀ z∈Dark D,depth G a b z=2 := by
  classical
  have ss : s∈Shore S := by simp [sS]
  have sub := visible_subset_singleton_even sd hc ss as' bs'
  have eq : Vis D=PositiveEven G s := eq_of_subset_of_card_le sub (by
    rw [v6]; exact positive_even_cap (d:=6) (even s))
  have cutEven {z : V} (zd : z∈Dark D) : Even (depth G a b z) := by
    obtain ⟨dm,dn⟩ := mem_sdiff.mp zd
    have zs : z≠s := fun h=>disjoint_left.mp (shore_disjoint sd) ss (h ▸ dm)
    have ne : z∉PositiveEven G s := by rwa [←eq]
    have dist := singleton_distance sS hc as' bs' zs
    by_contra odd
    have sev : Even (G.dist s z) := by
      rw [dist]
      change ¬Even (min (G.dist a z) (G.dist b z)) at odd
      simp only [Nat.even_iff] at odd ⊢
      omega
    exact ne (mem_erase.mpr ⟨zs,mem_filter.mpr ⟨mem_univ _,sev⟩⟩)
  have first {z : V} (zd : z∈Shore D) (h : 2≤depth G a b z) : z∈Dark D := by
    refine mem_sdiff.mpr ⟨zd,?_⟩
    intro p
    rcases (mem_filter.mp p).2 with az|bz
    · have d := dist_eq_one_iff_adj.mpr az
      have e := min_le_left (G.dist a z) (G.dist b z)
      change 2≤min _ _ at h
      omega
    have d := dist_eq_one_iff_adj.mpr bz
    have e := min_le_right (G.dist a z) (G.dist b z)
    change 2≤min _ _ at h
    omega
  intro z mz
  have ⟨zd,zn⟩ := mem_sdiff.mp mz
  have ⟨za,zb⟩ := (mem_shore.mp zd).choose
  have pa := hc.one_lt_dist_of_ne_of_not_adj za.symm (fun az=>zn (mem_filter.mpr ⟨zd,.inl az⟩))
  have pb := hc.one_lt_dist_of_ne_of_not_adj zb.symm (fun bz=>zn (mem_filter.mpr ⟨zd,.inr bz⟩))
  have lo : 2≤depth G a b z := by change 2≤min _ _; omega
  have evenZ := cutEven mz
  by_contra high
  have hi : 4≤depth G a b z := by simp only [Nat.even_iff] at evenZ; omega
  obtain ⟨w,wd,_,hw⟩ := depth_predecessor_on_shore hc zd lo
  have evenW := cutEven (first wd (by omega))
  simp only [Nat.even_iff] at evenZ evenW
  omega

#print axioms vis_six_of_nonadjacent_singleton
#print axioms all_dark_depth_two_of_visible_six
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
