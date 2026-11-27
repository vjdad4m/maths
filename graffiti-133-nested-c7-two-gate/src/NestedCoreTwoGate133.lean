import NestedCoreCritical133
import C7MultiP8Mean133
import C7MultiRadiusFourMean133
namespace Graffiti133NestedCore
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133ExteriorSlack
  Graffiti133MultiWeighted Graffiti133MultiP8
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

private theorem tri_incident {W : Type*} [Fintype W] [DecidableEq W] {J : SimpleGraph W}
    [DecidableRel J.Adj] {x a b : W} (xa : J.Adj x a) (xb : J.Adj x b) (ab : J.Adj a b) :
    1≤triangleIncidence J x :=
  Finset.card_pos.mpr ⟨{x,a,b},Finset.mem_filter.mpr ⟨SimpleGraph.mem_cliqueFinset_iff.mpr
    (SimpleGraph.is3Clique_triple_iff.mpr ⟨xa,xb,ab⟩),by simp⟩⟩

private theorem no_critical_singly_gated [DecidableRel G.Adj]
    (h4 : FourCycleFree G) (K : Finset V) (u v : V) (um : u∈K) (vm : v∈K)
    (seen : ∀ y∉K,G.Adj u y ∨ G.Adj v y)
    (gate : ∀ x∉K,∀ y∈K,G.Adj x y → y=u ∨ y=v)
    {x : V} (off : x∉K) (ux : G.Adj u x) (vx : ¬G.Adj v x)
    (hi : 5+3*triangleIncidence G x≤2*G.degree x) : False := by
  classical
  let N := G.neighborFinset x
  let A := N.filter (fun y=>y∉K ∧ G.Adj u y)
  let B := N.filter (fun y=>y∉K ∧ G.Adj v y)
  have ua (g : V) (gm : g∈K) :
      (N.filter (fun y=>y∉K ∧ G.Adj g y)).card≤1 := by
    apply Finset.card_le_one.mpr
    intro a am b bm
    obtain ⟨ae,_,ga⟩ := Finset.mem_filter.mp am
    obtain ⟨be,_,gb⟩ := Finset.mem_filter.mp bm
    exact h4 x g a b (fun eq=>off (eq ▸ gm))
      ((G.mem_neighborFinset _ _).mp ae) ga ((G.mem_neighborFinset _ _).mp be) gb
  have a1 : A.card≤1 := ua u um
  have b1 : B.card≤1 := ua v vm
  have sub : N⊆insert u (A∪B) := by
    intro y ym
    have e := (G.mem_neighborFinset _ _).mp ym
    by_cases w : y∈K
    · rcases gate x off y w e with eu | ev
      · exact Finset.mem_insert.mpr (Or.inl eu)
      · exact (vx (ev ▸ e.symm)).elim
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_union.mpr ((seen y w).imp
        (fun uy=>Finset.mem_filter.mpr ⟨ym,w,uy⟩)
        (fun vy=>Finset.mem_filter.mpr ⟨ym,w,vy⟩))
  have nc : N.card=G.degree x := G.card_neighborFinset_eq_degree x
  have bnd := Finset.card_le_card sub
  have ub := Finset.card_insert_le (s:=A∪B) (a:=u)
  have uc := Finset.card_union_le A B
  by_cases zero : A.Nonempty
  · obtain ⟨a,am⟩ := zero
    have ax := (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp am).1
    have au := (Finset.mem_filter.mp am).2.2
    have t := tri_incident ux.symm ax au
    omega
  · have emp : A=∅ := Finset.not_nonempty_iff_eq_empty.mp zero
    simp only [emp,Finset.card_empty,Finset.empty_union] at uc ub bnd
    omega

theorem two_gate_attachment_cannot_create_excess (K : Finset V) (u v : V)
    (uv : u≠v) (um : u∈K) (vm : v∈K) (h4 : FourCycleFree G) (base : ¬Pos G K)
    (sees : ∀ x∉K,G.Adj u x ∨ G.Adj v x)
    (gate : ∀ x∉K,∀ y∈K,G.Adj x y → y=u ∨ y=v) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  classical
  by_contra! high
  obtain ⟨T,kt,p,_,large⟩ := minimum_score_subhost K h4 high
  let W := (T : Set V)
  let J := G.induce (T : Set V)
  let L : Finset W := Finset.univ.filter (fun y : W=>y.val∈K)
  let a : W := ⟨u,kt um⟩
  let b : W := ⟨v,kt vm⟩
  have am : a∈L := Finset.mem_filter.mpr ⟨Finset.mem_univ _,um⟩
  have bm : b∈L := Finset.mem_filter.mpr ⟨Finset.mem_univ _,vm⟩
  have off (x : W) : x∉L↔x.val∉K := by simp [L]
  have see (x : W) (offx : x∉L) : J.Adj a x ∨ J.Adj b x := sees _ ((off x).mp offx)
  have ga (x : W) (offx : x∉L) (y : W) (yn : y∈L) (edge : J.Adj x y) : y=a ∨ y=b :=
    (gate _ ((off x).mp offx) _ (Finset.mem_filter.mp yn).2 edge).imp Subtype.ext Subtype.ext
  have both (x : W) (offx : x∉L) : J.Adj a x ∧ J.Adj b x := by
    have hi := large x ((off x).mp offx)
    rcases see x offx with aa | bb
    · by_cases eb : J.Adj b x
      · exact ⟨aa,eb⟩
      · exact (no_critical_singly_gated (restricted_c4 h4 T) L a b am bm see ga offx aa eb hi).elim
    · by_cases ea : J.Adj a x
      · exact ⟨ea,bb⟩
      · exact (no_critical_singly_gated (restricted_c4 h4 T) L b a bm am
          (fun z oz=>(see z oz).symm) (fun z oz y ym e=>(ga z oz y ym e).symm) offx bb ea hi).elim
  have tk : T⊆K := by
    intro x xt
    by_contra nx
    let y : W := ⟨x,xt⟩
    have yo : y∉L := (off y).mpr nx
    have hi := large y nx
    change 5+3*triangleIncidence J y≤2*J.degree y at hi
    have ab := both y yo
    let N := J.neighborFinset y
    have sub : N⊆({a,b} : Finset W) := by
      intro z zm
      have yz := (J.mem_neighborFinset _ _).mp zm
      by_cases zl : z∈L
      · simpa using ga y yo z zl yz
      · have e := both z zl
        exact (yz.ne ((restricted_c4 h4 T) a b y z
          (fun eq=>uv (congrArg Subtype.val eq)) ab.1 ab.2 e.1 e.2)).elim
    have lo := Finset.card_le_card sub
    have up := Finset.card_insert_le (s:=({b}:Finset W)) (a:=a)
    rw [Finset.card_singleton] at up
    have eq : N.card=J.degree y := J.card_neighborFinset_eq_degree y
    omega
  exact base ((Finset.Subset.antisymm tk kt) ▸ p)
/-- The cycle dominates the induced base K; an outer layer may attach to
    either or both of two gates. Non-gate base vertices have no outer edges. -/
theorem C7_base_with_two_gate_outer_layer_mean_four (K : Finset V) (u v : V)
    (um : u∈K) (vm : v∈K) (h4 : FourCycleFree G)
    (H : Hole (G.induce (K : Set V)) 7)
    (h8 : ¬∃ p : Fin 8→(K : Set V),InducedPath (G.induce (K : Set V)) p)
    (dom : ∀ y,Outside H.c y→∃ i,(G.induce (K : Set V)).Adj y (H.c i))
    (sees : ∀ x∉K,G.Adj u x ∨ G.Adj v x)
    (gate : ∀ x∉K,∀ y∈K,G.Adj x y → y=u ∨ y=v) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  have lo := P8_free_dominating_C7_mean_four H (restricted_c4 h4 K) h8 dom
  have base : ¬Pos G K := by
    intro p
    have p' := (pos_iff_local h4 K).mp p
    have card : Fintype.card (K : Set V)=K.card := Fintype.card_coe K
    rw [card] at lo
    exact (Nat.not_lt_of_ge lo) p'
  by_cases eq : u=v
  · subst v
    apply single_gate_attachment_cannot_create_excess K u h4 base
    · exact fun x xm=>(sees x xm).elim id id
    · exact fun x xm y ym e=>(gate x xm y ym e).elim id id
  · exact two_gate_attachment_cannot_create_excess K u v eq um vm h4 base sees gate

theorem radius_four_C7_base_with_two_gate_outer_layer_mean_four (K : Finset V) (u v : V)
    (um : u∈K) (vm : v∈K) (h4 : FourCycleFree G)
    (H : Hole (G.induce (K : Set V)) 7)
    (hc : (G.induce (K : Set V)).Connected) (hr : 4≤radius (G.induce (K : Set V)))
    (h9 : ¬∃ p : Fin 9→(K : Set V),InducedPath (G.induce (K : Set V)) p)
    (dom : ∀ y,Outside H.c y→∃ i,(G.induce (K : Set V)).Adj y (H.c i))
    (sees : ∀ x∉K,G.Adj u x ∨ G.Adj v x)
    (gate : ∀ x∉K,∀ y∈K,G.Adj x y → y=u ∨ y=v) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  have lo := radius_four_dominating_C7_mean_four H hc (restricted_c4 h4 K) h9 dom hr
  have base : ¬Pos G K := by
    intro p
    have p' := (pos_iff_local h4 K).mp p
    have card : Fintype.card (K : Set V)=K.card := Fintype.card_coe K
    rw [card] at lo
    exact (Nat.not_lt_of_ge lo) p'
  by_cases eq : u=v
  · subst v
    apply single_gate_attachment_cannot_create_excess K u h4 base
    · exact fun x xm=>(sees x xm).elim id id
    · exact fun x xm y ym e=>(gate x xm y ym e).elim id id
  · exact two_gate_attachment_cannot_create_excess K u v eq um vm h4 base sees gate

#print axioms radius_four_C7_base_with_two_gate_outer_layer_mean_four
#print axioms two_gate_attachment_cannot_create_excess
#print axioms C7_base_with_two_gate_outer_layer_mean_four
end Graffiti133NestedCore
