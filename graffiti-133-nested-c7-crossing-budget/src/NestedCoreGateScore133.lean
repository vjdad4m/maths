import NestedCoreCritical133
namespace Graffiti133NestedCore
open SimpleGraph Finset Graffiti133 Graffiti133ExteriorSlack Graffiti133ExactTriangleCharge
  Graffiti133MultiWeighted
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

theorem peeling_preserves_score (K T : Finset V) (kt : K⊆T)
    (h4 : FourCycleFree G)
    (peel : ∀ U : Finset V, K⊆U → U⊆T → U≠K →
      ∃ x : (U : Set V), x.val∉K ∧
        2*(G.induce (U : Set V)).degree x≤4+3*triangleIncidence (G.induce (U : Set V)) x) :
    (∑ v : (T : Set V),localIndependence (G.induce (T : Set V)) v)+4*K.card≤
      (∑ v : (K : Set V),localIndependence (G.induce (K : Set V)) v)+4*T.card := by
  let E (U : Finset V) := (G.induce (U : Set V)).edgeFinset.card
  let C (U : Finset V) := triangleCount (G.induce (U : Set V))
  have score (n : Nat) (U : Finset V) (sz : U.card=n) (ku : K⊆U) (ut : U⊆T) :
      2*E U+4*K.card+3*C K≤2*E K+4*U.card+3*C U := by
    induction n using Nat.strong_induction_on generalizing U with
    | h n ih =>
      by_cases eq : U=K
      · subst U
        exact le_rfl
      obtain ⟨x,off,lo⟩ := peel U ku ut eq
      let W := U.erase x.val
      have ww : W.card+1=U.card := Finset.card_erase_add_one x.property
      have ku' : K⊆W := fun y ym=>Finset.mem_erase.mpr ⟨fun eq=>off (eq ▸ ym),ku ym⟩
      have wu : W⊆U := Finset.erase_subset _ _
      have wn : W.card<n := by omega
      have prev := ih W.card wn W rfl ku' (wu.trans ut)
      have q := actual_induced_delta (G:=G) U x
      have aux {e0 e1 eK n0 n1 nK c0 c1 cK d tx : Nat}
          (order : n0+1=n1) (edges : e0+d=e1) (tris : c0+tx=c1)
          (little : 2*d≤4+3*tx) (prev : 2*e0+4*nK+3*cK≤2*eK+4*n0+3*c0) :
          2*e1+4*nK+3*cK≤2*eK+4*n1+3*c1 := by omega
      exact aux ww q.1 q.2 lo prev
  have bound := score T.card T rfl kt Subset.rfl
  have ktc := sum_degree_eq_local_add_triangles (restricted_c4 h4 K)
  have ttc := sum_degree_eq_local_add_triangles (restricted_c4 h4 T)
  have aux {e0 e1 c0 c1 n0 n1 s0 s1 : Nat} (eq0 : s0+3*c0=2*e0)
      (eq1 : s1+3*c1=2*e1) (bd : 2*e1+4*n0+3*c0≤2*e0+4*n1+3*c1) :
      s1+4*n0≤s0+4*n1 := by omega
  exact aux ktc ttc bound

theorem peeling_preserves_ambient_score (K : Finset V) (h4 : FourCycleFree G)
    (peel : ∀ U : Finset V, K⊆U → U≠K →
      ∃ x : (U : Set V), x.val∉K ∧
        2*(G.induce (U : Set V)).degree x≤4+3*triangleIncidence (G.induce (U : Set V)) x) :
    (∑ v : V,localIndependence G v)+4*K.card≤
      (∑ v : (K : Set V),localIndependence (G.induce (K : Set V)) v)+4*Fintype.card V := by
  let T := (Finset.univ : Finset V)
  have b := peeling_preserves_score K T (Finset.subset_univ _) h4 (fun U ku _ ne=>peel U ku ne)
  have hc := sum_degree_eq_local_add_triangles (restricted_c4 h4 T)
  have hg := sum_degree_eq_local_add_triangles h4
  have iso := full_induce_iso (G:=G)
  change (∑ v : (T : Set V),localIndependence (G.induce (T : Set V)) v)+
    3*triangleCount (G.induce (T : Set V))=2*(G.induce (T : Set V)).edgeFinset.card at hc
  rw [iso.card_edgeFinset_eq,triangle_count_iso iso] at hc
  have sm : (∑ v : (T : Set V),localIndependence (G.induce (T : Set V)) v)=
      ∑ v : V,localIndependence G v := Nat.add_right_cancel (hc.trans hg.symm)
  rw [sm,show T.card=Fintype.card V from Finset.card_univ] at b
  exact b

private theorem tri_incident {W : Type*} [Fintype W] [DecidableEq W] {J : SimpleGraph W}
    [DecidableRel J.Adj] {x a b : W} (xa : J.Adj x a) (xb : J.Adj x b) (ab : J.Adj a b) :
    1≤triangleIncidence J x :=
  Finset.card_pos.mpr ⟨{x,a,b},Finset.mem_filter.mpr ⟨SimpleGraph.mem_cliqueFinset_iff.mpr
    (SimpleGraph.is3Clique_triple_iff.mpr ⟨xa,xb,ab⟩),by simp⟩⟩

private theorem singly_gated_deletion_bound [DecidableRel G.Adj]
    (h4 : FourCycleFree G) (K : Finset V) (u v : V) (um : u∈K) (vm : v∈K)
    (seen : ∀ y∉K,G.Adj u y ∨ G.Adj v y)
    (gate : ∀ x∉K,∀ y∈K,G.Adj x y → y=u ∨ y=v)
    {x : V} (off : x∉K) (ux : G.Adj u x) (vx : ¬G.Adj v x)
    : 2*G.degree x≤4+3*triangleIncidence G x := by
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

theorem two_gate_peeling (K : Finset V) (u v : V)
    (uv : u≠v) (um : u∈K) (vm : v∈K) (h4 : FourCycleFree G)
    (sees : ∀ x∉K,G.Adj u x ∨ G.Adj v x)
    (gate : ∀ x∉K,∀ y∈K,G.Adj x y → y=u ∨ y=v)
    (T : Finset V) (kt : K⊆T) (ne : T≠K) :
    ∃ x : (T : Set V), x.val∉K ∧
        2*(G.induce (T : Set V)).degree x≤4+3*triangleIncidence (G.induce (T : Set V)) x := by
  classical
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
  have j4 : FourCycleFree J := restricted_c4 h4 T
  by_cases one : ∃ x : W, x∉L ∧ ((J.Adj a x ∧ ¬J.Adj b x) ∨ (J.Adj b x ∧ ¬J.Adj a x))
  · obtain ⟨x,xo,h⟩ := one
    refine ⟨x,(off x).mp xo,?_⟩
    rcases h with ⟨yes,no⟩ | ⟨yes,no⟩
    · exact singly_gated_deletion_bound j4 L a b am bm see ga xo yes no
    · exact singly_gated_deletion_bound j4 L b a bm am
        (fun z oz=>(see z oz).symm) (fun z oz y ym e=>(ga z oz y ym e).symm) xo yes no
  · have both (x : W) (xo : x∉L) : J.Adj a x ∧ J.Adj b x := by
      rcases see x xo with aa | bb
      · by_cases eb : J.Adj b x
        · exact ⟨aa,eb⟩
        · exact (one ⟨x,xo,Or.inl ⟨aa,eb⟩⟩).elim
      · by_cases ea : J.Adj a x
        · exact ⟨ea,bb⟩
        · exact (one ⟨x,xo,Or.inr ⟨bb,ea⟩⟩).elim
    have tk : ¬T⊆K := fun tk=>ne (Finset.Subset.antisymm tk kt)
    obtain ⟨x,xt,xk⟩ := Finset.not_subset.mp tk
    let y : W := ⟨x,xt⟩
    have yo : y∉L := (off y).mpr xk
    refine ⟨y,xk,?_⟩
    change 2*J.degree y≤4+3*triangleIncidence J y
    have ab := both y yo
    let N := J.neighborFinset y
    have sub : N⊆({a,b} : Finset W) := by
      intro z zm
      have yz := (J.mem_neighborFinset _ _).mp zm
      by_cases zl : z∈L
      · simpa using ga y yo z zl yz
      · have e := both z zl
        exact (yz.ne (j4 a b y z
          (fun eq=>uv (congrArg Subtype.val eq)) ab.1 ab.2 e.1 e.2)).elim
    have lo := Finset.card_le_card sub
    have up := Finset.card_insert_le (s:=({b}:Finset W)) (a:=a)
    rw [Finset.card_singleton] at up
    have eq : N.card=J.degree y := J.card_neighborFinset_eq_degree y
    omega

theorem two_gate_preserves_score (K : Finset V) (u v : V)
    (uv : u≠v) (um : u∈K) (vm : v∈K) (h4 : FourCycleFree G)
    (sees : ∀ x∉K,G.Adj u x ∨ G.Adj v x)
    (gate : ∀ x∉K,∀ y∈K,G.Adj x y → y=u ∨ y=v) :
    (∑ w : V,localIndependence G w)+4*K.card≤
      (∑ w : (K : Set V),localIndependence (G.induce (K : Set V)) w)+4*Fintype.card V :=
  peeling_preserves_ambient_score K h4 (two_gate_peeling K u v uv um vm h4 sees gate)

private theorem subgraph_c4 {J : SimpleGraph V} (JG : J≤G) (h4 : FourCycleFree G) :
    FourCycleFree J :=
  fun a b x y ne ax bx ay byy=> h4 a b x y ne (JG ax) (JG bx) (JG ay) (JG byy)

theorem score_difference_le_twice_added_edges (J : SimpleGraph V) (JG : J≤G)
    (h4 : FourCycleFree G) :
    (∑ w : V,localIndependence G w) ≤
      (∑ w : V,localIndependence J w)+2*(G.edgeFinset \ J.edgeFinset).card := by
  classical
  have e := Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono JG)
  have t := Finset.card_le_card (SimpleGraph.cliqueFinset_mono (G:=J) G (n:=3) JG)
  change triangleCount J≤triangleCount G at t
  have gj := sum_degree_eq_local_add_triangles (subgraph_c4 JG h4)
  have gg := sum_degree_eq_local_add_triangles h4
  have aux {ej eg tj tg lj lg k : Nat} (es : k+ej=eg) (tr : tj≤tg)
      (j : lj+3*tj=2*ej) (g : lg+3*tg=2*eg) : lg≤lj+2*k := by omega
  exact aux e t gj gg

def gateTrim (G : SimpleGraph V) (K : Finset V) (u v : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ((x∈K ↔ y∈K) ∨ x=u ∨ x=v ∨ y=u ∨ y=v)
  symm := by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    rcases h.2 with e|e|e|e|e
    · exact Or.inl e.symm
    · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr e)))
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
  loopless x h := G.loopless x h.1

theorem gate_trim_crossing_slack (K : Finset V) (u v : V)
    (uv : u≠v) (um : u∈K) (vm : v∈K) (h4 : FourCycleFree G)
    (sees : ∀ x∉K,G.Adj u x ∨ G.Adj v x)
    (slack : (∑ w : (K : Set V),localIndependence (G.induce (K : Set V)) w)+
      2*(G.edgeFinset \ (gateTrim G K u v).edgeFinset).card≤4*K.card) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  let J := gateTrim G K u v
  have le : J≤G := fun _ _ h=>h.1
  have same : J.induce (K : Set V)=G.induce (K : Set V) := by
    ext x y
    refine ⟨fun h=>h.1,fun h=>⟨h,Or.inl ?_⟩⟩
    exact iff_of_true x.property y.property
  have seesJ (x : V) (xo : x∉K) : J.Adj u x ∨ J.Adj v x := by
    rcases sees x xo with e|e
    · exact Or.inl ⟨e,Or.inr (Or.inl rfl)⟩
    · exact Or.inr ⟨e,Or.inr (Or.inr (Or.inl rfl))⟩
  have gateJ (x : V) (xo : x∉K) (y : V) (ym : y∈K) (e : J.Adj x y) : y=u ∨ y=v := by
    rcases e.2 with h|h|h|h|h
    · exact (xo (h.mpr ym)).elim
    · exact (xo (h ▸ um)).elim
    · exact (xo (h ▸ vm)).elim
    · exact Or.inl h
    · exact Or.inr h
  have preserve := two_gate_preserves_score (G:=J) K u v uv um vm (subgraph_c4 le h4) seesJ gateJ
  rw [same] at preserve
  have restore := score_difference_le_twice_added_edges J le h4
  change (∑ w : (K : Set V),localIndependence (G.induce (K : Set V)) w)+
    2*(G.edgeFinset \ J.edgeFinset).card≤4*K.card at slack
  have aux {g j b e k n : Nat} (r : g≤j+2*e) (p : j+4*k≤b+4*n)
      (s : b+2*e≤4*k) : g≤4*n := by omega
  exact aux restore preserve slack

#print axioms score_difference_le_twice_added_edges
#print axioms gate_trim_crossing_slack
#print axioms two_gate_peeling
#print axioms two_gate_preserves_score
#print axioms peeling_preserves_score
#print axioms peeling_preserves_ambient_score
end Graffiti133NestedCore
