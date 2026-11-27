import C7MultiScoreHelpers133

namespace Graffiti133NestedCore
open SimpleGraph Finset Graffiti133 Graffiti133ExteriorSlack Graffiti133ExactTriangleCharge
  Graffiti133MultiWeighted
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

def Pos (G : SimpleGraph V) (T : Finset V) : Prop :=
  4*T.card+3*triangleCount (G.induce (T : Set V)) < 2*(G.induce (T : Set V)).edgeFinset.card

theorem pos_iff_local (h4 : FourCycleFree G) (T : Finset V) :
    Pos G T ↔ 4*T.card < ∑ v : (T : Set V),localIndependence (G.induce (T : Set V)) v := by
  unfold Pos
  have ch := sum_degree_eq_local_add_triangles (restricted_c4 h4 T)
  have aux {n c e l : Nat} (eq : l+3*c=2*e) : 4*n+3*c<2*e ↔ 4*n<l := by omega
  exact aux ch

theorem minimum_score_subhost (C : Finset V)
    (h4 : FourCycleFree G) (excess : 4*Fintype.card V < ∑ v : V,localIndependence G v) :
    ∃ T : Finset V, C⊆T ∧ Pos G T ∧
      (∀ S⊆T, C⊆S → S.card<T.card → ¬Pos G S) ∧
      (∀ x : (T : Set V), x.val∉C →
        5+3*triangleIncidence (G.induce (T : Set V)) x ≤ 2*(G.induce (T : Set V)).degree x) := by
  classical
  let Q := (Finset.univ : Finset (Finset V)).filter (fun T=>C⊆T ∧ Pos G T)
  have qmem (T : Finset V) : T∈Q ↔ C⊆T ∧ Pos G T := by simp [Q]
  have full : Pos G Finset.univ := by
    unfold Pos
    rw [Finset.card_univ,(full_induce_iso (G:=G)).card_edgeFinset_eq,
      triangle_count_iso (full_induce_iso (G:=G))]
    have ch := sum_degree_eq_local_add_triangles h4
    have aux {l n e c : Nat} (ch : l+3*c=2*e) (high : 4*n<l) : 4*n+3*c<2*e := by omega
    exact aux ch excess
  obtain ⟨T,hm,mn⟩ := Finset.exists_min_image Q Finset.card
    ⟨Finset.univ,(qmem _).mpr ⟨Finset.subset_univ _,full⟩⟩
  have ct := (qmem T).mp hm
  have noSmaller (S : Finset V) (_ : S⊆T) (cs : C⊆S) (lt : S.card<T.card) : ¬Pos G S :=
    fun hp=>(Nat.not_le_of_gt lt) (mn S ((qmem S).mpr ⟨cs,hp⟩))
  refine ⟨T,ct.1,ct.2,noSmaller,?_⟩
  intro x nx
  let S := T.erase x.val
  have su : S⊆T := Finset.erase_subset _ _
  have cs : C⊆S := fun y yc=>Finset.mem_erase.mpr ⟨fun eq=>nx (eq ▸ yc),ct.1 yc⟩
  have sz : S.card+1=T.card := Finset.card_erase_add_one x.property
  have npos := Nat.le_of_not_gt (noSmaller S su cs (by omega))
  have yes := ct.2
  unfold Pos at yes
  have q := actual_induced_delta (G:=G) T x
  have aux {s t e0 e1 c0 c1 d c : Nat} (sz : s+1=t)
      (npos : 2*e0≤4*s+3*c0) (yes : 4*t+3*c1<2*e1)
      (e : e0+d=e1) (k : c0+c=c1) : 5+3*c≤2*d := by omega
  exact aux sz npos yes q.1 q.2

theorem retained_core_dominates (C T : Finset V) (ct : C⊆T)
    (dom : ∀ x : V, x∈C ∨ ∃ c∈C,G.Adj x c) :
    ∀ x : (T : Set V), x.val∈C ∨ ∃ c : (T : Set V), c.val∈C ∧
      (G.induce (T : Set V)).Adj x c := by
  intro x
  rcases dom x.val with inside | ⟨c,hc,e⟩
  · exact Or.inl inside
  · exact Or.inr ⟨⟨c,ct hc⟩,hc,e⟩

theorem retained_no_path {k : Nat} (h : ¬∃ p : Fin k→V,InducedPath G p) (T : Finset V) :
    ¬∃ p : Fin k→(T : Set V),InducedPath (G.induce (T : Set V)) p := by
  rintro ⟨p,hp⟩
  exact h ⟨Subtype.val ∘ p,Subtype.val_injective.comp hp.1,hp.2⟩

theorem shared_root_remote_unique (h4 : FourCycleFree G) (R : Finset V) (u : V)
    (sees : ∀ r∈R,G.Adj u r) {x a b : V} (ne : x≠u)
    (ar : a∈R) (br : b∈R) (xa : G.Adj x a) (xb : G.Adj x b) : a=b :=
  h4 _ _ _ _ ne xa (sees a ar) xb (sees b br)

theorem high_remote_hits_near (h4 : FourCycleFree G) (R : Finset V) (u : V)
    (sees : ∀ r∈R,G.Adj u r) (x : V) (xr : x∈R) (high : 3≤G.degree x) :
    ∃ z, z∉R ∧ z≠u ∧ G.Adj x z := by
  classical
  by_contra! no
  have xu : x≠u := (sees _ xr).ne.symm
  have choice : ∀ z∈G.neighborFinset x,z≠u → z∈R := by
    intro z hm zu
    by_contra zr
    exact no z zr zu ((G.mem_neighborFinset _ _).mp hm)
  let N := (G.neighborFinset x).erase u
  have small : N.card≤1 := by
    apply Finset.card_le_one.mpr
    intro a am b bm
    have ha := Finset.mem_erase.mp am
    have hb := Finset.mem_erase.mp bm
    exact shared_root_remote_unique h4 R u sees xu (choice _ ha.2 ha.1) (choice _ hb.2 hb.1)
      ((G.mem_neighborFinset _ _).mp ha.2) ((G.mem_neighborFinset _ _).mp hb.2)
  have um : u∈G.neighborFinset x := (G.mem_neighborFinset _ _).mpr (sees _ xr).symm
  have cnt := Finset.card_erase_add_one um
  change N.card+1=(G.neighborFinset x).card at cnt
  have deg := G.card_neighborFinset_eq_degree x
  omega

theorem remote_attachment_card_le_near (h4 : FourCycleFree G) (R N : Finset V) (u : V)
    (sees : ∀ r∈R,G.Adj u r) (high : ∀ r∈R,3≤G.degree r)
    (near : ∀ r∈R,∀ z, z∉R → z≠u → G.Adj r z → z∈N) :
    R.card≤N.card := by
  classical
  have hit (r : (R : Set V)) : ∃ z,z∈N ∧ z≠u ∧ G.Adj r.val z := by
    obtain ⟨z,zn,zu,adj⟩ := high_remote_hits_near h4 R u sees r.val r.property (high _ r.property)
    exact ⟨z,near _ r.property _ zn zu adj,zu,adj⟩
  choose f fc using hit
  rw [←Fintype.card_coe R, ←Finset.card_univ]
  apply Finset.card_le_card_of_injOn (fun x : (R : Set V)=>f x)
    (s:=(Finset.univ : Finset (R : Set V))) (t:=N)
  · intro x _
    exact (fc x).1
  · intro a _ b _ eq
    change f a=f b at eq
    apply Subtype.ext
    exact shared_root_remote_unique h4 R u sees (fc a).2.1 a.property b.property
      (fc a).2.2.symm (by rw [eq]; exact (fc b).2.2.symm)
 
theorem peelable_extension_cannot_create_excess (K : Finset V) (h4 : FourCycleFree G)
    (base : ¬Pos G K)
    (peel : ∀ T : Finset V, K⊆T → T≠K →
      ∃ x : (T : Set V), x.val∉K ∧ (G.induce (T : Set V)).degree x≤2) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  by_contra! high
  obtain ⟨T,kt,p,_,large⟩ := minimum_score_subhost K h4 high
  by_cases eq : T=K
  · exact base (eq ▸ p)
  · obtain ⟨x,out,lo⟩ := peel T kt eq
    have hi := large x out
    omega

private theorem induced_degree_le (T : Finset V) (x : (T : Set V)) :
    (G.induce (T : Set V)).degree x≤G.degree x.val := by
  classical
  rw [←(G.induce (T : Set V)).card_neighborFinset_eq_degree,←G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn Subtype.val
  · intro y ym
    exact (G.mem_neighborFinset _ _).mpr
      ((G.induce (T : Set V)).mem_neighborFinset _ _ |>.mp ym)
  · exact Subtype.val_injective.injOn

theorem low_degree_extension_cannot_create_excess (K : Finset V) (h4 : FourCycleFree G)
    (base : ¬Pos G K) (low : ∀ x∉K,G.degree x≤2) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  by_contra! high
  obtain ⟨T,kt,p,_,large⟩ := minimum_score_subhost K h4 high
  have tk : T⊆K := by
    intro x xt
    by_contra nx
    have hi := large ⟨x,xt⟩ nx
    have le : (G.induce (T : Set V)).degree ⟨x,xt⟩≤2 :=
      (induced_degree_le (G:=G) T ⟨x,xt⟩).trans (low x nx)
    omega
  exact base ((Finset.Subset.antisymm tk kt) ▸ p)

theorem single_gate_attachment_cannot_create_excess (K : Finset V) (u : V)
    (h4 : FourCycleFree G) (base : ¬Pos G K)
    (sees : ∀ x∉K,G.Adj u x)
    (gate : ∀ x∉K,∀ y∈K,G.Adj x y → y=u) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  apply low_degree_extension_cannot_create_excess K h4 base
  intro x nx
  by_contra! high
  let R := Finset.univ \ K
  have see (r : V) (rm : r∈R) : G.Adj u r := sees r (Finset.mem_sdiff.mp rm).2
  obtain ⟨z,zr,zu,xz⟩ := high_remote_hits_near h4 R u see x (by simp [R,nx]) (by omega)
  have zk : z∈K := by simpa [R] using zr
  exact zu (gate x nx z zk xz)

#print axioms peelable_extension_cannot_create_excess
#print axioms single_gate_attachment_cannot_create_excess
#print axioms low_degree_extension_cannot_create_excess
#print axioms high_remote_hits_near
#print axioms remote_attachment_card_le_near
#print axioms pos_iff_local
#print axioms minimum_score_subhost
#print axioms retained_core_dominates
#print axioms retained_no_path
end Graffiti133NestedCore
