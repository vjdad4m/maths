import NestedCoreCleanRemoteScore133
import NestedCoreAdjacentGate133

namespace Graffiti133NestedSingleGate
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133NestedCore
  Graffiti133ExteriorSlack Graffiti133ExactTriangleCharge Graffiti133MultiWeighted
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

theorem clean_remote_layer_signed_budget_with_isolation
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    (K A I : Finset V) (ak : A⊆K) (ik : I⊆Finset.univ \ K)
    (isolated : ∀ i∈I,∀ r∉K,¬cleanEdge G A i r)
    (remote : ∀ w∉K,Remote H w)
    (near : ∀ a∈A,Outside H.c a ∧ (contactSet H a).Nonempty)
    (triples : (A.filter fun a=>3≤(contactSet H a).card).card≤2)
    (has : ∀ w∉K,(gateTags G A w).Nonempty)
    (gate : ∀ w∉K,∀ y∈K,G.Adj w y → y∈A)
    (tri : ∀ a∉K,∀ b∉K,∀ c∉K,cleanEdge G A a b→cleanEdge G A b c→¬G.Adj a c) :
    (∑ w : V,localIndependence G w)+4*K.card+(noncoreTriangles G K).card+2*I.card ≤
      (∑ w : (K : Set V),localIndependence (G.induce (K : Set V)) w)+
        4*Fintype.card V+2*(∑ w∈Finset.univ \ K,((gateTags G A w).card-1)) := by
  classical
  let R := (Finset.univ : Finset V) \ K
  let L := cleanGateGraph G A
  let t (x : V) := (gateTags G A x).card
  have out (w : V) (wm : w∈R) : w∉K := (Finset.mem_sdiff.mp wm).2
  have dis : Disjoint K R := Finset.disjoint_left.mpr (fun w wk wr=>out w wr wk)
  have union : K∪R=Finset.univ := by ext w; simp [R,or_comm]
  have sizes : K.card+R.card=Fintype.card V := by rw [←Finset.card_union_of_disjoint dis,union,Finset.card_univ]
  have cross : (arcSet G.Adj R K).card=∑ w∈R,t w := by
    rw [card_arcSet_eq_rows]
    apply Finset.sum_congr rfl
    intro x xm
    congr 1
    ext y
    simp only [gateTags,Finset.mem_filter]
    exact ⟨fun h=>⟨gate x (out x xm) y h.1 h.2,h.2⟩,fun h=>⟨ak h.1,h.2⟩⟩
  have cost : (arcSet G.Adj R K).card=R.card+(∑ w∈R,(t w-1)) := by
    rw [cross]
    have row (w : V) (wm : w∈R) : t w=1+(t w-1) := by
      have z : 0<t w := Finset.card_pos.mpr (has w (out w wm))
      omega
    calc
      (∑ w∈R,t w) = ∑ w∈R,(1+(t w-1)) := Finset.sum_congr rfl row
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  let Q₀ := R \ I
  have sub (w : V) (wm : w∈Q₀) : w∈R := (Finset.mem_sdiff.mp wm).1
  have clean := clean_edge_bound_for_remote_with_few_triple_gates H h4 h9 Q₀ A
    (fun w wm=>remote w (out w (sub w wm))) near triples (fun w wm=>has w (out w (sub w wm)))
    (fun a am b bm c cm=>tri a (out a (sub a am)) b (out b (sub b bm)) c (out c (sub c cm)))
  have remove : arcSet L.Adj R R=arcSet L.Adj Q₀ Q₀ := by
    ext e
    rw [mem_arcSet,mem_arcSet]
    constructor
    · rintro ⟨x,y,edge⟩
      refine ⟨Finset.mem_sdiff.mpr ⟨x,?_⟩,Finset.mem_sdiff.mpr ⟨y,?_⟩,edge⟩
      · exact fun inI=>isolated e.1 inI e.2 (out _ y) edge
      · exact fun inI=>isolated e.2 inI e.1 (out _ x) edge.symm
    · exact fun q=>⟨sub _ q.1,sub _ q.2.1,q.2.2⟩
  have cleanArc : (arcSet L.Adj R R).card+2*I.card≤2*R.card := by
    rw [remove,card_arcs_core (G:=L) Q₀]
    change (L.induce (Q₀ : Set V)).edgeFinset.card≤Q₀.card at clean
    have csum : Q₀.card+I.card=R.card := Finset.card_sdiff_add_card_eq_card ik
    omega
  let Q := arcSet G.Adj R R
  let p (e : V×V) := Disjoint (gateTags G A e.1) (gateTags G A e.2)
  have qc : Q.filter p=arcSet L.Adj R R := by
    ext e
    simp only [Q,Finset.mem_filter,mem_arcSet,p,L,cleanGateGraph,cleanEdge]
    tauto
  have qs : Q.filter (fun e=>¬p e)=arcSet (fun x y=>G.Adj x y ∧
      ¬Disjoint (gateTags G A x) (gateTags G A y)) R R := by
    ext e
    simp only [Q,Finset.mem_filter,mem_arcSet,p]
    tauto
  have split := Finset.filter_card_add_filter_neg_card_eq_card (s:=Q) p
  rw [qc,qs] at split
  have shared := shared_arc_card_le_twice_triangles (G:=G) A K R ak dis
  have d := degree_score_arcs_decomposition (G:=G) K R dis union
  have tr := triangle_core_partition (G:=G) K
  have cb := sum_degree_eq_local_add_triangles (restricted_c4 h4 K)
  have cg := sum_degree_eq_local_add_triangles h4
  have aux {l0 l1 e0 e1 tr0 tr1 tx ck sh w cx nr nk n ex iso : Nat}
      (sz : nk+nr=n) (es : 2*e1=2*e0+2*cx+w) (ts : tr0+tx=tr1)
      (part : ck+sh=w) (c : ck+2*iso≤2*nr) (s : sh≤2*tx) (x : cx=nr+ex)
      (b : l0+3*tr0=2*e0) (g : l1+3*tr1=2*e1) :
      l1+4*nk+tx+2*iso≤l0+4*n+2*ex := by omega
  change (∑ w : V,localIndependence G w)+4*K.card+(noncoreTriangles G K).card+2*I.card ≤
      (∑ w : (K : Set V),localIndependence (G.induce (K : Set V)) w)+
        4*Fintype.card V+2*(∑ w∈R,(t w-1))
  exact aux sizes d tr split cleanArc shared cost cb cg


def VeryShortGate (H : Hole G 7) (z : V) : Prop :=
  Outside H.c z ∧ ∃ i : Fin 7,
    (∀ k,G.Adj z (H.c k)↔k=i) ∨ (∀ k,G.Adj z (H.c k)↔k=i ∨ k=i+1)

theorem very_short_gate_contact_bound (H : Hole G 7) (z : V) (sh : VeryShortGate H z) :
    (contactSet H z).card≤2 := by
  obtain ⟨_,i,paint|paint⟩ := sh
  · have eq : contactSet H z={i} := by ext x; simp [mem_contactSet,paint x]
    rw [eq,Finset.card_singleton]
    decide
  · have eq : contactSet H z={i,i+1} := by ext x; simp [mem_contactSet,paint x]
    rw [eq]
    exact (Finset.card_insert_le (s:=({i+1}:Finset (Fin 7))) (a:=i)).trans (by simp)

theorem very_short_gate_isolates_clean_remote
    (H : Hole G 7) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    (A : Finset V) {z r s : V} (zr : VeryShortGate H z)
    (za : z∈A) (rr : Remote H r) (sr : Remote H s) (rz : G.Adj r z) :
    ¬cleanEdge G A r s := by
  intro edge
  obtain ⟨off,i,paint|paint⟩ := zr
  · have sz := remote_neighbor_must_share_singleton_gate H h9 off rr sr i paint rz edge.1
    exact Finset.disjoint_left.mp edge.2 (Finset.mem_filter.mpr ⟨za,rz⟩)
      (Finset.mem_filter.mpr ⟨za,sz⟩)
  · have sz := remote_neighbor_must_share_adjacent_pair_gate H h9 off rr sr i paint rz edge.1
    exact Finset.disjoint_left.mp edge.2 (Finset.mem_filter.mpr ⟨za,rz⟩)
      (Finset.mem_filter.mpr ⟨za,sz⟩)

private theorem paired_gate_card {u v x : V} (uv : u≠v) (sees : G.Adj x u ∨ G.Adj x v) :
    (gateTags G ({u,v} : Finset V) x).card =
      1+(if G.Adj x u ∧ G.Adj x v then 1 else 0) := by
  classical
  by_cases xu : G.Adj x u <;> by_cases xv : G.Adj x v
  · simp [gateTags,Finset.filter_insert,Finset.filter_singleton,xu,xv,uv]
  · simp [gateTags,Finset.filter_insert,Finset.filter_singleton,xu,xv,uv]
  · simp [gateTags,Finset.filter_insert,Finset.filter_singleton,xu,xv,uv]
  · exact (sees.elim xu xv).elim

private theorem tag_partition (A : Finset V) {u v : V} (ua : u∈A) (va : v∈A) (x : V) :
    (gateTags G A x).card=(gateTags G ({u,v} : Finset V) x).card+
      (gateTags G (A\{u,v}) x).card := by
  classical
  have ap : Disjoint (gateTags G ({u,v} : Finset V) x) (gateTags G (A\{u,v}) x) := by
    apply Finset.disjoint_left.mpr
    intro y ym yn
    exact (Finset.mem_sdiff.mp ((Finset.mem_filter.mp yn).1)).2 (Finset.mem_filter.mp ym).1
  rw [←Finset.card_union_of_disjoint ap]
  congr 1
  ext y
  constructor
  · intro ym
    obtain ⟨ya,xy⟩ := Finset.mem_filter.mp ym
    by_cases yp : y∈({u,v}:Finset V)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨yp,xy⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨ya,yp⟩,xy⟩))
  · intro ym
    rcases Finset.mem_union.mp ym with f|f
    · obtain ⟨fp,xy⟩ := Finset.mem_filter.mp f
      simp only [Finset.mem_insert,Finset.mem_singleton] at fp
      exact Finset.mem_filter.mpr ⟨fp.elim (fun p=>p.symm ▸ ua) (fun p=>p.symm ▸ va),xy⟩
    · obtain ⟨fp,xy⟩ := Finset.mem_filter.mp f
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp fp).1,xy⟩

theorem paired_gate_extras_budget (K A : Finset V) (u v : V) (h4 : FourCycleFree G)
    (uv : u≠v) (ua : u∈A) (va : v∈A)
    (sees : ∀ x∉K,G.Adj x u ∨ G.Adj x v)
    (one : ∀ x∉K,(gateTags G (A\{u,v}) x).card≤1) :
    (∑ x∈Finset.univ \ K,((gateTags G A x).card-1)) ≤
      ((Finset.univ \ K).filter fun x=>(gateTags G (A\{u,v}) x).Nonempty).card+1 := by
  classical
  let R := (Finset.univ : Finset V) \ K
  let B := A\{u,v}
  let F (x : V) : Prop := (gateTags G B x).Nonempty
  let D (x : V) : Prop := G.Adj x u ∧ G.Adj x v
  have at1 : (R.filter D).card≤1 := by
    apply Finset.card_le_one.mpr
    intro r rm s sm
    obtain ⟨_,ru,rv⟩ := Finset.mem_filter.mp rm
    obtain ⟨_,su,sv⟩ := Finset.mem_filter.mp sm
    exact h4 u v r s uv ru.symm rv.symm su.symm sv.symm
  have row (x : V) (xm : x∈R) : (gateTags G A x).card-1≤
      (if F x then 1 else 0)+(if D x then 1 else 0) := by
    have xo := (Finset.mem_sdiff.mp xm).2
    have e := tag_partition (G:=G) A ua va x
    have anchor := paired_gate_card (G:=G) uv (sees x xo)
    have ex : (gateTags G B x).card≤(if F x then 1 else 0) := by
      by_cases pos : F x
      · rw [if_pos pos]
        exact one x xo
      · rw [if_neg pos]
        change ¬(gateTags G B x).Nonempty at pos
        rw [Finset.not_nonempty_iff_eq_empty.mp pos,Finset.card_empty]
    change (gateTags G A x).card = (gateTags G ({u,v}:Finset V) x).card+(gateTags G B x).card at e
    change (gateTags G ({u,v}:Finset V) x).card=1+(if D x then 1 else 0) at anchor
    omega
  calc
    _ ≤ ∑ x∈R,((if F x then 1 else 0)+(if D x then 1 else 0)) := Finset.sum_le_sum row
    _ = (R.filter F).card+(R.filter D).card := by rw [Finset.sum_add_distrib,←Finset.card_filter,←Finset.card_filter]
    _ ≤ _ := Nat.add_le_add_left at1 _

theorem C7_unlimited_very_short_nongate_crossings_mean_four
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    (K A : Finset V) (ak : A⊆K) (cy : ∀ i,H.c i∈K)
    (dom : ∀ y : (K : Set V),Outside (restrictedHole H K cy).c y →
      ∃ i,(G.induce (K : Set V)).Adj y ((restrictedHole H K cy).c i))
    (baseMultis : (multiVertices (restrictedHole H K cy)).card≤4)
    (remote : ∀ w∉K,Remote H w)
    (near : ∀ a∈A,Outside H.c a ∧ (contactSet H a).Nonempty)
    (gate : ∀ w∉K,∀ y∈K,G.Adj w y → y∈A)
    (u v : V) (uv : u≠v) (um : u∈A) (vm : v∈A)
    (sees : ∀ w∉K,G.Adj w u ∨ G.Adj w v)
    (short : ∀ z∈A\{u,v},VeryShortGate H z)
    (one : ∀ x∉K,(gateTags G (A\{u,v}) x).card≤1) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  classical
  let R := (Finset.univ : Finset V) \ K
  let B := A\{u,v}
  let I := R.filter (fun x=>(gateTags G B x).Nonempty)
  have ik : I⊆R := Finset.filter_subset _ _
  have iso (x : V) (xm : x∈I) (y : V) (yo : y∉K) : ¬cleanEdge G A x y := by
    obtain ⟨xR,is⟩ := Finset.mem_filter.mp xm
    obtain ⟨z,zm⟩ := is
    obtain ⟨zb,xz⟩ := Finset.mem_filter.mp zm
    exact very_short_gate_isolates_clean_remote H h9 A (short z zb) (Finset.mem_sdiff.mp zb).1
      (remote x (Finset.mem_sdiff.mp xR).2) (remote y yo) xz
  have has (x : V) (xk : x∉K) : (gateTags G A x).Nonempty := by
    rcases sees x xk with xu|xv
    · exact ⟨u,Finset.mem_filter.mpr ⟨um,xu⟩⟩
    · exact ⟨v,Finset.mem_filter.mpr ⟨vm,xv⟩⟩
  have off (x : V) (xk : x∉K) : x∉A := fun xa=>xk (ak xa)
  have angles := two_anchors_force_clean_angles (G:=G) (W:={x | x∉K}) A h4 off um vm sees
  have sub : A.filter (fun z=>3≤(contactSet H z).card)⊆({u,v}:Finset V) := by
    intro z zm
    by_contra outside
    obtain ⟨za,large⟩ := Finset.mem_filter.mp zm
    have small := very_short_gate_contact_bound H z (short z (Finset.mem_sdiff.mpr ⟨za,outside⟩))
    omega
  have triples : (A.filter fun z=>3≤(contactSet H z).card).card≤2 := by
    have a := Finset.card_le_card sub
    have b := Finset.card_insert_le (s:=({v}:Finset V)) (a:=u)
    rw [Finset.card_singleton] at b
    omega
  have transfer := clean_remote_layer_signed_budget_with_isolation H h4 h9 K A I ak ik iso
    remote near triples has gate angles
  have extras := paired_gate_extras_budget K A u v h4 uv um vm sees one
  change (∑ x∈R,((gateTags G A x).card-1))≤I.card+1 at extras
  have base := C7_dominating_slack_depending_on_multis (restrictedHole H K cy)
    (restricted_c4 h4 K) (retained_no_path h9 K) dom
  have card : Fintype.card (K : Set V)=K.card := Fintype.card_coe K
  rw [card] at base
  have aux {l p k n t i e m : Nat} (a : l+4*k+t+2*i≤p+4*n+2*e) (b : e ≤ (i+1))
      (c : p+14≤4*k+3*m) (d : m≤4) : l≤4*n := by omega
  exact aux transfer extras base baseMultis

#print axioms C7_unlimited_very_short_nongate_crossings_mean_four
#print axioms paired_gate_extras_budget
#print axioms very_short_gate_isolates_clean_remote
#print axioms clean_remote_layer_signed_budget_with_isolation
end Graffiti133NestedSingleGate
