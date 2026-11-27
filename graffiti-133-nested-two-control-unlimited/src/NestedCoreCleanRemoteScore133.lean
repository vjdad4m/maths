import NestedCoreShortArm133
import NestedCoreTwoExcess133
import NestedCoreC7CrossBudget133

namespace Graffiti133NestedSingleGate
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133NestedFour
  Graffiti133NestedCore Graffiti133ExteriorSlack Graffiti133ExactTriangleCharge Graffiti133MultiWeighted
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

noncomputable def cleanGateGraph (G : SimpleGraph V) (A : Finset V) : SimpleGraph V where
  Adj x y := cleanEdge G A x y
  symm := by intro x y e; exact ⟨e.1.symm,e.2.symm⟩
  loopless := by intro x e; exact G.loopless x e.1

private theorem path4_tuple {a b c d : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d)
    (ac : ¬G.Adj a c) (ad : ¬G.Adj a d) (bd : ¬G.Adj b d)
    (nac : a≠c) (nad : a≠d) (nbd : b≠d) :
    InducedPath G (![a,b,c,d] : Fin 4→V) := by
  have nab := ab.ne
  have nbc := bc.ne
  have ncd := cd.ne
  constructor
  · intro i j e
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j ij
    fin_cases i <;> fin_cases j <;> norm_num at ij ⊢ <;> simp_all

private theorem arm_of_adj_tuple {W : Set V} {g a b c d : V}
    (aw : a∈W) (bw : b∈W) (cw : c∈W) (dw : d∈W)
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d)
    (ac : ¬G.Adj a c) (ad : ¬G.Adj a d) (bd : ¬G.Adj b d)
    (nac : a≠c) (nad : a≠d) (nbd : b≠d)
    (ga : G.Adj g a) (gb : ¬G.Adj g b) (gc : ¬G.Adj g c) (gd : ¬G.Adj g d) :
    Arm (G:=G) W g := by
  refine ⟨![a,b,c,d],path4_tuple ab bc cd ac ad bd nac nad nbd,?_,?_⟩
  · intro i
    fin_cases i <;> simp_all
  · intro i
    fin_cases i <;> simp_all

private theorem clean_branch_gate_arm {W : Set V} (A : Finset V) (h4 : FourCycleFree G)
    (off : ∀ x∈W,x∉A)
    (tri : ∀ a∈W,∀ b∈W,∀ c∈W,cleanEdge G A a b→cleanEdge G A b c→¬G.Adj a c)
    {v x y w z g : V} (vv : v∈W) (xv : x∈W) (yv : y∈W) (wv : w∈W) (zv : z∈W)
    (vx : cleanEdge G A v x) (vy : cleanEdge G A v y) (vw : cleanEdge G A v w)
    (yz : cleanEdge G A y z) (zvne : z≠v)
    (xyne : x≠y) (xwne : x≠w) (ywne : y≠w)
    (ga : g∈A) (gx : G.Adj g x) :
    Arm (G:=G) W g := by
  have tx : g∈gateTags G A x := Finset.mem_filter.mpr ⟨ga,gx.symm⟩
  have gv : ¬G.Adj g v := fun yes=>
    Finset.disjoint_left.mp vx.2 (Finset.mem_filter.mpr ⟨ga,yes.symm⟩) tx
  have noG (b : V) (bn : x≠b) (vb : G.Adj v b) : ¬G.Adj g b := by
    intro yes
    exact bn (h4 v g x b (fun eq=>off v vv (eq ▸ ga)) vx.1 gx vb yes)
  have gy := noG y xyne vy.1
  have gw := noG w xwne vw.1
  by_cases gz : G.Adj g z
  · have zw : z≠w := fun eq=>gw (eq ▸ gz)
    have nZV := tri z zv y yv v vv ⟨yz.1.symm,yz.2.symm⟩ ⟨vy.1.symm,vy.2.symm⟩
    have nYW := tri y yv v vv w wv ⟨vy.1.symm,vy.2.symm⟩ vw
    have nZW : ¬G.Adj z w := by
      intro yes
      exact zvne (h4 y w z v ywne yz.1 yes.symm vy.1.symm vw.1.symm)
    exact arm_of_adj_tuple zv yv vv wv yz.1.symm vy.1.symm vw.1 nZV nZW nYW
      zvne zw ywne gz gy gv gw
  · have xz : x≠z := fun eq=>gz (eq ▸ gx)
    have nXY := tri x xv v vv y yv ⟨vx.1.symm,vx.2.symm⟩ vy
    have nVZ := tri v vv y yv z zv vy yz
    have nXZ : ¬G.Adj x z := by
      intro yes
      exact zvne (h4 x y z v xyne yes yz.1 vx.1.symm vy.1.symm)
    exact arm_of_adj_tuple xv vv yv zv vx.1.symm vy.1 yz.1 nXY nXZ nVZ
      xyne xz zvne.symm gx gv gy gz

theorem clean_triangle_free_gives_clean_angle_free {W : Set V} (A : Finset V)
    (h4 : FourCycleFree G) (off : ∀ x∈W,x∉A)
    (tri : ∀ a∈W,∀ b∈W,∀ c∈W,cleanEdge G A a b→cleanEdge G A b c→¬cleanEdge G A a c) :
    ∀ a∈W,∀ b∈W,∀ c∈W,cleanEdge G A a b→cleanEdge G A b c→¬G.Adj a c := by
  intro a aw b bw c cw ab bc ac
  have distinct := gate_tag_rows_disjoint h4 A (off b bw) ac.ne ab.1.symm bc.1
  exact tri a aw b bw c cw ab bc ⟨ac,distinct⟩

theorem three_clean_branch_arm_gates {W : Set V} (A : Finset V) (h4 : FourCycleFree G)
    (has : ∀ x∈W,(gateTags G A x).Nonempty) (off : ∀ x∈W,x∉A)
    (tri : ∀ a∈W,∀ b∈W,∀ c∈W,cleanEdge G A a b→cleanEdge G A b c→¬G.Adj a c)
    (B : Branch (cleanGateGraph G A) W) :
    ∃ S : Finset V,S⊆A ∧ S.card=3 ∧ ∀ a∈S,Arm (G:=G) W a := by
  classical
  obtain ⟨p,pm⟩ := has B.x B.xW
  obtain ⟨q,qm⟩ := has B.y B.yW
  obtain ⟨r,rm⟩ := has B.z B.zW
  obtain ⟨pa,px⟩ := Finset.mem_filter.mp pm
  obtain ⟨qa,qy⟩ := Finset.mem_filter.mp qm
  obtain ⟨ra,rz⟩ := Finset.mem_filter.mp rm
  have vx : cleanEdge G A B.v B.x := B.vx
  have vy : cleanEdge G A B.v B.y := B.vy
  have vz : cleanEdge G A B.v B.z := B.vz
  have txY := gate_tag_rows_disjoint h4 A (off _ B.vW) B.xy vx.1 vy.1
  have txZ := gate_tag_rows_disjoint h4 A (off _ B.vW) B.xz vx.1 vz.1
  have tyZ := gate_tag_rows_disjoint h4 A (off _ B.vW) B.yz vy.1 vz.1
  have pq : p≠q := fun eq=>Finset.disjoint_left.mp txY pm (eq.symm ▸ qm)
  have pr : p≠r := fun eq=>Finset.disjoint_left.mp txZ pm (eq.symm ▸ rm)
  have qr : q≠r := fun eq=>Finset.disjoint_left.mp tyZ qm (eq.symm ▸ rm)
  obtain ⟨a,aw,an,xa⟩ := B.hasNext B.x (Or.inl rfl)
  obtain ⟨b,bw,bn,yb⟩ := B.hasNext B.y (Or.inr (Or.inl rfl))
  have ap : Arm (G:=G) W p :=
    clean_branch_gate_arm A h4 off tri B.vW B.xW B.yW B.zW bw vx vy vz
      yb bn B.xy B.xz B.yz pa px.symm
  have aq : Arm (G:=G) W q :=
    clean_branch_gate_arm A h4 off tri B.vW B.yW B.xW B.zW aw vy vx vz
      xa an B.xy.symm B.yz B.xz qa qy.symm
  have ar : Arm (G:=G) W r :=
    clean_branch_gate_arm A h4 off tri B.vW B.zW B.xW B.yW aw vz vx vy
      xa an B.xz.symm B.yz.symm B.xy ra rz.symm
  let S : Finset V := {p,q,r}
  refine ⟨S,?_,by simp [S,pq,pr,qr],?_⟩
  · intro c cm
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at cm
    rcases cm with rfl|rfl|rfl
    · exact pa
    · exact qa
    · exact ra
  · intro c cm
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at cm
    rcases cm with rfl|rfl|rfl
    · exact ap
    · exact aq
    · exact ar

theorem clean_edge_bound_for_remote_with_few_triple_gates
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    (W A : Finset V) (moves : ∀ w∈W,Remote H w)
    (near : ∀ a∈A,Outside H.c a ∧ (contactSet H a).Nonempty)
    (triples : (A.filter fun a=>3≤(contactSet H a).card).card≤2)
    (has : ∀ w∈W,(gateTags G A w).Nonempty)
    (tri : ∀ a∈W,∀ b∈W,∀ c∈W,cleanEdge G A a b→cleanEdge G A b c→¬G.Adj a c) :
    ((cleanGateGraph G A).induce (W : Set V)).edgeFinset.card≤W.card := by
  classical
  by_contra! high
  obtain ⟨B⟩ := branch_from_induced_edge_excess W high
  have off (w : V) (wm : w∈W) : w∉A := by
    intro wa
    obtain ⟨i,im⟩ := (near w wa).2
    exact (moves w wm).2 i ((mem_contactSet H w i).mp im)
  obtain ⟨S,sa,s3,arms⟩ := three_clean_branch_arm_gates A h4 has off tri B
  have sub : S⊆A.filter (fun a=>3≤(contactSet H a).card) := by
    intro z zm
    have za := sa zm
    have above : 3≤(contactSet H z).card := by
      by_contra! low
      exact short_gate_excludes_remote_clean_arm H h9 (W:=(W : Set V)) moves z
        (near z za).1 (near z za).2 (by omega) (arms z zm)
    exact Finset.mem_filter.mpr ⟨za,above⟩
  have a := Finset.card_le_card sub
  omega

theorem clean_remote_layer_signed_budget
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    (K A : Finset V) (ak : A⊆K)
    (remote : ∀ w∉K,Remote H w)
    (near : ∀ a∈A,Outside H.c a ∧ (contactSet H a).Nonempty)
    (triples : (A.filter fun a=>3≤(contactSet H a).card).card≤2)
    (has : ∀ w∉K,(gateTags G A w).Nonempty)
    (gate : ∀ w∉K,∀ y∈K,G.Adj w y → y∈A)
    (tri : ∀ a∉K,∀ b∉K,∀ c∉K,cleanEdge G A a b→cleanEdge G A b c→¬G.Adj a c) :
    (∑ w : V,localIndependence G w)+4*K.card+(noncoreTriangles G K).card ≤
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
  have clean := clean_edge_bound_for_remote_with_few_triple_gates H h4 h9 R A
    (fun w wm=>remote w (out w wm)) near triples (fun w wm=>has w (out w wm))
    (fun a am b bm c cm=>tri a (out a am) b (out b bm) c (out c cm))
  have cleanArc : (arcSet L.Adj R R).card≤2*R.card := by
    rw [card_arcs_core (G:=L) R]
    exact Nat.mul_le_mul_left 2 clean
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
  have aux {l0 l1 e0 e1 tr0 tr1 tx ck sh w cx nr nk n ex : Nat}
      (sz : nk+nr=n) (es : 2*e1=2*e0+2*cx+w) (ts : tr0+tx=tr1)
      (part : ck+sh=w) (c : ck≤2*nr) (s : sh≤2*tx) (x : cx=nr+ex)
      (b : l0+3*tr0=2*e0) (g : l1+3*tr1=2*e1) :
      l1+4*nk+tx≤l0+4*n+2*ex := by omega
  change (∑ w : V,localIndependence G w)+4*K.card+(noncoreTriangles G K).card ≤
      (∑ w : (K : Set V),localIndependence (G.induce (K : Set V)) w)+
        4*Fintype.card V+2*(∑ w∈R,(t w-1))
  exact aux sizes d tr split cleanArc shared cost cb cg

theorem C7_few_triple_gates_remote_budget_mean_four
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    (K A : Finset V) (ak : A⊆K) (cy : ∀ i,H.c i∈K)
    (dom : ∀ y : (K : Set V),Outside (restrictedHole H K cy).c y →
      ∃ i,(G.induce (K : Set V)).Adj y ((restrictedHole H K cy).c i))
    (remote : ∀ w∉K,Remote H w)
    (near : ∀ a∈A,Outside H.c a ∧ (contactSet H a).Nonempty)
    (triples : (A.filter fun a=>3≤(contactSet H a).card).card≤2)
    (has : ∀ w∉K,(gateTags G A w).Nonempty)
    (gate : ∀ w∉K,∀ y∈K,G.Adj w y → y∈A)
    (tri : ∀ a∉K,∀ b∉K,∀ c∉K,cleanEdge G A a b→cleanEdge G A b c→¬G.Adj a c)
    (budget : 3*(multiVertices (restrictedHole H K cy)).card+
      2*(∑ w∈Finset.univ \ K,((gateTags G A w).card-1))≤14+(noncoreTriangles G K).card) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  have a := clean_remote_layer_signed_budget H h4 h9 K A ak remote near triples has gate tri
  have b := C7_dominating_slack_depending_on_multis (restrictedHole H K cy)
    (restricted_c4 h4 K) (retained_no_path h9 K) dom
  have card : Fintype.card (K : Set V)=K.card := Fintype.card_coe K
  rw [card] at b
  have close {l b m k n c e : Nat} (h : l+4*k+c≤b+4*n+2*e)
      (near : b+14≤4*k+3*m) (budget : 3*m+2*e≤14+c) : l≤4*n := by omega
  exact close a b budget

theorem two_anchors_force_clean_angles {W : Set V} (A : Finset V) (h4 : FourCycleFree G)
    (off : ∀ x∈W,x∉A) {u v : V} (um : u∈A) (vm : v∈A)
    (sees : ∀ x∈W,G.Adj x u ∨ G.Adj x v) :
    ∀ a∈W,∀ b∈W,∀ c∈W,cleanEdge G A a b→cleanEdge G A b c→¬G.Adj a c := by
  apply clean_triangle_free_gives_clean_angle_free A h4 off
  intro a am b bm c cm ab bc ac
  have separate {x y : V} (xy : cleanEdge G A x y) {g : V} (gm : g∈A) :
      ¬(G.Adj x g ∧ G.Adj y g) := by
    rintro ⟨xg,yg⟩
    exact Finset.disjoint_left.mp xy.2 (Finset.mem_filter.mpr ⟨gm,xg⟩) (Finset.mem_filter.mpr ⟨gm,yg⟩)
  have abu := separate ab um
  have abv := separate ab vm
  have bcu := separate bc um
  have bcv := separate bc vm
  have acu := separate ac um
  have acv := separate ac vm
  have aa := sees a am
  have bb := sees b bm
  have cc := sees c cm
  tauto

theorem C7_two_anchor_remote_budget_mean_four
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    (K A : Finset V) (ak : A⊆K) (cy : ∀ i,H.c i∈K)
    (dom : ∀ y : (K : Set V),Outside (restrictedHole H K cy).c y →
      ∃ i,(G.induce (K : Set V)).Adj y ((restrictedHole H K cy).c i))
    (remote : ∀ w∉K,Remote H w)
    (near : ∀ a∈A,Outside H.c a ∧ (contactSet H a).Nonempty)
    (triples : (A.filter fun a=>3≤(contactSet H a).card).card≤2)
    (gate : ∀ w∉K,∀ y∈K,G.Adj w y → y∈A)
    (u v : V) (um : u∈A) (vm : v∈A)
    (sees : ∀ w∉K,G.Adj w u ∨ G.Adj w v)
    (budget : 3*(multiVertices (restrictedHole H K cy)).card+
      2*(∑ w∈Finset.univ \ K,((gateTags G A w).card-1))≤14+(noncoreTriangles G K).card) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  classical
  have has (x : V) (xk : x∉K) : (gateTags G A x).Nonempty := by
    rcases sees x xk with xu|xv
    · exact ⟨u,Finset.mem_filter.mpr ⟨um,xu⟩⟩
    · exact ⟨v,Finset.mem_filter.mpr ⟨vm,xv⟩⟩
  have off (x : V) (xk : x∉K) : x∉A := fun xa=>xk (ak xa)
  have angles := two_anchors_force_clean_angles (G:=G) (W:={x | x∉K}) A h4 off um vm sees
  exact C7_few_triple_gates_remote_budget_mean_four H h4 h9 K A ak cy dom remote near triples
    has gate angles budget

#print axioms two_anchors_force_clean_angles
#print axioms C7_two_anchor_remote_budget_mean_four
#print axioms C7_few_triple_gates_remote_budget_mean_four
#print axioms clean_remote_layer_signed_budget
#print axioms clean_triangle_free_gives_clean_angle_free
#print axioms three_clean_branch_arm_gates
#print axioms clean_edge_bound_for_remote_with_few_triple_gates
end Graffiti133NestedSingleGate
