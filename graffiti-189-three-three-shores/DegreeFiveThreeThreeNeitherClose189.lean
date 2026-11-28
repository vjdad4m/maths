import DegreeFiveThreeThreeNeitherGeometry189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp count_cut_degree_on_two_shores portColor from DegreeFiveThreeForeignImpossible189
open private nonport_neighbors_subset from DegreeFiveThreeFiveShapes189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {C D : Cmp (G:=G) (a:=a) (b:=b)} {p q f : V}
set_option linter.unusedSectionVars false

namespace FiveMissShore33
variable (F : FiveMissShore33 C D p q f)

include F in
theorem no_local_shape
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (D3 : (cutPorts D).card=3) : False := by
  classical
  let L := F.L
  let T := F.T
  let Q₃ := F.shell 3
  let Q₄ := F.shell 4
  let E₄ := univ.filter (fun x : V=>G.dist a x=4)
  have ⟨l2,m1,budget⟩ := F.layers_le hc two even degree D3
  change L.card+F.M.card+E₄.card≤4 at budget
  change 2≤L.card at l2
  have ⟨u,ul,uf,un⟩ := F.exists_L_nonport l2
  have uns := nonport_neighbors_subset (F.mem_L.mp ul).1 un
  have tsub : T⊆Shore C := fun x xt=>(F.mem_T.mp xt).1
  have t3sub : Q₃⊆T := filter_subset _ _
  have t4sub : Q₄⊆E₄ := fun x h=>mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2⟩
  have sep : Disjoint L T := disjoint_left.mpr (fun x xl xt=>(F.mem_T.mp xt).2.2.2 xl)
  by_cases lEq : L.card=2
  · have cap (r k : V) (ord : (r=p ∧ k=q) ∨ (r=q ∧ k=p))
        (rS : r∈Shore C) (ar : G.Adj a r) (rk : r≠k) (r5 : 5≤G.degree r) : Q₃.card≤2 := by
      have h := F.port_degree_cap hc rS ar rk ord
      change G.degree r≤3+(L.filter (G.Adj r)).card at h
      have rP : r=p ∨ r=q := ord.imp And.left And.left
      have re : L.filter (G.Adj r)=L := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
      have br : G.Adj b r := by
        apply Classical.byContradiction
        intro no
        have n := F.port_exclusive_degree_cap hc rS ar rk ord no
        change G.degree r≤2+(L.filter (G.Adj r)).card at n
        rw [re] at n
        omega
      apply F.charge_set_cap hc even D3 rP (t3sub.trans tsub)
      intro x hx
      obtain ⟨xt,d⟩ := mem_filter.mp hx
      by_cases xf : x=f
      · subst x
        exact F.shared_charge_f hc rP xt br
      obtain ⟨y,yl,xy⟩ := F.near_T3 hc xt d xf
      change y∈L at yl
      have ry : G.Adj r y := (mem_filter.mp (re.symm ▸ yl)).2
      exact F.local_route_charge hc rP xt ry xy
    have cap3 : Q₃.card≤2 := (degree p q F.p_q).elim
      (cap p q (.inl ⟨rfl,rfl⟩) F.p_shore F.ap F.p_q)
      (cap q p (.inr ⟨rfl,rfl⟩) F.q_shore F.aq F.p_q.symm)
    have c4 : (T=Q₃ ∧ Q₄=∅) ∨ (Q₄.card≤1 ∧ ∀ x∈Shore C,5≤G.degree x) := by
      by_cases e : E₄.Nonempty
      · have n := card_pos.mpr e
        have k := card_le_card t4sub
        exact .inr ⟨by omega,(F.all_high_of_M_one hc conn degree D3 (by omega)).1⟩
      have no : ∀ x : V,G.dist a x≠4 := fun x hx=>e ⟨x,mem_filter.mpr ⟨mem_univ _,hx⟩⟩
      exact .inl ⟨F.no_four_implies_T_shell_three hc no,
        Finset.eq_empty_iff_forall_not_mem.mpr (fun x hx=>no x (mem_filter.mp hx).2)⟩
    exact three_three_two_visible_local_impossible F.shape lEq cap3 F.f_shore F.f_neighbors_b
      ul uf uns sep t3sub (fun x hx=>F.T3_neighbors hc hx) (F.first_shell hc two) degree c4
  have l3 : L.card=3 := by omega
  have mEq : F.M.card=1 := by omega
  have ⟨high,b5⟩ := F.all_high_of_M_one hc conn degree D3 mEq
  have no : ∀ x : V,G.dist a x≠4 := by
    intro x x4
    have h : 0<E₄.card := card_pos.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,x4⟩⟩
    omega
  have eT := F.no_four_implies_T_shell_three hc no
  let Yp := T∩DistanceTwo G p
  let Yq := T∩DistanceTwo G q
  have capP : Yp.card≤2 := F.charge_set_cap hc even D3 (.inl rfl)
    (inter_subset_left.trans tsub) inter_subset_right
  have capQ : Yq.card≤2 := F.charge_set_cap hc even D3 (.inr rfl)
    (inter_subset_left.trans tsub) inter_subset_right
  have localT (x : V) (xt : x∈T) (xf : x≠f) :
      G.neighborFinset x⊆(L.filter (G.Adj x))∪T.erase x := by
    intro y ym
    have xy := (mem_neighborFinset G x y).mp ym
    rcases F.T_non_f_adj_boundary hc xt xf xy with yL|yT
    · exact mem_union_left _ (mem_filter.mpr ⟨yL,xy⟩)
    exact mem_union_right _ (mem_erase.mpr ⟨xy.ne.symm,yT⟩)
  have hit (x : V) (xt : x∈T) (xf : x≠f) : (L.filter (G.Adj x)).Nonempty := by
    have x3 : x∈F.shell 3 := eT ▸ xt
    obtain ⟨y,yl,xy⟩ := F.near_T3 hc xt (mem_filter.mp x3).2 xf
    exact ⟨y,mem_filter.mpr ⟨yl,xy⟩⟩
  have p5 := high p F.p_shore
  have q5 := high q F.q_shore
  have n := F.port_degree_cap hc F.p_shore F.ap F.p_q (.inl ⟨rfl,rfl⟩)
  have m := F.port_degree_cap hc F.q_shore F.aq F.p_q.symm (.inr ⟨rfl,rfl⟩)
  have p2 : 2≤(L.filter (G.Adj p)).card := by change G.degree p≤3+(L.filter (G.Adj p)).card at n; omega
  have q2 : 2≤(L.filter (G.Adj q)).card := by change G.degree q≤3+(L.filter (G.Adj q)).card at m; omega
  have one : G.Adj b p ∨ G.Adj b q := by
    apply Classical.byContradiction
    intro no
    have cSub : portColor C b⊆{f} := by
      intro x hx
      obtain ⟨xc,bx⟩ := mem_filter.mp hx
      rcases F.port_iff.mp (mem_filter.mpr ⟨xc,.inr bx⟩) with h|h|h
      · exact (no (.inl (h ▸ bx))).elim
      · exact (no (.inr (h ▸ bx))).elim
      exact mem_singleton.mpr h
    have dSub : portColor D b⊆cutPorts D := by
      intro x hx
      obtain ⟨xd,bx⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨xd,.inr bx⟩
    have c := card_le_card cSub
    have d := card_le_card dSub
    have z := count_cut_degree_on_two_shores F.neq cover two (.inr rfl : b=a ∨ b=b)
    rw [card_singleton] at c
    omega
  have facts (r k : V) (rP : r=p ∨ r=q) (rS : r∈Shore C) (ar : G.Adj a r) (rk : r≠k)
      (ord : (r=p ∧ k=q) ∨ (r=q ∧ k=p))
      (ft : f∈T) : f∈T∩DistanceTwo G r ∨ ∀ x∈L,G.Adj r x := by
    by_cases br : G.Adj b r
    · exact .inl (mem_inter.mpr ⟨ft,F.shared_charge_f hc rP ft br⟩)
    have n := F.port_exclusive_degree_cap hc rS ar rk ord br
    change G.degree r≤2+(L.filter (G.Adj r)).card at n
    have r5 := high r rS
    have re : L.filter (G.Adj r)=L := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
    exact .inr fun x xl=>(mem_filter.mp (re.symm ▸ xl)).2
  exact three_three_three_visible_local_impossible F.shape l3 ul uns F.f_shore high
    capP capQ localT
    (fun ft=>F.f_neighbors ft hc)
    hit
    (fun x xt _ y _ py xy=>mem_inter.mpr ⟨xt,F.local_route_charge hc (.inl rfl) xt py xy⟩)
    (fun x xt _ y _ qy xy=>mem_inter.mpr ⟨xt,F.local_route_charge hc (.inr rfl) xt qy xy⟩)
    (fun x xl=>F.adj_of_L hc two xl) p2 q2
    (facts p q (.inl rfl) F.p_shore F.ap F.p_q (.inl ⟨rfl,rfl⟩))
    (facts q p (.inr rfl) F.q_shore F.aq F.p_q.symm (.inr ⟨rfl,rfl⟩))
    (fun ft=>one.imp (fun br=>mem_inter.mpr ⟨ft,F.shared_charge_f hc (.inl rfl) ft br⟩)
      (fun br=>mem_inter.mpr ⟨ft,F.shared_charge_f hc (.inr rfl) ft br⟩))

#print axioms no_local_shape
end FiveMissShore33
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
