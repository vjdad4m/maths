import DegreeFiveThreeThreeNeitherLThree189
import DegreeFiveThreeThreeUniversalShape189
import FiveOfSixPorts189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint shore_nonempty shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private secondShore four_in_nonsingleton second_positive_of_small_ports from DegreeFiveDistanceTwoThreeClose189
open private Cmp count_cut_degree_on_two_shores portColor from DegreeFiveThreeForeignImpossible189
open private nonport_neighbors_subset nonport_degree_bound_small from DegreeFiveThreeFiveShapes189
open private dark visible_in_nonports from DegreeFiveTwoThreeBase189
open private cross_ports_at_distance_two distance_two_at_cut_lower from DegreeFiveTwoThreeVisTwo189
open private two_walk_middle from DistanceTwoCut189
open private order_four_of_one_visible from DegreeFiveThreeThreeUniversalShape189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

structure FiveMissShore33 (C D : Cmp (G:=G) (a:=a) (b:=b)) (p q f : V) : Prop where
  neq : C≠D
  p_q : p≠q
  p_f : p≠f
  q_f : q≠f
  ports : cutPorts C={p,q,f}
  allD : ∀ z∈cutPorts D,G.Adj a z
  ap : G.Adj a p
  aq : G.Adj a q
  af : ¬G.Adj a f
  bf : G.Adj b f

namespace FiveMissShore33
variable {C D : Cmp (G:=G) (a:=a) (b:=b)} {p q f : V}
variable (F : FiveMissShore33 C D p q f)

include F in
theorem p_shore : p∈Shore C :=
  (mem_filter.mp (show p∈cutPorts C by simp [F.ports])).1

include F in
theorem q_shore : q∈Shore C :=
  (mem_filter.mp (show q∈cutPorts C by simp [F.ports])).1

include F in
theorem f_shore : f∈Shore C :=
  (mem_filter.mp (show f∈cutPorts C by simp [F.ports])).1

noncomputable def L (_ : FiveMissShore33 C D p q f) : Finset V := secondShore C a
noncomputable def M (_ : FiveMissShore33 C D p q f) : Finset V := secondShore D a
noncomputable def T (F : FiveMissShore33 C D p q f) : Finset V := Shore C \ insert p (insert q F.L)
noncomputable def shell (F : FiveMissShore33 C D p q f) (i : ℕ) : Finset V :=
  F.T.filter (fun u=>G.dist a u=i)

theorem mem_L {x : V} : x∈F.L ↔ x∈Shore C ∧ G.dist a x=2 := by
  simp [L,secondShore,DistanceTwo]

theorem mem_T {x : V} : x∈F.T ↔ x∈Shore C ∧ x≠p ∧ x≠q ∧ x∉F.L := by
  simp [T,not_or,and_assoc]

theorem shape : Shore C = insert p (insert q (F.L∪F.T)) := by
  ext x
  constructor
  · intro xs
    by_cases xp : x=p
    · simp [xp]
    by_cases xq : x=q
    · simp [xq]
    by_cases xl : x∈F.L
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ xl))
    exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ (F.mem_T.mpr ⟨xs,xp,xq,xl⟩)))
  intro h
  rcases mem_insert.mp h with e|h
  · exact e.symm ▸ F.p_shore
  rcases mem_insert.mp h with e|h
  · exact e.symm ▸ F.q_shore
  exact (mem_union.mp h).elim (fun m=>(F.mem_L.mp m).1) (fun m=>(F.mem_T.mp m).1)

include F in
theorem covered_iff {x : V} (xs : x∈Shore C) : G.Adj a x ↔ x=p ∨ x=q := by
  constructor
  · intro ax
    have m : x∈cutPorts C := mem_filter.mpr ⟨xs,.inl ax⟩
    have cases' : x=p ∨ x=q ∨ x=f := by simpa [F.ports] using m
    rcases cases' with h|h|h
    · exact .inl h
    · exact .inr h
    exact (F.af (h ▸ ax)).elim
  rintro (rfl|rfl)
  · exact F.ap
  exact F.aq

include F in
theorem port_iff {x : V} : x∈cutPorts C ↔ x=p ∨ x=q ∨ x=f := by
  simp [F.ports]

theorem adj_of_L (hc : G.Connected) (two : G.dist a b=2) {x : V} (xl : x∈F.L) :
    G.Adj p x ∨ G.Adj q x := by
  obtain ⟨xc,depth⟩ := F.mem_L.mp xl
  obtain ⟨path,pl⟩ := hc.exists_walk_length_eq_dist a x
  obtain ⟨w,aw,wx⟩ := two_walk_middle path (pl.trans depth)
  rcases shore_closed C x xc w wx.symm with wa|wb|wc
  · exact (G.loopless a (wa ▸ aw)).elim
  · have h := dist_eq_one_iff_adj.mpr (wb ▸ aw : G.Adj a b)
    omega
  rcases (F.covered_iff wc).mp aw with e|e
  · exact .inl (e ▸ wx)
  exact .inr (e ▸ wx)


theorem T_depth (hc : G.Connected) {x : V} (xt : x∈F.T) : 3≤G.dist a x := by
  obtain ⟨xc,xp,xq,xl⟩ := F.mem_T.mp xt
  have nz : G.dist a x≠0 := fun e=>(shore_off C).1
    (Eq.mp (congrArg (fun z : V=>z∈Shore C) ((hc.dist_eq_zero_iff).mp e).symm) xc)
  have no : ¬G.Adj a x := fun h=>((F.covered_iff xc).mp h).elim xp xq
  have n1 : G.dist a x≠1 := fun h=>no (dist_eq_one_iff_adj.mp h)
  have n2 : G.dist a x≠2 := fun h=>xl (F.mem_L.mpr ⟨xc,h⟩)
  omega

include F in
theorem f_depth_le (hc : G.Connected) (two : G.dist a b=2) : G.dist a f≤3 := by
  have d := dist_eq_one_iff_adj.mpr F.bf
  have t := hc.dist_triangle (u:=a) (v:=b) (w:=f)
  omega

theorem T_non_f_adj_boundary (hc : G.Connected) {x y : V} (xt : x∈F.T) (xf : x≠f)
    (xy : G.Adj x y) : y∈F.L ∨ y∈F.T := by
  obtain ⟨xc,xp,xq,_⟩ := F.mem_T.mp xt
  have xnp : x∉cutPorts C := fun h=>(F.port_iff.mp h).elim xp (fun e=>e.elim xq xf)
  have ys := (mem_erase.mp ((nonport_neighbors_subset xc xnp) ((mem_neighborFinset G x y).mpr xy))).2
  have far := F.T_depth hc xt
  have no (z : V) (az : G.Adj a z) (e : y=z) : False := by
    have m := G.dist_le (Walk.cons az (Walk.cons (e ▸ xy.symm) Walk.nil))
    simp only [length_cons,length_nil] at m
    omega
  have yp : y≠p := no p F.ap
  have yq : y≠q := no q F.aq
  by_cases yl : y∈F.L
  · exact .inl yl
  exact .inr (F.mem_T.mpr ⟨ys,yp,yq,yl⟩)


theorem T_adj_boundary (hc : G.Connected) {x y : V} (xt : x∈F.T) (xy : G.Adj x y) :
    y∈F.L ∨ y∈F.T ∨ (x=f ∧ y=b) := by
  by_cases xf : x=f
  · subst x
    rcases shore_closed C f F.f_shore y xy with e|e|ys
    · exact (F.af (e ▸ xy.symm)).elim
    · exact .inr (.inr ⟨rfl,e⟩)
    have far := F.T_depth hc xt
    have no (z : V) (az : G.Adj a z) (e : y=z) : False := by
      have m := G.dist_le (Walk.cons az (Walk.cons (e ▸ xy.symm) Walk.nil))
      simp only [length_cons,length_nil] at m
      omega
    by_cases yl : y∈F.L
    · exact .inl yl
    exact .inr (.inl (F.mem_T.mpr ⟨ys,fun e=>no p F.ap e,fun e=>no q F.aq e,yl⟩))
  exact (F.T_non_f_adj_boundary hc xt xf xy).imp id Or.inl

theorem near_T3 (hc : G.Connected) {x : V} (xt : x∈F.T) (x3 : G.dist a x=3)
    (xf : x≠f) : ∃ y∈F.L,G.Adj x y := by
  obtain ⟨p',hp⟩ := hc.exists_walk_length_eq_dist x a
  have len : p'.length=3 := by rw [hp,dist_comm,x3]
  have middle {u v : V} (w : G.Walk u v) (l : w.length=3) (met : G.dist v u=3) :
      ∃ z,G.Adj u z ∧ G.dist v z=2 := by
    cases w with
    | nil => simp at l
    | @cons u z v e w =>
      refine ⟨z,e,?_⟩
      have n := G.dist_le w.reverse
      simp only [length_reverse] at n
      have m := hc.dist_triangle (u:=v) (v:=z) (w:=u)
      have step := dist_eq_one_iff_adj.mpr e.symm
      simp only [length_cons] at l
      omega
  obtain ⟨y,xy,ay⟩ := middle p' len x3
  rcases F.T_non_f_adj_boundary hc xt xf xy with yl|yt
  · exact ⟨y,yl,xy⟩
  have far := F.T_depth hc yt
  omega

theorem first_shell (hc : G.Connected) (two : G.dist a b=2) :
    F.T.Nonempty → (F.shell 3).Nonempty := by
  classical
  rintro ⟨x,xt⟩
  let P := F.T.image (G.dist a)
  have ne : P.Nonempty := ⟨G.dist a x,mem_image_of_mem _ xt⟩
  let n := P.min' ne
  have nh : n∈P := P.min'_mem ne
  obtain ⟨x,xt,hx⟩ := mem_image.mp nh
  have xge := F.T_depth hc xt
  have x3 : G.dist a x=3 := by
    by_contra no
    obtain ⟨path,hp⟩ := hc.exists_walk_length_eq_dist x a
    have distPos : 0<path.length := by rw [hp,dist_comm]; omega
    have tail {u v : V} (w : G.Walk u v) (pos : 0<w.length)
        (_d : 0<G.dist v u) (min : w.length=G.dist v u) :
        ∃ y,G.Adj u y ∧ G.dist v y+1=G.dist v u := by
      cases w with
      | nil => simp at pos
      | @cons u y v e w =>
        refine ⟨y,e,?_⟩
        have n := G.dist_le w.reverse
        simp only [length_reverse] at n
        have z := hc.dist_triangle (u:=v) (v:=y) (w:=u)
        have step := dist_eq_one_iff_adj.mpr e.symm
        simp only [length_cons] at min
        omega
    have xne : x≠f := fun e=>no (by
      have k := F.f_depth_le hc two
      rw [e] at xge ⊢
      omega)
    have eq : path.length=G.dist a x := by rw [hp,dist_comm]
    obtain ⟨y,xy,hy⟩ := tail path distPos (by omega) eq
    rcases F.T_non_f_adj_boundary hc xt xne xy with yl|yt
    · have h := (F.mem_L.mp yl).2
      omega
    have mn := P.min'_le (G.dist a y) (mem_image_of_mem _ yt)
    change n≤G.dist a y at mn
    omega
  exact ⟨x,mem_filter.mpr ⟨xt,x3⟩⟩


theorem near_port_neighbors (hc : G.Connected)
    {r k : V} (rc : r∈Shore C) (ar : G.Adj a r) (_rk : r≠k)
    (cover : (r=p ∧ k=q) ∨ (r=q ∧ k=p)) :
    G.neighborFinset r⊆insert a (insert b (insert k (F.L.filter (G.Adj r)))) := by
  intro x xn
  have rx := (mem_neighborFinset G r x).mp xn
  rcases shore_closed C r rc x rx with xa|xb|xc
  · exact mem_insert.mpr (.inl xa)
  · exact mem_insert_of_mem (mem_insert.mpr (.inl xb))
  by_cases xk : x=k
  · exact mem_insert_of_mem (mem_insert_of_mem (mem_insert.mpr (.inl xk)))
  have no : ¬G.Adj a x := by
    intro h
    rcases (F.covered_iff xc).mp h with xp|xq <;> rcases cover with ⟨rp,kq⟩|⟨rq,kp⟩
    · exact rx.ne (rp.trans xp.symm)
    · exact xk (xp.trans kp.symm)
    · exact xk (xq.trans kq.symm)
    · exact rx.ne (rq.trans xq.symm)
  have ax : a≠x := fun e=>(shore_off C).1 (Eq.mp (congrArg (fun z : V=>z∈Shore C) e.symm) xc)
  have xd := d2 hc ax no ar rx
  have xl : x∈F.L := mem_inter.mpr ⟨xc,xd⟩
  exact mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨xl,rx⟩)))

theorem port_degree_cap (hc : G.Connected)
    {r k : V} (rc : r∈Shore C) (ar : G.Adj a r) (rk : r≠k)
    (cover : (r=p ∧ k=q) ∨ (r=q ∧ k=p)) :
    G.degree r≤3+(F.L.filter (G.Adj r)).card := by
  have s := F.near_port_neighbors hc rc ar rk cover
  have h := card_le_card s
  rw [card_neighborFinset_eq_degree] at h
  have x := card_insert_le a (insert b (insert k (F.L.filter (G.Adj r))))
  have y := card_insert_le b (insert k (F.L.filter (G.Adj r)))
  have z := card_insert_le k (F.L.filter (G.Adj r))
  omega

theorem port_exclusive_degree_cap (hc : G.Connected)
    {r k : V} (rc : r∈Shore C) (ar : G.Adj a r) (rk : r≠k)
    (cover : (r=p ∧ k=q) ∨ (r=q ∧ k=p)) (nor : ¬G.Adj b r) :
    G.degree r≤2+(F.L.filter (G.Adj r)).card := by
  have s := F.near_port_neighbors hc rc ar rk cover
  have s' : G.neighborFinset r⊆insert a (insert k (F.L.filter (G.Adj r))) := by
    intro x xn
    rcases mem_insert.mp (s xn) with xa|x'
    · exact mem_insert.mpr (.inl xa)
    rcases mem_insert.mp x' with xb|rest
    · exact (nor ((xb ▸ (mem_neighborFinset G r x).mp xn).symm)).elim
    exact mem_insert_of_mem rest
  have h := card_le_card s'
  rw [card_neighborFinset_eq_degree] at h
  have y := card_insert_le a (insert k (F.L.filter (G.Adj r)))
  have z := card_insert_le k (F.L.filter (G.Adj r))
  omega

theorem local_route_charge (hc : G.Connected) {r x y : V}
    (rP : r=p ∨ r=q) (xt : x∈F.T) (ry : G.Adj r y) (xy : G.Adj x y) :
    x∈DistanceTwo G r := by
  have ar : G.Adj a r := rP.elim (fun e=>e.symm ▸ F.ap) (fun e=>e.symm ▸ F.aq)
  have t := F.T_depth hc xt
  have ⟨_,xp,xq,_⟩ := F.mem_T.mp xt
  have ne : r≠x := fun e=>(rP.elim (fun h=>xp (e.symm.trans h))
    (fun h=>xq (e.symm.trans h)))
  have no : ¬G.Adj r x := by
    intro h
    have m := G.dist_le (Walk.cons ar (Walk.cons h Walk.nil))
    simp only [length_cons,length_nil] at m
    omega
  exact d2 hc ne no ry xy.symm

theorem shared_charge_f (hc : G.Connected) {r : V} (rP : r=p ∨ r=q)
    (ft : f∈F.T) (br : G.Adj b r) : f∈DistanceTwo G r :=
  F.local_route_charge hc rP ft br.symm F.bf.symm

include F in
theorem charge_set_cap (hc : G.Connected)
    (even : ∀ z,(EvenFrom G z).card≤6) (D3 : (cutPorts D).card=3)
    {r : V} (rp : r=p ∨ r=q) {W : Finset V}
    (wc : W⊆Shore C) (charge : W⊆DistanceTwo G r) : W.card≤2 := by
  have rc : r∈Shore C := rp.elim (fun e=>e.symm ▸ F.p_shore) (fun e=>e.symm ▸ F.q_shore)
  have ar : G.Adj a r := rp.elim (fun e=>e.symm ▸ F.ap) (fun e=>e.symm ▸ F.aq)
  have dp := cross_ports_at_distance_two hc F.neq rc ar F.allD
  have dis : Disjoint (cutPorts D) W := (shore_disjoint F.neq).symm.mono (filter_subset _ _) wc
  have n := (card_le_card (union_subset dp charge)).trans (distanceTwo_le_of_even 5 r (even r))
  rw [card_union_of_disjoint dis,D3] at n
  omega

theorem exists_L_nonport (h : 2≤F.L.card) : ∃ u∈F.L,u≠f ∧ u∉cutPorts C := by
  classical
  obtain ⟨x,xl,y,yl,xy⟩ := one_lt_card.mp (by omega : 1<F.L.card)
  have notCovered : ∀ z∈F.L,z≠p ∧ z≠q := by
    intro z zl
    have z2 := (F.mem_L.mp zl).2
    have p1 := dist_eq_one_iff_adj.mpr F.ap
    have q1 := dist_eq_one_iff_adj.mpr F.aq
    exact ⟨fun e=>by rw [e] at z2; omega,fun e=>by rw [e] at z2; omega⟩
  have out (z : V) (zl : z∈F.L) (zf : z≠f) : z∉cutPorts C := by
    intro zp
    obtain ⟨np,nq⟩ := notCovered z zl
    exact (F.port_iff.mp zp).elim np (fun h=>h.elim nq zf)
  by_cases xf : x=f
  · have yf : y≠f := fun h=>xy (xf.trans h.symm)
    exact ⟨y,yl,yf,out y yl yf⟩
  exact ⟨x,xl,xf,out x xl xf⟩


private theorem dist_level_exists (hc : G.Connected) (a : V) (n : ℕ) :
    ∀ k : ℕ, ∀ x : V,G.dist a x=k → n≤k → ∃ y : V,G.dist a y=n := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro x ax nk
    by_cases eq : n=k
    · exact ⟨x,ax.trans eq.symm⟩
    have pos : 0<k := by omega
    obtain ⟨p',hp⟩ := hc.exists_walk_length_eq_dist x a
    have ppos : 0<p'.length := by rw [hp,dist_comm,ax]; omega
    have prev {v w : V} (p : G.Walk v w) (h : 0<p.length) (min : p.length=G.dist w v) :
        ∃ y : V,G.dist w y+1=G.dist w v := by
      cases p with
      | nil => simp at h
      | @cons v y w e q =>
        refine ⟨y,?_⟩
        have z := G.dist_le q.reverse
        simp only [length_reverse] at z
        have tri := hc.dist_triangle (u:=w) (v:=y) (w:=v)
        have d := dist_eq_one_iff_adj.mpr e.symm
        simp only [length_cons] at min
        omega
    have hm : p'.length=G.dist a x := by rw [hp,dist_comm]
    obtain ⟨y,ay⟩ := prev p' ppos hm
    exact ih _ (by omega) y rfl (by omega)

theorem no_four_implies_T_shell_three (hc : G.Connected)
    (no : ∀ x : V,G.dist a x≠4) : F.T=F.shell 3 := by
  classical
  apply Subset.antisymm _ (filter_subset _ _)
  intro x xt
  have lo := F.T_depth hc xt
  have e : G.dist a x=3 := by
    by_contra n
    obtain ⟨z,hz⟩ := dist_level_exists hc a 4 (G.dist a x) x rfl (by omega)
    exact no z hz
  exact mem_filter.mpr ⟨xt,e⟩


theorem f_neighbors (s : f∈F.T) (hc : G.Connected) :
    G.neighborFinset f⊆insert b (F.L∪F.T.erase f) := by
  intro y yn
  have fy := (mem_neighborFinset G f y).mp yn
  rcases F.T_adj_boundary hc s fy with yl|yt|⟨_,yb⟩
  · exact mem_insert_of_mem (mem_union_left _ yl)
  · exact mem_insert_of_mem (mem_union_right _ (mem_erase.mpr ⟨fy.ne.symm,yt⟩))
  exact mem_insert.mpr (.inl yb)

include F in
theorem f_neighbors_b :
    G.neighborFinset f⊆insert b ((Shore C).erase f) := by
  intro y yn
  have fy := (mem_neighborFinset G f y).mp yn
  rcases shore_closed C f F.f_shore y fy with ya|yb|yc
  · exact (F.af (ya ▸ fy.symm)).elim
  · exact mem_insert.mpr (.inl yb)
  exact mem_insert_of_mem (mem_erase.mpr ⟨fy.ne.symm,yc⟩)

theorem T3_neighbors (hc : G.Connected) {x : V} (x3 : x∈F.shell 3) :
    G.neighborFinset x⊆ (F.L∪(F.shell 3).erase x∪F.shell 4)∪
      (if x=f then ({b} : Finset V) else ∅) := by
  classical
  intro y yn
  obtain ⟨xt,hi⟩ := mem_filter.mp x3
  have xy := (mem_neighborFinset G x y).mp yn
  rcases F.T_adj_boundary hc xt xy with yl|yt|⟨xf,yb⟩
  · exact mem_union_left _ (mem_union_left _ (mem_union_left _ yl))
  · have m := hc.dist_triangle (u:=a) (v:=x) (w:=y)
    have h := dist_eq_one_iff_adj.mpr xy
    have k := F.T_depth hc yt
    have cases' : G.dist a y=3 ∨ G.dist a y=4 := by omega
    rcases cases' with eq|eq
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _
        (mem_erase.mpr ⟨xy.ne.symm,mem_filter.mpr ⟨yt,eq⟩⟩)))
    exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨yt,eq⟩))
  exact mem_union_right _ (by rw [if_pos xf,mem_singleton]; exact yb)

theorem all_high_of_M_one (hc : G.Connected)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (D3 : (cutPorts D).card=3) (M1 : F.M.card=1) :
    (∀ x∈Shore C,5≤G.degree x) ∧ 5≤G.degree b := by
  obtain ⟨_,z,zd,low⟩ := order_four_of_one_visible hc conn D3 F.allD M1
  constructor
  · intro x xc
    exact (degree x z (fun e=>disjoint_left.mp (shore_disjoint F.neq) xc (e.symm ▸ zd))).resolve_right low
  exact (degree b z
    (fun e=>(shore_off D).2 (Eq.mp (congrArg (fun x : V=>x∈Shore D) e.symm) zd))).resolve_right low

theorem layers_le (hc : G.Connected) (two : G.dist a b=2)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (D3 : (cutPorts D).card=3) :
    2≤F.L.card ∧ 1≤F.M.card ∧
      F.L.card+F.M.card+(univ.filter (fun x : V=>G.dist a x=4)).card≤4 := by
  have v2 : 2≤F.L.card := by
    rcases degree p q F.p_q with hp|hq
    · have cap := F.port_degree_cap hc F.p_shore F.ap F.p_q (.inl ⟨rfl,rfl⟩)
      have c := card_le_card (show F.L.filter (G.Adj p)⊆F.L from filter_subset _ _)
      omega
    have cap := F.port_degree_cap hc F.q_shore F.aq F.p_q.symm (.inr ⟨rfl,rfl⟩)
    have c := card_le_card (show F.L.filter (G.Adj q)⊆F.L from filter_subset _ _)
    omega
  have m1 : 1≤F.M.card := by
    obtain ⟨x,xp⟩ := card_pos.mp (show 0<(cutPorts D).card by omega)
    have sz := card_le_card (show cutPorts D⊆Shore D from filter_subset _ _)
    have g := four_in_nonsingleton degree (show 2≤(Shore D).card by omega)
    exact second_positive_of_small_ports (shore_off D).1 ⟨x,(mem_filter.mp xp).1,F.allD x xp⟩
      hc g (by omega) (.inl rfl)
  have k := distance_two_at_cut_lower two F.neq
  change 1+F.L.card+F.M.card≤(DistanceTwo G a).card at k
  have t := four_layer_add_distance_two_le_five even a
  exact ⟨v2,m1,by omega⟩

end FiveMissShore33
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
