import PathFirst180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A spanning cycle is supplied by its degree-two edge set; deleting each
cycle edge leaves a connected spanning path. -/
structure CycleEdges (H : SimpleGraph V) [DecidableRel H.Adj] : Prop where
  two : ∀ x, H.degree x=2
  cut : ∀ {x y}, H.Adj x y → (H.deleteEdges {s(x,y)}).Connected

omit [DecidableEq V] in
private theorem cycle_neighbors (H : SimpleGraph V) [DecidableRel H.Adj] (circle : CycleEdges H) (x : V) :
    ∃ a b, H.Adj x a ∧ H.Adj x b ∧ a≠b := by
  obtain ⟨a,b,ha,hb,ab⟩ := one_lt_card_iff.mp (show 1<(H.neighborFinset x).card by rw [card_neighborFinset_eq_degree,circle.two]; decide)
  exact ⟨a,b,(H.mem_neighborFinset ..).mp ha,(H.mem_neighborFinset ..).mp hb,ab⟩

omit [DecidableEq V] in
private theorem cycle_order (H : SimpleGraph V) [DecidableRel H.Adj] (circle : CycleEdges H) :
    H.edgeFinset.card=Fintype.card V := by
  have total := H.sum_degrees_eq_twice_card_edges
  simp only [circle.two,sum_const,card_univ,smul_eq_mul] at total
  omega

private theorem cycle_parities (H : SimpleGraph V) [DecidableRel H.Adj] (circle : CycleEdges H)
    (P : Finset V) (cross : ∀ {i j}, H.Adj i j → (i∈P ↔ j∉P)) : 2*P.card=Fintype.card V := by
  classical
  have ind : Indep H P := fun _ h _ k _ e => (cross e).mp h k
  have count := independent_mass H P ind
  have cover : P.biUnion (fun v => H.incidenceFinset v)=H.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      constructor
      · intro h; obtain ⟨x,_,hx⟩ := mem_biUnion.mp h
        rw [H.incidenceFinset_eq_filter] at hx
        exact (mem_filter.mp hx).1
      · intro h
        by_cases ap : a∈P
        · exact mem_biUnion.mpr ⟨a,ap,by rw [H.incidenceFinset_eq_filter]; exact mem_filter.mpr ⟨h,by simp⟩⟩
        · exact mem_biUnion.mpr ⟨b,(cross (mem_edgeFinset.mp h).symm).mpr ap,by rw [H.incidenceFinset_eq_filter]; exact mem_filter.mpr ⟨h,by simp⟩⟩
  rw [cover,cycle_order H circle] at count
  simp only [circle.two,sum_const,smul_eq_mul] at count
  omega

private theorem cycle_cut_path (H : SimpleGraph V) [DecidableRel H.Adj] (circle : CycleEdges H) {a b : V}
    (ab : H.Adj a b) : let T := H.deleteEdges {s(a,b)}
    T.IsTree ∧ leaves T={a,b} := by
  classical
  let T := H.deleteEdges {s(a,b)}
  have fin : T.edgeFinset=H.edgeFinset.erase s(a,b) := by
    ext e
    induction e using Sym2.ind with
    | _ i j =>
      simp only [mem_edgeFinset,mem_erase,mem_edgeSet,T,deleteEdges_adj,Set.mem_singleton_iff]
      tauto
  have ec := card_erase_add_one (show s(a,b)∈H.edgeFinset from mem_edgeFinset.mpr ab)
  rw [←fin,cycle_order H circle] at ec
  have tree : T.IsTree := isTree_iff_connected_and_card.mpr ⟨circle.cut ab,by
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,←edgeFinset_card]; exact ec⟩
  have ends {i j : V} (edge : H.Adj i j) (same : s(i,j)=s(a,b)) : T.degree i=1 := by
    have eq : T.neighborFinset i=(H.neighborFinset i).erase j := by
      ext z
      simp only [mem_neighborFinset,mem_erase,T,deleteEdges_adj,Set.mem_singleton_iff,←same,Sym2.eq_iff]
      have ni := edge.ne
      tauto
    have c := card_erase_add_one ((H.mem_neighborFinset ..).mpr edge)
    rw [←eq,card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,circle.two] at c
    omega
  refine ⟨tree,?_⟩
  ext z
  change z∈leaves T ↔ z∈({a,b}:Finset V)
  simp only [leaves,mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
  by_cases za : z=a
  · subst z; exact ⟨fun _ => Or.inl rfl,fun _ => ends ab rfl⟩
  by_cases zb : z=b
  · subst z; exact ⟨fun _ => Or.inr rfl,fun _ => ends ab.symm (Sym2.eq_swap ..)⟩
  have eq : T.neighborFinset z=H.neighborFinset z := by
    ext t
    simp only [mem_neighborFinset,T,deleteEdges_adj,Set.mem_singleton_iff,Sym2.eq_iff]
    tauto
  have two := congrArg card eq
  rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,circle.two] at two
  exact ⟨fun h => (by have bad : (2:ℕ)=1 := two.symm.trans h; contradiction),
    fun h => (h.elim za zb).elim⟩

/-- Tightness one vertex below full bipartite order lets the cut cycle
read the independent mark of any nonroot vertex outside the parity class. -/
private theorem cycle_point (J H : SimpleGraph V) [DecidableRel H.Adj] (circle : CycleEdges H)
    (sub : H≤J) (hn : 1<Fintype.card V) (r : V) (P A : Finset V) (ai : Indep J A) (ne : A≠P)
    (cross : ∀ {i j}, H.Adj i j → (i∈P ↔ j∉P))
    (rank : bipartiteNum J+1=Fintype.card V)
    (tight : weightedLeaves J (eligible A P r)+bipartiteNum J=1+A.card+P.card)
    (q : V) (qr : q≠r) (qp : q∉P) :
    weightedLeaves J (eligible A P r)=if q∈A then 2 else 1 := by
  classical
  obtain ⟨a,b,qa,qb,ab⟩ := cycle_neighbors H circle q
  obtain ⟨z,qz,zr⟩ : ∃ z,H.Adj q z ∧ z≠r := by
    by_cases ar : a=r
    · exact ⟨b,qb,fun br => ab (ar.trans br.symm)⟩
    · exact ⟨a,qa,ar⟩
  have zp : z∈P := (cross qz.symm).mpr qp
  let T := H.deleteEdges {s(q,z)}
  have th : T≤H := H.deleteEdges_le _
  obtain ⟨tr,lf⟩ := cycle_cut_path H circle qz
  change leaves T={q,z} at lf
  have intr : r∉leaves T := by rw [lf]; simp [qr.symm,zr.symm]
  obtain ⟨opt,_,_⟩ := one_defect_rigid J T tr (th.trans sub) hn r intr A P ai ne (fun e => cross (th e)) rank tight
  rw [←opt,lf]
  have zu : z∈eligible A P r := eligible_iff.mpr ⟨Or.inr zp,Or.inl zr⟩
  by_cases qa : q∈A
  · have qu : q∈eligible A P r := eligible_iff.mpr ⟨Or.inl qa,Or.inl qr⟩
    rw [if_pos qa,inter_eq_right.mpr (insert_subset qu (singleton_subset_iff.mpr zu)),card_pair qz.ne]
  · have qu : q∉eligible A P r := fun h => (eligible_iff.mp h).1.elim qa qp
    have eq : eligible A P r∩{q,z}={z} := by ext x; simp only [mem_inter,mem_insert,mem_singleton]; aesop
    rw [if_neg qa,eq,card_singleton]

/-- In a tight nonconfined lower graph of bipartite order n-1 containing a
spanning alternating cycle, every crossing common middle of a deep chord is eligible. -/
theorem cycle_forces_middle (J H : SimpleGraph V) [DecidableRel H.Adj] (circle : CycleEdges H)
    (hn : 1<Fintype.card V) (r u v w : V) (odd : Bool) (A : Finset V)
    (sub : H≤alternating J (parity J r odd))
    (ai : Indep (J⊔SimpleGraph.edge u v) A) (nc : ¬A⊆parity J r odd) (uv : u≠v)
    (deep : 2≤J.dist u r) (deepv : 2≤J.dist v r)
    (uw : (alternating J (parity J r odd)).Adj u w) (vw : (alternating J (parity J r odd)).Adj v w)
    (rank : bipartiteNum J+1=Fintype.card V)
    (tight : weightedLeaves J (eligible A (parity J r odd) r)+bipartiteNum J=1+A.card+(parity J r odd).card) :
    w∈eligible A (parity J r odd) r := by
  classical
  let P := parity J r odd
  change ¬A⊆P at nc
  change weightedLeaves J (eligible A P r)+bipartiteNum J=1+A.card+P.card at tight
  have cross {i j} (e : H.Adj i j) : i∈P ↔ j∉P := (sub e).2
  have ij : Indep J A := fun x hx y hy neq e => ai x hx y hy neq (Or.inl e)
  have point := cycle_point J H circle (fun _ _ e => (sub e).1) hn r P A ij (fun eq => nc eq.le) cross rank tight
  have wr : w≠r := by rintro rfl; rw [dist_eq_one_iff_adj.mpr uw.1] at deep; omega
  by_contra no
  have wp : w∉P := fun h => no (eligible_iff.mpr ⟨Or.inr h,Or.inl wr⟩)
  have wa : w∉A := fun h => no (eligible_iff.mpr ⟨Or.inl h,Or.inl wr⟩)
  have low := point w wr wp
  rw [if_neg wa] at low
  have only (x:V) (xa:x∈A) (xp:x∉P) : x=r := by
    by_contra xr
    have other := point x xr xp
    rw [if_pos xa] at other
    omega
  obtain ⟨j,ja,jp⟩ := not_subset.mp nc
  have jr := only j ja jp
  subst j
  have diff : A\P={r} := by
    ext z
    constructor
    · intro h; exact mem_singleton.mpr (only z (mem_sdiff.mp h).1 (mem_sdiff.mp h).2)
    · rintro h; obtain rfl := mem_singleton.mp h; exact mem_sdiff.mpr ⟨ja,jp⟩
  have aCount := card_sdiff_add_card_inter A P
  rw [diff,card_singleton] at aCount
  have pCount := card_sdiff_add_card_inter P A
  rw [inter_comm P A] at pCount
  have halves := cycle_parities H circle P cross
  have diffCount : (P\A).card=2 := by omega
  obtain ⟨s,t,rs,rt,st⟩ := cycle_neighbors H circle r
  have miss (z:V) (rz:H.Adj r z) : z∈P\A := mem_sdiff.mpr
    ⟨(cross rz.symm).mpr jp,fun za => ij r ja z za rz.ne (sub rz).1⟩
  have pair : ({s,t}:Finset V)=P\A := eq_of_subset_of_card_le (insert_subset (miss s rs) (singleton_subset_iff.mpr (miss t rt)))
    (by rw [card_pair st,diffCount])
  have marked_tip (x : V) (xp : x∈P) (d : 2≤J.dist x r) : x∈A := by
    by_contra xa
    have outside := mem_sdiff.mpr ⟨xp,xa⟩
    rw [←pair] at outside
    have rx : J.Adj r x := by
      rcases (show x=s ∨ x=t by simpa using outside) with rfl|rfl
      · exact (sub rs).1
      · exact (sub rt).1
    rw [dist_eq_one_iff_adj.mpr rx.symm] at d
    omega
  exact ai u (marked_tip u (uw.2.mpr wp) deep) v (marked_tip v (vw.2.mpr wp) deepv) uv
    (Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,uv⟩))

private theorem cycle_alternatives (J H : SimpleGraph V) [DecidableRel H.Adj] (circle : CycleEdges H)
    (sub : H≤J) (r u v w : V) (uv : u≠v) (old : ¬J.Adj u v)
    (wr : w≠r) (ur : u≠r) (vr : v≠r) (far : ¬J.Adj r u) :
    ∃ a b, a≠b ∧ H.Adj a u ∧ H.Adj b v ∧ a≠w ∧ b≠w := by
  classical
  have alternate (x : V) : ∃ z,H.Adj x z ∧ z≠w := by
    obtain ⟨i,j,xi,xj,ij⟩ := cycle_neighbors H circle x
    by_cases h : i=w
    · exact ⟨j,xj,fun jw => ij (h.trans jw.symm)⟩
    · exact ⟨i,xi,h⟩
  obtain ⟨z,uz,zw⟩ := alternate u
  obtain ⟨t,vt,tw⟩ := alternate v
  by_contra deny
  have same {a b : V} (ua:H.Adj u a) (vb:H.Adj v b) (aw:a≠w) (bw:b≠w) : a=b :=
    Classical.byContradiction (fun ab => deny ⟨a,b,ab,ua.symm,vb.symm,aw,bw⟩)
  obtain rfl := same uz vt zw tw
  have first {i j : V} (ij:H.Adj i j) (jw:j≠w)
      (cover:∀ y,H.Adj i y → y≠w → y=j) : H.neighborFinset i={j,w} := by
    apply eq_of_subset_of_card_le
    · intro y hy
      by_cases yw : y=w
      · simp [yw]
      · simp [cover y ((H.mem_neighborFinset ..).mp hy) yw]
    · rw [card_pair jw,card_neighborFinset_eq_degree,circle.two]
  have nu := first uz zw (fun _ e h => same e vt h tw)
  have nv := first vt tw (fun _ e h => (same uz e zw h).symm)
  have uw : H.Adj u w := (H.mem_neighborFinset ..).mp (nu ▸ mem_insert_of_mem (mem_singleton_self _))
  have vw : H.Adj v w := (H.mem_neighborFinset ..).mp (nv ▸ mem_insert_of_mem (mem_singleton_self _))
  have reverse {i : V} (ui:H.Adj u i) (vi:H.Adj v i) : H.neighborFinset i={u,v} := by
    symm
    apply eq_of_subset_of_card_le (insert_subset ((H.mem_neighborFinset ..).mpr ui.symm) (singleton_subset_iff.mpr ((H.mem_neighborFinset ..).mpr vi.symm)))
    rw [card_neighborFinset_eq_degree,circle.two,card_pair uv]
  have nw := reverse uw vw
  have nz := reverse uz vt
  let S := ({u,v,w,z}:Finset V)
  have closed {a b : V} (h:a∈S) (e:H.Adj a b) : b∈S := by
    have nb := (H.mem_neighborFinset ..).mpr e
    simp only [S,mem_insert,mem_singleton] at h ⊢
    rcases h with rfl|rfl|rfl|rfl <;> first | rw [nu] at nb | rw [nv] at nb | rw [nw] at nb | rw [nz] at nb
    all_goals simp only [mem_insert,mem_singleton] at nb
    all_goals tauto
  have stay {a b : V} (p:H.Walk a b) : a∈S → b∈S := by
    induction p with
    | nil => exact id
    | cons e _ ih => exact fun h => ih (closed h e)
  obtain ⟨p⟩ := ((circle.cut uz).mono (H.deleteEdges_le _)) u r
  have entry := stay p (show u∈S by simp [S])
  have zr : z≠r := fun eq => far (eq ▸ (sub uz).symm)
  simp [S,ur.symm,vr.symm,wr.symm,zr.symm] at entry

/-- A rank-critical, tight lower graph one vertex short of full bipartite
order forces the first form for a deep flat chord whenever its crossing graph
contains a spanning cycle and the tips have a crossing common neighbor. -/
theorem cycle_forces_first (J H : SimpleGraph V) [DecidableRel J.Adj] [DecidableRel H.Adj]
    (circle : CycleEdges H) (jc : J.Connected) (hn : 3<Fintype.card V) (r u v w : V)
    (uv : u≠v) (old : ¬J.Adj u v) (odd : Bool) (A : Finset V)
    (ai : Indep (J⊔SimpleGraph.edge u v) A) (flat : J.dist u r=J.dist v r) (deep : 3≤J.dist u r)
    (sub : H≤alternating J (parity J r odd))
    (uw : (alternating J (parity J r odd)).Adj u w) (vw : (alternating J (parity J r odd)).Adj v w)
    (rank : bipartiteNum J+1=Fintype.card V)
    (drop : bipartiteNum J=bipartiteNum (J⊔SimpleGraph.edge u v)+1)
    (tight : weightedLeaves J (eligible A (parity J r odd) r)+bipartiteNum J=1+A.card+(parity J r odd).card) :
    ∀ w', J.Adj u w' → J.Adj v w' → FirstForm J (eligible A (parity J r odd) r) u v w' := by
  classical
  let P := parity J r odd
  let U := eligible A P r
  suffices cert : FirstForm J U u v w by
    intro other uo vo
    exact (first_iff_erased_gain J jc (by omega) u v other uv old uo vo.symm U).mpr
      ((first_iff_erased_gain J jc (by omega) u v w uv old uw.1 vw.1.symm U).mp cert)
  by_cases ap : A⊆P
  · exact confined_crossing_first J jc (by omega) r u v w uv old flat odd A ai ap uw vw drop tight
  have Vdeep : 3≤J.dist v r := flat ▸ deep
  have mark := cycle_forces_middle J H circle (by omega) r u v w odd A sub ai ap uv (by omega) (by omega) uw vw rank tight
  have far {x:V} (d:2≤J.dist x r) : x≠r ∧ ¬J.Adj r x := by
    refine ⟨?_,?_⟩
    · rintro rfl; rw [dist_self] at d; omega
    · intro e; rw [dist_eq_one_iff_adj.mpr e.symm] at d; omega
  have nb {x z:V} (d:3≤J.dist x r) (e:J.Adj x z) : 2≤J.dist z r := by
    have bound := jc.dist_triangle (u:=x) (v:=z) (w:=r)
    rw [dist_eq_one_iff_adj.mpr e] at bound
    omega
  have wr := (far (nb deep uw.1)).1
  obtain ⟨a,b,ab,au,bv,aw,bw⟩ := cycle_alternatives J H circle (fun _ _ e => (sub e).1) r u v w uv old wr
    (far (by omega : 2≤J.dist u r)).1 (far (by omega : 2≤J.dist v r)).1 (far (by omega : 2≤J.dist u r)).2
  obtain ⟨s,t,rs,rt,st⟩ := cycle_neighbors H circle r
  have root : 2≤J.degree r := by
    have keep : ({s,t}:Finset V)⊆J.neighborFinset r :=
      insert_subset ((J.mem_neighborFinset ..).mpr (sub rs).1) (singleton_subset_iff.mpr ((J.mem_neighborFinset ..).mpr (sub rt).1))
    simpa only [card_pair st,card_neighborFinset_eq_degree] using card_le_card keep
  apply first_on_separated_path J jc hn r a u w v b odd A (fun x hx y hy neq e => ai x hx y hy neq (Or.inl e))
    (fun eq => ap eq.le) uv ab old (sub au) uw vw (sub bv) _ _ root wr (Or.inl (by omega)) (Or.inl mark) tight
  · intro x hx
    have av : a≠v := fun e => old (e ▸ (sub au).1.symm)
    have bu : b≠u := fun e => old (e ▸ (sub bv).1)
    rcases (show x=a ∨ x=b by simpa using hx) with rfl|rfl
    · simp [au.ne,av,aw]
    · simp [bu,bv.ne,bw]
  · intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · exact far (nb deep (sub au).1.symm)
    · exact far (nb Vdeep (sub bv).1.symm)
    · exact far (by omega)
    · exact far (by omega)

/-- Without any cycle hypothesis, a tight mark constrains the actual
crossing degree at every marked vertex of parity opposite to the root.
When the root is also marked their degree surpluses share the same budget. -/
theorem opposite_degree_budget (J : SimpleGraph V) (jc : J.Connected) (hn : 1<Fintype.card V)
    (r q : V) (odd : Bool) (A : Finset V) (ai : Indep J A) (ne : A≠parity J r odd)
    (two : ∃ s t,J.Adj r s ∧ J.Adj r t ∧ s≠t)
    (oq : r∈parity J r odd ↔ q∉parity J r odd) (qm : q∈A∪parity J r odd)
    (tight : weightedLeaves J (eligible A (parity J r odd) r)+bipartiteNum J=1+A.card+(parity J r odd).card) :
    let K := alternating J (parity J r odd)
    letI := Classical.decRel K.Adj
    bipartiteNum J+K.degree q≤Fintype.card V+1 ∧
      (r∈A∪parity J r odd → bipartiteNum J+K.degree q+K.degree r≤Fintype.card V+3) := by
  classical
  let P := parity J r odd
  let K := alternating J P
  let D := (A∪P)\(A∩P)
  have opp {a b} (e : K.Adj a b) : a∈P ↔ b∉P := e.2
  change r∈P ↔ q∉P at oq
  have qr : q≠r := by intro eq; subst q; tauto
  let p (x:V) := if K.Adj r x then r else q
  let d (x:V) := if x=q then 0 else if x=r then 1 else 2
  have down (x:V) (xq:x≠q) : d (p x)<d x := by
    by_cases xr : x=r
    · subst x; simp [p,d,qr.symm]
    by_cases rx : K.Adj r x <;> simp [p,d,rx,xr,xq,qr.symm]
  obtain ⟨F,ft,fe⟩ := virtual_tree q p d down
  obtain ⟨T,tk,tr,keep⟩ := keep_target K F (alternating_parity J jc r odd).1 ft
  have qstar {x} (qx:K.Adj q x) : T.Adj q x := by
    have nr : ¬K.Adj r x := by intro rx; have := opp qx; have := opp rx; tauto
    exact keep ⟨qx,(show F.Adj x q by simpa only [p,if_neg nr] using fe x qx.ne.symm).symm⟩
  have rstar {x} (rx:K.Adj r x) : T.Adj r x := by
    by_cases xq : x=q
    · subst x; exact (qstar rx.symm).symm
    exact keep ⟨rx,(show F.Adj x r by simpa only [p,if_pos rx] using fe x xq).symm⟩
  obtain ⟨a,b,ra,rb,ab⟩ := two
  have rootEdges := (alternating_parity J jc r odd).2
  have intr : r∉leaves T := fun lf => ab (leaf_unique T lf (rstar (rootEdges a ra)) (rstar (rootEdges b rb)))
  have deg (z : V) (keep : ∀ x,K.Adj z x → T.Adj z x) : K.degree z≤T.degree z := by
    rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
    exact card_le_card (fun x h => (T.mem_neighborFinset ..).mpr (keep x ((K.mem_neighborFinset ..).mp h)))
  have dq := deg q (fun _ e => qstar e)
  have dr := deg r (fun _ e => rstar e)
  have pos : D.Nonempty := by
    by_contra! no
    apply ne
    ext x
    have out : x∉D := fun h => no ⟨x,h⟩
    change x∈A ↔ x∈P
    simp only [D,mem_sdiff,mem_union,mem_inter] at out
    tauto
  have c := forest_strict T tr D pos
  have tj : T≤J := fun _ _ e => (tk e).1
  have ident := tree_defect T tr hn r intr A P (fun x hx y hy neq e => ai x hx y hy neq (tj e)) (fun e => (tk e).2)
  change Fintype.card V+_+(T.edgeFinset∩D.sym2).card=1+A.card+P.card+D.card+_ at ident
  have cap := score_of_tree J T tj tr (eligible A P r)
  change weightedLeaves J (eligible A P r)+bipartiteNum J=1+A.card+P.card at tight
  have term := single_le_sum (f:=fun v => T.degree v-2) (fun _ _ => Nat.zero_le _) qm
  change T.degree q-2≤∑ x∈A∪P,(T.degree x-2) at term
  change bipartiteNum J+K.degree q≤Fintype.card V+1 ∧ (r∈A∪P → bipartiteNum J+K.degree q+K.degree r≤Fintype.card V+3)
  refine ⟨by omega,?_⟩
  intro rm
  have both := sum_le_sum_of_subset_of_nonneg (f:=fun v => T.degree v-2)
    (insert_subset qm (singleton_subset_iff.mpr rm)) (fun _ _ _ => Nat.zero_le _)
  rw [sum_insert (by simpa using qr : q∉({r}:Finset V)),sum_singleton] at both
  change (T.degree q-2)+(T.degree r-2)≤∑ x∈A∪P,(T.degree x-2) at both
  omega

/-- In a tight one-defect state, a spanning cycle uses every crossing
edge if all vertices of parity opposite to the root are marked. -/
theorem tight_cycle_exhausts_crossing (J H : SimpleGraph V) [DecidableRel H.Adj]
    (circle : CycleEdges H) (jc : J.Connected) (hn : 1<Fintype.card V) (r : V) (odd : Bool)
    (A : Finset V) (ai : Indep J A) (ne : A≠parity J r odd)
    (sub : H≤alternating J (parity J r odd))
    (marked : ∀ q, (r∈parity J r odd ↔ q∉parity J r odd) → q∈A∪parity J r odd)
    (rank : bipartiteNum J+1=Fintype.card V)
    (tight : weightedLeaves J (eligible A (parity J r odd) r)+bipartiteNum J=1+A.card+(parity J r odd).card) :
    alternating J (parity J r odd)≤H := by
  classical
  let P := parity J r odd
  let K := alternating J P
  have opp {a b} (e : K.Adj a b) : a∈P ↔ b∉P := e.2
  have star (q : V) (oq : r∈P ↔ q∉P) : K.neighborFinset q⊆H.neighborFinset q := by
    obtain ⟨a,b,ra,rb,ab⟩ := cycle_neighbors H circle r
    have bound := (opposite_degree_budget J jc hn r q odd A ai ne ⟨a,b,(sub ra).1,(sub rb).1,ab⟩ oq (marked q oq) tight).1
    change bipartiteNum J+K.degree q≤Fintype.card V+1 at bound
    have h0 : H.neighborFinset q⊆K.neighborFinset q :=
      fun x h => (K.mem_neighborFinset ..).mpr (sub ((H.mem_neighborFinset ..).mp h))
    have eq := eq_of_subset_of_card_le h0 (by
      rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,circle.two]
      omega)
    exact eq.ge
  intro a b e
  change K.Adj a b at e
  by_cases oa : r∈P ↔ a∉P
  · exact (H.mem_neighborFinset ..).mp (star a oa ((K.mem_neighborFinset ..).mpr e))
  · have ab := opp e
    have ob : r∈P ↔ b∉P := by tauto
    exact ((H.mem_neighborFinset ..).mp (star b ob ((K.mem_neighborFinset ..).mpr e.symm))).symm

/-- For a nonconfined tight mark at deficit one, an alternating spanning
cycle is the entire crossing graph. No chord or common middle is assumed. -/
theorem nonconfined_cycle_is_all (J H : SimpleGraph V) [DecidableRel H.Adj]
    (circle : CycleEdges H) (jc : J.Connected) (hn : 1<Fintype.card V) (r : V) (odd : Bool)
    (A : Finset V) (ai : Indep J A) (nc : ¬A⊆parity J r odd)
    (sub : H≤alternating J (parity J r odd))
    (rank : bipartiteNum J+1=Fintype.card V)
    (tight : weightedLeaves J (eligible A (parity J r odd) r)+bipartiteNum J=1+A.card+(parity J r odd).card) :
    H=alternating J (parity J r odd) := by
  classical
  let P := parity J r odd
  change ¬A⊆P at nc
  obtain ⟨j,ja,jp⟩ := not_subset.mp nc
  have cross {x y} (e:H.Adj x y) : x∈P ↔ y∉P := (sub e).2
  have ne : A≠P := fun eq => nc eq.le
  have point := cycle_point J H circle (fun _ _ e => (sub e).1) hn r P A ai ne cross rank tight
  apply le_antisymm sub (tight_cycle_exhausts_crossing J H circle jc hn r odd A ai ne sub _ rank tight)
  intro q oq
  by_cases qp : q∈P
  · exact mem_union_right _ qp
  have rp := oq.mpr qp
  have qr : q≠r := fun eq => qp (eq ▸ rp)
  have jr : j≠r := fun eq => jp (eq ▸ rp)
  have low := point j jr jp
  rw [if_pos ja] at low
  by_contra no
  have qa : q∉A := fun h => no (mem_union_left _ h)
  have bad := point q qr qp
  rw [if_neg qa] at bad
  omega

/-- Away from any three specified vertices there is a cycle edge once
the order exceeds six, by counting their incident edge sets. -/
private theorem unused_cycle_edge (H : SimpleGraph V) [DecidableRel H.Adj] (circle : CycleEdges H)
    (hn : 6<Fintype.card V) (r u v : V) :
    ∃ a b,H.Adj a b ∧ a∉({r,u,v}:Finset V) ∧ b∉({r,u,v}:Finset V) := by
  classical
  let S := H.incidenceFinset r∪H.incidenceFinset u∪H.incidenceFinset v
  have size : S.card≤6 := by
    have l := card_union_le (H.incidenceFinset r) (H.incidenceFinset u)
    have h := card_union_le (H.incidenceFinset r∪H.incidenceFinset u) (H.incidenceFinset v)
    simp only [card_incidenceFinset_eq_degree,circle.two] at l h
    change (H.incidenceFinset r∪H.incidenceFinset u∪H.incidenceFinset v).card≤6
    omega
  have nsub : ¬H.edgeFinset⊆S := fun h => by have := card_le_card h; rw [cycle_order H circle] at this; omega
  obtain ⟨e,he,no⟩ := not_subset.mp nsub
  induction e using Sym2.ind with
  | _ a b =>
    have out (x:V) (hx:x∈({r,u,v}:Finset V)) : x∉s(a,b) := by
      intro mem
      have inc : s(a,b)∈H.incidenceFinset x := by rw [H.incidenceFinset_eq_filter]; exact mem_filter.mpr ⟨he,mem⟩
      apply no
      simp only [S,mem_union]
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl|rfl|rfl
      · exact Or.inl (Or.inl inc)
      · exact Or.inl (Or.inr inc)
      · exact Or.inr inc
    exact ⟨a,b,mem_edgeFinset.mp he,fun h => out a h (by simp),fun h => out b h (by simp)⟩

/-- At order seven and above, depth two already suffices. In particular
this includes every alternating-Hamiltonian instance with eccentricity at
least four and tip depth at least two. -/
theorem cycle_first_depth_two (J H : SimpleGraph V) [DecidableRel H.Adj]
    (circle : CycleEdges H) (jc : J.Connected) (hn : 6<Fintype.card V) (r u v w : V)
    (uv : u≠v) (old : ¬J.Adj u v) (odd : Bool) (A : Finset V)
    (ai : Indep (J⊔SimpleGraph.edge u v) A) (flat : J.dist u r=J.dist v r) (deep : 2≤J.dist u r)
    (sub : H≤alternating J (parity J r odd))
    (uw : (alternating J (parity J r odd)).Adj u w) (vw : (alternating J (parity J r odd)).Adj v w)
    (rank : bipartiteNum J+1=Fintype.card V)
    (drop : bipartiteNum J=bipartiteNum (J⊔SimpleGraph.edge u v)+1)
    (tight : weightedLeaves J (eligible A (parity J r odd) r)+bipartiteNum J=1+A.card+(parity J r odd).card) :
    ∀ w', J.Adj u w' → J.Adj v w' → FirstForm J (eligible A (parity J r odd) r) u v w' := by
  classical
  let P := parity J r odd
  let U := eligible A P r
  suffices cert : FirstForm J U u v w by
    intro other uo vo
    exact (first_iff_erased_gain J jc (by omega) u v other uv old uo vo.symm U).mpr
      ((first_iff_erased_gain J jc (by omega) u v w uv old uw.1 vw.1.symm U).mp cert)
  by_cases ap : A⊆P
  · exact confined_crossing_first J jc (by omega) r u v w uv old flat odd A ai ap uw vw drop tight
  have dv : 2≤J.dist v r := flat ▸ deep
  have mark := cycle_forces_middle J H circle (by omega) r u v w odd A sub ai ap uv deep dv uw vw rank tight
  have ne : A≠P := fun e => ap e.le
  have ij : Indep J A := fun x hx y hy neq e => ai x hx y hy neq (Or.inl e)
  have cross {x y} (e:H.Adj x y) : x∈P ↔ y∉P := (sub e).2
  have equal := (nonconfined_cycle_is_all J H circle jc (by omega) r odd A ij ap sub rank tight).ge
  obtain ⟨a,b,ab,af,bf⟩ := unused_cycle_edge H circle hn r u v
  simp only [mem_insert,mem_singleton,not_or] at af bf
  let T := H.deleteEdges {s(a,b)}
  obtain ⟨tr,lf⟩ := cycle_cut_path H circle ab
  change leaves T={a,b} at lf
  have safe (z:V) (za:z≠a) (zb:z≠b) : z∉leaves T := by rw [lf]; simp [za,zb]
  have intr := safe r (Ne.symm af.1) (Ne.symm bf.1)
  have th : T≤H := H.deleteEdges_le _
  have tj : T≤J := fun _ _ e => (sub (th e)).1
  obtain ⟨opt,two,_⟩ := one_defect_rigid J T tr tj (by omega) r intr A P ij ne (fun e => cross (th e)) rank tight
  have tu : T.Adj u w := deleteEdges_adj.mpr ⟨equal uw,by simp [Sym2.eq_iff,Ne.symm af.2.1,Ne.symm bf.2.1]⟩
  have tv : T.Adj v w := deleteEdges_adj.mpr ⟨equal vw,by simp [Sym2.eq_iff,Ne.symm af.2.2,Ne.symm bf.2.2]⟩
  apply first_of_tree J T (by omega) u v w uv old tr tj U opt tu tv mark (two w (mem_union.mpr (eligible_iff.mp mark).1))
  intro z zt _
  rcases (show z=u ∨ z=v by simpa using zt) with rfl|rfl
  · exact safe z (Ne.symm af.2.1) (Ne.symm bf.2.1)
  · exact safe z (Ne.symm af.2.2) (Ne.symm bf.2.2)

#print axioms opposite_degree_budget
#print axioms nonconfined_cycle_is_all
#print axioms tight_cycle_exhausts_crossing
#print axioms cycle_first_depth_two
#print axioms cycle_forces_first
#print axioms cycle_forces_middle
end Minimal180
