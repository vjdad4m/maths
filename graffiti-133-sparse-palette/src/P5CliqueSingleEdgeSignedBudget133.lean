import P5CliqueFourConsecutivePorts133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- In the one-edge palette, a full-score single-site client at an isolated
port must see an exterior vertex touching the other isolated port. -/
theorem one_edge_palette_high_isolate_dichotomy
    (h4 : FourCycleFree G) (D : Finset V) (a b c d : V)
    (am : a∈D) (bm : b∈D) (cm : c∈D) (dm : d∈D)
    (ab : a≠b) (ac : a≠c) (ad : a≠d) (bd : b≠d) (cd : c≠d)
    (bc : G.Adj b c)
    (attach : ∀ q∉D,∃ t∈({a,b,c,d}:Finset V),G.Adj q t)
    (palette : ∀ q∉D,∀ p∈D,G.Adj q p→p∈({a,b,c,d}:Finset V))
    (q : V) (qo : q∉D) (high : 3<localIndependence G q) :
    (G.Adj q a ∧ G.Adj q d) ∨
      (G.Adj q a ∧ ¬G.Adj q d ∧ ∃ w∉D,G.Adj q w ∧ G.Adj w d) ∨
      (G.Adj q d ∧ ¬G.Adj q a ∧ ∃ w∉D,G.Adj q w ∧ G.Adj w a) := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let P : Finset V := {a,b,c,d}
  have ps : P⊆D := by
    intro x xm
    simp only [P,Finset.mem_insert,Finset.mem_singleton] at xm
    rcases xm with rfl|rfl|rfl|rfl <;> assumption
  have pc : P.card=4 := by simp [P,ab,ac,ad,bc.ne,bd,cd]
  have bp : b∈P := by simp [P]
  have cp : c∈P := by simp [P]
  have att := attach
  choose tag htag using att
  let f (q : V) := if h : q∉D then tag q h else q
  have pick (q : V) (qo : q∉D) : f q∈P ∧ G.Adj q (f q) := by simpa only [f,dif_pos qo] using htag q qo
  have pickD (q : V) (qo : q∉D) : f q∈D ∧ G.Adj q (f q) := ⟨ps (pick q qo).1,(pick q qo).2⟩
  have qb : ¬G.Adj q b := fun e=>(not_le_of_gt high)
    (outside_independence_le_of_nonisolated_port h4 D f pickD P pc palette q qo b c bm cm cp e bc)
  have qc : ¬G.Adj q c := fun e=>(not_le_of_gt high)
    (outside_independence_le_of_nonisolated_port h4 D f pickD P pc palette q qo c b cm bm bp e bc.symm)
  have yes : G.Adj q a ∨ G.Adj q d := by
    obtain ⟨p,pm,qp⟩ := attach q qo
    simp only [Finset.mem_insert,Finset.mem_singleton] at pm
    rcases pm with rfl|rfl|rfl|rfl
    · exact Or.inl qp
    · exact (qb qp).elim
    · exact (qc qp).elim
    · exact Or.inr qp
  let N := (D.filter (G.Adj q))∪((Q.filter (G.Adj q)).image f)
  have sub : N⊆P := by
    apply Finset.union_subset
    · intro v vm
      exact palette q qo v (Finset.mem_filter.mp vm).1 (Finset.mem_filter.mp vm).2
    · intro v vm
      obtain ⟨w,wm,rfl⟩ := Finset.mem_image.mp vm
      exact (pick w (Finset.mem_sdiff.mp (Finset.mem_filter.mp wm).1).2).1
  have full := outside_independence_le_core_neighbors_union_assigned_ports h4 D f pickD q qo
  change localIndependence G q≤N.card at full
  have eq : N=P := Finset.eq_of_subset_of_card_le sub (by omega)
  have witness (i : V) (ip : i∈P) (qi : ¬G.Adj q i) :
      ∃ w∉D,G.Adj q w ∧ G.Adj w i := by
    have im : i∈N := eq.symm ▸ ip
    rcases Finset.mem_union.mp im with ind|out
    · exact (qi (Finset.mem_filter.mp ind).2).elim
    obtain ⟨w,wm,e⟩ := Finset.mem_image.mp out
    have wo := (Finset.mem_sdiff.mp (Finset.mem_filter.mp wm).1).2
    exact ⟨w,wo,(Finset.mem_filter.mp wm).2,e ▸ (pick w wo).2⟩
  by_cases qa : G.Adj q a
  · by_cases qd : G.Adj q d
    · exact Or.inl ⟨qa,qd⟩
    · exact Or.inr (Or.inl ⟨qa,qd,witness d (by simp [P]) qd⟩)
  · exact Or.inr (Or.inr ⟨yes.resolve_left qa,qa,witness a (by simp [P]) qa⟩)

#print axioms one_edge_palette_high_isolate_dichotomy
/-- Nondeficient recipients of a forced cross-isolate edge from a high client. -/
noncomputable def oneEdgeBadReceivers (G : SimpleGraph V) (D : Finset V) (a d : V) : Finset V :=
  ((Finset.univ : Finset V)\D).filter (fun w=>2<localIndependence G w ∧
    ∃ q∉D, 3<localIndependence G q ∧ G.Adj q w ∧
      ((G.Adj q a ∧ ¬G.Adj q d ∧ G.Adj w d) ∨ (G.Adj q d ∧ ¬G.Adj q a ∧ G.Adj w a)))

noncomputable def doubleIsolateClients (G : SimpleGraph V) (D : Finset V) (a d : V) : Finset V :=
  ((Finset.univ : Finset V)\D).filter (fun q=>G.Adj q a ∧ G.Adj q d)

theorem one_edge_palette_signed_outer_budget
    (h4 : FourCycleFree G) (D : Finset V) (a b c d : V)
    (am : a∈D) (bm : b∈D) (cm : c∈D) (dm : d∈D)
    (ab : a≠b) (ac : a≠c) (ad : a≠d) (bd : b≠d) (cd : c≠d)
    (bc : G.Adj b c)
    (attach : ∀ q∉D,∃ t∈({a,b,c,d}:Finset V),G.Adj q t)
    (palette : ∀ q∉D,∀ p∈D,G.Adj q p→p∈({a,b,c,d}:Finset V)) :
    let Q := (Finset.univ : Finset V)\D
    (∑ q∈Q,localIndependence G q)≤3*Q.card+
      (oneEdgeBadReceivers G D a d).card+2*(doubleIsolateClients G D a d).card := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let P : Finset V := {a,b,c,d}
  let H := Q.filter (fun q=>3<localIndependence G q)
  let L := Q.filter (fun q=>localIndependence G q≤2)
  let A := Q.filter (fun q=>3<localIndependence G q ∧ G.Adj q a ∧ ¬G.Adj q d)
  let Z := Q.filter (fun q=>3<localIndependence G q ∧ G.Adj q d ∧ ¬G.Adj q a)
  let X := doubleIsolateClients G D a d
  let B := oneEdgeBadReceivers G D a d
  have qo (q : V) (m : q∈Q) : q∉D := (Finset.mem_sdiff.mp m).2
  have getA (q : {q // q∈A}) :
      ∃ w∈Q,G.Adj q.val w ∧ G.Adj w d := by
    obtain ⟨qQ,high,qa,qd⟩ := Finset.mem_filter.mp q.property
    rcases one_edge_palette_high_isolate_dichotomy h4 D a b c d am bm cm dm ab ac ad bd cd bc
      attach palette q.val (qo _ qQ) high with h|h|h
    · exact (qd h.2).elim
    · obtain ⟨w,wo,qw,wd⟩ := h.2.2
      exact ⟨w,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,wo⟩,qw,wd⟩
    · exact (h.2.1 qa).elim
  have getZ (q : {q // q∈Z}) :
      ∃ w∈Q,G.Adj q.val w ∧ G.Adj w a := by
    obtain ⟨qQ,high,qd,qa⟩ := Finset.mem_filter.mp q.property
    rcases one_edge_palette_high_isolate_dichotomy h4 D a b c d am bm cm dm ab ac ad bd cd bc
      attach palette q.val (qo _ qQ) high with h|h|h
    · exact (qa h.1).elim
    · exact (h.2.1 qd).elim
    · obtain ⟨w,wo,qw,wa⟩ := h.2.2
      exact ⟨w,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,wo⟩,qw,wa⟩
  choose f fQ fq fd using getA
  choose g gQ gq ga using getZ
  let F := Finset.univ.image f
  let J := Finset.univ.image g
  have finj : Function.Injective f := by
    intro x y e
    obtain ⟨_,_,xa,_⟩ := Finset.mem_filter.mp x.property
    obtain ⟨_,_,ya,_⟩ := Finset.mem_filter.mp y.property
    apply Subtype.ext
    exact h4 a (f x) x.val y.val (fun eq=>qo (f x) (fQ x) (eq ▸ am))
      xa.symm (fq x).symm ya.symm (e.symm ▸ (fq y).symm)
  have ginj : Function.Injective g := by
    intro x y e
    obtain ⟨_,_,xd,_⟩ := Finset.mem_filter.mp x.property
    obtain ⟨_,_,yd,_⟩ := Finset.mem_filter.mp y.property
    apply Subtype.ext
    exact h4 d (g x) x.val y.val (fun eq=>qo (g x) (gQ x) (eq ▸ dm))
      xd.symm (gq x).symm yd.symm (e.symm ▸ (gq y).symm)
  have fc : F.card=A.card := by
    rw [Finset.card_image_of_injective _ finj,Finset.card_univ,Fintype.card_coe]
  have gc : J.card=Z.card := by
    rw [Finset.card_image_of_injective _ ginj,Finset.card_univ,Fintype.card_coe]
  have union : F∪J⊆L∪B := by
    intro w wm
    rcases Finset.mem_union.mp wm with fM|gM
    · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp fM
      by_cases low : localIndependence G (f x)≤2
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨fQ x,low⟩))
      obtain ⟨xQ,high,xa,xd⟩ := Finset.mem_filter.mp x.property
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨fQ x,by omega,x.val,qo _ xQ,high,fq x,Or.inl ⟨xa,xd,fd x⟩⟩))
    · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp gM
      by_cases low : localIndependence G (g x)≤2
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨gQ x,low⟩))
      obtain ⟨xQ,high,xd,xa⟩ := Finset.mem_filter.mp x.property
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨gQ x,by omega,x.val,qo _ xQ,high,gq x,Or.inr ⟨xd,xa,ga x⟩⟩))
  have inter : F∩J⊆X := by
    intro w wm
    obtain ⟨fm,gm⟩ := Finset.mem_inter.mp wm
    obtain ⟨x,_,e⟩ := Finset.mem_image.mp fm
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp gm
    exact Finset.mem_filter.mpr ⟨gQ y,ga y,e ▸ fd x⟩
  have cover : H⊆(A∪Z)∪X := by
    intro q hm
    obtain ⟨qQ,high⟩ := Finset.mem_filter.mp hm
    rcases one_edge_palette_high_isolate_dichotomy h4 D a b c d am bm cm dm ab ac ad bd cd bc
      attach palette q (qo q qQ) high with h|h|h
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨qQ,h⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨qQ,high,h.1,h.2.1⟩))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨qQ,high,h.1,h.2.1⟩))))
  have signed : H.card≤L.card+B.card+2*X.card := by
    have u := (Finset.card_le_card union).trans (Finset.card_union_le _ _)
    have i := Finset.card_le_card inter
    have ac := Finset.card_union_add_card_inter F J
    have h := Finset.card_le_card cover
    have h1 := Finset.card_union_le (A∪Z) X
    have h2 := Finset.card_union_le A Z
    omega
  have ps : P⊆D := by
    intro x xm
    simp only [P,Finset.mem_insert,Finset.mem_singleton] at xm
    rcases xm with rfl|rfl|rfl|rfl <;> assumption
  have pc : P.card=4 := by simp [P,ab,ac,ad,bc.ne,bd,cd]
  choose tag htag using attach
  let k (q : V) := if h : q∉D then tag q h else q
  have pick (q : V) (qo : q∉D) : k q∈P ∧ G.Adj q (k q) := by simpa only [k,dif_pos qo] using htag q qo
  have localCap (q : V) (nq : q∉D) : localIndependence G q≤4 :=
    pc ▸ outside_independence_le_attachment_palette h4 D P k
      (fun q qo=>⟨ps (pick q qo).1,pick q qo⟩) palette q nq
  have point (q : V) (qm : q∈Q) : localIndependence G q+(if q∈L then 1 else 0)≤
      3+(if q∈H then 1 else 0) := by
    have l : q∈L ↔ localIndependence G q≤2 := by simp [L,qm]
    have h : q∈H ↔ 3<localIndependence G q := by simp [H,qm]
    have z := localCap q (qo q qm)
    by_cases lo : localIndependence G q≤2
    · rw [if_pos (l.mpr lo),if_neg (fun e=>by have v := h.mp e; omega)]
      omega
    by_cases hi : 3<localIndependence G q
    · rw [if_neg (fun e=>lo (l.mp e)),if_pos (h.mpr hi)]
      omega
    · rw [if_neg (fun e=>lo (l.mp e)),if_neg (fun e=>hi (h.mp e))]
      omega
  have ss := Finset.sum_le_sum point
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at ss
  have hsum : (∑ q∈Q,(if q∈H then 1 else 0 : Nat))=H.card := by
    rw [←Finset.card_filter]
    congr 1
    ext q
    simp only [Finset.mem_filter,H]
    tauto
  have lsum : (∑ q∈Q,(if q∈L then 1 else 0 : Nat))=L.card := by
    rw [←Finset.card_filter]
    congr 1
    ext q
    simp only [Finset.mem_filter,L]
    tauto
  have cs : (∑ _q∈Q,(3:Nat))=3*Q.card := by simp [Nat.mul_comm]
  rw [hsum,lsum,cs] at ss
  change (∑ q∈Q,localIndependence G q)+L.card≤3*Q.card+H.card at ss
  change (∑ q∈Q,localIndependence G q)≤3*Q.card+B.card+2*X.card
  omega

#print axioms one_edge_palette_signed_outer_budget
theorem double_isolate_clients_at_most_one
    (h4 : FourCycleFree G) (D : Finset V) (a d : V) (ad : a≠d) :
    (doubleIsolateClients G D a d).card≤1 := by
  apply Finset.card_le_one.mpr
  intro x xm y ym
  obtain ⟨_,xa,xd⟩ := Finset.mem_filter.mp xm
  obtain ⟨_,ya,yd⟩ := Finset.mem_filter.mp ym
  exact h4 a d x y ad xa.symm xd.symm ya.symm yd.symm

theorem one_edge_palette_ambient_mean_four_of_signed_slack
    (h4 : FourCycleFree G) (D : Finset V) (a b c d : V)
    (am : a∈D) (bm : b∈D) (cm : c∈D) (dm : d∈D)
    (ab : a≠b) (ac : a≠c) (ad : a≠d) (bd : b≠d) (cd : c≠d)
    (bc : G.Adj b c)
    (attach : ∀ q∉D,∃ t∈({a,b,c,d}:Finset V),G.Adj q t)
    (palette : ∀ q∉D,∀ p∈D,G.Adj q p→p∈({a,b,c,d}:Finset V))
    (slack :
      let Q := (Finset.univ : Finset V)\D
      (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+
        (∑ q∈Q,((D.filter (G.Adj q)).card-1))+
        (oneEdgeBadReceivers G D a d).card+2*(doubleIsolateClients G D a d).card≤4*D.card) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let P : Finset V := {a,b,c,d}
  have ps : P⊆D := by
    intro x xm
    simp only [P,Finset.mem_insert,Finset.mem_singleton] at xm
    rcases xm with rfl|rfl|rfl|rfl <;> assumption
  have outer := one_edge_palette_signed_outer_budget h4 D a b c d am bm cm dm ab ac ad bd cd bc attach palette
  choose tag htag using attach
  let k (q : V) := if h : q∉D then tag q h else q
  have pick (q : V) (qo : q∉D) : k q∈P ∧ G.Adj q (k q) := by simpa only [k,dif_pos qo] using htag q qo
  have cross := core_crossings_eq_card_add_extra D k (fun q qo=>⟨ps (pick q qo).1,(pick q qo).2⟩)
  have bound := core_and_exterior_independence_sum (G:=G) D
  have cards := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  rw [Finset.card_univ] at cards
  change Q.card+D.card=Fintype.card V at cards
  change (∑ q∈Q,(D.filter (G.Adj q)).card)=Q.card+(∑ q∈Q,((D.filter (G.Adj q)).card-1)) at cross
  change _≤_ + (∑ q∈Q,localIndependence G q) + (∑ q∈Q,(D.filter (G.Adj q)).card) at bound
  change (∑ q∈Q,localIndependence G q)≤3*Q.card+
    (oneEdgeBadReceivers G D a d).card+2*(doubleIsolateClients G D a d).card at outer
  change (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+
    (∑ q∈Q,((D.filter (G.Adj q)).card-1))+
    (oneEdgeBadReceivers G D a d).card+2*(doubleIsolateClients G D a d).card≤4*D.card at slack
  omega

#print axioms double_isolate_clients_at_most_one
#print axioms one_edge_palette_ambient_mean_four_of_signed_slack
end Graffiti133P5CliqueArms
