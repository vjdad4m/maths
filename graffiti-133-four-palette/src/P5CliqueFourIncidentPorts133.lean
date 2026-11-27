import P5CliqueFourConsecutivePorts133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem outside_independence_le_of_two_port_neighbors
    (h4 : FourCycleFree G) (D : Finset V) (tag : V→V)
    (choosePort : ∀ v∉D,tag v∈D ∧ G.Adj v (tag v))
    (P : Finset V) (pc : P.card=4)
    (palette : ∀ q∉D, ∀ p∈D,G.Adj q p →p∈P)
    (q : V) (qo : q∉D) (p t u : V) (pm : p∈D) (tm : t∈D) (um : u∈D)
    (tp : t∈P) (up : u∈P) (tu : t≠u)
    (qp : G.Adj q p) (pt : G.Adj p t) (pu : G.Adj p u) : localIndependence G q≤2 := by
  classical
  let Q := (Finset.univ : Finset V)\D
  unfold localIndependence
  apply Finset.sup_le_iff.mpr
  intro S hS
  have info : (∀ x∈S,G.Adj q x) ∧ (∀ x∈S,∀ y∈S,¬G.Adj x y) := by
    simpa only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_iff,
      Finset.mem_univ,true_and] using hS
  let f (v : V) := if v∈D then v else tag v
  have hit (v : V) (vm : v∈S) : f v∈P := by
    by_cases vd : v∈D
    · simpa only [f,if_pos vd] using palette q qo v vd (info.1 _ vm)
    · simpa only [f,if_neg vd] using palette v vd (tag v) (choosePort v vd).1 (choosePort v vd).2
  have inj : Set.InjOn f (S : Set V) := by
    intro v vm w wm e
    by_cases vd : v∈D
    · by_cases wd : w∈D
      · simpa only [f,if_pos vd,if_pos wd] using e
      simp only [f,if_pos vd,if_neg wd] at e
      exact ((info.2 w wm v vm) (e.symm ▸ (choosePort w wd).2)).elim
    by_cases wd : w∈D
    · simp only [f,if_neg vd,if_pos wd] at e
      exact ((info.2 v vm w wm) (e ▸ (choosePort v vd).2)).elim
    simp only [f,if_neg vd,if_neg wd] at e
    have qn : q≠tag v := fun eq=>qo (eq.symm ▸ (choosePort v vd).1)
    exact h4 q (tag v) v w qn (info.1 _ vm) (choosePort v vd).2.symm
      (info.1 _ wm) (e.symm ▸ (choosePort w wd).2).symm
  have sub : S.image f⊆P := by
    intro v vm
    obtain ⟨w,wm,rfl⟩ := Finset.mem_image.mp vm
    exact hit w wm
  have rep (v x : V) (vd : v∈D) (pv : G.Adj p v) (xm : x∈S) (ex : f x=v) : x=v := by
    have xd : x∈D := by
      by_contra xd
      simp only [f,if_neg xd] at ex
      have vx : G.Adj v x := (ex ▸ (choosePort x xd).2).symm
      have e := h4 q v p x (fun e=>qo (e.symm ▸ vd)) qp pv.symm (info.1 _ xm) vx
      exact xd (e ▸ pm)
    simpa only [f,if_pos xd] using ex
  have miss (v : V) (vd : v∈D) (pv : G.Adj p v) : ¬(p∈S.image f ∧ v∈S.image f) := by
    rintro ⟨hp,hv⟩
    obtain ⟨x,xm,ex⟩ := Finset.mem_image.mp hp
    obtain ⟨y,ym,ey⟩ := Finset.mem_image.mp hv
    have eq := rep v y vd pv ym ey
    subst y
    by_cases xd : x∈D
    · have xp : x=p := by simpa only [f,if_pos xd] using ex
      subst x
      exact info.2 p xm v ym pv
    · simp only [f,if_neg xd] at ex
      have px : G.Adj p x := (ex ▸ (choosePort x xd).2).symm
      have e := h4 q p x v (fun e=>qo (e.symm ▸ pm)) (info.1 _ xm) px (info.1 _ ym) pv
      exact xd (e.symm ▸ vd)
  have miss2 : ¬(t∈S.image f ∧ u∈S.image f) := by
    rintro ⟨ht,hu⟩
    obtain ⟨x,xm,ex⟩ := Finset.mem_image.mp ht
    obtain ⟨y,ym,ey⟩ := Finset.mem_image.mp hu
    have eqx := rep t x tm pt xm ex
    have eqy := rep u y um pu ym ey
    subst x
    subst y
    exact tu (h4 q p t u (fun e=>qo (e.symm ▸ pm)) (info.1 _ xm) pt (info.1 _ ym) pu)
  have pin : p∈P := palette q qo p pm qp
  have ip : (S.image f).card=S.card := Finset.card_image_of_injOn inj
  have erase2 (v w : V) (vp : v∈P) (wp : w∈P) (ne : w≠v)
      (vm : v∉S.image f) (wm : w∉S.image f) : S.card≤2 := by
    have incl : (S.image f)⊆(P.erase v).erase w := fun x xm =>
      Finset.mem_erase.mpr ⟨fun e=>wm (e ▸ xm),Finset.mem_erase.mpr ⟨fun e=>vm (e ▸ xm),sub xm⟩⟩
    have z1 := Finset.card_erase_add_one vp
    have z2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨ne,wp⟩)
    have le := Finset.card_le_card incl
    omega
  by_cases hp : p∈S.image f
  · exact erase2 t u tp up tu.symm (fun e=>miss t tm pt ⟨hp,e⟩) (fun e=>miss u um pu ⟨hp,e⟩)
  by_cases ht : t∈S.image f
  · exact erase2 p u pin up pu.ne.symm hp (fun e=>miss2 ⟨ht,e⟩)
  · exact erase2 p t pin tp pt.ne.symm hp ht

#print axioms outside_independence_le_of_two_port_neighbors
private theorem P7free_connected_core_budget_gap (D : Finset V)
    (h4 : FourCycleFree G) (hc : (G.induce (D : Set V)).Connected)
    (h7 : NoPath (G.induce (D : Set V)) 7) :
    (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)≤3*D.card := by
  classical
  let J := G.induce (D : Set V)
  have four : FourCycleFree J := by
    intro a b x y ne ax bx ay by'
    exact Subtype.ext (h4 a.val b.val x.val y.val (fun e=>ne (Subtype.ext e)) ax bx ay by')
  have eq : Fintype.card (D : Set V)=D.card := Fintype.card_coe _
  change (∑ x : (D : Set V),localIndependence J x)≤3*D.card
  by_contra h
  have high : 3*Fintype.card (D : Set V)<∑ x : (D : Set V),localIndependence J x := by omega
  have mean : 3<averageLocal J := by
    letI := hc.nonempty
    have pos : (0:ℚ)<(Fintype.card (D : Set V):ℚ) := by exact_mod_cast Fintype.card_pos (α:=(D : Set V))
    unfold averageLocal
    apply (lt_div_iff₀ pos).mpr
    rw [← Nat.cast_sum]
    exact_mod_cast high
  exact h7 (Graffiti133Revisit.P7_of_strict_mean_three J hc four mean)

theorem four_port_one_isolate_admissible_ambient_mean_four
    (h4 : FourCycleFree G) (D P : Finset V) (sub : P⊆D) (pc : P.card=4)
    (attach : ∀ q∉D,∃ p∈P,G.Adj q p)
    (palette : ∀ q∉D,∀ p∈D,G.Adj q p→p∈P)
    (a b c d : V) (bp : b∈P) (cp : c∈P) (dp : d∈P) (cd : c≠d)
    (bc : G.Adj b c) (bd : G.Adj b d)
    (othersNonisolated : ∀ p∈P,p≠a→∃ t∈P,G.Adj p t)
    (hc : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7)
    (paircap : ((P.powersetCard 2).filter (fun F=>¬∃ x∈D,∀ p∈F,G.Adj x p)).card≤D.card) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  choose f fw using attach
  let tag (q : V) := if h : q∉D then f q h else q
  have pick (q : V) (qo : q∉D) : tag q∈P ∧ G.Adj q (tag q) := by simpa only [tag,dif_pos qo] using fw q qo
  have pickD (q : V) (qo : q∉D) : tag q∈D ∧ G.Adj q (tag q) := ⟨sub (pick q qo).1,(pick q qo).2⟩
  have qout (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  have localCap (q : V) (qo : q∉D) : localIndependence G q≤4 :=
    pc ▸ outside_independence_le_attachment_palette h4 D P tag
      (fun v vo=>⟨(pickD v vo).1,pick v vo⟩) palette q qo
  have allAtA (q : V) (qo : q∉D) (high : 3<localIndependence G q)
      (p : V) (pm : p∈D) (qp : G.Adj q p) : p=a := by
    by_contra ne
    obtain ⟨u,up,pu⟩ := othersNonisolated p (palette q qo p pm qp) ne
    exact (not_le_of_gt high) (outside_independence_le_of_nonisolated_port h4 D tag pickD P pc
      palette q qo p u pm (sub up) up qp pu)
  have seeA (q : V) (qo : q∉D) (high : 3<localIndependence G q) : G.Adj q a := by
    rw [←allAtA q qo high (tag q) (pickD q qo).1 (pickD q qo).2]
    exact (pickD q qo).2
  have bAbsent (q : V) (qo : q∉D) (high : 3<localIndependence G q) : ¬G.Adj q b := by
    intro qb
    exact (not_le_of_gt high) (outside_independence_le_of_nonisolated_port h4 D tag pickD
      P pc palette q qo b c (sub bp) (sub cp) cp qb bc)
  have hit (q : V) (qo : q∉D) (high : 3<localIndependence G q) :
      ∃ w∈Q, G.Adj q w ∧ G.Adj w b := by
    let N := (D.filter (G.Adj q))∪((Q.filter (G.Adj q)).image tag)
    have s : N⊆P := by
      apply Finset.union_subset
      · intro w wm
        exact palette q qo w (Finset.mem_filter.mp wm).1 (Finset.mem_filter.mp wm).2
      · intro w wm
        obtain ⟨v,vm,rfl⟩ := Finset.mem_image.mp wm
        exact (pick v (qout v (Finset.mem_filter.mp vm).1)).1
    have le := outside_independence_le_core_neighbors_union_assigned_ports h4 D tag pickD q qo
    change localIndependence G q≤N.card at le
    have eq : N=P := Finset.eq_of_subset_of_card_le s (by omega)
    have bm : b∈N := eq.symm ▸ bp
    rcases Finset.mem_union.mp bm with inD|inImg
    · exact (bAbsent q qo high (Finset.mem_filter.mp inD).2).elim
    obtain ⟨w,wm,e⟩ := Finset.mem_image.mp inImg
    exact ⟨w,(Finset.mem_filter.mp wm).1,(Finset.mem_filter.mp wm).2,
      e ▸ (pick w (qout w (Finset.mem_filter.mp wm).1)).2⟩
  let High := Q.filter (fun q=>3<localIndependence G q)
  let Low := Q.filter (fun q=>localIndependence G q≤2)
  have al : a∈D ∨ High=∅ := by
    by_cases ad : a∈D
    · exact Or.inl ad
    right
    ext q
    constructor
    · intro qm
      obtain ⟨qq,hq⟩ := Finset.mem_filter.mp qm
      exact (ad (allAtA q (qout q qq) hq (tag q) (pickD q (qout q qq)).1
        (pickD q (qout q qq)).2 ▸ (pickD q (qout q qq)).1)).elim
    · simp
  have charge : High.card≤Low.card := by
    rcases al with ad|eq
    · have ex (q : {q // q∈High}) : ∃ w∈Low,G.Adj q.val w := by
        have qm := Finset.mem_filter.mp q.property
        obtain ⟨x,xm,qx,xb⟩ := hit q.val (qout q.val qm.1) qm.2
        have lx := outside_independence_le_of_two_port_neighbors h4 D tag pickD P pc palette
          x (qout x xm) b c d (sub bp) (sub cp) (sub dp) cp dp cd xb bc bd
        exact ⟨x,Finset.mem_filter.mpr ⟨xm,lx⟩,qx⟩
      choose g gm ga using ex
      let F : {q // q∈High}→{x // x∈Low} := fun q=>⟨g q,gm q⟩
      have inj : Function.Injective F := by
        intro q r qr
        have ee : g q=g r := congrArg Subtype.val qr
        have qm := Finset.mem_filter.mp q.property
        have rm := Finset.mem_filter.mp r.property
        apply Subtype.ext
        exact h4 a (g q) q.val r.val
          (fun e=>qout (g q) (Finset.mem_filter.mp (gm q)).1 (e ▸ ad))
          (seeA q.val (qout q.val qm.1) qm.2).symm (ga q).symm
          (seeA r.val (qout r.val rm.1) rm.2).symm (ee.symm ▸ ga r).symm
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective F inj
    · simp [eq]
  have outer : (∑ q∈Q,localIndependence G q)≤3*Q.card := by
    have point (q : V) (qm : q∈Q) : localIndependence G q+(if q∈Low then 1 else 0)≤
        3+(if q∈High then 1 else 0) := by
      have l : q∈Low ↔ localIndependence G q≤2 := by simp [Low,qm]
      have h : q∈High ↔ 3<localIndependence G q := by simp [High,qm]
      have z := localCap q (qout q qm)
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
    have hsum : (∑ q∈Q,(if q∈High then 1 else 0 : Nat))=High.card := by
      rw [←Finset.card_filter]
      congr 1
      ext q
      simp only [Finset.mem_filter,High]
      tauto
    have lsum : (∑ q∈Q,(if q∈Low then 1 else 0 : Nat))=Low.card := by
      rw [←Finset.card_filter]
      congr 1
      ext q
      simp only [Finset.mem_filter,Low]
      tauto
    rw [hsum,lsum] at ss
    have cs : (∑ _q∈Q,(3:Nat))=3*Q.card := by simp [Nat.mul_comm]
    rw [cs] at ss
    change (∑ q∈Q,localIndependence G q)+Low.card≤3*Q.card+High.card at ss
    exact Nat.le_of_add_le_add_right (ss.trans (Nat.add_le_add_left charge (3*Q.card)))
  have extra := extra_port_incidence_le_admissible_pair h4 D P sub tag pick palette
  have cross := core_crossings_eq_card_add_extra D tag pickD
  have bound := core_and_exterior_independence_sum (G:=G) D
  have core := P7free_connected_core_budget_gap D h4 hc h7
  have cards := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  rw [Finset.card_univ] at cards
  change Q.card+D.card=Fintype.card V at cards
  change (∑ q∈Q,((D.filter (G.Adj q)).card-1))≤_ at extra
  change (∑ q∈Q,(D.filter (G.Adj q)).card)=Q.card+(∑ q∈Q,((D.filter (G.Adj q)).card-1)) at cross
  change _≤_ + (∑ q∈Q,localIndependence G q) + (∑ q∈Q,(D.filter (G.Adj q)).card) at bound
  omega

#print axioms four_port_one_isolate_admissible_ambient_mean_four
theorem four_port_incident_edges_ambient_mean_four
    (h4 : FourCycleFree G) (D : Finset V) (a b c d : V)
    (am : a∈D) (bm : b∈D) (cm : c∈D) (dm : d∈D)
    (ab : a≠b) (ac : a≠c) (ad : a≠d) (cd : c≠d)
    (bc : G.Adj b c) (bd : G.Adj b d)
    (attach : ∀ q∉D,∃ t∈({a,b,c,d} : Finset V),G.Adj q t)
    (palette : ∀ q∉D,∀ p∈D,G.Adj q p→p∈({a,b,c,d} : Finset V))
    (hc : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let P : Finset V := {a,b,c,d}
  have sub : P⊆D := by
    intro x xm
    simp only [P,Finset.mem_insert,Finset.mem_singleton] at xm
    rcases xm with rfl|rfl|rfl|rfl <;> assumption
  have pc : P.card=4 := by simp [P,ab,ac,ad,bc.ne,bd.ne,cd]
  have ap : a∈P := by simp [P]
  have bp : b∈P := by simp [P]
  have cp : c∈P := by simp [P]
  have dp : d∈P := by simp [P]
  have other (p : V) (pp : p∈P) (ne : p≠a) : ∃ t∈P,G.Adj p t := by
    simp only [P,Finset.mem_insert,Finset.mem_singleton] at pp
    rcases pp with rfl|rfl|rfl|rfl
    · exact (ne rfl).elim
    · exact ⟨c,cp,bc⟩
    · exact ⟨b,bp,bc.symm⟩
    · exact ⟨b,bp,bd.symm⟩
  let S := P.powersetCard 2
  let A := S.filter (fun F=>¬∃ x∈D,∀ p∈F,G.Adj x p)
  have s6 : S.card=6 := by rw [Finset.card_powersetCard,pc]; decide
  have excluded (x y z : V) (xp : x∈P) (yp : y∈P) (xy : x≠y)
      (zm : z∈D) (zx : G.Adj z x) (zy : G.Adj z y) :
        ({x,y}:Finset V)∈S ∧ ({x,y}:Finset V)∉A := by
    constructor
    · exact Finset.mem_powersetCard.mpr ⟨by simp [Finset.insert_subset_iff,xp,yp],by simp [xy]⟩
    · intro h
      apply (Finset.mem_filter.mp h).2
      refine ⟨z,zm,?_⟩
      intro p pp
      simp only [Finset.mem_insert,Finset.mem_singleton] at pp
      rcases pp with rfl|rfl <;> assumption
  let X : Finset V := {c,d}
  have x : X∈S ∧ X∉A := excluded c d b cp dp cd bm bc bd
  have ax : A⊆S.erase X := fun F fm=>Finset.mem_erase.mpr
    ⟨fun e=>x.2 (e ▸ fm),(Finset.mem_filter.mp fm).1⟩
  have z1 := Finset.card_erase_add_one x.1
  have cap := Finset.card_le_card ax
  by_cases large : 5≤D.card
  · exact four_port_one_isolate_admissible_ambient_mean_four h4 D P sub pc attach palette
      a b c d bp cp dp cd bc bd other hc h7 (show A.card≤D.card by omega)
  have d4 : D.card=4 := by
    have le := Finset.card_le_card sub
    omega
  have de : D=P := (Finset.eq_of_subset_of_card_le sub (by omega)).symm
  have find : ∃ u∈P,G.Adj a u := by
    let aa : (D : Set V) := ⟨a,am⟩
    let bb : (D : Set V) := ⟨b,bm⟩
    refine (hc.preconnected aa bb).elim ?_
    intro p
    have ne : aa≠bb := fun e=>ab (congrArg Subtype.val e)
    exact ⟨p.snd.val,de ▸ p.snd.property,p.adj_snd (p.not_nil_of_ne ne)⟩
  obtain ⟨u,up,au⟩ := find
  have all (p : V) (pp : p∈P) : ∃ t∈P,G.Adj p t := by
    by_cases e : p=a
    · exact ⟨u,up,e.symm ▸ au⟩
    exact other p pp e
  simp only [P,Finset.mem_insert,Finset.mem_singleton] at up
  rcases up with eu|eu|eu|eu
  · exact (G.loopless a (eu ▸ au)).elim
  · let Y : Finset V := {a,c}
    have y : Y∈S ∧ Y∉A := excluded a c b ap cp ac bm (eu ▸ au).symm bc
    have xy : X≠Y := by
      intro eq
      have m : a∈X := eq.symm ▸ (Finset.mem_insert_self _ _ : a∈Y)
      simp [X,ac,ad] at m
    have ay : A⊆(S.erase X).erase Y := fun F fm=>Finset.mem_erase.mpr
      ⟨fun e=>y.2 (e ▸ fm),ax fm⟩
    have z2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨xy.symm,y.1⟩)
    have le := Finset.card_le_card ay
    exact four_port_nonisolated_admissible_ambient_mean_four h4 D P sub pc attach palette
      all hc h7 (show A.card≤D.card by omega)
  · exact four_consecutive_ports_ambient_mean_four h4 D a c b d am cm bm dm (eu ▸ au) bc.symm bd
      ab ad cd (by simpa [Finset.insert_comm b c] using attach)
      (by simpa [Finset.insert_comm b c] using palette) hc h7
  · have ep : ({a,d,b,c} : Finset V)=P := by
      ext p
      simp only [P,Finset.mem_insert,Finset.mem_singleton]
      tauto
    exact four_consecutive_ports_ambient_mean_four h4 D a d b c am dm bm cm (eu ▸ au) bd.symm bc
      ab ac cd.symm (ep.symm ▸ attach) (ep.symm ▸ palette) hc h7

#print axioms four_port_incident_edges_ambient_mean_four
end Graffiti133P5CliqueArms
