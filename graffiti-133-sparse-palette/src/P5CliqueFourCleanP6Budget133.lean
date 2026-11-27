import P5CliqueFourNearThreeArmFans133
import P5CliqueOppositeP6Charge133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem clean_port_stem_reverse {n : Nat} (f : Fin n→V) (fp : InducedPath G f) :
    InducedPath G (f ∘ Fin.rev) := by
  refine ⟨fp.1.comp Fin.rev_injective,fun i j ij=>?_⟩
  have e : Fin.rev j<Fin.rev i := Fin.rev_lt_rev.mpr ij
  change G.Adj (f (Fin.rev i)) (f (Fin.rev j)) ↔ i.val+1=j.val
  rw [SimpleGraph.adj_comm,fp.2 _ _ e]
  simp only [Fin.val_rev]
  omega

theorem clean_P6_four_port_high_clients_at_most_eight
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pinj : Function.Injective p)
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (single : ∀ q∉D,∀ i,G.Adj q (p i)→∀ x∈D,G.Adj q x↔x=p i)
    (f : Fin 6→V) (fp : InducedPath G f) (fd : ∀ j,f j∈D)
    (left : f 0=p 0) (right : f 5=p 1)
    (off : ∀ i : Fin 4, 2 ≤ i.val → ∀ j,p i≠f j) :
    (((Finset.univ : Finset V)\D).filter (fun q=>3<localIndependence G q)).card≤8 := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let C (i : Fin 4) := Q.filter (fun q=>G.Adj q (p i))
  let A (i : Fin 4) := (C i).filter (fun q=>3<localIndependence G q)
  let H := Q.filter (fun q=>3<localIndependence G q)
  have qo (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  have outerNear (i j : Fin 4) (ij : i≠j) (q : V) (qQ : q∈Q)
      (qi : G.Adj q (p i)) (hq : 3<localIndependence G q) :
      ∃ w∈C j,G.Adj q w := by
    let e := Equiv.swap 0 i
    let p' (k : Fin 4) := p (e k)
    have et : e 0=i := by simp [e]
    have att' (q : V) (qo : q∉D) : ∃ j,G.Adj q (p' j) := by
      obtain ⟨j,h⟩ := attach q qo
      exact ⟨e.symm j,by simpa [p'] using h⟩
    have pal' (q : V) (qo : q∉D) (x : V) (xd : x∈D) (qx : G.Adj q x) : ∃ j,x=p' j := by
      obtain ⟨j,h⟩ := palette q qo x xd qx
      exact ⟨e.symm j,by simpa [p'] using h⟩
    have ea : G.Adj q (p' 0) := by simpa [p',et] using qi
    obtain ⟨g,g0,gout,only,star⟩ := high_client_singleton_four_port_has_fan h4 D p' (fun k=>pm (e k))
      (pinj.comp e.injective) att' pal' (fun q qo j=>single q qo (e j)) q (qo _ qQ) ea hq
    let j' := e.symm j
    have j'0 : j'≠0 := fun eq=>ij (by simpa [j',et] using (congrArg e eq).symm)
    have ep : p' j'=p j := by simp [p',j']
    have qg : G.Adj q (g j') := g0 ▸ (star 0 j' (Fin.pos_iff_ne_zero.mpr j'0)).mpr rfl
    have gp : G.Adj (g j') (p j) := (only j' _ (pm j)).mpr ep.symm
    exact ⟨g j',Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,gout j'⟩,gp⟩,qg⟩
  have injection (i j : Fin 4) (ij : i≠j) : (A i).card≤(C j).card := by
    have ex (q : {q : V // q∈A i}) : ∃ w∈C j,G.Adj q.val w := by
      obtain ⟨qm,qh⟩ := Finset.mem_filter.mp q.property
      obtain ⟨qQ,qi⟩ := Finset.mem_filter.mp qm
      exact outerNear i j ij q.val qQ qi qh
    choose g gm ga using ex
    let F : {q : V // q∈A i}→{w : V // w∈C j} := fun q=>⟨g q,gm q⟩
    have fi : Function.Injective F := by
      intro q r eq
      have ep : g q=g r := congrArg Subtype.val eq
      have qport := (Finset.mem_filter.mp (Finset.mem_filter.mp q.property).1).2
      have rport := (Finset.mem_filter.mp (Finset.mem_filter.mp r.property).1).2
      apply Subtype.ext
      exact h4 (p i) (g q) q.val r.val
        (fun e=>qo _ (Finset.mem_filter.mp (gm q)).1 (e ▸ pm i)) qport.symm (ga q).symm
        rport.symm (ep.symm ▸ (ga r).symm)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective F fi
  have capOther (g : Fin 6→V) (gp : InducedPath G g) (gd : ∀ j,g j∈D)
      (i j : Fin 4) (gl : g 0=p i) (gr : g 5=p j)
      (offPort : ∀ l≥2,∀ v : Fin 6,p l≠g v)
      (joff : j≠2) (ilow : i.val < 2) (jlow : j.val < 2)
      (k : Fin 4) (ki : k≠i) (x : V) (xm : x∈A k) : (C i).card≤2 := by
    obtain ⟨xc,xh⟩ := Finset.mem_filter.mp xm
    obtain ⟨xQ,xk⟩ := Finset.mem_filter.mp xc
    have xo := qo _ xQ
    have rinfo : ∀ w∈C i,w∉D ∧ ∀ z∈D,G.Adj w z↔z=g 0 := by
      intro w wm
      obtain ⟨wQ,wi⟩ := Finset.mem_filter.mp wm
      exact ⟨qo _ wQ,gl.symm ▸ single w (qo _ wQ) i wi⟩
    by_cases kj : k=j
    · subst k
      obtain ⟨y,ym,xy⟩ := outerNear j 2 joff x xQ xk xh
      obtain ⟨yQ,y2⟩ := Finset.mem_filter.mp ym
      exact opposite_P6_port_client_cap_two h4 h9 D (C i) g gp gd x y xo (qo _ yQ) xy
        (gr.symm ▸ single x xo j xk) (p 2) (single y (qo _ yQ) 2 y2) (offPort 2 (by decide)) rinfo
    · obtain ⟨y,ym,xy⟩ := outerNear k j kj x xQ xk xh
      obtain ⟨yQ,yj⟩ := Finset.mem_filter.mp ym
      have ge : 2 ≤ k.val := by
        by_cases good : 2 ≤ k.val
        · exact good
        exfalso
        have kn : k.val < 2 := lt_of_not_ge good
        have hk0 : k=0 ∨ k=1 := by
          have z : k.val=0 ∨ k.val=1 := by omega
          exact z.imp (fun e=>Fin.ext e) (fun e=>Fin.ext e)
        have hi0 : i=0 ∨ i=1 := by
          have z : i.val=0 ∨ i.val=1 := by omega
          exact z.imp (fun e=>Fin.ext e) (fun e=>Fin.ext e)
        have hj0 : j=0 ∨ j=1 := by
          have z : j.val=0 ∨ j.val=1 := by omega
          exact z.imp (fun e=>Fin.ext e) (fun e=>Fin.ext e)
        have ij : i≠j := fun e=>((by decide : (0:Fin 6)≠5) (gp.1 (gl.trans ((congrArg p e).trans gr.symm))))
        rcases hk0 with e|e <;> rcases hi0 with f|f <;> rcases hj0 with g|g <;>
          first | exact ki (e.trans f.symm) | exact kj (e.trans g.symm) | exact ij (f.trans g.symm)
      exact opposite_P6_port_client_cap_two h4 h9 D (C i) g gp gd y x (qo _ yQ) xo xy.symm
        (gr.symm ▸ single y (qo _ yQ) j yj) (p k) (single x xo k xk) (offPort k ge) rinfo
  have cap0 (i : Fin 4) (ne : i≠0) (x : V) (xm : x∈A i) : (C 0).card≤2 := by
    exact capOther f fp fd 0 1 left right (fun l h=>off l h) (by decide) (by decide) (by decide) i ne x xm
  have cap1 (i : Fin 4) (ne : i≠1) (x : V) (xm : x∈A i) : (C 1).card≤2 := by
    exact capOther (f∘Fin.rev) (clean_port_stem_reverse f fp) (fun j=>fd j.rev) 1 0
      (show (f∘Fin.rev) 0=p 1 from right) (show (f∘Fin.rev) 5=p 0 from left)
      (fun l h j=>off l h j.rev) (by decide) (by decide) (by decide) i ne x xm
  have hpart : H⊆Finset.univ.biUnion A := by
    intro v vm
    obtain ⟨vQ,vh⟩ := Finset.mem_filter.mp vm
    obtain ⟨i,vi⟩ := attach v (qo _ vQ)
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨vQ,vi⟩,vh⟩⟩
  have large0 (c : 2<(C 0).card) : H.card≤2 := by
    have one : H⊆A 0 := by
      intro q qm
      obtain ⟨qQ,qh⟩ := Finset.mem_filter.mp qm
      obtain ⟨i,qi⟩ := attach q (qo _ qQ)
      have a : q∈A i := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨qQ,qi⟩,qh⟩
      by_cases i0 : i=0
      · exact i0 ▸ a
      exact ((not_le_of_gt c) (cap0 i i0 q a)).elim
    by_cases emp : H=∅
    · simp [emp]
    obtain ⟨q,qm⟩ := Finset.nonempty_iff_ne_empty.mpr emp
    exact (Finset.card_le_card one).trans ((injection 0 1 (by decide)).trans (cap1 0 (by decide) q (one qm)))
  have large1 (c : 2<(C 1).card) : H.card≤2 := by
    have one : H⊆A 1 := by
      intro q qm
      obtain ⟨qQ,qh⟩ := Finset.mem_filter.mp qm
      obtain ⟨i,qi⟩ := attach q (qo _ qQ)
      have a : q∈A i := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨qQ,qi⟩,qh⟩
      by_cases i1 : i=1
      · exact i1 ▸ a
      exact ((not_le_of_gt c) (cap1 i i1 q a)).elim
    by_cases emp : H=∅
    · simp [emp]
    obtain ⟨q,qm⟩ := Finset.nonempty_iff_ne_empty.mpr emp
    exact (Finset.card_le_card one).trans ((injection 1 0 (by decide)).trans (cap0 1 (by decide) q (one qm)))
  change H.card≤8
  by_cases lc : 2<(C 0).card
  · exact (large0 lc).trans (by decide)
  by_cases rc : 2<(C 1).card
  · exact (large1 rc).trans (by decide)
  have l2 : (C 0).card≤2 := by omega
  have r2 : (C 1).card≤2 := by omega
  have all (i : Fin 4) : (A i).card≤2 := by
    fin_cases i
    · exact (Finset.card_filter_le _ _).trans l2
    · exact (Finset.card_filter_le _ _).trans r2
    · exact (injection 2 0 (by decide)).trans l2
    · exact (injection 3 0 (by decide)).trans l2
  calc
    _≤(Finset.univ.biUnion A).card := Finset.card_le_card hpart
    _≤ ∑ i:Fin 4,(A i).card := Finset.card_biUnion_le
    _≤ ∑ _i:Fin 4,2 := Finset.sum_le_sum (fun i _=>all i)
    _=8 := by decide

#print axioms clean_P6_four_port_high_clients_at_most_eight
private theorem P7free_connected_core_budget_long_stem (D : Finset V)
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

theorem clean_P6_four_port_ambient_mean_four
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pinj : Function.Injective p)
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (single : ∀ q∉D,∀ i,G.Adj q (p i)→∀ x∈D,G.Adj q x↔x=p i)
    (f : Fin 6→V) (fp : InducedPath G f) (fd : ∀ j,f j∈D)
    (left : f 0=p 0) (right : f 5=p 1)
    (off : ∀ i : Fin 4, 2 ≤ i.val → ∀ j,p i≠f j)
    (Dconn : (G.induce (D : Set V)).Connected)
    (h7 : NoPath (G.induce (D : Set V)) 7) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let P := (Finset.univ : Finset (Fin 4)).image p
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pinj,Finset.card_univ]; decide
  let A := Q.filter (fun q=>3<localIndependence G q)
  have a8 : A.card≤8 := clean_P6_four_port_high_clients_at_most_eight h4 h9 D p pm pinj
    attach palette single f fp fd left right off
  have qa (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  let F := (Finset.univ : Finset (Fin 6)).image f
  have cf : F.card=6 := by rw [Finset.card_image_of_injective _ fp.1,Finset.card_univ]; decide
  have np (i : Fin 4) (hi : 2 ≤ i.val) : p i∉F := by
    intro mem
    obtain ⟨j,_,eq⟩ := Finset.mem_image.mp mem
    exact off i hi j eq.symm
  have n23 : p 2≠p 3 := fun e=>(by decide : (2:Fin 4)≠3) (pinj e)
  have z1 := Finset.card_insert_of_not_mem (np 2 (by decide))
  have none : p 3∉insert (p 2) F := by
    intro h
    exact (Finset.mem_insert.mp h).elim (fun e=>n23 e.symm) (np 3 (by decide))
  have z2 := Finset.card_insert_of_not_mem none
  have subD : insert (p 3) (insert (p 2) F) ⊆ D := by
    intro x xm
    rcases Finset.mem_insert.mp xm with e|xm
    · exact e.symm ▸ pm 3
    rcases Finset.mem_insert.mp xm with e|xm
    · exact e.symm ▸ pm 2
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp xm
    exact fd i
  have d8 : 8≤D.card := by
    have c := Finset.card_le_card subD
    omega
  have core := P7free_connected_core_budget_long_stem D h4 Dconn h7
  choose tag htag using attach
  let f (q : V) := if h : q∉D then p (tag q h) else q
  have pick (q : V) (qo : q∉D) : f q∈D ∧ f q∈P ∧ G.Adj q (f q) := by
    have e : f q=p (tag q qo) := dif_pos qo
    rw [e]
    exact ⟨pm _,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,htag q qo⟩
  have palette' (q : V) (qo : q∉D) (w : V) (wd : w∈D) (qw : G.Adj q w) : w∈P := by
    obtain ⟨i,e⟩ := palette q qo w wd qw
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩
  have localCap (q : V) (qo : q∉D) : localIndependence G q≤4 :=
    p4 ▸ outside_independence_le_attachment_palette h4 D P f pick palette' q qo
  have outer : (∑ q∈Q,localIndependence G q)≤3*Q.card+8 := by
    have point (q : V) (qm : q∈Q) : localIndependence G q≤3+(if q∈A then 1 else 0) := by
      by_cases high : 3<localIndependence G q
      · rw [if_pos (Finset.mem_filter.mpr ⟨qm,high⟩)]
        exact localCap q (qa q qm)
      · have hA : q∉A := fun e=>high (Finset.mem_filter.mp e).2
        rw [if_neg hA]
        omega
    have ss := Finset.sum_le_sum point
    rw [Finset.sum_add_distrib] at ss
    have hsum : (∑ q∈Q,(if q∈A then 1 else 0 : Nat))=A.card := by
      rw [←Finset.card_filter]
      congr 1
      ext q
      simp only [Finset.mem_filter,A]
      tauto
    have cs : (∑ _q∈Q,(3:Nat))=3*Q.card := by simp [Nat.mul_comm]
    rw [hsum,cs] at ss
    exact ss.trans (Nat.add_le_add_left a8 _)
  have crossings : (∑ q∈Q,(D.filter (G.Adj q)).card)=Q.card := by
    calc
      _=∑ _q∈Q,1 := by
        apply Finset.sum_congr rfl
        intro q qm
        have att := htag q (qa q qm)
        have once := single q (qa q qm) _ att
        have eq : D.filter (G.Adj q)={p (tag q (qa q qm))} := by
          ext w
          constructor
          · intro wm
            obtain ⟨wd,e⟩ := Finset.mem_filter.mp wm
            exact Finset.mem_singleton.mpr ((once w wd).mp e)
          · intro wm
            obtain rfl := Finset.mem_singleton.mp wm
            exact Finset.mem_filter.mpr ⟨pm _,att⟩
        rw [eq,Finset.card_singleton]
      _=_ := by simp
  have bound := core_and_exterior_independence_sum (G:=G) D
  have cards := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  rw [Finset.card_univ] at cards
  change Q.card+D.card=Fintype.card V at cards
  change _≤_ + (∑ q∈Q,localIndependence G q) + (∑ q∈Q,(D.filter (G.Adj q)).card) at bound
  omega

#print axioms clean_P6_four_port_ambient_mean_four
end Graffiti133P5CliqueArms
