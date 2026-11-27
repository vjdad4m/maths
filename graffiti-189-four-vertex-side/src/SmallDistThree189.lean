import DistThreeShape189
import SmallPort189
namespace Graffiti189LongestPath.TwoCut.CutPair
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.TwoCut
open Graffiti189LongestPath.FourCut.Three
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2700000
set_option linter.unusedSectionVars false
variable {a b : V} (S : CutPair G a b)

private theorem side_path (atleast : 3≤G.dist a b) (min2 : ∀ x,2≤G.degree x)
    (i : Bool) (upper : (S.H i).card≤6) :
    ∃ x, (G.Adj a x ∨ G.Adj b x) ∧ ∃ y, ∃ p : G.Walk x y, p.IsPath ∧
      ∀ z,z∈p.support ↔ z∈S.H i := by
  classical
  let M := {x : V // x∈S.H i}
  let K := G.induce (↑(S.H i) : Set V)
  let P : Finset M := univ.filter (fun x => G.Adj a x.val ∨ G.Adj b x.val)
  have portmem {x : M} : x∈P ↔ G.Adj a x.val ∨ G.Adj b x.val := by simp [P]
  have no_common {x : V} (ax : G.Adj a x) (bx : G.Adj b x) : False := by
    have d := G.dist_le (Walk.cons ax (Walk.cons bx.symm .nil))
    simp at d
    omega
  have cP : 2≤P.card := by
    obtain ⟨x,xs,ax⟩ := S.hita i
    obtain ⟨y,ys,by'⟩ := S.hitb i
    refine one_lt_card.mpr ⟨⟨x,xs⟩,portmem.mpr (Or.inl ax),⟨y,ys⟩,portmem.mpr (Or.inr by'),?_⟩
    intro e
    have xy : x=y := congrArg (fun z : M => z.val) e
    exact no_common ax (xy.symm ▸ by')
  have size : Fintype.card M≤6 := by simpa only [M,Fintype.card_coe] using upper
  let f : M ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have degree_bound (x : M) :
      G.degree x.val≤K.degree x+(if x∈P then 1 else 0) := by
    let B := ({a,b} : Finset V).filter (G.Adj x.val)
    have bcap : B.card≤(if x∈P then 1 else 0) := by
      by_cases xp : x∈P
      · simp only [xp,if_true]
        apply card_le_one.mpr
        intro y hy z hz
        obtain ⟨yy,xy⟩ := mem_filter.mp hy
        obtain ⟨zz,xz⟩ := mem_filter.mp hz
        simp only [mem_insert,mem_singleton] at yy zz
        rcases yy with rfl|rfl <;> rcases zz with rfl|rfl
        · rfl
        · exact (no_common xy.symm xz.symm).elim
        · exact (no_common xz.symm xy.symm).elim
        · rfl
      · simp only [xp,if_false,Nat.le_zero]
        apply card_eq_zero.mpr
        apply eq_empty_iff_forall_not_mem.mpr
        intro z hz
        obtain ⟨zz,xz⟩ := mem_filter.mp hz
        simp only [mem_insert,mem_singleton] at zz
        rcases zz with rfl|rfl
        · exact xp (portmem.mpr (Or.inl xz.symm))
        · exact xp (portmem.mpr (Or.inr xz.symm))
    have sub : G.neighborFinset x.val ⊆ B ∪ (K.neighborFinset x).map f := by
      intro y hy
      have xy := (mem_neighborFinset G x.val y).mp hy
      rcases S.closed i x.val x.property y xy with rfl|rfl|yh
      · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨by simp,xy⟩))
      · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨by simp,xy⟩))
      · refine mem_union.mpr (Or.inr (mem_map.mpr ⟨⟨y,yh⟩,?_,rfl⟩))
        exact (mem_neighborFinset K x ⟨y,yh⟩).mpr xy
    have c := card_le_card sub
    have h := card_union_le B ((K.neighborFinset x).map f)
    rw [card_neighborFinset_eq_degree] at c
    rw [card_map,card_neighborFinset_eq_degree] at h
    omega
  have high (x : M) (hi : 4≤G.degree x.val) : HighAt K P x := by
    have d := degree_bound x
    by_cases xp : x∈P <;> simp [HighAt,xp] at d ⊢ <;> omega
  have highpair (x y : M) (ne : x≠y) : HighAt K P x ∨ HighAt K P y :=
    (S.degree x.val y.val (fun e => ne (Subtype.ext e))).imp (high x) (high y)
  have kp (x : M) : 1≤K.degree x := by
    have d := degree_bound x
    have m := min2 x.val
    by_cases xp : x∈P <;> simp [xp] at d <;> omega
  have k2 (x : M) (xp : x∉P) : 2≤K.degree x := by
    have d := degree_bound x
    have m := min2 x.val
    simp [xp] at d
    omega
  obtain ⟨x,xp,y,p,hp,hs⟩ := spanning_path_from_port_of_six (G:=K) P cP size highpair kp k2
  let incl : K →g G := { toFun := Subtype.val, map_rel' := fun e => e }
  have pn : (p.map incl).IsPath := by
    apply IsPath.mk'
    rw [support_map]
    exact (List.nodup_map_iff Subtype.val_injective).mpr hp.support_nodup
  refine ⟨x.val,portmem.mp xp,y.val,p.map incl,pn,?_⟩
  intro z
  rw [support_map,List.mem_map]
  constructor
  · rintro ⟨u,_,rfl⟩
    exact u.property
  · intro zh
    exact ⟨⟨z,zh⟩,hs ⟨z,zh⟩,rfl⟩

private theorem splice_clique {i j : Bool} (ij : i≠j) (small : (S.H i).card=4)
    (atleast : 3≤G.dist a b) {x y : V} (ax : G.Adj a x) {q : G.Walk x y} (hq : q.IsPath)
    (qs : ∀ z,z∈q.support ↔ z∈S.H j) :
    ∃ u v : V, ∃ r : G.Walk u v, r.IsPath ∧ ∀ z,z∈r.support := by
  obtain ⟨u,ui,au⟩ := S.hita i
  obtain ⟨v,vi,bv⟩ := S.hitb i
  have uv : u≠v := fun e => by
    have bu : G.Adj b u := e.symm ▸ bv
    have d := G.dist_le (Walk.cons au (Walk.cons bu.symm Walk.nil))
    simp at d
    omega
  let T := ((S.H i).erase u).erase v
  have tc : T.card=2 := by
    rw [show T=((S.H i).erase u).erase v from rfl,
      card_erase_of_mem (mem_erase.mpr ⟨uv.symm,vi⟩),card_erase_of_mem ui,small]
  have to_side : T⊆S.H i := (erase_subset _ _).trans (erase_subset _ _)
  obtain ⟨m,mt,n,w,hw,wS,nT⟩ := path_from_universal_ports (G:=G) T (∅ : Finset V)
    (by simp) (by omega) (by simp) (by
      intro x xp y yp ne
      have hyp : y∈T := by simpa using yp
      exact S.side_four_clique atleast small (to_side xp) (to_side hyp) ne)
  have nT' : n∈T := nT (by simp [tc])
  have nm : n≠u := (mem_erase.mp (mem_erase.mp nT').2).1
  have mv : v≠m := (mem_erase.mp mt).1.symm
  have vn := S.side_four_clique atleast small vi (to_side mt) mv
  have nu := S.side_four_clique atleast small (to_side nT') ui nm
  let right : G.Walk n y := .cons nu (.cons au.symm (.cons ax q))
  let mid := w.append right
  have ms : mid.support = w.support ++ u :: a :: q.support := by simp [mid,right,support_append]
  have asu : a∉q.support := fun e => (S.off j).1 ((qs _).mp e)
  have usu : u∉a::q.support := by
    rw [List.mem_cons]
    rintro (e|e)
    · exact (S.off i).1 (e ▸ ui)
    · exact disjoint_left.mp (S.disjoint_sides ij) ui ((qs _).mp e)
  have lmem {z : V} (hz : z∈w.support) : z∈T := by simpa using (wS _).mp hz
  have mp : mid.IsPath := by
    apply IsPath.mk'
    rw [ms,List.nodup_append]
    refine ⟨hw.support_nodup,List.nodup_cons.mpr ⟨usu,List.nodup_cons.mpr ⟨asu,hq.support_nodup⟩⟩,?_⟩
    intro z zw zr
    have zt := lmem zw
    simp only [List.mem_cons] at zr
    rcases zr with rfl|rfl|zr
    · exact (mem_erase.mp (mem_erase.mp zt).2).1 rfl
    · exact (S.off i).1 (to_side zt)
    · exact disjoint_left.mp (S.disjoint_sides ij) (to_side zt) ((qs _).mp zr)
  have vno : v∉mid.support := by
    rw [ms,List.mem_append]
    rintro (h|h)
    · exact (mem_erase.mp (lmem h)).1 rfl
    simp only [List.mem_cons] at h
    rcases h with e|e|h
    · exact uv e.symm
    · exact (S.off i).1 (e ▸ vi)
    · exact disjoint_left.mp (S.disjoint_sides ij) vi ((qs _).mp h)
  have bno : b∉(Walk.cons vn mid).support := by
    simp only [support_cons,List.mem_cons,ms,List.mem_append]
    rintro (e|h|e|e|h)
    · exact (S.off i).2 (e.symm ▸ vi)
    · exact (S.off i).2 (to_side (lmem h))
    · exact (S.off i).2 (e.symm ▸ ui)
    · exact S.ab e.symm
    · exact (S.off j).2 ((qs _).mp h)
  refine ⟨b,y,.cons bv (.cons vn mid),(mp.cons vno).cons bno,?_⟩
  intro z
  simp only [support_cons,List.mem_cons,ms,List.mem_append,qs]
  rcases S.all z with za|zb|⟨k,hk⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl za))))
  · exact Or.inl zb
  by_cases eq : k=i
  · subst k
    by_cases zv : z=v
    · exact Or.inr (Or.inl zv)
    by_cases zu : z=u
    · exact Or.inr (Or.inr (Or.inr (Or.inl zu)))
    have zt : z∈T := mem_erase.mpr ⟨zv,mem_erase.mpr ⟨zu,hk⟩⟩
    exact Or.inr (Or.inr (Or.inl ((wS _).mpr (by simp [zt]))))
  · have kj : k=j := by cases i <;> cases j <;> cases k <;> simp_all
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (kj ▸ hk)))))

/-- A distance-three cut with component orders 4 and at most 6 is traceable. -/
theorem traceable_four_six (atleast : 3≤G.dist a b) (min2 : ∀ x,2≤G.degree x)
    {i j : Bool} (ij : i≠j) (four : (S.H i).card=4) (six : (S.H j).card≤6) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsPath ∧ ∀ z,z∈p.support := by
  obtain ⟨x,ax|bx,y,p,hp,hs⟩ := S.side_path atleast min2 j six
  · exact S.splice_clique ij four atleast ax hp hs
  · have far : 3≤G.dist b a := by rwa [dist_comm]
    exact S.flip.splice_clique ij four far bx hp hs

#print axioms traceable_four_six
end Graffiti189LongestPath.TwoCut.CutPair
