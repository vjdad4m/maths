import CutTorsoBudget

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem two_step_into_shore {A : Set V} {r : V} (conn : (G.induce A).Preconnected)
    (some : ∃ x ∈ A, G.Adj r x) (missing : ∃ y ∈ A, ¬ G.Adj r y) :
    ∃ x ∈ A, ∃ y ∈ A, G.Adj r x ∧ G.Adj x y ∧ ¬ G.Adj r y := by
  obtain ⟨x,xA,rx⟩ := some
  obtain ⟨y,yA,ry⟩ := missing
  obtain ⟨p⟩ := conn ⟨x,xA⟩ ⟨y,yA⟩
  obtain ⟨u,hu,v,hv,uv⟩ :=
    crossingOnWalk (U := {v : A | G.Adj r v.val}) p rx ry
  exact ⟨u.val,u.property,v.val,v.property,hu,uv,hv⟩

private def joinedTree (fork : Bool) (i j : Fin 6) : Prop :=
  let s := min i.val j.val
  let t := max i.val j.val
  (s = 0 ∧ (t = 1 ∨ t = 4)) ∨ (s = 1 ∧ (t = 2 ∨ (fork = true ∧ t = 3))) ∨
    (fork = false ∧ s = 2 ∧ t = 3) ∨ (s = 4 ∧ t = 5)

private theorem joinedTree_parents (fork : Bool) : ∀ i : Fin 6, i ≠ 0 →
    ∃ j : Fin 6, joinedTree fork i j ∧ j < i ∧
      ∀ k : Fin 6, joinedTree fork i k → k < i → k = j := by
  cases fork <;> unfold joinedTree <;> decide

variable [Fintype V]

set_option maxHeartbeats 2000000 in
/-- A port with one contact into one shore and an induced two-step
path into a second shore forces the first shore to be a clique. -/
theorem clique_of_unique_contact_and_two_step {A B : Set V} {r a b c : V}
    (budget : treeNumber G ≤ 5)
    (apart : Disjoint A B) (anti : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y)
    (rA : r ∉ A) (rB : r ∉ B)
    (conn : (G.induce A).Preconnected)
    (aA : a ∈ A) (ra : G.Adj r a) (only : ∀ x ∈ A, G.Adj r x → x = a)
    (bB : b ∈ B) (cB : c ∈ B) (rb : G.Adj r b) (bc : G.Adj b c) (rc : ¬ G.Adj r c) :
    A.Pairwise G.Adj := by
  classical
  have impossible {u v : V} (uA : u ∈ A) (vA : v ∈ A)
      (au : G.Adj a u) (av : a ≠ v) (uv : u ≠ v) (fork : Bool)
      (edgeAV : G.Adj a v ↔ fork = true) (edgeUV : G.Adj u v ↔ fork = false) : False := by
    have dis (x : V) (xA : x ∈ A) (y : V) (yB : y ∈ B) : x ≠ y :=
      fun e => Set.disjoint_left.mp apart xA (e.symm ▸ yB)
    have rna : r ≠ a := fun e => rA (e.symm ▸ aA)
    have rnu : r ≠ u := fun e => rA (e.symm ▸ uA)
    have rnv : r ≠ v := fun e => rA (e.symm ▸ vA)
    have rnb : r ≠ b := fun e => rB (e.symm ▸ bB)
    have rnc : r ≠ c := fun e => rB (e.symm ▸ cB)
    have anB := dis a aA b bB
    have anC := dis a aA c cB
    have unB := dis u uA b bB
    have unC := dis u uA c cB
    have vnB := dis v vA b bB
    have vnC := dis v vA c cB
    have ru : ¬ G.Adj r u := fun e => au.ne ((only u uA e).symm)
    have rv : ¬ G.Adj r v := fun e => av ((only v vA e).symm)
    have ur : ¬ G.Adj u r := fun e => ru e.symm
    have vr : ¬ G.Adj v r := fun e => rv e.symm
    have cr : ¬ G.Adj c r := fun e => rc e.symm
    let f : Fin 6 → V := ![r,a,u,v,b,c]
    have nd : [r,a,u,v,b,c].Nodup := by
      simp [rna,rnu,rnv,rnb,rnc,au.ne,av,uv,bc.ne,anB,anC,unB,unC,vnB,vnC]
    have get (i : Fin 6) : f i = [r,a,u,v,b,c].get i := by fin_cases i <;> rfl
    have inj : Function.Injective f := fun i j e =>
      (List.nodup_iff_injective_get.mp nd) ((get i).symm.trans (e.trans (get j)))
    have chart (i j : Fin 6) : G.Adj (f i) (f j) ↔ joinedTree fork i j := by
      fin_cases i <;> fin_cases j <;>
        simp (config := { decide := true }) [f,joinedTree,ra,ra.symm,rb,rb.symm,bc,bc.symm,
          au,au.symm,ru,rv,rc,ur,vr,cr,
          edgeAV,edgeUV,G.adj_comm v a,G.adj_comm v u,
          anti a aA b bB,anti a aA c cB,anti u uA b bB,anti u uA c cB,anti v vA b bB,anti v vA c cB,
          G.adj_comm b a,G.adj_comm c a,G.adj_comm b u,G.adj_comm c u,G.adj_comm b v,G.adj_comm c v]
    have six : 6 ≤ treeNumber G := by
      apply six_le_treeNumber_of_ordering ⟨f,inj⟩
      intro i hi
      obtain ⟨j,e,lt,uniq⟩ := joinedTree_parents fork i hi
      exact ⟨j,(chart _ _).mpr e,lt,fun k adj hk => uniq k ((chart _ _).mp adj) hk⟩
    omega
  have universal : ∀ v ∈ A, v ≠ a → G.Adj a v := by
    intro v vA va
    by_cases av : G.Adj a v
    · exact av
    · let a' : A := ⟨a,aA⟩
      let v' : A := ⟨v,vA⟩
      have reach := conn a' v'
      have ne : a' ≠ v' := fun e => va (congrArg (fun t : A => t.val) e).symm
      obtain ⟨p,hp⟩ := reach.exists_walk_length_eq_dist
      have long : 1 < p.length := hp.symm ▸ reach.one_lt_dist_of_ne_of_not_adj ne av
      let u := p.getVert 1
      let w := p.getVert 2
      have au' := p.adj_getVert_succ (i := 0) (by omega)
      rw [p.getVert_zero] at au'
      have au : G.Adj a u.val := au'
      have uw : G.Adj u.val w.val := p.adj_getVert_succ (i := 1) long
      have aw' := geodesic_adj_iff p hp (i := 0) (j := 2) (by omega) (by omega)
      rw [p.getVert_zero] at aw'
      have aw : ¬ G.Adj a w.val := fun e => by have := aw'.mp e; omega
      have wa : a ≠ w.val := by
        intro eq
        have atStart := (p.isPath_of_length_eq_dist hp).getVert_eq_start_iff (i := 2) (by omega)
        have index := atStart.mp (Subtype.ext eq.symm)
        omega
      exact (impossible u.property w.property au wa uw.ne false
        (by simpa using aw) (by simp [uw])).elim
  intro u uA v vA uv
  by_cases edge : G.Adj u v
  · exact edge
  have ua : u ≠ a := fun h => edge (h.symm ▸ universal v vA (fun e => uv (h.trans e.symm)))
  have va : v ≠ a := fun h => edge ((h.symm ▸ universal u uA (fun e => uv (e.trans h.symm))).symm)
  exact (impossible uA vA (universal u uA ua) va.symm uv true
    (by simp [universal v vA va]) (by simpa using edge)).elim

#print axioms clique_of_unique_contact_and_two_step

end Graffiti199Depleted.Catalogue
