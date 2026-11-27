import CubicCutShore

open private three_names_exhaust_neighbors from DepletedFootprint

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

private def threeArms (i j : Fin 6) : Prop :=
  let s := min i.val j.val
  let t := max i.val j.val
  (s = 0 ∧ (t = 1 ∨ t = 3 ∨ t = 5)) ∨ (s = 1 ∧ t = 2) ∨ (s = 3 ∧ t = 4)

private theorem armParents : ∀ i : Fin 6, i ≠ 0 →
    ∃ j : Fin 6, threeArms i j ∧ j < i ∧
      ∀ k : Fin 6, threeArms i k → k < i → k = j := by
  unfold threeArms
  decide

omit [Fintype V] [DecidableRel G.Adj] in
private theorem nonisolated_in_shore {A : Set V} {v : V}
    (conn : (G.induce A).Preconnected) (vA : v ∈ A)
    (two : ∃ a ∈ A, ∃ b ∈ A, a ≠ b) : ∃ x ∈ A, G.Adj v x := by
  classical
  obtain ⟨a,aA,b,bA,ab⟩ := two
  have other : ∃ x ∈ A, v ≠ x := by
    by_cases e : v = a
    · exact ⟨b,bA,e.trans_ne ab⟩
    · exact ⟨a,aA,e⟩
  obtain ⟨x,xA,ne⟩ := other
  obtain ⟨p⟩ := conn ⟨v,vA⟩ ⟨x,xA⟩
  have nn := Walk.not_nil_of_ne (p := p) (fun e => ne (congrArg Subtype.val e))
  exact ⟨p.snd.val,p.snd.property,p.adj_snd nn⟩

omit [Fintype V] [DecidableRel G.Adj] in
private theorem shore_anticomplete {D : Finset V} {A B : Set V}
    (outsideB : ∀ d ∈ D, d ∉ B) (boundary : ShoreBoundary G D A)
    (apart : Disjoint A B) {x y : V} (xA : x ∈ A) (yB : y ∈ B) : ¬ G.Adj x y :=
  fun e => outsideB y (boundary x xA y (fun h => Set.disjoint_left.mp apart h yB) e) yB

set_option maxHeartbeats 2000000 in
/-- A cubic cut vertex cannot meet three components when two of
the components have edges. Two length-two arms and the third contact
would give an induced tree on six vertices. -/
theorem cubic_port_three_shores_impossible {D : Finset V} {A B C : Set V} {r : V}
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (size : D.card = 3)
    (rD : r ∈ D) (degree : G.degree r = 3)
    (outsideA : ∀ d ∈ D, d ∉ A) (outsideB : ∀ d ∈ D, d ∉ B) (outsideC : ∀ d ∈ D, d ∉ C)
    (apartAB : Disjoint A B) (apartAC : Disjoint A C) (apartBC : Disjoint B C)
    (boundaryA : ShoreBoundary G D A) (boundaryB : ShoreBoundary G D B)
    (boundaryC : ShoreBoundary G D C)
    (connA : (G.induce A).Preconnected) (connB : (G.induce B).Preconnected)
    (twoA : ∃ a ∈ A, ∃ b ∈ A, a ≠ b) (twoB : ∃ a ∈ B, ∃ b ∈ B, a ≠ b)
    (nonemptyC : C.Nonempty) : False := by
  classical
  obtain ⟨a,aA,ra⟩ := contact_of_shore conn size.le outsideA boundaryA
    (by obtain ⟨v,vA,_⟩ := twoA; exact ⟨v,vA⟩) rD
  obtain ⟨b,bB,rb⟩ := contact_of_shore conn size.le outsideB boundaryB
    (by obtain ⟨v,vB,_⟩ := twoB; exact ⟨v,vB⟩) rD
  obtain ⟨c,cC,rc⟩ := contact_of_shore conn size.le outsideC boundaryC nonemptyC rD
  obtain ⟨u,uA,au⟩ := nonisolated_in_shore connA aA twoA
  obtain ⟨v,vB,bv⟩ := nonisolated_in_shore connB bB twoB
  have dis {X Y : Set V} (d : Disjoint X Y) {x y : V} (xX : x ∈ X) (yY : y ∈ Y) : x ≠ y :=
    fun h => Set.disjoint_left.mp d xX (h.symm ▸ yY)
  have ab := dis apartAB aA bB
  have ac := dis apartAC aA cC
  have bc := dis apartBC bB cC
  have all (x : V) (hx : G.Adj r x) : x = a ∨ x = b ∨ x = c := by
    obtain ⟨i,h,e⟩ := three_names_exhaust_neighbors (Function.Embedding.refl V)
      ab ac bc degree ra rb rc x hx
    have ix : i = x := e
    simpa only [← ix,List.mem_cons,List.not_mem_nil,or_false] using h
  have ru : ¬ G.Adj r u := fun e => (all u e).elim au.ne.symm
    (fun h => h.elim (dis apartAB uA bB) (dis apartAC uA cC))
  have rv : ¬ G.Adj r v := fun e => (all v e).elim (dis apartAB aA vB).symm
    (fun h => h.elim bv.ne.symm (dis apartBC vB cC))
  have ur : ¬ G.Adj u r := fun e => ru e.symm
  have vr : ¬ G.Adj v r := fun e => rv e.symm
  have rna : r ≠ a := fun e => outsideA r rD (e.symm ▸ aA)
  have rnu : r ≠ u := fun e => outsideA r rD (e.symm ▸ uA)
  have rnb : r ≠ b := fun e => outsideB r rD (e.symm ▸ bB)
  have rnv : r ≠ v := fun e => outsideB r rD (e.symm ▸ vB)
  have rnc : r ≠ c := fun e => outsideC r rD (e.symm ▸ cC)
  have av := dis apartAB aA vB
  have ub := dis apartAB uA bB
  have uv := dis apartAB uA vB
  have uc := dis apartAC uA cC
  have vc := dis apartBC vB cC
  let f : Fin 6 → V := ![r,a,u,b,v,c]
  have nd : [r,a,u,b,v,c].Nodup := by
    simp [rna,rnu,rnb,rnv,rnc,au.ne,bv.ne,ab,ac,bc,av,ub,uv,uc,vc]
  have get (i : Fin 6) : f i = [r,a,u,b,v,c].get i := by fin_cases i <;> rfl
  have inj : Function.Injective f := fun i j e =>
    (List.nodup_iff_injective_get.mp nd) ((get i).symm.trans (e.trans (get j)))
  have chart (i j : Fin 6) : G.Adj (f i) (f j) ↔ threeArms i j := by
    fin_cases i <;> fin_cases j <;>
      simp (config := { decide := true }) [f,threeArms,ra,ra.symm,rb,rb.symm,rc,rc.symm,
        au,au.symm,bv,bv.symm,ru,rv,ur,vr,
        shore_anticomplete outsideB boundaryA apartAB aA bB,
        shore_anticomplete outsideB boundaryA apartAB aA vB,
        shore_anticomplete outsideB boundaryA apartAB uA bB,
        shore_anticomplete outsideB boundaryA apartAB uA vB,
        shore_anticomplete outsideC boundaryA apartAC aA cC,
        shore_anticomplete outsideC boundaryA apartAC uA cC,
        shore_anticomplete outsideC boundaryB apartBC bB cC,
        shore_anticomplete outsideC boundaryB apartBC vB cC,
        G.adj_comm b a,G.adj_comm v a,G.adj_comm b u,G.adj_comm v u,
        G.adj_comm c a,G.adj_comm c u,G.adj_comm c b,G.adj_comm c v]
  have six : 6 ≤ treeNumber G := by
    apply six_le_treeNumber_of_ordering ⟨f,inj⟩
    intro i hi
    obtain ⟨j,e,lt,only⟩ := armParents i hi
    exact ⟨j,(chart _ _).mpr e,lt,fun k ek lk => only k ((chart _ _).mp ek) lk⟩
  omega

#print axioms cubic_port_three_shores_impossible

end Graffiti199Depleted.Catalogue
