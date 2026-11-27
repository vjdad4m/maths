import NearPerfectReplica

open Finset SimpleGraph
namespace KelmansCactus.NearPerfectReplica.Layout
open ThreePort Substitute PathSlides NearPerfectCommonCap
noncomputable section

variable {U J : Type*} [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J]
variable {A : SimpleGraph U} {B : SimpleGraph J} {r : U}
variable (L : Layout A B r)

omit [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J] in
/-- Every original root neighbor has a unique associated port. -/
theorem port_of_edge {u : Cell r} (edge : A.Adj r u.val) :
    ∃ j, L.port j=u := by
  obtain ⟨j,h⟩ := L.rootSlots.surjective ⟨u.val,edge⟩
  exact ⟨j,Subtype.ext (congrArg (fun v : A.neighborSet r=>v.val) h)⟩

omit [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J] in
theorem edge_of_port (j : Fin 3) : A.Adj r (L.port j).val :=
  (L.rootSlots j).property

/-- Neighbors in the host correspond bijectively to original
neighbors in the brick: the unique external edge at a port
replaces the removed root edge. -/
theorem cubic [DecidableRel A.Adj] (deg : ∀ x,A.degree x=3) (x : Host J r) :
    L.graph.degree x=3 := by
  classical
  let f : L.graph.neighborSet x → A.neighborSet x.2.val := fun y =>
    if same : y.val.1=x.1 then
      ⟨y.val.2.val,(L.internal_adj same.symm).mp y.property⟩
    else
      ⟨r,by
        obtain ⟨s,ex,_⟩ := (L.external_adj (Ne.symm same)).mp y.property
        have eq : (L.port s.2).val=x.2.val := congrArg (fun z : Host J r=>z.2.val) ex
        exact eq ▸ (L.edge_of_port s.2).symm⟩
  have fIn (y : L.graph.neighborSet x) (h : y.val.1=x.1) : (f y).val=y.val.2.val := by
    simp [f,h]
  have fOut (y : L.graph.neighborSet x) (h : y.val.1≠x.1) : (f y).val=r := by
    simp [f,h]
  have inj : Function.Injective f := by
    intro y z eq
    have vals : (f y).val=(f z).val := congrArg (fun v : A.neighborSet x.2.val=>v.val) eq
    by_cases yy : y.val.1=x.1
    · by_cases zz : z.val.1=x.1
      · rw [fIn y yy,fIn z zz] at vals
        exact Subtype.ext (Prod.ext (yy.trans zz.symm) (Subtype.ext vals))
      · rw [fIn y yy,fOut z zz] at vals
        exact (y.val.2.property vals).elim
    · by_cases zz : z.val.1=x.1
      · rw [fOut y yy,fIn z zz] at vals
        exact (z.val.2.property vals.symm).elim
      · obtain ⟨s,ex,ey⟩ := (L.external_adj (Ne.symm yy)).mp y.property
        obtain ⟨t,fx,ez⟩ := (L.external_adj (Ne.symm zz)).mp z.property
        have e := L.p_inj (ex.trans fx.symm)
        exact Subtype.ext (ey.symm.trans (e ▸ ez))
  have surj : Function.Surjective f := by
    intro z
    by_cases same : z.val=r
    · have vz : A.Adj x.2.val z.val := z.property
      have edge : A.Adj r x.2.val := by simpa only [same] using vz.symm
      obtain ⟨j,jp⟩ := L.port_of_edge edge
      have ex : L.p (x.1,j)=x := Prod.ext rfl jp
      have e : L.graph.Adj x (L.q (x.1,j)) := ex ▸ L.edge_at_slot (x.1,j)
      exact ⟨⟨L.q (x.1,j),e⟩,Subtype.ext
        ((fOut ⟨L.q (x.1,j),e⟩ (L.target_ne (x.1,j))).trans same.symm)⟩
    · let y : Host J r := (x.1,⟨z.val,same⟩)
      have e : L.graph.Adj x y := (L.internal_adj (x:=x) (y:=y) rfl).mpr z.property
      exact ⟨⟨y,e⟩,Subtype.ext (fIn ⟨y,e⟩ rfl)⟩
  rw [←card_neighborSet_eq_degree,Fintype.card_of_bijective ⟨inj,surj⟩,
    card_neighborSet_eq_degree]
  exact deg _

def embedCap (i k : J) (ki : k≠i) : U↪Host J r where
  toFun u := if same : u=r then (k,L.port 0) else (i,⟨u,same⟩)
  inj' := by
    intro u v eq
    dsimp only at eq
    by_cases ur : u=r
    · by_cases vr : v=r
      · exact ur.trans vr.symm
      · rw [dif_pos ur,dif_neg vr] at eq
        exact (ki (congrArg Prod.fst eq)).elim
    · by_cases vr : v=r
      · rw [dif_neg ur,dif_pos vr] at eq
        exact (ki ((congrArg Prod.fst eq).symm)).elim
      · rw [dif_neg ur,dif_neg vr] at eq
        exact congrArg (fun z : Host J r=>z.2.val) eq

omit [Fintype U] [Fintype J] [DecidableEq J] in
theorem embedCap_of_nonroot {i k : J} {ki : k≠i} {u : U} (h : u≠r) :
    L.embedCap i k ki u=(i,⟨u,h⟩) := by
  simp [embedCap,h]

theorem cell_image (i k : J) (ki : k≠i) :
    cell (r:=r) i=(univ.erase r).map (L.embedCap i k ki) := by
  ext x
  constructor
  · intro m
    have ix := mem_cell.mp m
    refine mem_map.mpr ⟨x.2.val,mem_erase.mpr ⟨x.2.property,mem_univ _⟩,?_⟩
    rw [L.embedCap_of_nonroot x.2.property]
    exact Prod.ext ix.symm (Subtype.ext rfl)
  · rintro m
    obtain ⟨u,um,rfl⟩ := mem_map.mp m
    rw [L.embedCap_of_nonroot (mem_erase.mp um).1]
    exact mem_cell.mpr rfl

theorem close_of_few_vacancies {P : Parts (Host J r)} (ok : PackIn L.graph univ P)
    (res : Fintype.card U%3=0) (cardJ : 2≤Fintype.card J)
    (budget : 2*((univ : Finset (Host J r))\P.biUnion id).card < Fintype.card J) :
    KelmansStarter.HasP3Factor A := by
  classical
  have other (i : J) : ∃ k : J,k≠i := by
    haveI : Nontrivial J := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne i
  choose k neq using other
  let e := fun i=>L.embedCap i (k i) (neq i)
  apply few_holes_on_replica_forces_original_factor ok r
    (fun j=>(L.port j).val) (L.edge_of_port) res e cell
    (fun i=>L.cell_image i (k i) (neq i)) cells_disjoint L.p L.q ?_
    L.mate L.mate_sq (fun _=>rfl) L.cell_seam ?_ budget
  · intro i j
    change (i,L.port j)=L.embedCap i (k i) (neq i) (L.port j).val
    rw [L.embedCap_of_nonroot (L.port j).property]
  · intro i x xc y yc adj
    have xEq := mem_cell.mp xc
    have yEq := mem_cell.mp yc
    have xIm : e i x.2.val=x :=
      (L.embedCap_of_nonroot x.2.property).trans (Prod.ext xEq.symm (Subtype.ext rfl))
    have yIm : e i y.2.val=y :=
      (L.embedCap_of_nonroot y.2.property).trans (Prod.ext yEq.symm (Subtype.ext rfl))
    exact ⟨x.2.val,y.2.val,(L.internal_adj (xEq.trans yEq.symm)).mp adj,xIm,yIm⟩

#print axioms cubic
#print axioms close_of_few_vacancies
end
end KelmansCactus.NearPerfectReplica.Layout
