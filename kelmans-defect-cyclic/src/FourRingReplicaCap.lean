import FourRingReplica

open Finset SimpleGraph
namespace KelmansCactus.FourRingReplica.Layout
open ThreePort Substitute PathSlides FourRingBudget FourRingCap FourRingPhase
noncomputable section
variable {U J : Type*} [DecidableEq U]
variable {A : SimpleGraph U} {r : Bool→U}
variable (L : Layout A r)

def embedCap (i j : J) (ji : j≠i) : U↪Host J r where
  toFun u := if a : u=r false then (j,L.port (false,false)) else
    if b : u=r true then (j,L.port (false,true)) else (i,⟨u,a,b⟩)
  inj' := by
    intro x y eq
    dsimp only at eq
    by_cases xf : x=r false <;> by_cases yf : y=r false
    · exact xf.trans yf.symm
    · by_cases yt : y=r true
      · simp only [dif_pos xf,dif_neg yf,dif_pos yt] at eq
        have fail := L.port.injective (congrArg (fun t : Host J r=>t.2) eq)
        exact (Bool.false_ne_true (congrArg Prod.snd fail)).elim
      · simp only [dif_pos xf,dif_neg yf,dif_neg yt] at eq
        exact (ji (congrArg (fun t : Host J r=>t.1) eq)).elim
    · by_cases xt : x=r true
      · simp only [dif_neg xf,dif_pos yf,dif_pos xt] at eq
        have fail := L.port.injective (congrArg (fun t : Host J r=>t.2) eq)
        exact (Bool.false_ne_true (congrArg Prod.snd fail).symm).elim
      · simp only [dif_neg xf,dif_pos yf,dif_neg xt] at eq
        exact (ji (congrArg (fun t : Host J r=>t.1) eq).symm).elim
    · by_cases xt : x=r true <;> by_cases yt : y=r true
      · exact xt.trans yt.symm
      · simp only [dif_neg xf,dif_neg yf,dif_pos xt,dif_neg yt] at eq
        exact (ji (congrArg (fun t : Host J r=>t.1) eq)).elim
      · simp only [dif_neg xf,dif_neg yf,dif_neg xt,dif_pos yt] at eq
        exact (ji (congrArg (fun t : Host J r=>t.1) eq).symm).elim
      · simp only [dif_neg xf,dif_neg yf,dif_neg xt,dif_neg yt] at eq
        exact congrArg (fun t : Host J r=>t.2.val) eq

theorem embedCap_nonroot {i j : J} {ji : j≠i} (u : Piece r) :
    L.embedCap i j ji u.val=(i,u) := by
  simp [embedCap,u.property.1,u.property.2]

theorem embedCap_rootF {i j : J} {ji : j≠i} :
    L.embedCap i j ji (r false)=(j,L.port (false,false)) := by
  simp [embedCap]

theorem embedCap_rootT {i j : J} {ji : j≠i} :
    L.embedCap i j ji (r true)=(j,L.port (false,true)) := by
  simp [embedCap,L.rootEdge.ne.symm]

variable [Fintype U] [Fintype J] [DecidableEq J]
theorem cap_image (i j : J) (ji : j≠i) :
    cell (r:=r) i=((univ.erase (r false)).erase (r true)).map (L.embedCap i j ji) := by
  ext x
  constructor
  · intro m
    have xi := mem_cell.mp m
    refine mem_map.mpr ⟨x.2.val,mem_erase.mpr ⟨x.2.property.2,
      mem_erase.mpr ⟨x.2.property.1,mem_univ _⟩⟩,?_⟩
    rw [L.embedCap_nonroot x.2]
    exact Prod.ext xi.symm rfl
  · rintro m
    obtain ⟨u,um,rfl⟩ := mem_map.mp m
    let v : Piece r := ⟨u,(mem_erase.mp (mem_erase.mp um).2).1,(mem_erase.mp um).1⟩
    have h : L.embedCap i j ji u=(i,v) := L.embedCap_nonroot v
    rw [h]
    exact mem_cell.mpr rfl

/-- The actual two-root replica, rather than just abstract seam
hypotheses, transfers any below-one-hole-per-cell packing into
a full factor of its original shared cap. -/
theorem factor_of_few_vacancies (next : Equiv.Perm J) (fixed : ∀i,next i≠i)
    {P : Parts (Host J r)} (ok : PackIn (L.graph next fixed) univ P)
    (residue : Fintype.card U%3=0)
    (few : ((univ:Finset (Host J r))\P.biUnion id).card < Fintype.card J) :
    KelmansStarter.HasP3Factor A := by
  classical
  by_contra fail
  let e := fun i=>L.embedCap i (next i) (fixed i)
  let K : J→SimpleGraph (Host J r) := fun i=>A.map (e i)
  let root : J→Bool→Host J r := fun i b=>e i (r b)
  have cap (i : J) : Cap (G:=L.graph next fixed) (K i) (cell i) (L.p i) (root i) := by
    refine ⟨?_,SimpleGraph.map_adj_apply.mpr L.rootEdge,?_,?_⟩
    · intro b m
      have eq := mem_cell.mp m
      cases b
      · exact fixed i (congrArg Prod.fst (L.embedCap_rootF (i:=i) (j:=next i) (ji:=fixed i)).symm |>.trans eq)
      · exact fixed i (congrArg Prod.fst (L.embedCap_rootT (i:=i) (j:=next i) (ji:=fixed i)).symm |>.trans eq)
    · intro s
      have im : e i (L.port s).val=L.p i s := L.embedCap_nonroot (L.port s)
      rw [←im]
      exact SimpleGraph.map_adj_apply.mpr (L.conn s)
    · intro x xm y ym a
      have xx := mem_cell.mp xm
      have yy := mem_cell.mp ym
      have xIm : e i x.2.val=x := (L.embedCap_nonroot x.2).trans (Prod.ext xx.symm rfl)
      have yIm : e i y.2.val=y := (L.embedCap_nonroot y.2).trans (Prod.ext yy.symm rfl)
      exact ⟨x.2.val,y.2.val,(L.internal next (xx.trans yy.symm)).mp a,xIm,yIm⟩
  have bad (i : J) : ¬Closed (K i) (insert (root i false) (insert (root i true) (cell i))) := by
    intro h
    have image : insert (root i false) (insert (root i true) (cell i)) =
        (univ : Finset U).map (e i) := by
      rw [L.cap_image i (next i) (fixed i)]
      change insert ((e i) (r false)) (insert ((e i) (r true))
        (((univ.erase (r false)).erase (r true)).map (e i))) = _
      rw [←map_insert,←map_insert,insert_erase,insert_erase (mem_univ (r false))]
      exact mem_erase.mpr ⟨L.rootEdge.ne.symm,mem_univ _⟩
    rw [image] at h
    exact fail (FourReplace.full_factor_of_closed_image (e i)
      (fun _ _ a=>SimpleGraph.map_adj_apply.mp a) h)
  have mod1 (i : J) : (cell (r:=r) i).card%3=1 := by
    rw [L.cell_card i]
    have pos : 0<Fintype.card U := Fintype.card_pos_iff.mpr ⟨r false⟩
    omega
  have counted := one_vacancy_per_bad_cell ok cell cellDisjoint L.p (L.q next)
    next (L.reverse_seam next) (L.cellSeam next fixed) mod1 K root cap bad
  exact Nat.not_le_of_gt few counted

#print axioms factor_of_few_vacancies
end
end KelmansCactus.FourRingReplica.Layout
