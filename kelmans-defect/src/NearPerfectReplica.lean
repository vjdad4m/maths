import NearPerfectCommonCap

open Finset SimpleGraph
namespace KelmansCactus.NearPerfectReplica
open ThreePort Substitute PathSlides NearPerfectCommonCap
noncomputable section

variable {U J : Type*}

/-- Three ports in each base vertex, together with a common rooted brick.
The orientation of each seam is the correspondence between the two
appearances of the same base edge in the endpoint's neighbor set. -/
structure Layout (A : SimpleGraph U) (B : SimpleGraph J) (r : U) where
  rootSlots : Fin 3 ≃ A.neighborSet r
  baseSlots : ∀ i : J, Fin 3 ≃ B.neighborSet i

def Layout.fromCubic (A : SimpleGraph U) (B : SimpleGraph J) (r : U)
    [Fintype U] [Fintype J] [DecidableRel A.Adj] [DecidableRel B.Adj]
    (da : ∀ v,A.degree v=3) (db : ∀ i,B.degree i=3) : Layout A B r :=
  ⟨(Fintype.equivFinOfCardEq ((card_neighborSet_eq_degree A r).trans (da r))).symm,
    fun i=>(Fintype.equivFinOfCardEq ((card_neighborSet_eq_degree B i).trans (db i))).symm⟩

abbrev Cell (r : U) := {v : U // v ≠ r}
abbrev Host (J : Type*) (r : U) := J × Cell r

variable {A : SimpleGraph U} {B : SimpleGraph J} {r : U}
variable (L : Layout A B r)

namespace Layout
def port (j : Fin 3) : Cell r :=
  ⟨(L.rootSlots j).val,(L.rootSlots j).property.ne.symm⟩

theorem port_inj : Function.Injective L.port := by
  intro a b e
  exact L.rootSlots.injective (Subtype.ext (congrArg (fun v : Cell r=>v.val) e))

def p (s : J×Fin 3) : Host J r := (s.1,L.port s.2)

theorem p_inj : Function.Injective L.p := by
  intro a b e
  exact Prod.ext (congrArg (fun v : Host J r=>v.1) e)
    (L.port_inj (congrArg (fun v : Host J r=>v.2) e))

def target (s : J×Fin 3) : J := (L.baseSlots s.1 s.2).val

theorem at_target (s : J×Fin 3) : B.Adj s.1 (L.target s) :=
  (L.baseSlots s.1 s.2).property

theorem target_ne (s : J×Fin 3) : L.target s≠s.1 := (L.at_target s).ne.symm

def mate (s : J×Fin 3) : J×Fin 3 :=
  (L.target s,(L.baseSlots (L.target s)).symm ⟨s.1,(L.at_target s).symm⟩)

@[simp] theorem mate_fst (s : J×Fin 3) : (L.mate s).1=L.target s := rfl

@[simp] theorem target_mate (s : J×Fin 3) : L.target (L.mate s)=s.1 := by
  unfold target mate
  simp

theorem slot_eq_of_target {s t : J×Fin 3} (fst : s.1=t.1)
    (snd : L.target s=L.target t) : s=t := by
  obtain ⟨i,j⟩ := s
  obtain ⟨k,l⟩ := t
  change i=k at fst
  subst k
  exact Prod.ext rfl ((L.baseSlots i).injective (Subtype.ext snd))

theorem mate_sq : Function.Involutive L.mate := by
  intro s
  exact L.slot_eq_of_target (L.target_mate s) (L.target_mate (L.mate s))

def q (s : J×Fin 3) : Host J r := L.p (L.mate s)

theorem q_inj : Function.Injective L.q := L.p_inj.comp L.mate_sq.injective

def graph : SimpleGraph (Host J r) where
  Adj x y := (x.1=y.1 ∧ A.Adj x.2.val y.2.val) ∨ ∃ s, L.p s=x ∧ L.q s=y
  symm := by
    rintro x y (⟨same,e⟩|⟨s,ex,ey⟩)
    · exact Or.inl ⟨same.symm,e.symm⟩
    · exact Or.inr ⟨L.mate s,ey,by simpa only [q,L.mate_sq s] using ex⟩
  loopless := by
    rintro x (⟨_,e⟩|⟨s,ex,ey⟩)
    · exact A.loopless x.2.val e
    · exact L.target_ne s (congrArg Prod.fst (ey.trans ex.symm))

instance : DecidableRel L.graph.Adj := Classical.decRel _

theorem seam_has_distinct_cells (s : J×Fin 3) : (L.p s).1≠(L.q s).1 :=
  (L.target_ne s).symm

theorem internal_adj {x y : Host J r} (same : x.1=y.1) :
    L.graph.Adj x y ↔ A.Adj x.2.val y.2.val := by
  constructor
  · rintro (⟨_,h⟩|⟨s,rfl,rfl⟩)
    · exact h
    · exact False.elim (L.seam_has_distinct_cells s same)
  · exact fun h => Or.inl ⟨same,h⟩

theorem external_adj {x y : Host J r} (diff : x.1≠y.1) :
    L.graph.Adj x y ↔ ∃ s, L.p s=x ∧ L.q s=y := by
  exact or_iff_right (fun h=>diff h.1)

theorem edge_at_slot (s : J×Fin 3) : L.graph.Adj (L.p s) (L.q s) :=
  Or.inr ⟨s,rfl,rfl⟩

variable [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J]

def cell (i : J) : Finset (Host J r) := univ.filter (fun x=>x.1=i)

@[simp] theorem mem_cell {i : J} {x : Host J r} : x ∈ cell (r:=r) i ↔ x.1=i := by
  simp [cell]

theorem cells_disjoint : (↑(univ : Finset J) : Set J).PairwiseDisjoint (cell (r:=r)) := by
  intro a _ b _ ne
  exact disjoint_left.mpr fun x xa xb=>ne ((mem_cell.mp xa).symm.trans (mem_cell.mp xb))

theorem cell_seam (i : J) :
    Seam (G:=L.graph) (cell i) (fun j=>L.p (i,j)) (fun j=>L.q (i,j)) := by
  refine ⟨fun j=>mem_cell.mpr rfl,fun j h=>L.target_ne (i,j) (mem_cell.mp h),
    fun j k e=>congrArg Prod.snd (L.p_inj e),
    fun j k e=>congrArg Prod.snd (L.q_inj e),?_⟩
  intro x xc y ny
  have xi := mem_cell.mp xc
  have different : x.1≠y.1 := fun eq=>ny (mem_cell.mpr (eq.symm.trans xi))
  rw [L.external_adj different]
  constructor
  · rintro ⟨⟨k,j⟩,xx,yy⟩
    have kEq : k=i := (congrArg Prod.fst xx).trans xi
    exact ⟨j,kEq ▸ xx,kEq ▸ yy⟩
  · rintro ⟨j,xx,yy⟩
    exact ⟨(i,j),xx,yy⟩

end Layout

theorem host_card [Fintype U] [DecidableEq U] [Fintype J] :
    Fintype.card (Host J r)=Fintype.card J*(Fintype.card U-1) := by
  rw [Fintype.card_prod]
  congr 1
  have c := Fintype.card_subtype_compl (fun x:U=>x=r)
  simpa only [Fintype.card_unique] using c

#print axioms Layout.cell_seam
#print axioms host_card
end
end KelmansCactus.NearPerfectReplica
