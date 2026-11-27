import HubDeletion
open private treeNumber_after_delete_le from CubicDeletion
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V} {x y p r : V}

def hubFill (G : SimpleGraph V) {r y : V} (ry : r ≠ y) : SimpleGraph V where
  Adj s t := G.Adj s t ∨ (s=r ∧ t=y) ∨ (s=y ∧ t=r)
  symm := by rintro s t (e|⟨h,k⟩|⟨h,k⟩); exact Or.inl e.symm; exact Or.inr (Or.inr ⟨k,h⟩); exact Or.inr (Or.inl ⟨k,h⟩)
  loopless := by rintro s (e|⟨h,k⟩|⟨h,k⟩); exact G.loopless _ e; exact ry (h.symm.trans k); exact ry (k.symm.trans h)

variable [Fintype V] [DecidableEq V]
omit [DecidableEq V] in
private theorem tree_mono_embedding {W : Type*} [Fintype W] {H : SimpleGraph W}
    (f : W ↪ V) (chart : ∀ s t, G.Adj (f s) (f t) ↔ H.Adj s t) : treeNumber H ≤ treeNumber G := by
  classical
  unfold treeNumber
  apply Finset.sup_le
  intro T hT
  have tree := (Finset.mem_filter.mp hT).2
  let e : (↑T : Set W) ↪ V := (Function.Embedding.subtype _).trans f
  simpa using card_le_treeNumber_of_induced_copy e (fun s t => chart s.val t.val) tree

theorem hubFill_budget (ry : r ≠ y) (rx : r ≠ x) (yx : y ≠ x) (px : p ≠ x)
    (only : ∀ v, G.Adj p v ↔ v=r ∨ v=x ∨ v=y) :
    treeNumber ((hubFill G ry).induce (HubKeep x p)) ≤ treeNumber G := by
  classical
  let U : Set V := {v | v ≠ x}
  let H := G.induce U
  let R : U := ⟨r,rx⟩
  let Y : U := ⟨y,yx⟩
  let P : U := ⟨p,px⟩
  let D : Finset U := {R,Y}
  let B : Set U := {P}
  have bd : ShoreBoundary H D B := by
    intro s sm t _ st
    have eq : s=P := sm
    have e : G.Adj p t.val := by subst s; exact st
    rcases (only _).mp e with h|h|h
    · exact Finset.mem_insert_self R _ |> fun m => (show t=R from Subtype.ext h).symm ▸ m
    · exact (t.property h).elim
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (Subtype.ext h))
  have pc : (H.induce B).Preconnected := by
    intro s t
    have eq : s=t := Subtype.ext ((show s.val=P from s.property).trans (show t.val=P from t.property).symm)
    exact eq ▸ SimpleGraph.Reachable.rfl
  have hit : ∀ s ∈ D, ∃ t ∈ B, H.Adj s t := by
    intro s sm
    refine ⟨P,rfl,?_⟩
    rcases (show s=R ∨ s=Y by simpa [D] using sm) with e|e
    · exact e.symm ▸ ((only r).mpr (Or.inl rfl)).symm
    · exact e.symm ▸ ((only y).mpr (Or.inr (Or.inr rfl))).symm
  let f : HubKeep x p ↪ (Bᶜ : Set U) := ⟨fun v => ⟨⟨v.val,v.property.1⟩,fun e => v.property.2 (congrArg Subtype.val (show (⟨v.val,v.property.1⟩ : U)=P from e))⟩,
    fun s t e => Subtype.ext (congrArg (fun w : (Bᶜ : Set U) => w.val.val) e)⟩
  apply (tree_mono_embedding (G:=cutTorso H D B) f ?_).trans
    ((cutTorso_treeNumber_le bd pc hit).trans (treeNumber_after_delete_le (G:=G) x))
  intro s t
  have mem (v : HubKeep x p) : (f v).val ∈ D ↔ v.val=r ∨ v.val=y := by
    simp only [D,Finset.mem_insert,Finset.mem_singleton]
    exact or_congr Subtype.ext_iff Subtype.ext_iff
  constructor
  · rintro (edge|⟨ne,ss,tt⟩)
    · exact Or.inl edge
    · rcases (mem s).mp ss with h|h <;> rcases (mem t).mp tt with k|k
      · exact (ne (congrArg f (Subtype.ext (h.trans k.symm)))).elim
      · exact Or.inr (Or.inl ⟨h,k⟩)
      · exact Or.inr (Or.inr ⟨h,k⟩)
      · exact (ne (congrArg f (Subtype.ext (h.trans k.symm)))).elim
  · rintro (edge|⟨h,k⟩|⟨h,k⟩)
    · exact Or.inl edge
    · exact Or.inr ⟨fun e => ry (h.symm.trans ((congrArg Subtype.val (f.injective e)).trans k)),(mem s).mpr (Or.inl h),(mem t).mpr (Or.inr k)⟩
    · exact Or.inr ⟨fun e => ry (k.symm.trans ((congrArg Subtype.val (f.injective e)).symm.trans h)),(mem s).mpr (Or.inr h),(mem t).mpr (Or.inl k)⟩

theorem hubFill_connectivity [DecidableRel G.Adj] (conn : ConnectivityAtLeast G 3)
    (order : 6 ≤ Fintype.card V) (cross : CrossingBetweenSurvivingEdges G) (xp : x ≠ p)
    (ry : r ≠ y) (safe : ∀ v, G.Adj x v → G.degree v = 3 → v=p)
    (only : ∀ v, G.Adj p v ↔ v=r ∨ v=x ∨ v=y) :
    ConnectivityAtLeast ((hubFill G ry).induce (HubKeep x p)) 3 := by
  classical
  apply connectivity_after_hub_pair conn order cross xp safe (fun _ _ e => Or.inl e)
  intro D small
  by_cases any : ∃ w : Survives D, G.Adj p w.val.val
  · obtain ⟨w,wp⟩ := any
    refine ⟨w,?_⟩
    intro v vp
    have ends (s : Survives D) (h : G.Adj p s.val.val) : s.val.val=r ∨ s.val.val=y :=
      ((only _).mp h).elim Or.inl (fun e => Or.inr (e.resolve_left s.val.property.1))
    rcases ends w wp with h|h <;> rcases ends v vp with k|k
    · exact Or.inr (Subtype.ext (Subtype.ext (h.trans k.symm)))
    · exact Or.inl (Or.inr (Or.inl ⟨h,k⟩))
    · exact Or.inl (Or.inr (Or.inr ⟨h,k⟩))
    · exact Or.inr (Subtype.ext (Subtype.ext (h.trans k.symm)))
  · have sz := hubKeep_card xp
    have room : D.card < (Finset.univ : Finset (HubKeep x p)).card := by rw [Finset.card_univ]; omega
    obtain ⟨w,_,off⟩ := Finset.exists_mem_not_mem_of_card_lt_card room
    exact ⟨⟨w,off⟩,fun v h => (any ⟨v,h⟩).elim⟩

#print axioms hubFill_budget
#print axioms hubFill_connectivity
end Graffiti199Depleted.Catalogue.Incomplete

