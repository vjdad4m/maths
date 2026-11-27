import SparseBlocks180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

omit [Fintype V] [DecidableEq V] in
private theorem lift_ind (N C : Finset V) (ic : Indep G C) (p : Bool)
    (clean : p=true → Disjoint C N) : Indep (ear G N) (lift C p) := by
  rintro (u|u) hu (v|v) hv ne e
  · exact ic _ ((inl_lift ..).mp hu) _ ((inl_lift ..).mp hv) (fun h => ne (congrArg Sum.inl h)) e
  · exact disjoint_left.mp (clean ((inr_lift ..).mp hv)) ((inl_lift ..).mp hu) e
  · exact disjoint_left.mp (clean ((inr_lift ..).mp hu)) ((inl_lift ..).mp hv) e
  · exact e.elim

omit [Fintype V] in
theorem extend_color (N C D : Finset V) (ic : Indep G C) (id : Indep G D)
    (dis : Disjoint C D) (clean : Disjoint C N) :
    TwoColor (ear G N) (lift (C ∪ D) true) := by
  classical
  refine ⟨lift C true,lift D false,?_,?_,lift_ind G N C ic true (fun _ => clean),
    lift_ind G N D id false (by simp)⟩
  · apply disjoint_left.mpr
    rintro (v|v) a b
    · exact disjoint_left.mp dis ((inl_lift ..).mp a) ((inl_lift ..).mp b)
    · simp at b
  · ext v; cases v <;> simp

/-- The bipartite number increases exactly when an old maximum two-color
witness admits a color avoiding the entire attachment neighborhood. -/
theorem color_gain_iff (N : Finset V) :
    bipartiteNum G<bipartiteNum (ear G N) ↔
    ∃ C D, Indep G C ∧ Indep G D ∧ Disjoint C D ∧ C.card+D.card=bipartiteNum G ∧ Disjoint C N := by
  classical
  constructor
  · intro up
    obtain ⟨X,col,eq⟩ := optB (ear G N)
    let z : V ⊕ Unit := .inr ()
    let base := pull Sum.inl X
    have rest := restrict_color G (ear G N) Sum.inl Sum.inl_injective (fun e => e) col
    have rb := size_bip G rest
    have repr := present X
    have count := congrArg card repr
    rw [card_lift] at count
    have zx : z∈X := by
      by_contra no
      change Sum.inr ()∉X at no
      simp only [decide_eq_false no,Bool.toNat_false,Nat.add_zero] at count
      omega
    have top : base.card=bipartiteNum G := by
      change Sum.inr ()∈X at zx
      simp only [decide_eq_true zx,Bool.toNat_true] at count
      change base.card≤_ at rb
      change X.card=base.card+1 at count
      omega
    obtain ⟨B,F,dis,sel,ib,if'⟩ := col
    have form (B F : Finset (V ⊕ Unit)) (ib : Indep (ear G N) B) (if' : Indep (ear G N) F)
        (dis : Disjoint B F) (sel : B ∪ F=X) (zb : z∈B) :
        ∃ C D, Indep G C ∧ Indep G D ∧ Disjoint C D ∧ C.card+D.card=bipartiteNum G ∧ Disjoint C N := by
      let C := pull Sum.inl B
      let D := pull Sum.inl F
      have ind (S : Finset (V ⊕ Unit)) (i : Indep (ear G N) S) : Indep G (pull Sum.inl S) :=
        fun a ha b hb ne e => i _ (mem_pull.mp ha) _ (mem_pull.mp hb) (fun h => ne (Sum.inl.inj h)) e
      have cd : Disjoint C D := disjoint_left.mpr (fun _ a b => disjoint_left.mp dis (mem_pull.mp a) (mem_pull.mp b))
      have set : C ∪ D=base := by ext x; simp [C,D,base,← sel]
      refine ⟨C,D,ind _ ib,ind _ if',cd,?_,?_⟩
      · rw [← card_union_of_disjoint cd,set,top]
      · exact disjoint_left.mpr (fun v vc vn => ib _ (mem_pull.mp vc) _ zb (fun h => Sum.noConfusion h) vn)
    rw [← sel] at zx
    rcases mem_union.mp zx with zb|zf
    · exact form B F ib if' dis sel zb
    · exact form F B if' ib dis.symm ((union_comm ..).trans sel) zf
  · rintro ⟨C,D,ic,id,dis,top,clean⟩
    have b := size_bip (ear G N) (extend_color G N C D ic id dis clean)
    rw [card_lift,card_union_of_disjoint dis,top] at b
    exact b

/-- An unrestricted failed instance forces both colors into the neighborhood
of each stable singly counted or uncounted vertex, for every old maximum
coloring, provided its smaller restricted state satisfies the bound. -/
theorem blocked_colors (N : Finset V) (same : bipartiteNum (ear G N)=bipartiteNum G)
    (C D : Finset V) (ic : Indep G C) (id : Indep G D) (dis : Disjoint C D)
    (top : C.card+D.card=bipartiteNum G) :
    (C ∩ N).Nonempty ∧ (D ∩ N).Nonempty := by
  classical
  have no := mt (color_gain_iff G N).mpr (show ¬bipartiteNum G<bipartiteNum (ear G N) by omega)
  constructor
  · exact not_disjoint_iff_nonempty_inter.mp (fun clean => no ⟨C,D,ic,id,dis,top,clean⟩)
  · exact not_disjoint_iff_nonempty_inter.mp (fun clean => no ⟨D,C,id,ic,dis.symm,(Nat.add_comm ..).trans top,clean⟩)

#print axioms color_gain_iff
#print axioms blocked_colors
end Minimal180
