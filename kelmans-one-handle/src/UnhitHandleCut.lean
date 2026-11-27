import MinimalShore

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.OddUncross
open HandleExtension HandleExtension.Edges.AtomicHitting FourRingCutAux
noncomputable section
variable {V : Type*} {G : SimpleGraph V}
variable (E : Edges G)

/-- The chosen edges are entirely in opposite shores. -/
def Opposes (c : V→Bool) : Prop :=
  ∃ b : Bool,(∀x,E.Ends false x→c x=b) ∧ (∀x,E.Ends true x→c x= !b)

private theorem opp_of_endpoints (c : V→Bool) (b : Bool)
    (p : c (E.a false)=b) (q : c (E.b false)=b)
    (r : c (E.a true)= !b) (s : c (E.b true)= !b) : Opposes E c := by
  refine ⟨b,?_,?_⟩
  · rintro _ (rfl|rfl) <;> assumption
  · rintro _ (rfl|rfl) <;> assumption

/-- If the edges are not opposite, they have a color in common (each
edge has at least one endpoint in that color). Both subdivision
vertices can be put there, without increasing the old boundary. -/
private theorem common_colour (c : V→Bool) (no : ¬Opposes E c) :
    ∃ b : Bool,∀s,c (E.a s)=b ∨ c (E.b s)=b := by
  classical
  refine Classical.byContradiction ?_
  intro n
  have exist (b : Bool) : ∃s,c (E.a s)≠b ∧ c (E.b s)≠b := by
    refine Classical.byContradiction ?_
    intro h
    exact n ⟨b,fun s=>by
      by_cases a : c (E.a s)=b
      · exact Or.inl a
      · exact Or.inr (Classical.byContradiction (fun z=>h ⟨s,a,z⟩))⟩
  obtain ⟨i,ai,bi⟩ := exist false
  obtain ⟨j,aj,bj⟩ := exist true
  have iA : c (E.a i)=true := by
    cases eq : c (E.a i)
    · exact (ai eq).elim
    · rfl
  have iB : c (E.b i)=true := by
    cases eq : c (E.b i)
    · exact (bi eq).elim
    · rfl
  have jA : c (E.a j)=false := Bool.eq_false_iff.mpr aj
  have jB : c (E.b j)=false := Bool.eq_false_iff.mpr bj
  cases i <;> cases j
  · exact ai jA
  · exact no (opp_of_endpoints E c true iA iB jA jB)
  · exact no (opp_of_endpoints E c false jA jB iA iB)
  · exact ai jA

private def extend (c : V→Bool) (b : Bool) : V⊕Bool→Bool
  | .inl x => c x
  | .inr _ => b

private def oldEnd (c : V→Bool) (b : Bool) (s : Bool) : V :=
  if c (E.a s)=b then E.a s else E.b s

private theorem oldEnd_ends (c : V→Bool) (b s : Bool) : E.Ends s (oldEnd E c b s) := by
  unfold oldEnd
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem oldEnd_col (c : V→Bool) (b s : Bool)
    (h : c (E.a s)=b ∨ c (E.b s)=b) : c (oldEnd E c b s)=b := by
  unfold oldEnd
  by_cases yes : c (E.a s)=b
  · rwa [if_pos yes]
  · rw [if_neg yes]
    exact h.resolve_left yes

private def proj (c : V→Bool) (b : Bool) : V⊕Bool→V
  | .inl x => x
  | .inr s => oldEnd E c b s

private theorem pair_of_ends {s : Bool} {u v : V} (us : E.Ends s u) (vs : E.Ends s v)
    (ne : u≠v) : E.PairFor s u v := by
  rcases us with h|h <;> rcases vs with k|k
  · exact (ne (h.trans k.symm)).elim
  · exact Or.inl ⟨h,k⟩
  · exact Or.inr ⟨h,k⟩
  · exact (ne (h.trans k.symm)).elim

variable [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Project the crossing edges of the extended coloring injectively
onto old crossing edges. A crossing subdivided edge has only one
crossing half when its new vertex picks a matching endpoint color. -/
private theorem extended_cut_le (c : V→Bool) (b : Bool)
    (h : ∀s,c (E.a s)=b ∨ c (E.b s)=b) :
    (boundary E.host (extend c b)).card≤(boundary G c).card := by
  classical
  let f : (V⊕Bool)×(V⊕Bool)→V×V := fun p=>(proj E c b p.1,proj E c b p.2)
  have col (x : V⊕Bool) : c (proj E c b x)=extend c b x := by
    cases x
    · rfl
    · exact oldEnd_col E c b _ (h _)
  have rep (p : (V⊕Bool)×(V⊕Bool)) (pm : p∈boundary E.host (extend c b)) :
      ((∃ a d : V,p=(Sum.inl a,Sum.inl d)) ∧ G.Adj (f p).1 (f p).2 ∧
          ¬E.Removed (f p).1 (f p).2) ∨
      ∃ s : Bool, E.PairFor s (f p).1 (f p).2 ∧
        ((∃ a : V,p=(Sum.inl a,Sum.inr s)) ∨ (∃ d : V,p=(Sum.inr s,Sum.inl d))) := by
    obtain ⟨yes,no,adj⟩ := mem_boundary.mp pm
    have neq : (f p).1≠(f p).2 := by
      intro e
      have g := congrArg c e
      change c (proj E c b p.1)=c (proj E c b p.2) at g
      rw [col,col,yes,no] at g
      cases g
    rcases p with ⟨u,v⟩
    cases u <;> cases v
    · exact Or.inl ⟨⟨_,_,rfl⟩,adj.1,adj.2⟩
    · refine Or.inr ⟨_,pair_of_ends E adj (oldEnd_ends E c b _) neq,Or.inl ⟨_,rfl⟩⟩
    · refine Or.inr ⟨_,pair_of_ends E (oldEnd_ends E c b _) adj neq,Or.inr ⟨_,rfl⟩⟩
    · exact (Bool.false_ne_true (no.symm.trans yes)).elim
  apply card_le_card_of_injOn f
  · intro p pm
    obtain ⟨yes,no,_⟩ := mem_boundary.mp pm
    have ed : G.Adj (f p).1 (f p).2 := by
      rcases rep p pm with a|⟨s,w,_⟩
      · exact a.2.1
      · exact E.pair_adj w
    exact mem_boundary.mpr ⟨(col _).trans yes,(col _).trans no,ed⟩
  · intro p pm q qm eq
    rcases rep p pm with ⟨⟨a,d,ap⟩,_,np⟩|⟨s,sp,spKind⟩ <;>
      rcases rep q qm with ⟨⟨e,g,eqQ⟩,_,nq⟩|⟨t,tq,tqKind⟩
    · subst p; subst q
      exact Prod.ext (congrArg Sum.inl (congrArg Prod.fst eq))
        (congrArg Sum.inl (congrArg Prod.snd eq))
    · rw [←eq] at tq
      exact (np ⟨t,tq⟩).elim
    · rw [eq] at sp
      exact (nq ⟨s,sp⟩).elim
    · have ts : s=t := E.separated (E.pair_ends sp).1
        ((congrArg Prod.fst eq).symm ▸ (E.pair_ends tq).1)
      subst t
      rcases spKind with ⟨a,rfl⟩|⟨a,rfl⟩ <;>
        rcases tqKind with ⟨d,rfl⟩|⟨d,rfl⟩
      · exact Prod.ext (congrArg Sum.inl (congrArg Prod.fst eq)) rfl
      · exact (Bool.false_ne_true ((mem_boundary.mp pm).2.1.symm.trans (mem_boundary.mp qm).1)).elim
      · exact (Bool.false_ne_true ((mem_boundary.mp qm).2.1.symm.trans (mem_boundary.mp pm).1)).elim
      · exact Prod.ext rfl (congrArg Sum.inl (congrArg Prod.snd eq))

omit [DecidableEq V] in
/-- Any nontrivial cut not hit by the chosen old edges survives
the handle addition, even if the cut is already small. -/
theorem unhit_cut_survives (c : V→Bool) (non : ¬TrivialCut c)
    (miss : ¬Opposes E c) :
    ∃ C : V⊕Bool→Bool, ¬TrivialCut C ∧ (boundary E.host C).card≤(boundary G c).card := by
  obtain ⟨b,h⟩ := common_colour E c miss
  refine ⟨extend c b,?_,extended_cut_le E c b h⟩
  intro bad
  apply non
  rcases bad with h|h
  · exact Or.inl (fun x y hx hy=>Sum.inl.inj (h _ _ hx hy))
  · exact Or.inr (fun x y hx hy=>Sum.inl.inj (h _ _ hx hy))

variable [DecidableRel G.Adj]

/-- A given choice makes the handle host cyclically four-connected
exactly when its two old edges oppose every nontrivial three-cut. -/
theorem cyclic_host_iff_hits (cub : ∀v,G.degree v=3) (minimum : MinBoundaryThree G) :
    SmallTrivial E.host ↔ HitsSmallCuts E := by
  constructor
  · intro yes c low non
    obtain ⟨p,q⟩ := both_colours_of_nontrivial non
    refine ⟨minimum c p q,?_⟩
    refine Classical.byContradiction ?_
    intro miss
    obtain ⟨C,nonC,le⟩ := unhit_cut_survives E c non miss
    exact nonC (yes C (le.trans low))
  · exact cyclic_host_of_hitting E cub

#print axioms unhit_cut_survives
#print axioms cyclic_host_iff_hits
end
end KelmansCactus.AtomicBridge.OddUncross
