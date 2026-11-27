import SquareCapGeometry

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteSubdivisionCore
open SquareCap (boundary SmallTrivial)
universe u v
variable {V : Type u} {I : Type v} {G : SimpleGraph V}

/-- Independent edges to subdivide exactly once. -/
structure Marks (G : SimpleGraph V) (I : Type v) where
  a : I→V
  b : I→V
  edge : ∀ i,G.Adj (a i) (b i)
  separated : ∀ {i j x},(x=a i∨x=b i)→(x=a j∨x=b j)→i=j

namespace Marks
variable (M : Marks G I)

def Ends (i : I) (x : V) : Prop := x=M.a i∨x=M.b i
def Pair (i : I) (x y : V) : Prop := (x=M.a i∧y=M.b i)∨(x=M.b i∧y=M.a i)
def Removed (x y : V) : Prop := ∃ i,M.Pair i x y

theorem pair_symm {i x y} (h : M.Pair i x y) : M.Pair i y x := by
  rcases h with ⟨a,b⟩|⟨a,b⟩
  · exact Or.inr ⟨b,a⟩
  · exact Or.inl ⟨b,a⟩

theorem both_ends {i x y} (h : M.Pair i x y) : M.Ends i x ∧ M.Ends i y := by
  rcases h with ⟨a,b⟩|⟨a,b⟩
  · exact ⟨Or.inl a,Or.inr b⟩
  · exact ⟨Or.inr a,Or.inl b⟩

theorem pair_adj {i x y} (h : M.Pair i x y) : G.Adj x y := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact M.edge i
  · exact (M.edge i).symm

theorem slot_unique {i j x y} (a : M.Pair i x y) (b : M.Pair j x y) : i=j :=
  M.separated (M.both_ends a).1 (M.both_ends b).1

def expanded : SimpleGraph (V⊕I) where
  Adj x y :=
    match x,y with
    | .inl x,.inl y => G.Adj x y ∧ ¬M.Removed x y
    | .inl x,.inr i | .inr i,.inl x => M.Ends i x
    | .inr _,.inr _ => False
  symm := by
    rintro (x|i) (y|j) h
    · exact ⟨h.1.symm,fun ⟨k,ed⟩=>h.2 ⟨k,M.pair_symm ed⟩⟩
    · exact h
    · exact h
    · exact h
  loopless := by
    rintro (x|i) h
    · exact G.loopless x h.1
    · exact h

variable [Fintype V] [Fintype I]
def restriction (c : V⊕I→Bool) (x : V) : Bool := c (Sum.inl x)
def naturalColour (c : V→Bool) : V⊕I→Bool := Sum.elim c (fun i=>c (M.a i))

private theorem mem_cut {U : Type*} [Fintype U] {J : SimpleGraph U}
    {c : U→Bool} {p q : U} :
    (p,q)∈boundary J c ↔ c p=true∧c q=false∧J.Adj p q := by
  classical
  simp [boundary]

omit [Fintype V] [Fintype I] in
private def down (c : V⊕I→Bool) (q : (V⊕I)×(V⊕I)) : V×V :=
  match q with
  | (.inl x,.inl y) => (x,y)
  | (.inr i,.inl _) | (.inl _,.inr i) =>
    if c (Sum.inl (M.a i)) then (M.a i,M.b i) else (M.b i,M.a i)
  | (.inr i,.inr j) => (M.a i,M.a j)

omit [Fintype V] [Fintype I] in
private noncomputable def up (c : V⊕I→Bool) (p : V×V) : (V⊕I)×(V⊕I) := by
  classical
  exact if h : M.Removed p.1 p.2 then
    let i := Classical.choose h
    if c (Sum.inr i) then (Sum.inr i,Sum.inl p.2)
    else (Sum.inl p.1,Sum.inr i)
  else (Sum.inl p.1,Sum.inl p.2)

private theorem up_mem (c : V⊕I→Bool) {q : V×V}
    (hq : q∈boundary G (restriction c)) : M.up c q∈boundary M.expanded c := by
  classical
  rcases q with ⟨a,b⟩
  obtain ⟨ta,fb,ed⟩ := mem_cut.mp hq
  unfold up
  dsimp only
  split
  · rename_i proof
    have hs := M.both_ends (Classical.choose_spec proof)
    cases ht : c (Sum.inr (Classical.choose proof))
    · simpa only [Bool.false_eq_true,if_false] using
        (mem_cut.mpr ⟨ta,ht,hs.1⟩ : (Sum.inl a,Sum.inr (Classical.choose proof))∈boundary M.expanded c)
    · simpa only [if_true] using
        (mem_cut.mpr ⟨ht,fb,hs.2⟩ : (Sum.inr (Classical.choose proof),Sum.inl b)∈boundary M.expanded c)
  · rename_i no
    exact mem_cut.mpr ⟨ta,fb,ed,no⟩

omit [Fintype I] in
private theorem down_up (c : V⊕I→Bool) {p : V×V}
    (pm : p∈boundary G (restriction c)) : M.down c (M.up c p)=p := by
  classical
  rcases p with ⟨a,b⟩
  obtain ⟨ta,fb,_⟩ := mem_cut.mp pm
  unfold up
  dsimp only
  split
  · rename_i h
    generalize hi : Classical.choose h = i
    have p := Classical.choose_spec h
    rw [hi] at p
    rcases p with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · change c (Sum.inl (M.a i))=true at ta
      cases hc : c (Sum.inr i) <;> simp [hc,down,ta]
    · change c (Sum.inl (M.a i))=false at fb
      cases hc : c (Sum.inr i) <;> simp [hc,down,fb]
  · rfl

/-- A cut after subdivision cannot cost less than its restriction
to the original vertices. -/
theorem cut_mono (c : V⊕I→Bool) :
    (boundary G (restriction c)).card≤(boundary M.expanded c).card := by
  classical
  let C := boundary G (restriction c)
  have sub : C.image (M.up c)⊆boundary M.expanded c := by
    intro z zm
    obtain ⟨q,qm,rfl⟩ := mem_image.mp zm
    exact M.up_mem c qm
  have inj : Set.InjOn (M.up c) (↑C:Set (V×V)) := by
    intro a am b bm same
    exact (M.down_up c am).symm.trans ((congrArg (M.down c) same).trans (M.down_up c bm))
  have bound := card_le_card sub
  rwa [card_image_of_injOn inj] at bound

private theorem chosen_left (c : V→Bool) {q : (V⊕I)×(V⊕I)}
    (qm : q∈boundary M.expanded (M.naturalColour c)) :
    M.up (M.naturalColour c) (M.down (M.naturalColour c) q)=q ∧
      M.down (M.naturalColour c) q∈boundary G c := by
  classical
  rcases q with ⟨x,y⟩
  obtain ⟨tx,fy,ed⟩ := mem_cut.mp qm
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have xy : G.Adj x y∧¬M.Removed x y := ed
      refine ⟨?_,mem_cut.mpr ⟨tx,fy,xy.1⟩⟩
      simp [down,up,xy.2]
    | inr i =>
      change c x=true at tx
      change c (M.a i)=false at fy
      have ep : M.Ends i x := ed
      rcases ep with h|h
      · rw [h,fy] at tx
        contradiction
      · subst x
        have mp : M.Pair i (M.b i) (M.a i) := Or.inr ⟨rfl,rfl⟩
        have ex : M.Removed (M.b i) (M.a i) := ⟨i,mp⟩
        have eq := M.slot_unique (Classical.choose_spec ex) mp
        have qD : M.down (M.naturalColour c) (Sum.inl (M.b i),Sum.inr i)=(M.b i,M.a i) := by
          simp [down,naturalColour,fy]
        rw [qD]
        refine ⟨?_,mem_cut.mpr ⟨tx,fy,(M.edge i).symm⟩⟩
        unfold up
        simp only [ex,dif_pos,eq,naturalColour,Sum.elim_inr,fy,Bool.false_eq_true,if_false]
  | inr i =>
    cases y with
    | inl y =>
      change c (M.a i)=true at tx
      change c y=false at fy
      have ep : M.Ends i y := ed
      rcases ep with h|h
      · rw [h,tx] at fy
        contradiction
      · subst y
        have mp : M.Pair i (M.a i) (M.b i) := Or.inl ⟨rfl,rfl⟩
        have ex : M.Removed (M.a i) (M.b i) := ⟨i,mp⟩
        have eq := M.slot_unique (Classical.choose_spec ex) mp
        have qD : M.down (M.naturalColour c) (Sum.inr i,Sum.inl (M.b i))=(M.a i,M.b i) := by
          simp [down,naturalColour,tx]
        rw [qD]
        refine ⟨?_,mem_cut.mpr ⟨tx,fy,M.edge i⟩⟩
        unfold up
        simp only [ex,dif_pos,eq,naturalColour,Sum.elim_inr,tx,if_true]
    | inr j => exact False.elim ed

/-- Coloring every inserted vertex like its first old neighbor
preserves the exact width of the core cut. -/
theorem cut_exact (c : V→Bool) :
    (boundary M.expanded (M.naturalColour c)).card=(boundary G c).card := by
  classical
  apply le_antisymm ?_ (M.cut_mono (M.naturalColour c))
  let C := boundary M.expanded (M.naturalColour c)
  have sub : C.image (M.down (M.naturalColour c))⊆boundary G c := by
    intro z zm
    obtain ⟨q,qm,rfl⟩ := mem_image.mp zm
    exact (M.chosen_left c qm).2
  have inj : Set.InjOn (M.down (M.naturalColour c)) (↑C:Set ((V⊕I)×(V⊕I))) := by
    intro a am b bm eq
    exact (M.chosen_left c am).1.symm.trans
      ((congrArg (M.up (M.naturalColour c)) eq).trans (M.chosen_left c bm).1)
  have w := card_le_card sub
  rwa [card_image_of_injOn inj] at w

/-- The correct connectivity condition to preserve on the expanded
board counts only the old (degree-three) vertices on each side.
Requiring all nontrivial board cuts to have width four would be
too strong: a subdividing vertex and a neighbor form a 3-shore. -/
theorem cyclic_four_iff_fat :
    SmallTrivial G ↔
      ∀ c : V⊕I→Bool,(boundary M.expanded c).card≤3 →
        (∀ x y : V,c (Sum.inl x)=true→c (Sum.inl y)=true→x=y) ∨
        (∀ x y : V,c (Sum.inl x)=false→c (Sum.inl y)=false→x=y) := by
  constructor
  · intro good c cut
    exact good (restriction c) ((M.cut_mono c).trans cut)
  · intro good c cut
    exact good (M.naturalColour c) ((M.cut_exact c).le.trans cut)

#print axioms cut_mono
#print axioms cut_exact
#print axioms cyclic_four_iff_fat
end Marks
end KelmansCactus.AtomicBridge.RemoteSubdivisionCore
