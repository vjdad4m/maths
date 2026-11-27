import HighCutProfile
import Mathlib.Combinatorics.Hall.Finite

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V]
variable {D : Finset V} {A : Set V}

/-- The vertices of a given side with a neighbor in a set of terminals. -/
noncomputable def shoreAttachments (G : SimpleGraph V) (A : Set V) (T : Finset V) :
    Finset V := by
  classical
  exact T.biUnion (fun p => Finset.univ.filter (fun x => x ∈ A ∧ G.Adj p x))

theorem mem_shoreAttachments {T : Finset V} {x : V} :
    x ∈ shoreAttachments G A T ↔ x ∈ A ∧ ∃ p ∈ T, G.Adj p x := by
  classical
  simp only [shoreAttachments,Finset.mem_biUnion,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨p,hp,hA,hpX⟩
    exact ⟨hA,p,hp,hpX⟩
  · rintro ⟨hA,p,hp,hpX⟩
    exact ⟨p,hp,hA,hpX⟩

/-- In a three-connected graph, every subset of the three terminals of
a side of order at least three has at least as many distinct contacts.
An exterior vertex outside the cut is needed for the separation argument. -/
theorem shore_hall
    (conn : ConnectivityAtLeast G 3) (cutSize : D.card = 3)
    (off : ∀ x ∈ D, x ∉ A) (boundary : ShoreBoundary G D A)
    (large : 3 ≤ Nat.card A) (other : ∃ b : V, b ∉ A ∧ b ∉ D)
    {T : Finset V} (subset : T ⊆ D) : T.card ≤ (shoreAttachments G A T).card := by
  classical
  by_contra! bad
  let N := shoreAttachments G A T
  let R := (D \ T) ∪ N
  have tcard := Finset.card_le_card subset
  rw [cutSize] at tcard
  have scard := Finset.card_sdiff_add_card_eq_card subset
  rw [cutSize] at scard
  have sums := Finset.card_union_le (D \ T) N
  have small : R.card < 3 := by change ((D \ T) ∪ N).card < 3; change N.card < T.card at bad; omega
  letI : Fintype A := Fintype.ofFinite A
  have cardA : 3 ≤ A.toFinset.card := by
    rw [Set.toFinset_card]
    rwa [Nat.card_eq_fintype_card] at large
  have less : N.card < A.toFinset.card := by change N.card < T.card at bad; omega
  obtain ⟨a,ha,aN⟩ := Finset.exists_mem_not_mem_of_card_lt_card less
  have aA : a ∈ A := Set.mem_toFinset.mp ha
  have aR : a ∉ R := by
    intro h
    rcases Finset.mem_union.mp h with hD|hN
    · exact off _ (Finset.mem_sdiff.mp hD).1 aA
    · exact aN hN
  obtain ⟨b,bA,bD⟩ := other
  have bR : b ∉ R := by
    intro h
    rcases Finset.mem_union.mp h with hD|hN
    · exact bD (Finset.mem_sdiff.mp hD).1
    · exact bA (mem_shoreAttachments.mp hN).1
  obtain ⟨w⟩ := (conn.2 R small).preconnected ⟨a,aR⟩ ⟨b,bR⟩
  obtain ⟨x,xA,y,yA,xy⟩ :=
    crossingOnWalk (U := {x : Survives R | x.val ∈ A}) w aA bA
  have yD := boundary x.val xA y.val yA xy
  have yT : y.val ∈ T := by
    by_contra absent
    exact y.property (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨yD,absent⟩))
  have xN : x.val ∈ N := mem_shoreAttachments.mpr ⟨xA,y.val,yT,G.symm xy⟩
  exact x.property (Finset.mem_union_right _ xN)

/-- The attachment certificate selects three distinct shore vertices,
each adjacent to the corresponding cut vertex. -/
theorem shore_distinct_attachments
    (conn : ConnectivityAtLeast G 3) (cutSize : D.card = 3)
    (off : ∀ x ∈ D, x ∉ A) (boundary : ShoreBoundary G D A)
    (large : 3 ≤ Nat.card A) (other : ∃ b : V, b ∉ A ∧ b ∉ D) :
    ∃ f : ↥D ↪ A, ∀ p : D, G.Adj p.val (f p).val := by
  classical
  let candidates (p : ↥D) := Finset.univ.filter (fun x => x ∈ A ∧ G.Adj p.val x)
  let e : ↥D ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have hall (S : Finset ↥D) : S.card ≤ (S.biUnion candidates).card := by
    have sub : S.map e ⊆ D := by
      intro x hx
      obtain ⟨p,_,rfl⟩ := Finset.mem_map.mp hx
      exact p.property
    have eq : S.biUnion candidates = shoreAttachments G A (S.map e) := by
      ext x
      simp only [candidates,shoreAttachments,Finset.mem_biUnion,Finset.mem_map,Finset.mem_filter,
        Finset.mem_univ,true_and]
      constructor
      · rintro ⟨p,pS,xA,edge⟩
        exact ⟨p.val,⟨p,pS,rfl⟩,xA,edge⟩
      · rintro ⟨_,⟨p,pS,rfl⟩,xA,edge⟩
        exact ⟨p,pS,xA,edge⟩
    rw [eq,← Finset.card_map e]
    exact shore_hall conn cutSize off boundary large other sub
  obtain ⟨f,inj,matched⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' candidates).mp hall
  have evidence (p : ↥D) : f p ∈ A ∧ G.Adj p.val (f p) := (Finset.mem_filter.mp (matched p)).2
  exact ⟨⟨fun p => ⟨f p,(evidence p).1⟩,fun _ _ eq => inj (congrArg Subtype.val eq)⟩,
    fun p => (evidence p).2⟩

/-- Apply the certificate to either of the distinguished components in an
actual surviving-edge crossing failure. -/
theorem LargeCrossingFailure.distinct_attachments
    (F : LargeCrossingFailure G) (conn : ConnectivityAtLeast G 3) :
    (∃ f : ↥F.cut ↪ componentShore F.cut F.first, ∀ p : F.cut, G.Adj p.val (f p).val) ∧
    (∃ f : ↥F.cut ↪ componentShore F.cut F.second, ∀ p : F.cut, G.Adj p.val (f p).val) := by
  have dis := Set.disjoint_left.mp (componentShore_disjoint F.different)
  obtain ⟨a⟩ := (componentShore_connected F.cut F.first).nonempty
  obtain ⟨b⟩ := (componentShore_connected F.cut F.second).nonempty
  exact ⟨shore_distinct_attachments conn F.size (componentShore_off_cut F.cut F.first)
    (componentShore_boundary F.cut F.first) F.first_large
      ⟨b.val,fun inFirst => dis inFirst b.property,
        fun inCut => componentShore_off_cut F.cut F.second _ inCut b.property⟩,
    shore_distinct_attachments conn F.size (componentShore_off_cut F.cut F.second)
      (componentShore_boundary F.cut F.second) F.second_large
      ⟨a.val,fun inSecond => dis a.property inSecond,
        fun inCut => componentShore_off_cut F.cut F.first _ inCut a.property⟩⟩

#print axioms shore_hall
#print axioms shore_distinct_attachments
#print axioms LargeCrossingFailure.distinct_attachments

end Graffiti199Depleted.Catalogue
