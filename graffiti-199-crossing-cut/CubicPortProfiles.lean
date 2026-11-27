import CubicCutShore

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

private theorem cubic_misses_in_other_shore {A : Set V} [Fintype A] {r b : V}
    (big : 3 ≤ Fintype.card A) (outside : b ∉ A) (rb : G.Adj r b) (degree : G.degree r = 3) :
    ∃ a ∈ A, ¬ G.Adj r a := by
  classical
  by_contra! all
  let N := G.neighborFinset r
  have bN : b ∈ N := (G.mem_neighborFinset _ _).mpr rb
  let f : A → (N.erase b : Finset V) := fun x => ⟨x.val,Finset.mem_erase.mpr
    ⟨fun e => outside (e ▸ x.property),(G.mem_neighborFinset _ _).mpr (all x.val x.property)⟩⟩
  have inj : Function.Injective f := fun _ _ e => Subtype.ext
    (congrArg (fun t : (N.erase b : Finset V) => t.val) e)
  have upper := Fintype.card_le_of_injective f inj
  change Fintype.card A ≤ Fintype.card (N.erase b : Finset V) at upper
  rw [Fintype.card_coe,Finset.card_erase_of_mem bN,G.card_neighborFinset_eq_degree,degree] at upper
  omega

/-- If a cubic port sees two connected shores, each of order at least
three, at least one shore is a clique. A third neighbor outside the two
shores forces both to be cliques. -/
theorem clique_shore_of_cubic_port {D : Finset V} {A B : Set V} [Fintype A] [Fintype B]
    {r : V} (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (size : D.card = 3)
    (rD : r ∈ D) (degree : G.degree r = 3)
    (bigA : 3 ≤ Fintype.card A) (bigB : 3 ≤ Fintype.card B)
    (outsideA : ∀ d ∈ D, d ∉ A) (outsideB : ∀ d ∈ D, d ∉ B)
    (apart : Disjoint A B)
    (boundaryA : ShoreBoundary G D A) (boundaryB : ShoreBoundary G D B)
    (connA : (G.induce A).Connected) (connB : (G.induce B).Connected) :
    (((∃! a : V, a ∈ A ∧ G.Adj r a) ∧ A.Pairwise G.Adj) ∨
      ((∃! b : V, b ∈ B ∧ G.Adj r b) ∧ B.Pairwise G.Adj)) ∧
      (∀ d ∉ A, d ∉ B → G.Adj r d → A.Pairwise G.Adj ∧ B.Pairwise G.Adj) := by
  classical
  have dis := Set.disjoint_left.mp apart
  obtain ⟨x⟩ := connA.nonempty
  obtain ⟨y⟩ := connB.nonempty
  obtain ⟨a,aA,ra⟩ := contact_of_shore conn size.le outsideA boundaryA ⟨x.val,x.property⟩ rD
  obtain ⟨b,bB,rb⟩ := contact_of_shore conn size.le outsideB boundaryB ⟨y.val,y.property⟩ rD
  have anti (u : V) (uA : u ∈ A) (v : V) (vB : v ∈ B) (e : G.Adj u v) : False :=
    outsideB v (boundaryA u uA v (fun vA => dis vA vB) e) vB
  have missA := cubic_misses_in_other_shore bigA (fun h => dis h bB) rb degree
  have missB := cubic_misses_in_other_shore bigB (dis aA) ra degree
  obtain ⟨i,iA,j,jA,ri,ij,rj⟩ := two_step_into_shore connA.preconnected ⟨a,aA,ra⟩ missA
  obtain ⟨s,sB,t,tB,rs,st,rt⟩ := two_step_into_shore connB.preconnected ⟨b,bB,rb⟩ missB
  let N := G.neighborFinset r
  let X := N.filter fun v => v ∈ A
  let Y := N.filter fun v => v ∈ B
  have xSpec (v : V) : v ∈ X ↔ G.Adj r v ∧ v ∈ A := by
    simp [X,N]
  have ySpec (v : V) : v ∈ Y ↔ G.Adj r v ∧ v ∈ B := by
    simp [Y,N]
  have disXY : Disjoint X Y := Finset.disjoint_left.mpr
    (fun v hx hy => dis ((xSpec v).mp hx).2 ((ySpec v).mp hy).2)
  have xPos := Finset.card_pos.mpr (show X.Nonempty from ⟨a,(xSpec a).mpr ⟨ra,aA⟩⟩)
  have yPos := Finset.card_pos.mpr (show Y.Nonempty from ⟨b,(ySpec b).mpr ⟨rb,bB⟩⟩)
  have union := Finset.card_union_of_disjoint disXY
  have three : X.card + Y.card ≤ 3 := by
    rw [← union,← degree,← G.card_neighborFinset_eq_degree]
    exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset ..) (Finset.filter_subset ..))
  have xClique (h : X.card = 1) : A.Pairwise G.Adj := by
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp h
    have vSpec := (xSpec v).mp (hv.symm ▸ Finset.mem_singleton_self v)
    have only (w : V) (wA : w ∈ A) (rwEdge : G.Adj r w) : w = v :=
      Finset.mem_singleton.mp (hv ▸ (xSpec w).mpr ⟨rwEdge,wA⟩)
    exact clique_of_unique_contact_and_two_step budget apart anti (outsideA _ rD) (outsideB _ rD)
      connA.preconnected vSpec.2 vSpec.1 only sB tB rs st rt
  have yClique (h : Y.card = 1) : B.Pairwise G.Adj := by
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp h
    have vSpec := (ySpec v).mp (hv.symm ▸ Finset.mem_singleton_self v)
    have only (w : V) (wB : w ∈ B) (rwEdge : G.Adj r w) : w = v :=
      Finset.mem_singleton.mp (hv ▸ (ySpec w).mpr ⟨rwEdge,wB⟩)
    exact clique_of_unique_contact_and_two_step budget apart.symm
      (fun w wB u uA e => anti u uA w wB e.symm) (outsideB _ rD) (outsideA _ rD)
      connB.preconnected vSpec.2 vSpec.1 only iA jA ri ij rj
  have unique_contact {S : Set V} {K : Finset V}
      (spec : ∀ v, v ∈ K ↔ G.Adj r v ∧ v ∈ S) (one : K.card = 1) :
      ∃! v : V, v ∈ S ∧ G.Adj r v := by
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp one
    have near := (spec v).mp (hv.symm ▸ Finset.mem_singleton_self v)
    refine ⟨v,⟨near.2,near.1⟩,?_⟩
    intro w hw
    exact Finset.mem_singleton.mp (hv ▸ (spec w).mpr ⟨hw.2,hw.1⟩)
  constructor
  · by_cases h : X.card = 1
    · exact Or.inl ⟨unique_contact xSpec h,xClique h⟩
    · have one : Y.card = 1 := by omega
      exact Or.inr ⟨unique_contact ySpec one,yClique one⟩
  · intro d dA dB rd
    have dN : d ∈ N := (G.mem_neighborFinset _ _).mpr rd
    have sub : X ∪ Y ⊆ N.erase d := by
      intro v hv
      rcases Finset.mem_union.mp hv with h|h
      · have ⟨rv,vA⟩ := (xSpec v).mp h
        exact Finset.mem_erase.mpr ⟨fun e => dA (e ▸ vA),(G.mem_neighborFinset _ _).mpr rv⟩
      · have ⟨rv,vB⟩ := (ySpec v).mp h
        exact Finset.mem_erase.mpr ⟨fun e => dB (e ▸ vB),(G.mem_neighborFinset _ _).mpr rv⟩
    have cap := Finset.card_le_card sub
    rw [union,Finset.card_erase_of_mem dN,G.card_neighborFinset_eq_degree,degree] at cap
    exact ⟨xClique (by omega),yClique (by omega)⟩

#print axioms clique_shore_of_cubic_port

end Graffiti199Depleted.Catalogue
