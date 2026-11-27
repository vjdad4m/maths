import BicycleHubChannels133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure TaggedChannel (G : SimpleGraph V) (B S : Finset V) (a : V) where
  n : Nat
  pos : 0<n
  f : Fin n → (S : Set V)
  path : InducedPath (G.induce (S : Set V)) f
  spans : Function.Surjective f
  b : V
  bIn : b∈B
  singletonNe : n=1 → b≠a
  attached : ∀ (i : Fin n) (z : V), z∈B →
    (G.Adj z (f i).val ↔ (i.val=0 ∧ z=a) ∨ (i.val+1=n ∧ z=b))

theorem tag_degree_two_channel [DecidableRel G.Adj] (B S : Finset V)
    (sep : Disjoint S B) (conn : (G.induce (S : Set V)).Connected)
    (d2 : ∀ x∈S, G.degree x=2)
    (close : ∀ x∈S, ∀ y∉B, G.Adj x y → y∈S)
    {a p : V} (aB : a∈B) (pS : p∈S) (edge : G.Adj p a) :
    Nonempty (TaggedChannel G B S a) := by
  classical
  have aOut : a∉S := fun h=>Finset.disjoint_left.mp sep h aB
  obtain ⟨n,pos,f,hf,sur,root⟩ := induced_degree_two_channel conn (⟨p,pS⟩ : (S : Set V)) aOut edge
    (fun v h _ _ _ => degree_le_two_three_neighbors (d2 v h).le)
  let first : Fin n := ⟨0,pos⟩
  let last : Fin n := ⟨n-1,by omega⟩
  have eFirst : G.Adj (f first).val a := by
    change G.Adj (f ⟨0,pos⟩).val a
    rw [root]
    exact edge
  have seek : ∃ b∈B, G.Adj (f last).val b ∧ (n=1→b≠a) := by
    by_cases hn : n=1
    · have eq : last=first := Fin.ext (by change n-1=0; omega)
      rw [eq]
      have more : 1<(G.neighborFinset (f first).val).card := by
        rw [G.card_neighborFinset_eq_degree,d2 _ (f first).property]
        decide
      obtain ⟨b,mb,ne⟩ := Finset.exists_ne_of_one_lt_card more a
      have eb := (G.mem_neighborFinset _ _).mp mb
      have bB : b∈B := by
        by_contra! no
        have bs := close _ (f first).property b no eb
        obtain ⟨j,je⟩ := sur ⟨b,bs⟩
        have eqj : j=first := Fin.ext (by change j.val=0; have jj:=j.isLt; omega)
        rw [eqj] at je
        exact eb.ne (congrArg Subtype.val je)
      exact ⟨b,bB,eb,fun _=>ne⟩
    · let j : Fin n := ⟨n-2,by omega⟩
      have more : 1<(G.neighborFinset (f last).val).card := by
        rw [G.card_neighborFinset_eq_degree,d2 _ (f last).property]
        decide
      obtain ⟨b,mb,ne⟩ := Finset.exists_ne_of_one_lt_card more (f j).val
      have eb := (G.mem_neighborFinset _ _).mp mb
      have bB : b∈B := by
        by_contra! no
        have bs := close _ (f last).property b no eb
        obtain ⟨i,eq⟩ := sur ⟨b,bs⟩
        have hv : (f i).val=b := congrArg Subtype.val eq
        have act : (G.induce (S : Set V)).Adj (f last) (f i) := by
          change G.Adj _ (f i).val
          rwa [hv]
        have h := (induced_adj_both_orders hf last i).mp act
        have ij : i=j := Fin.ext (by
          change i.val=n-2
          have hh : last.val=n-1 := rfl
          have lt:=i.isLt
          omega)
        exact ne (by rw [←hv,ij])
      exact ⟨b,bB,eb,fun q => (hn q).elim⟩
  obtain ⟨b,bB,lastB,oneNe⟩ := seek
  refine ⟨⟨n,pos,f,hf,sur,b,bB,oneNe,fun i z zB => ?_⟩⟩
  constructor
  · intro ez
    have cap := (d2 _ (f i).property).le
    have zOut : z∉S := fun h=>Finset.disjoint_left.mp sep h zB
    by_cases h1 : n=1
    · have eq : i=first := Fin.ext (by change i.val=0; have lt := i.isLt; omega)
      have eq' : i=last := Fin.ext (by change i.val=n-1; have lt := i.isLt; omega)
      rcases degree_le_two_three_neighbors cap (eq.symm ▸ eFirst) (eq'.symm ▸ lastB) ez.symm with h|h|h
      · exact ((oneNe h1) h.symm).elim
      · exact Or.inl ⟨by have lt:=i.isLt; omega,h.symm⟩
      · exact Or.inr ⟨by have lt:=i.isLt; omega,h.symm⟩
    · by_cases iz : i.val=0
      · have eq : i=first := Fin.ext iz
        let j : Fin n := ⟨1,by omega⟩
        have eij : G.Adj (f i).val (f j).val :=
          (induced_adj_both_orders hf i j).mpr (Or.inl (by change i.val+1=1; omega))
        rcases degree_le_two_three_neighbors cap (eq.symm ▸ eFirst) eij ez.symm with h|h|h
        · exact (aOut (h.symm ▸ (f j).property)).elim
        · exact Or.inl ⟨iz,h.symm⟩
        · exact (zOut (h ▸ (f j).property)).elim
      · by_cases en : i.val+1=n
        · have eq : i=last := Fin.ext (by change i.val=n-1; omega)
          let j : Fin n := ⟨n-2,by omega⟩
          have eij : G.Adj (f i).val (f j).val :=
            (induced_adj_both_orders hf i j).mpr (Or.inr (by change n-2+1=i.val; omega))
          rcases degree_le_two_three_neighbors cap (eq.symm ▸ lastB) eij ez.symm with h|h|h
          · exact (Finset.disjoint_left.mp sep (h.symm ▸ (f j).property) bB).elim
          · exact Or.inr ⟨en,h.symm⟩
          · exact (zOut (h ▸ (f j).property)).elim
        · let j : Fin n := ⟨i.val-1,by omega⟩
          let k : Fin n := ⟨i.val+1,by omega⟩
          have eij : G.Adj (f i).val (f j).val :=
            (induced_adj_both_orders hf i j).mpr (Or.inr (by change i.val-1+1=i.val; omega))
          have eik : G.Adj (f i).val (f k).val :=
            (induced_adj_both_orders hf i k).mpr (Or.inl rfl)
          rcases degree_le_two_three_neighbors cap eij eik ez.symm with h|h|h
          · have eq := congrArg Fin.val (hf.1 (Subtype.ext h))
            change i.val-1=i.val+1 at eq
            omega
          · exact (zOut (h ▸ (f j).property)).elim
          · exact (zOut (h ▸ (f k).property)).elim
  · rintro (⟨iz,rfl⟩|⟨il,rfl⟩)
    · have eq : i=first := Fin.ext iz
      exact (eq.symm ▸ eFirst).symm
    · have eq : i=last := Fin.ext (by change i.val=n-1; omega)
      exact (eq.symm ▸ lastB).symm

#print axioms tag_degree_two_channel
end Graffiti133Bicycle
