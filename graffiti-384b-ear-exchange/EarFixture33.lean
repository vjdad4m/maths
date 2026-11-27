import Exchange33

namespace Graffiti384b.EarFixture33
open Finset SimpleGraph

def baseNeighbors : Fin 6 → Finset (Fin 6)
  | 0 => {1,2,3,4,5}
  | 1 => {0,3,4,5}
  | 2 => {0,3,4}
  | 3 => {0,1,2}
  | 4 => {0,1,2}
  | 5 => {0,1}

def core : SimpleGraph (Fin 6) where
  Adj u v := v∈baseNeighbors u
  symm := by
    have h : ∀ u v : Fin 6,v∈baseNeighbors u → u∈baseNeighbors v := by decide
    exact fun x y => h x y
  loopless := by change ∀ u : Fin 6,u∉baseNeighbors u; decide

instance : DecidableRel core.Adj := fun u v => inferInstanceAs (Decidable (v∈baseNeighbors u))

/-- The extra vertex 6 is adjacent only to the specified root. -/
def withLeaf (a : Fin 6) : SimpleGraph (Fin 7) where
  Adj u v := (∃ i j : Fin 6,u=i.castSucc ∧ v=j.castSucc ∧ core.Adj i j) ∨
    (u=6 ∧ v=a.castSucc) ∨ (v=6 ∧ u=a.castSucc)
  symm := by
    intro u v h
    rcases h with ⟨i,j,ui,vj,edge⟩|h|h
    · exact Or.inl ⟨j,i,vj,ui,edge.symm⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless := by
    intro u h
    rcases h with ⟨i,j,ui,uj,edge⟩|⟨hu,ha⟩|⟨hu,ha⟩
    · exact edge.ne (Fin.castSucc_injective _ (ui.symm.trans uj))
    all_goals have eq := congrArg Fin.val (ha.symm.trans hu); change a.val=6 at eq; omega

instance (a : Fin 6) : DecidableRel (withLeaf a).Adj := fun u v => by unfold withLeaf; dsimp; infer_instance

private theorem gamma_of_test {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (test : (∃ D,TwoDominates G D ∧ D.card=k) ∧
      ∀ D,TwoDominates G D → k≤D.card) : gamma G=k := by
  have up : gamma G≤k := Nat.sInf_le test.1
  apply le_antisymm up
  have avail : {s : ℕ | ∃ D,TwoDominates G D ∧ D.card=s}.Nonempty := ⟨k,test.1⟩
  obtain ⟨D,dom,sz⟩ := Nat.sInf_mem avail
  change D.card=gamma G at sz
  rw [← sz]; exact test.2 D dom

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The two roots have equal core degree and triangle score. Each misses the
unique triangular ear. The pendant extensions have different minima. -/
theorem different_attachments :
    List.ofFn (trianglesAt core)=[5,3,2,2,2,1] ∧
    List.ofFn (fun v => core.degree v)=[5,4,3,3,3,2] ∧ core.neighborFinset 5={0,1} ∧ core.Adj 0 1 ∧
    gamma core=3 ∧ gamma (withLeaf 2)=3 ∧ gamma (withLeaf 3)=4 := by
  refine ⟨by decide,by decide,by decide,by decide,?_,?_,?_⟩
  all_goals apply gamma_of_test
  all_goals unfold TwoDominates; decide

end Graffiti384b.EarFixture33
#print axioms Graffiti384b.EarFixture33.different_attachments
