import FullScorePair33

namespace Graffiti384b.ForcedCubics
open Finset SimpleGraph EarAnchor EarOnClique33 HighEar CliquePivot33 RootCut
open private EarAnchor.sees_in_clique from CubicAnchor33
open private HighEar.nonEar from HighEarBypass33
open private CubicShore.square_frame from CubicDiamondCut33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Every five-clique has at most two vertices avoiding all uncredited cubics. -/
theorem safe_cap {e a c : V} (de : H.degree e=2) (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C M : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) (mc : M⊆C)
    (safe : ∀ x∈M,Safe H R x) : M.card≤2 := by
  classical
  have ex {P : Finset V} (sz : P.card≤2) (block : ∀ x∈C\P,∃ u,u∉R ∧ H.degree u=3 ∧ H.Adj u x) : M.card≤2 := by
    have sub : M⊆P := by
      intro x xm
      apply Classical.byContradiction; intro outside
      obtain ⟨u,ur,du,ux⟩ := block x (mem_sdiff.mpr ⟨mc xm,outside⟩)
      exact safe x xm u du ur ux
    exact (card_le_card sub).trans sz
  by_cases both : a∈C ∧ c∈C
  · have see := PinnedColor34.two H ac.ne ea ec (mem_insert_self a {c}) (mem_insert_of_mem (mem_singleton_self c))
    apply ex (P:={a,c}) (by simp [ac.ne])
    intro x xm
    obtain ⟨u,_,ur,du,ux,_,_⟩ := EarOnClique33.edge_cover H de pos inj tight cl
      (insert_subset both.1 (singleton_subset_iff.mpr both.2)) (card_pair ac.ne) see xm
    exact ⟨u,ur,du,ux⟩
  by_cases thin : additional H e a c=∅
  · by_cases ms : 2≤M.card
    · exact (palette H de ea ec ac thin pos inj tight cl both mc safe ms).2.2.1.le
    · omega
  obtain ⟨w,wm⟩ := nonempty_iff_ne_empty.mpr thin
  obtain ⟨we,aw,cw⟩ := (additional_mem H).mp wm
  by_cases three : w∈C ∧ (a∈C ∨ c∈C)
  · rcases three with ⟨wc,am|cm⟩
    · exact ex (P:={a,w}) (by simp [aw.ne]) (triple H de ec ea ac.symm cw aw we pos inj tight cl (fun h => both ⟨am,h⟩) am wc).1
    · exact ex (P:={c,w}) (by simp [cw.ne]) (triple H de ea ec ac aw cw we pos inj tight cl (fun h => both ⟨h,cm⟩) cm wc).1
  let A : Finset V := {e,w}
  let B : Finset V := {a,c}
  have fr := CubicShore.square_frame H ea ec aw cw we.symm ac.ne
  have en : e∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  have small : ((A∪B)∩C).card≤1 := by
    apply card_le_one.mpr
    intro i im j jm
    obtain ⟨ifm,ic⟩ := mem_inter.mp im
    obtain ⟨jfm,jc⟩ := mem_inter.mp jm
    simp only [A,B,mem_union,mem_insert,mem_singleton] at ifm jfm
    rcases ifm with (rfl|rfl)|(rfl|rfl) <;> rcases jfm with (rfl|rfl)|(rfl|rfl) <;> tauto
  have ef : e∈A∪B := mem_union_left _ (mem_insert_self ..)
  have sub : M⊆(A∪B)∩C := by
    intro x xm
    refine mem_inter.mpr ⟨?_,mc xm⟩
    apply Classical.byContradiction; intro out
    have min (v : V) (off : v∉A∪B) : 2≤H.degree v ∧ (v∉R → 3≤H.degree v) := by
      have uv := HighEar.nonEar H de (t:=v) (fun eq => off (eq ▸ ef)) pos inj
      exact ⟨by omega,fun _ => uv⟩
    obtain ⟨u,_,du,ux,ur,_,_⟩ := EarFrame33.cover H R A B fr min inj tight cl (mc xm) small out
    exact safe x xm u du ur ux
  exact (card_le_card sub).trans (by omega)

end Graffiti384b.ForcedCubics
#print axioms Graffiti384b.ForcedCubics.safe_cap
