import RemoteSpacedPrismHandle

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteSpacedPrismWidth
open RemoteSubdivisionCore (Marks)
open SquareCap (SmallTrivial NontrivialSide boundary)
noncomputable section
set_option linter.unusedSectionVars false

variable {V I : Type*} {G : SimpleGraph V} (M : Marks G I)

private def crossing (b : Bool) (i : I) (v : V) : (V⊕I)×(V⊕I) :=
  if b then (Sum.inr i,Sum.inl v) else (Sum.inl v,Sum.inr i)

private theorem crossing_inj {b : Bool} {i j : I} {u v : V}
    (e : crossing b i u = crossing b j v) : i=j∧u=v := by
  cases b <;> simpa [crossing,and_comm] using e

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype I] [DecidableEq I]

private theorem crossing_mem (c : V⊕I→Bool) {b : Bool} {i : I} {v : V}
    (iC : c (.inr i)=b) (vN : c (.inl v)≠b) (endp : M.Ends i v) :
    crossing b i v∈boundary M.expanded c := by
  change crossing b i v ∈ FourRingCutAux.boundary M.expanded c
  apply FourRingCutAux.mem_boundary.mpr
  cases b
  · have vC : c (Sum.inl v)=true := by cases h : c (Sum.inl v) <;> simp_all
    exact ⟨vC,iC,endp⟩
  · have vC : c (Sum.inl v)=false := by cases h : c (Sum.inl v) <;> simp_all
    exact ⟨iC,vC,endp⟩

private theorem slots_force_width (c : V⊕I→Bool) (b : Bool) {i j : I} (ij : i≠j)
    (s1 : c (.inr i)=b) (s2 : c (.inr j)=b) (none : ∀ x : V,c (.inl x)≠b) :
    3≤(boundary M.expanded c).card := by
  let p := crossing b i (M.a i)
  let q := crossing b i (M.b i)
  let r := crossing b j (M.a j)
  have pq : p≠q := fun e=>(M.edge i).ne (crossing_inj e).2
  have pr : p≠r := fun e=>ij (crossing_inj e).1
  have qr : q≠r := fun e=>ij (crossing_inj e).1
  have mp : p∈boundary M.expanded c := crossing_mem M c s1 (none _) (Or.inl rfl)
  have mq : q∈boundary M.expanded c := crossing_mem M c s1 (none _) (Or.inr rfl)
  have mr : r∈boundary M.expanded c := crossing_mem M c s2 (none _) (Or.inl rfl)
  have hs : ({p,q,r}:Finset ((V⊕I)×(V⊕I)))⊆boundary M.expanded c := by
    intro e h
    simp only [mem_insert,mem_singleton] at h
    rcases h with e|e|e <;> subst e <;> assumption
  have k := card_le_card hs
  simpa [pq,pr,qr] using k

private theorem sparse_side (cub : ∀ x,G.degree x=3) (c : V⊕I→Bool)
    (low : (boundary M.expanded c).card<3) (b : Bool)
    (few : ∀ x y : V,c (.inl x)=b→c (.inl y)=b→x=y)
    (wide : NontrivialSide c b) : False := by
  have oldCut := M.cut_mono c
  have none (x : V) : c (.inl x)≠b := by
    intro hx
    have one : (boundary G (Marks.restriction c)).card=G.degree x :=
      FourRingCutAux.singleton_colour_boundary G (Marks.restriction c) x
        (fun y hy => few y x (hy.trans hx) hx)
    have three := cub x
    omega
  obtain ⟨a,d,hA,hD,n⟩ := wide
  rcases a with a|i <;> rcases d with d|j
  · exact none a hA
  · exact none a hA
  · exact none d hD
  · have ij : i≠j := fun e=>n (congrArg Sum.inr e)
    have h := slots_force_width M c b ij hA hD none
    omega

/-- Width-three survivor domain required by the rank strategy. Core
3-connectivity alone would not assert it for arbitrary attachments;
it holds here for independent one-edge subdivisions. -/
theorem expanded_wide (cub : ∀ x,G.degree x=3) (cyc : SmallTrivial G)
    (c : V⊕I→Bool) (wide : ∀ b,NontrivialSide c b) :
    3≤(boundary M.expanded c).card := by
  by_contra! low
  have mo := M.cut_mono c
  have c3 : (boundary G (Marks.restriction c)).card≤3 := by omega
  rcases cyc (Marks.restriction c) c3 with t|f
  · exact sparse_side M cub c low true t (wide true)
  · exact sparse_side M cub c low false f (wide false)

#print axioms expanded_wide
end
end KelmansCactus.AtomicBridge.RemoteSpacedPrismWidth
