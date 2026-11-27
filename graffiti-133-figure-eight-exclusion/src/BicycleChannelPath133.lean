import CambyPathEnds133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Graffiti133Camby Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem connected_degree_two_spanning_path (hc : G.Connected) (r : V)
    (tip : ∀ a b, G.Adj r a → G.Adj r b → a=b)
    (cap : ∀ v a b c, G.Adj v a → G.Adj v b → G.Adj v c → a=b ∨ a=c ∨ b=c) :
    ∃ (n : Nat) (hn : 0<n) (f : Fin n → V),
      InducedPath G f ∧ Function.Surjective f ∧ f ⟨0,hn⟩=r := by
  classical
  let pred (n : Nat) : Prop := ∃ (hn : 0<n) (f : Fin n→V), InducedPath G f ∧ f ⟨0,hn⟩=r
  let Q := (Finset.range (Fintype.card V+1)).filter pred
  have hmem (n : Nat) : n∈Q ↔ pred n := by
    constructor
    · exact fun h => (Finset.mem_filter.mp h).2
    · intro h
      obtain ⟨hn,f,hf,he⟩ := h
      have hnC : n ≤ Fintype.card V := by simpa using Fintype.card_le_of_injective f hf.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),⟨hn,f,hf,he⟩⟩
  have one : 1∈Q := (hmem _).mpr
    ⟨by decide, fun _ => r, ⟨fun _ _ _ => Subsingleton.elim _ _,fun i j h =>
      ((not_lt_of_ge (by rw [Subsingleton.elim i j])) h).elim⟩,rfl⟩
  obtain ⟨n,hn,hm⟩ := Finset.exists_max_image Q id ⟨1,one⟩
  obtain ⟨pos,f,hf,root⟩ := (hmem n).mp hn
  let last : Fin n := ⟨n-1,by omega⟩
  have blocked (z : V) (off : ∀ i,z≠f i) (i : Fin n) (nonlast : i.val+1<n) :
      ¬G.Adj z (f i) := by
    intro e
    let b : Fin n := ⟨i.val+1,nonlast⟩
    have ib : i < b := by change i.val < i.val+1; omega
    have step : G.Adj (f i) (f b) := (hf.2 i b ib).2 rfl
    by_cases zero : i.val=0
    · have ri : f i=r := by rw [show i=(⟨0,pos⟩ : Fin n) from Fin.ext zero]; exact root
      rw [ri] at e step
      exact off b (tip z _ e.symm step)
    · let a : Fin n := ⟨i.val-1,by omega⟩
      have ai : a < i := by change i.val-1 < i.val; omega
      have rev : G.Adj (f a) (f i) := (hf.2 a i ai).mpr (by change i.val-1+1=i.val; omega)
      have ne : f a≠f b := hf.1.ne (ne_of_lt (ai.trans ib))
      rcases cap (f i) (f a) (f b) z rev.symm step e.symm with eq|eq|eq
      · exact ne eq
      · exact (off a) eq.symm
      · exact (off b) eq.symm
  have stop (z : V) (off : ∀ i,z≠f i) : ¬ G.Adj z (f last) := by
    intro e
    let p : Fin (n+1) → V := Fin.lastCases z f
    have pn : InducedPath G p := append_induced pos hf z off e (fun i h => blocked z off i h)
    have ps : p ⟨0,by omega⟩=r := by
      change p ((⟨0,pos⟩ : Fin n).castSucc)=r
      change Fin.lastCases z f ((⟨0,pos⟩ : Fin n).castSucc)=r
      exact (Fin.lastCases_castSucc ..).trans root
    have hh := hm (n+1) ((hmem _).mpr ⟨by omega,p,pn,ps⟩)
    change n+1≤n at hh
    omega
  have close {x y : V} (e : G.Adj x y) (hx : ∃ i,f i=x) : ∃ i,f i=y := by
    obtain ⟨i,rfl⟩ := hx
    by_cases yes : ∃ i,f i=y
    · exact yes
    exfalso
    have off (j : Fin n) : y≠f j := fun eq => yes ⟨j,eq.symm⟩
    by_cases h : i.val+1<n
    · exact blocked y off i h e.symm
    · have eq : i=last := Fin.ext (by change i.val=n-1; omega)
      exact stop y off (eq ▸ e.symm)
  have reach {x y : V} (p : G.Walk x y) (hx : ∃ i,f i=x) : ∃ i,f i=y := by
    induction p with
    | nil => exact hx
    | cons e _ ih => exact ih (close e hx)
  refine ⟨n,pos,f,hf,fun v => ?_,root⟩
  obtain ⟨p⟩ := hc r v
  exact reach p ⟨⟨0,pos⟩,root⟩

theorem induced_degree_two_channel {E : Set V} [Fintype E]
    (hc : (G.induce E).Connected) (r : E) {b : V} (hb : b∉E) (br : G.Adj r.val b)
    (cap : ∀ v∈E, ∀ i j k, G.Adj v i → G.Adj v j → G.Adj v k → i=j ∨ i=k ∨ j=k) :
    ∃ (n : Nat) (hn : 0<n) (f : Fin n → E),
      InducedPath (G.induce E) f ∧ Function.Surjective f ∧ f ⟨0,hn⟩=r := by
  apply connected_degree_two_spanning_path hc r
  · intro i j ei ej
    have f := cap r.val r.property i.val j.val b ei ej br
    rcases f with h|h|h
    · exact Subtype.ext h
    · exact (hb (h ▸ i.property)).elim
    · exact (hb (h ▸ j.property)).elim
  · intro x i j k ei ej ek
    rcases cap x.val x.property i.val j.val k.val ei ej ek with h|h|h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))

#print axioms induced_degree_two_channel
#print axioms connected_degree_two_spanning_path
end Graffiti133Bicycle
