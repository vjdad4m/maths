import Failure183

namespace Graffiti183.Exceptional
open SimpleGraph Finset Short177

/-- Adjacency in a hole indexed by natural cyclic order. -/
def CycleAdj {m : ℕ} (i j : Fin m) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
    (i.val = 0 ∧ j.val + 1 = m) ∨ (j.val = 0 ∧ i.val + 1 = m)

def PathAdj {m : ℕ} (i j : Fin m) : Prop := i.val + 1 = j.val ∨ j.val + 1 = i.val

variable {V : Type*}
variable {G : SimpleGraph V}

def indexSet {m : ℕ} (f : Fin m ↪ V) : Finset V := Finset.univ.map f

lemma mem_indexSet {m : ℕ} {f : Fin m ↪ V} {v : V} :
    v ∈ indexSet f ↔ ∃ i, f i = v := by simp [indexSet]

lemma mem_indexSet_self {m : ℕ} (f : Fin m ↪ V) (i : Fin m) : f i ∈ indexSet f :=
  mem_indexSet.mpr ⟨i,rfl⟩

@[simp] lemma indexSet_card {m : ℕ} (f : Fin m ↪ V) : (indexSet f).card = m := by simp [indexSet]

/-- Every consecutive interval lies in one connected component of any induced
subgraph that contains that interval. -/
lemma interval_reach {m : ℕ} (f : Fin m ↪ V)
    (hstep : ∀ i j, i.val+1=j.val → G.Adj (f i) (f j))
    {D : Finset V} {a b : Fin m} (ab : a.val ≤ b.val)
    (hD : ∀ i, a.val ≤ i.val → i.val ≤ b.val → f i ∈ D) :
    (G.induce (D : Set V)).Reachable
      ⟨f a,hD a (by omega) ab⟩ ⟨f b,hD b ab (by omega)⟩ := by
  let p (x : ℕ) (hx : a.val ≤ x) (hx' : x ≤ b.val) :
      (D : Set V) :=
    ⟨f ⟨x,by have := b.isLt; omega⟩,hD _ hx hx'⟩
  have hr (n : ℕ) (hn : a.val+n ≤ b.val) :
      (G.induce (D : Set V)).Reachable (p a.val (by omega) ab) (p (a.val+n) (by omega) hn) := by
    induction n with
    | zero => exact SimpleGraph.Reachable.rfl
    | succ n ih =>
      have hn' : a.val + n ≤ b.val := by omega
      have e : (G.induce (D : Set V)).Adj
          (p (a.val+n) (by omega) hn') (p (a.val+(n+1)) (by omega) hn) := by
        exact hstep _ _ (by change a.val+n+1=a.val+(n+1); omega)
      exact (ih hn').trans e.reachable
  have h := hr (b.val-a.val) (by omega)
  have he : a.val+(b.val-a.val)=b.val := by omega
  have ha' : p a.val (by omega) ab = ⟨f a,hD a (by omega) ab⟩ :=
    Subtype.ext (congrArg f (Fin.ext rfl))
  have hb' : p (a.val+(b.val-a.val)) (by omega) (by omega) =
      ⟨f b,hD b ab (by omega)⟩ :=
    Subtype.ext (congrArg f (Fin.ext he))
  simpa only [ha',hb'] using h

lemma connected_indexSet {m : ℕ} (hm : 0 < m) (f : Fin m ↪ V)
    (hstep : ∀ i j, i.val+1=j.val → G.Adj (f i) (f j)) :
    Graffiti177.Con G (indexSet f) := by
  apply (connected_iff_exists_forall_reachable _).mpr
  let a : Fin m := ⟨0,hm⟩
  refine ⟨⟨f a,mem_indexSet_self f a⟩,?_⟩
  intro x
  obtain ⟨i,hi⟩ := mem_indexSet.mp x.prop
  have h := interval_reach f hstep (a:=a) (b:=i) (Nat.zero_le _)
    (fun j _ _ => mem_indexSet_self f j)
  have hx : (⟨f i,mem_indexSet_self f i⟩ : (indexSet f : Set V)) = x := Subtype.ext hi
  simpa only [hx] using h

variable [DecidableEq V]

lemma twoColor_indexSet {m : ℕ} (f : Fin m ↪ V)
    (hc : ∀ i j, G.Adj (f i) (f j) → i.val % 2 ≠ j.val % 2) :
    TwoColor G (indexSet f) := by
  let A := (Finset.univ.filter (fun i : Fin m => i.val % 2 = 0)).map f
  let B := (Finset.univ.filter (fun i : Fin m => i.val % 2 = 1)).map f
  have hA (v : V) : v ∈ A ↔ ∃ i : Fin m, i.val % 2 = 0 ∧ f i = v := by simp [A]
  have hB (v : V) : v ∈ B ↔ ∃ i : Fin m, i.val % 2 = 1 ∧ f i = v := by simp [B]
  refine ⟨A,B,?_ ,?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨i,hi,e⟩ := (hA v).mp hv
    obtain ⟨j,hj,e'⟩ := (hB v).mp hw
    have := congrArg Fin.val (f.injective (e.trans e'.symm))
    omega
  · ext v
    simp only [mem_union, hA, hB, mem_indexSet]
    constructor
    · rintro (⟨i,_,e⟩ | ⟨i,_,e⟩) <;> exact ⟨i,e⟩
    · rintro ⟨i,e⟩
      have hpar : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
      rcases hpar with h | h
      · exact Or.inl ⟨i,h,e⟩
      · exact Or.inr ⟨i,h,e⟩
  · intro v hv w hw _ e
    obtain ⟨i,hi,rfl⟩ := (hA v).mp hv
    obtain ⟨j,hj,rfl⟩ := (hA w).mp hw
    exact (hc i j e) (hi.trans hj.symm)
  · intro v hv w hw _ e
    obtain ⟨i,hi,rfl⟩ := (hB v).mp hv
    obtain ⟨j,hj,rfl⟩ := (hB w).mp hw
    exact (hc i j e) (hi.trans hj.symm)

lemma indexed_path_bip {m : ℕ} (hm : 0 < m) (f : Fin m ↪ V)
    (h : ∀ i j, G.Adj (f i) (f j) ↔ PathAdj i j) :
    Graffiti177.Con G (indexSet f) ∧ TwoColor G (indexSet f) := by
  refine ⟨connected_indexSet hm f (fun i j e => (h i j).mpr (Or.inl e)),?_⟩
  apply twoColor_indexSet f
  intro i j e
  have hh := (h i j).mp e
  unfold PathAdj at hh
  omega

lemma indexed_even_cycle_bip {m : ℕ} (hm : 0 < m) (he : m % 2 = 0)
    (f : Fin m ↪ V) (h : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j) :
    Graffiti177.Con G (indexSet f) ∧ TwoColor G (indexSet f) := by
  refine ⟨connected_indexSet hm f (fun i j e => (h i j).mpr (Or.inl e)),?_⟩
  apply twoColor_indexSet f
  intro i j e
  have hh := (h i j).mp e
  unfold CycleAdj at hh
  omega

#print axioms indexed_path_bip

/-- No connected induced bipartite set of order m containing the two marked vertices.
The strict-order variant is useful for the argument based on a largest such set. -/
def NoLargeMarked (G : SimpleGraph V) (v w : V) (m : ℕ) : Prop :=
  ∀ S : Finset V, v ∈ S → w ∈ S → Graffiti177.Con G S → TwoColor G S → S.card < m

lemma no_large_path {v w : V} {m : ℕ} (h : NoLargeMarked G v w m)
    (f : Fin m ↪ V) (hm : 0 < m)
    (he : ∀ i j, G.Adj (f i) (f j) ↔ PathAdj i j)
    (hv : ∃ i, f i = v) (hw : ∃ i, f i = w) : False := by
  obtain ⟨hc,hb⟩ := indexed_path_bip hm f he
  have hh := h (indexSet f) (mem_indexSet.mpr hv) (mem_indexSet.mpr hw) hc hb
  rw [indexSet_card] at hh
  omega

end Graffiti183.Exceptional
