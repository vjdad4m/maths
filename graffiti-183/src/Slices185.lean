import GlueCut185
import RootClaw185

namespace Graffiti185.Cut
open SimpleGraph Finset
set_option maxHeartbeats 1500000
variable {V I : Type*}
variable (G : SimpleGraph V) (r : V) (label : V → I)

def slice (i : I) : Set V := {v | v = r ∨ label v = i}

abbrev Slice (i : I) := ↥(slice r label i)

def rSlice (i : I) : Slice r label i := ⟨r,Or.inl rfl⟩

lemma reach_slice (i : I)
    (hs : ∀ v w, v ≠ r → w ≠ r → G.Adj v w → label v = label w)
    {v : V} (w : G.Walk v r) (hv : v ∈ slice r label i) :
    (G.induce (slice r label i)).Reachable ⟨v,hv⟩ (rSlice r label i) := by
  by_cases hv' : v = r
  · subst v
    exact SimpleGraph.Reachable.rfl
  cases w with
  | nil => exact (hv' rfl).elim
  | @cons _ u _ e p =>
    have hu : u ∈ slice r label i := by
      by_cases hur : u = r
      · exact Or.inl hur
      · exact Or.inr ((hs _ _ hv' hur e).symm.trans (hv.resolve_left hv'))
    have he : (G.induce (slice r label i)).Adj ⟨_,hv⟩ ⟨u,hu⟩ := e
    exact he.reachable.trans (reach_slice i hs p hu)
termination_by w.length
decreasing_by
  simp_wf
  have hh : w = SimpleGraph.Walk.cons e p := eq_of_heq (by assumption)
  rw [hh]
  exact Nat.lt_succ_self _

lemma con_slice (i : I) (hc : G.Connected)
    (hs : ∀ v w, v ≠ r → w ≠ r → G.Adj v w → label v = label w) :
    (G.induce (slice r label i)).Connected := by
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨rSlice r label i,?_⟩
  intro v
  obtain ⟨w⟩ := hc.preconnected v.val r
  exact (reach_slice G r label i hs w v.prop).symm

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
noncomputable local instance sliceFintype (i : I) : Fintype (Slice r label i) := Fintype.ofFinite _

lemma data_slice_with_gain (i : I) (gain : ℕ) (hg : 1 ≤ gain)
    (witness : let R := slice r label i; let H := G.induce R; let root := rSlice r label i
      ∃ E B : Finset R, root ∈ E ∧ root ∈ B ∧ Graffiti177.Con H E ∧
        Graffiti179.closed H E = univ ∧ Short177.TwoColor H B ∧ E.card + gain ≤ B.card) :
    ∃ P : RootData G r label i, P.D.card + gain ≤ P.B.card := by
  classical
  let R := slice r label i
  let H := G.induce R
  let root : R := rSlice r label i
  obtain ⟨D,B,hDr,hBr,hcon,hfull,hbi,hbud⟩ := witness
  let f : R ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let D' := D.map f
  let B' := B.map f
  have rootd : r ∈ D' := mem_map.mpr ⟨root,hDr,rfl⟩
  have rootb : r ∈ B' := mem_map.mpr ⟨root,hBr,rfl⟩
  have fiber (S : Finset R) (x : V) (hx : x ∈ S.map f) (hxr : x ≠ r) :
      label x = i := by
    obtain ⟨y,_,rfl⟩ := mem_map.mp hx
    exact y.prop.resolve_left hxr
  let F : H.induce (↑D : Set R) →g G.induce (↑D' : Set V) :=
    ⟨fun y => ⟨f y.val,mem_map.mpr ⟨y.val,y.prop,rfl⟩⟩, fun e => e⟩
  have sur : Function.Surjective F := by
    intro y
    obtain ⟨x,hx,he⟩ := mem_map.mp y.prop
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  have con' : Graffiti177.Con G D' := hcon.map F sur
  have dom (x : V) (_hxr : x ≠ r) (hxi : label x = i) (hx : x ∉ D') :
      Graffiti177.Dominates G D' x := by
    let xx : R := ⟨x,Or.inr hxi⟩
    have hh : xx ∈ Graffiti179.closed H D := by rw [hfull]; simp
    have hnot : xx ∉ D := fun m => hx (mem_map.mpr ⟨xx,m,rfl⟩)
    obtain ⟨y,hy,he⟩ := ((Graffiti179.mem_closed H).mp hh).resolve_left hnot
    exact ⟨f y,mem_map.mpr ⟨y,hy,rfl⟩,he⟩
  obtain ⟨A,C,_hd,hAC,hA,hC⟩ := hbi
  let C0 : Bool := if r ∈ A.map f then true else false
  let χ (x : V) : Bool := if x ∈ A.map f then !C0 else C0
  have hroot : χ r = false := by
    by_cases q : r ∈ A.map f
    · simp only [χ, C0, if_pos q]
      rfl
    · simp only [χ, C0, if_neg q]
  have hdiff (x : V) (hx : x ∈ B') (y : V) (hy : y ∈ B') (he : G.Adj x y) :
      χ x ≠ χ y := by
    obtain ⟨u,hu,rfl⟩ := mem_map.mp hx
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hy
    have hu' : u ∈ A ∪ C := hAC.symm ▸ hu
    have hv' : v ∈ A ∪ C := hAC.symm ▸ hv
    have ee : H.Adj u v := he
    by_cases huA : u ∈ A <;> by_cases hvA : v ∈ A
    · exact (hA _ huA _ hvA ee.ne ee).elim
    · have uA := (Finset.mem_map' f).mpr huA
      have vA : f v ∉ A.map f := fun h => hvA ((Finset.mem_map' f).mp h)
      by_cases q : r ∈ A.map f
      · simp only [χ,C0,if_pos uA,if_neg vA,if_pos q]
        decide
      · simp only [χ,C0,if_pos uA,if_neg vA,if_neg q]
        decide
    · have vA := (Finset.mem_map' f).mpr hvA
      have uA : f u ∉ A.map f := fun h => huA ((Finset.mem_map' f).mp h)
      by_cases q : r ∈ A.map f
      · simp only [χ,C0,if_neg uA,if_pos vA,if_pos q]
        decide
      · simp only [χ,C0,if_neg uA,if_pos vA,if_neg q]
        decide
    · exact (hC _ ((mem_union.mp hu').resolve_left huA) _
        ((mem_union.mp hv').resolve_left hvA) ee.ne ee).elim
  have hbud' : D'.card + gain ≤ B'.card := by simpa [D', B'] using hbud
  exact ⟨⟨D',B',rootd,rootb,con',dom,fiber D,fiber B,χ,hroot,hdiff,by omega⟩,hbud'⟩

lemma data_slice (i : I) (hc : G.Connected)
    (hs : ∀ v w, v ≠ r → w ≠ r → G.Adj v w → label v = label w)
    (hne : ∃ v, v ≠ r ∧ label v = i) :
    Nonempty (RootData G r label i) := by
  classical
  let R := slice r label i
  let H := G.induce R
  let root : R := rSlice r label i
  obtain ⟨v,hvr,hvi⟩ := hne
  let a : R := ⟨v,Or.inr hvi⟩
  have har : a ≠ root := fun e => hvr (congrArg (fun x : R => (x : V)) e)
  letI : Nontrivial R := ⟨⟨a,root,har⟩⟩
  obtain ⟨P,hP⟩ := data_slice_with_gain G r label i 1 (by decide)
    (Graffiti179.rooted_dom H (con_slice G r label i hc hs) Fintype.one_lt_card root)
  exact ⟨P⟩

lemma data_slice_gain_two (i : I) (hc : G.Connected)
    (hs : ∀ v w, v ≠ r → w ≠ r → G.Adj v w → label v = label w)
    (hclaw : let R := slice r label i; let H := G.induce R; let root := rSlice r label i
      3 ≤ Graffiti179.localInd H root) :
    ∃ P : RootData G r label i, P.D.card + 2 ≤ P.B.card := by
  classical
  exact data_slice_with_gain G r label i 2 (by decide)
    (Graffiti179.rooted_dom_of_local_claw (G.induce (slice r label i))
      (con_slice G r label i hc hs) (rSlice r label i) hclaw)

variable [Fintype I] [Nonempty I]

theorem bound_cut_label (hc : G.Connected)
    (hs : ∀ v w, v ≠ r → w ≠ r → G.Adj v w → label v = label w)
    (hne : ∀ i : I, ∃ v, v ≠ r ∧ label v = i) :
    Fintype.card V + Fintype.card I ≤ Graffiti185.maxLeaves G + Graffiti185.bipartiteNumber G :=
  glued_bound G r label hs (fun i => Classical.choice (data_slice G r label i hc hs (hne i)))

theorem bound_cut_label_claw (hc : G.Connected)
    (hs : ∀ v w, v ≠ r → w ≠ r → G.Adj v w → label v = label w)
    (hne : ∀ i : I, ∃ v, v ≠ r ∧ label v = i) (i₀ : I)
    (hclaw : let R := slice r label i₀; let H := G.induce R; let root := rSlice r label i₀
      3 ≤ Graffiti179.localInd H root) :
    Fintype.card V + Fintype.card I + 1 ≤
      Graffiti185.maxLeaves G + Graffiti185.bipartiteNumber G := by
  classical
  obtain ⟨P₀,hP₀⟩ := data_slice_gain_two G r label i₀ hc hs hclaw
  let P (i : I) : RootData G r label i :=
    if hi : i = i₀ then hi.symm ▸ P₀ else Classical.choice (data_slice G r label i hc hs (hne i))
  let gain (i : I) : ℕ := 1 + if i = i₀ then 1 else 0
  have hgain (i : I) : (P i).D.card + gain i ≤ (P i).B.card := by
    by_cases hi : i = i₀
    · subst i
      simpa only [P,gain,if_pos rfl,dif_pos rfl] using hP₀
    · simp only [P,gain,if_neg hi,dif_neg hi,Nat.add_zero]
      exact (Classical.choice (data_slice G r label i hc hs (hne i))).budget
  have hsum : ∑ i, gain i = Fintype.card I + 1 := by
    simp [gain,Finset.sum_add_distrib]
  have h := glued_bound_gain G r label hs P gain hgain
  rw [hsum,← Nat.add_assoc] at h
  exact h

#print axioms bound_cut_label_claw
#print axioms bound_cut_label
end Graffiti185.Cut
