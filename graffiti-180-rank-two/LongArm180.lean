import VerticalForest180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain DescentOne
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A geodesic to a deepest disagreement, indexed by its distance layers.
Every step has a unique predecessor in the original graph. -/
theorem long_route {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    ∃ m : ℕ, ∃ f : ℕ→V, 0<m ∧ (∀ v∈D,G.dist v r≤m) ∧
      (∀ k≤m, f k∈D ∧ G.dist (f k) r=k) ∧ (∀ k<m,Arc G r (f k) (f (k+1))) := by
  classical
  intro P D
  have build (k : ℕ) (v : V) (vd : v∈D) (dv : G.dist v r=k) :
      ∃ f : ℕ→V, f k=v ∧ (∀ j≤k,f j∈D ∧ G.dist (f j) r=j) ∧
        ∀ j<k,Arc G r (f j) (f (j+1)) := by
    induction k generalizing v with
    | zero =>
      exact ⟨fun _ => v,rfl,fun j hj => ⟨vd,by change G.dist v r=j; omega⟩,fun _ no => (Nat.not_lt_zero _ no).elim⟩
    | succ k ih =>
      have vr : v≠r := by intro eq; rw [eq,dist_self] at dv; omega
      obtain ⟨p,vp,step⟩ := Graffiti169.exists_predecessor G h.connected r v vr
      obtain ⟨g,top,old,arcs⟩ := ih p (predecessor_closed h vd vp step) (by omega)
      let f (j : ℕ) := if j=k+1 then v else g j
      refine ⟨f,by simp [f],?_,?_⟩
      · intro j jk
        by_cases eq : j=k+1
        · subst j; simpa [f] using And.intro vd dv
        · simpa [f,eq] using old j (by omega)
      · intro j jk
        have ne : j≠k+1 := by omega
        by_cases eq : j=k
        · subst j
          simpa [f,ne,top] using unique_prior h vd vp.symm step
        · simpa [f,ne,eq] using arcs j (by omega)
  obtain ⟨v,vd,high⟩ := exists_max_image D (fun z => G.dist z r) ⟨r,h.root_disagreement⟩
  obtain ⟨f,_,data,arcs⟩ := build _ v vd rfl
  obtain ⟨w,rw⟩ := exists_adj G h.connected (by have := h.order; omega) r
  have pos := high w (both_ports h rw)
  rw [dist_eq_one_iff_adj.mpr rw.symm] at pos
  exact ⟨_,f,pos,high,data,arcs⟩

/-- Every horizontal edge meets the chosen longest arm. At a shared
disagreement depth the dual-layer theorem leaves only two possible endpoints. -/
theorem flat_hits {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) {m : ℕ} {f : ℕ→V} :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    (∀ i∈D,G.dist i r≤m) → (∀ k≤m,f k∈D ∧ G.dist (f k) r=k) →
      ∀ {a b}, G.Adj a b → (a∈P ↔ b∈P) →
        ∃ k, 0<k ∧ k≤m ∧ G.dist a r=k ∧ (a=f k ∨ b=f k) := by
  classical
  intro P D high data a b e same
  have l := h.connected.dist_triangle (u:=a) (v:=b) (w:=r)
  have q := h.connected.dist_triangle (u:=b) (v:=a) (w:=r)
  rw [dist_eq_one_iff_adj.mpr e] at l
  rw [dist_eq_one_iff_adj.mpr e.symm] at q
  have flat : G.dist a r=G.dist b r := by
    change a∈parity G r odd ↔ b∈parity G r odd at same
    simp only [mem_parity] at same
    cases odd <;> simp only [Bool.toNat_false,Bool.toNat_true] at same <;> omega
  have pos : 0<G.dist a r := by
    apply Nat.pos_of_ne_zero
    intro eq
    exact e.ne ((h.connected.dist_eq_zero_iff.mp eq).trans (h.connected.dist_eq_zero_iff.mp (flat.symm.trans eq)).symm)
  have hits : a∈D ∨ b∈D := by
    apply Classical.byContradiction
    intro no
    have flip {z : V} (zd : z∉D) : z∈A ↔ z∈P := by
      change z∉(A∪P)\(A∩P) at zd
      simp only [mem_sdiff,mem_union,mem_inter] at zd
      tauto
    have aa := flip (fun ad => no (Or.inl ad))
    have bb := flip (fun bd => no (Or.inr bd))
    by_cases ap : a∈P
    · exact h.independent a (aa.mpr ap) b (bb.mpr (same.mp ap)) e.ne e
    · have outside := outside_independent h
      apply outside a (mem_sdiff.mpr ⟨mem_univ _,?_⟩) b (mem_sdiff.mpr ⟨mem_univ _,?_⟩) e.ne e
      · exact fun v => ap ((mem_union.mp v).elim aa.mp id)
      · exact fun v => ap (same.mpr ((mem_union.mp v).elim bb.mp id))
  have cap : G.dist a r≤m := hits.elim (high a) (fun bd => flat ▸ high b bd)
  let k := G.dist a r
  have ⟨fd,df⟩ := data k cap
  refine ⟨k,pos,cap,rfl,?_⟩
  rcases hits with ad|bd
  · by_cases af : a=f k
    · exact Or.inl af
    · exact Or.inr (((dual_layer h ad fd af df.symm).1 b flat.symm).resolve_left e.ne.symm)
  · by_cases bf : b=f k
    · exact Or.inr bf
    · exact Or.inl (((dual_layer h bd fd bf (flat.symm.trans df.symm)).1 a flat).resolve_left e.ne)

#print axioms long_route
#print axioms flat_hits
end Minimal180.RootEar
