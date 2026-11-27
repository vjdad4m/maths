import RootChoice180
import Boundary180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def near (G : SimpleGraph V) (N : Finset V) (nz : N.Nonempty) (v : V) : ℕ :=
  N.inf' nz (fun x => G.dist v x)

omit [Fintype V] [DecidableEq V] in
theorem near_attained (G : SimpleGraph V) (N : Finset V) (nz : N.Nonempty) (v : V) :
    ∃ x∈N,G.dist v x=near G N nz v := by
  obtain ⟨x,xn,low⟩ := exists_min_image N (fun z => G.dist v z) nz
  exact ⟨x,xn,le_antisymm (le_inf' nz _ low) (inf'_le _ xn)⟩

omit [Fintype V] [DecidableEq V] in
theorem near_lip (G : SimpleGraph V) (gc : G.Connected) (N : Finset V) (nz : N.Nonempty)
    {a b : V} (edge : G.Adj a b) : near G N nz a≤near G N nz b+1 := by
  obtain ⟨x,xn,eq⟩ := near_attained G N nz b
  have tri := gc.dist_triangle (u:=a) (v:=b) (w:=x)
  rw [dist_eq_one_iff_adj.mpr edge,eq] at tri
  have lo : near G N nz a≤G.dist a x := inf'_le _ xn
  omega

omit [Fintype V] in
/-- Root distances after restoring a vertex, in terms of distance to the
whole attachment set in the deletion graph. -/
theorem apex_dist (G : SimpleGraph V) (gc : G.Connected) (N : Finset V) (nz : N.Nonempty) (v : V) :
    (ear G N).dist (.inl v) (.inr ())=near G N nz v+1 := by
  classical
  let d : V⊕Unit → ℕ := Sum.elim (fun x => near G N nz x+1) (fun _ => 0)
  have zero (x : V) (xn : x∈N) : near G N nz x=0 := by
    have le : near G N nz x≤G.dist x x := inf'_le _ xn
    rw [dist_self] at le; omega
  have hd := layers (ear G N) (.inr ()) d rfl (fun {a b} edge => by
    rcases a with a|u <;> rcases b with b|v
    · change near G N nz a+1≤near G N nz b+1+1
      have := near_lip G gc N nz (show G.Adj a b from edge); omega
    · change near G N nz a+1≤0+1; rw [zero a edge]
    · exact Nat.zero_le _
    · exact edge.elim) (fun x ne => by
      rcases x with x|u
      · by_cases xn : x∈N
        · exact ⟨.inr (),xn,by change near G N nz x+1=0+1; rw [zero x xn]⟩
        obtain ⟨y,yn,eq⟩ := near_attained G N nz x
        obtain ⟨z,xz,dec⟩ := Graffiti169.exists_predecessor G gc y x (fun e => xn (e ▸ yn))
        have low : near G N nz z≤G.dist z y := inf'_le _ yn
        have high := near_lip G gc N nz xz
        exact ⟨.inl z,xz,by change near G N nz x+1=near G N nz z+1+1; omega⟩
      · cases u; exact (ne rfl).elim)
  exact hd.2 (.inl v)

noncomputable def nearParity (G : SimpleGraph V) (N : Finset V) (nz : N.Nonempty) (p : Bool) : Finset V :=
  univ.filter (fun v => near G N nz v%2=p.toNat)

/-- Adding a root reverses the nearest-port parity on every surviving vertex. -/
theorem apex_parity (G : SimpleGraph V) (gc : G.Connected) (N : Finset V) (nz : N.Nonempty) (p : Bool) :
    parity (ear G N) (.inr ()) p=lift (nearParity G N nz (!p)) (!p) := by
  classical
  ext x
  cases x with
  | inl v =>
    simp only [mem_parity,inl_lift,nearParity,mem_filter,mem_univ,true_and,apex_dist G gc N nz]
    cases p <;> simp only [Bool.not_true,Bool.not_false,Bool.toNat_true,Bool.toNat_false] <;> omega
  | inr u => cases u; cases p <;> simp [mem_parity,dist_self]

omit [Fintype V] in
theorem apex_eligible (A P : Finset V) (a m : Bool) :
    eligible (lift A a) (lift P m) (.inr ())=lift (A∪P) (a && m) := by
  classical
  ext v
  rcases v with v|u
  · simp [eligible_iff]
  · cases u; cases a <;> cases m <;> simp [eligible_iff]

#print axioms near_attained
#print axioms near_lip
#print axioms apex_dist
#print axioms apex_parity
#print axioms apex_eligible
end Minimal180.PortParity
