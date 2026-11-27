import RootPort180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Simultaneous branching at two nonroot, independently marked vertices
with disjoint open neighborhoods. The marks may be in either parity. -/
theorem two_stars_gain (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r a z : V) (ar : a≠r) (zr : z≠r) (az : a≠z) (p : Bool) (A : Finset V) (ai : Indep G A)
    (am : a∈A) (zm : z∈A) (apart : ∀ v,G.Adj a v → ¬G.Adj z v) :
    (G.degree a-2)+(G.degree z-2)≤allowance G r p A := by
  classical
  let S : Finset V := {a,z}
  have splitS {v : V} (m : v∈S) : v=a ∨ v=z := (mem_insert.mp m).imp_right mem_singleton.mp
  have inc : S⊆A := insert_subset am (singleton_subset_iff.mpr zm)
  have nr (v : V) (m : v∈S) : v≠r := (splitS m).elim (fun e => e ▸ ar) (fun e => e ▸ zr)
  have unique {v i j : V} (im : i∈S) (jm : j∈S) (iv : G.Adj i v) (jv : G.Adj j v) : i=j := by
    rcases splitS im with rfl|rfl <;> rcases splitS jm with rfl|rfl <;> first | rfl | exact (apart _ iv jv).elim | exact (apart _ jv iv).elim
  let d (v : V) := G.dist v r
  let par v := if h : v=r then r else (Graffiti169.exists_predecessor G gc r v h).choose
  have spec (v : V) (vr : v≠r) : G.Adj v (par v) ∧ d v=d (par v)+1 := by
    simpa [d,par,vr] using (Graffiti169.exists_predecessor G gc r v vr).choose_spec
  let B := S.image par
  let tag (v : V) := if v∈S then 0 else if v∈B then 2 else 5
  let k (v : V) := 4*d v+tag v
  let attach (v : V) := ∃ i∈S,G.Adj i v ∧ v≠par i
  let q (v : V) := if h : attach v then h.choose else par v
  have noS {v i : V} (im : i∈S) (iv : G.Adj i v) : v∉S :=
    fun vm => ai i (inc im) v (inc vm) iv.ne iv
  have qt (v : V) (vm : v∈S) : q v=par v := by
    have n : ¬attach v := by
      intro yes
      obtain ⟨i,m,ed,_⟩ := yes
      exact noS m ed vm
    simp [q,n]
  have btag (i : V) (im : i∈S) : tag (par i)=2 := by
    have m : par i∈B := mem_image_of_mem _ im
    simp [tag,noS im (spec i (nr i im)).1,m]
  have step (v : V) (vr : v≠r) : G.Adj v (q v) ∧ k (q v)<k v := by
    by_cases h : attach v
    · obtain ⟨im,ed,np⟩ := h.choose_spec
      have bv : v∉B := by
        intro bv
        obtain ⟨j,jm,eq⟩ := mem_image.mp bv
        have jv : G.Adj j v := eq ▸ (spec j (nr j jm)).1
        exact np ((unique im jm ed jv) ▸ eq.symm)
      have near := gc.dist_triangle (u:=h.choose) (v:=v) (w:=r)
      rw [dist_eq_one_iff_adj.mpr ed] at near
      have ds : d h.choose≤d v+1 := by dsimp [d];omega
      have qq : q v=h.choose := dif_pos h
      rw [qq]
      refine ⟨ed.symm,?_⟩
      simp [k,tag,im,noS im ed,bv];omega
    · rw [show q v=par v from dif_neg h]
      obtain ⟨ed,dx⟩ := spec v vr
      refine ⟨ed,?_⟩
      change 4*d (par v)+tag (par v)<4*d v+tag v
      by_cases vm : v∈S
      · rw [btag v vm,show tag v=0 from if_pos vm];omega
      · have low : 2≤tag v := by simp only [tag,if_neg vm];split_ifs <;> decide
        have hi : tag (par v)≤5 := by simp only [tag];split_ifs <;> decide
        omega
  obtain ⟨T,tree,take⟩ := virtual_tree r q k (fun v vr => (step v vr).2)
  have imaged := parent_image T tree r q k (fun v vr => (step v vr).2) take
  have sub : T≤G := by
    intro x y ed
    have e : s(x,y)∈T.edgeFinset := mem_edgeFinset.mpr ed
    rw [←imaged] at e
    obtain ⟨v,vm,eq⟩ := mem_image.mp e
    have h := (step v (mem_erase.mp vm).1).1
    rcases Sym2.eq_iff.mp eq with ⟨i,j⟩|⟨i,j⟩
    · exact i ▸ j ▸ h
    · exact i ▸ j ▸ h.symm
  have full (i : V) (im : i∈S) : T.degree i=G.degree i := by
    have eq : T.neighborFinset i=G.neighborFinset i := by
      ext v;simp only [mem_neighborFinset]
      refine ⟨fun e => sub e,fun ed => ?_⟩
      by_cases ev : v=par i
      · rw [ev,←qt i im];exact take i (nr i im)
      · have h : attach v := ⟨i,im,ed,ev⟩
        have qq : q v=i := (dif_pos h : q v=h.choose).trans (unique h.choose_spec.1 im h.choose_spec.2.1 ed)
        have vr : v≠r := by
          intro e
          have dr : d i=1 := dist_eq_one_iff_adj.mpr (e ▸ ed)
          have s := (spec i (nr i im)).2
          have pr : par i=r := gc.dist_eq_zero_iff.mp (show d (par i)=0 by omega)
          exact ev (e.trans pr.symm)
        exact qq ▸ (take v vr).symm
    simpa only [card_neighborFinset_eq_degree] using congrArg card eq
  have pay (v : V) (m : v∈A∩parity G r p) (vr : v≠r) : q v∉A∪parity G r p := by
    obtain ⟨va,vp⟩ := mem_inter.mp m
    have h : ¬attach v := by
      intro yes
      obtain ⟨i,im,ed,_⟩ := yes
      exact ai i (inc im) v va ed.ne ed
    rw [show q v=par v from dif_neg h]
    obtain ⟨ed,dd⟩ := spec v vr
    refine fun pm => (mem_union.mp pm).elim (fun ma => ai v va _ ma ed.ne ed) (fun pp => ?_)
    have vv := (mem_parity ..).mp vp
    have parv := (mem_parity ..).mp pp
    change G.dist v r=G.dist (par v) r+1 at dd;omega
  have bound := parent_gain G T gc hn sub tree r p A ai q k (fun v vr => (step v vr).2) take pay ∅ (by simp)
  rw [card_empty,zero_add] at bound
  have za : z∈(A∪parity G r p).erase r := mem_erase.mpr ⟨zr,mem_union_left _ zm⟩
  have aa : a∈((A∪parity G r p).erase r).erase z := mem_erase.mpr ⟨az,mem_erase.mpr ⟨ar,mem_union_left _ am⟩⟩
  have one := single_le_sum (f:=fun v => T.degree v-2) (fun _ _ => Nat.zero_le _) aa
  change T.degree a-2≤∑ v∈((A∪parity G r p).erase r).erase z,(T.degree v-2) at one
  have total := add_sum_erase ((A∪parity G r p).erase r) (fun v => T.degree v-2) za
  change T.degree z-2+(∑ v∈((A∪parity G r p).erase r).erase z,(T.degree v-2))=
    ∑ v∈(A∪parity G r p).erase r,(T.degree v-2) at total
  rw [←full a (mem_insert_self ..),←full z (mem_insert_of_mem (mem_singleton_self _))]
  omega

#print axioms two_stars_gain
end Minimal180.OppositeGain
