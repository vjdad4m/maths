import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith

/-!
# Written on the Wall II, conjecture 242

For a finite nontrivial tree, twice its total domination number is at least
the number of components induced by the closed neighborhood of the degree-two
vertices plus its average eccentricity. The proof obtains the diameter in
place of average eccentricity. A singleton has no total dominating set, so
the minimum-size invariant is not defined on it.

The proof counts the slack in how many diameter-path vertices each member
of a minimum total dominating set can cover, then injects all but at most
one closure component into the resulting slots. This completes the earlier
written charging argument and the earlier partial Lean formalization.
Official catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
Lean 4.19.0 and Mathlib v4.19.0.
-/

set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Finset SimpleGraph
open scoped BigOperators

namespace Graffiti242
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def nbr (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact univ.filter (G.Adj v)

@[simp] theorem mem_nbr (G : SimpleGraph V) {x y : V} : y ∈ nbr G x ↔ G.Adj x y := by
  classical
  simp [nbr]

def TotalDominates (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

def totalDominationNumber (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}

def S (G : SimpleGraph V) (v : V) : Prop := (nbr G v).card = 2

def closedDegreeTwo (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter (fun v => S G v ∨ ∃ s, S G s ∧ G.Adj v s)

@[simp] theorem mem_closed (G : SimpleGraph V) (v : V) :
    v ∈ closedDegreeTwo G ↔ S G v ∨ ∃ s, S G s ∧ G.Adj v s := by
  classical
  simp [closedDegreeTwo]

private theorem finiteComponents {W : Type*} [Finite W] (H : SimpleGraph W) :
    Finite H.ConnectedComponent :=
  Finite.of_surjective H.connectedComponentMk (fun c => c.exists_rep)

def countComponents (G : SimpleGraph V) : ℕ :=
  @Fintype.card _ (@Fintype.ofFinite _ (finiteComponents (G.induce (closedDegreeTwo G : Set V))))

private theorem exists_min_td (G : SimpleGraph V) (hc : G.Connected) (hn : 2 ≤ Fintype.card V) :
    ∃ D : Finset V, TotalDominates G D ∧ D.card = totalDominationNumber G := by
  have hall : TotalDominates G Finset.univ := by
    intro v
    obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
    obtain ⟨p⟩ := hc v w
    cases p with
    | nil => exact (hw rfl).elim
    | cons h _ => exact ⟨_,mem_univ _,h⟩
  have hnon : {k : ℕ | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}.Nonempty :=
    ⟨Fintype.card V, Finset.univ, hall, Finset.card_univ⟩
  exact Nat.sInf_mem hnon


theorem take_length {a b : V} (p : G.Walk a b) (k : ℕ) :
    (p.take k).length = min k p.length := by
  induction p generalizing k with
  | nil => simp [Walk.take]
  | cons h p ih =>
    cases k with
    | zero => simp [Walk.take]
    | succ k =>
      simp only [Walk.take, Walk.length_cons, ih]
      omega

theorem drop_length {a b : V} (p : G.Walk a b) (k : ℕ) :
    (p.drop k).length = p.length-k := by
  induction p generalizing k with
  | nil => simp [Walk.drop]
  | cons h p ih =>
    cases k with
    | zero => simp [Walk.drop]
    | succ k =>
      simp only [Walk.drop, Walk.length_cons, ih]
      omega

theorem dist_index {a b : V} (hc : G.Connected) (p : G.Walk a b)
    (hp : p.length = G.dist a b) {i : ℕ} (hi : i ≤ p.length) :
    G.dist a (p.getVert i)=i := by
  have h1 := G.dist_le (p.take i)
  have h2 := G.dist_le (p.drop i)
  have h3 := hc.dist_triangle (u:=a) (v:=p.getVert i) (w:=b)
  rw [take_length] at h1
  rw [drop_length] at h2
  omega

theorem index_adj {a b : V} (hc : G.Connected) (p : G.Walk a b)
    (hp : p.length = G.dist a b) {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) :
    G.Adj (p.getVert i) (p.getVert j) ↔ i+1=j ∨ j+1=i := by
  constructor
  · intro ha
    have h1 := hc.dist_triangle (u:=a) (v:=p.getVert i) (w:=p.getVert j)
    have h2 := hc.dist_triangle (u:=a) (v:=p.getVert j) (w:=p.getVert i)
    rw [dist_index hc p hp hi,dist_index hc p hp hj,dist_eq_one_iff_adj.mpr ha] at h1
    rw [dist_index hc p hp hi,dist_index hc p hp hj,dist_eq_one_iff_adj.mpr ha.symm] at h2
    have hne : i ≠ j := fun h => ha.ne (congrArg p.getVert h)
    omega
  · rintro (h | h)
    · rw [← h]
      exact p.adj_getVert_succ (by omega)
    · rw [← h]
      exact (p.adj_getVert_succ (by omega)).symm

theorem support_connected {a b : V} (p : G.Walk a b) :
    (G.induce {v | v ∈ p.support}).Connected := by
  let Q : Set V := {v | v ∈ p.support}
  let H := G.induce Q
  let v (i : ℕ) : Q := ⟨p.getVert i,p.getVert_mem_support i⟩
  have hreachable (i : ℕ) (hi : i ≤ p.length) : H.Reachable (v 0) (v i) := by
    induction i with
    | zero => exact .rfl
    | succ i ih =>
      have hn : i < p.length := by omega
      have had : H.Adj (v i) (v (i+1)) := p.adj_getVert_succ hn
      exact (ih (by omega)).trans had.reachable
  letI : Nonempty Q := ⟨v 0⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.mp x.2
  obtain ⟨j,hj,hjl⟩ := Walk.mem_support_iff_exists_getVert.mp y.2
  have hix : v i = x := Subtype.ext hi
  have hjy : v j = y := Subtype.ext hj
  rw [← hix,← hjy]
  exact (hreachable i hil).symm.trans (hreachable j hjl)

theorem unique_path_support {P : Set V} (hT : G.IsTree) (hP : (G.induce P).Connected)
    {a b : V} (ha : a∈P) (hb : b∈P) (p : G.Walk a b) (hp : p.IsPath) :
    ∀ w ∈ p.support, w ∈ P := by
  let H := G.induce P
  let f : H →g G := ⟨Subtype.val, fun h => h⟩
  obtain ⟨q,hq⟩ := hP.exists_isPath (⟨a,ha⟩ : P) ⟨b,hb⟩
  let q' : G.Walk a b := q.map f
  have hq' : q'.IsPath := Walk.map_isPath_of_injective (fun _ _ h => Subtype.ext h) hq
  obtain ⟨z,_,hz⟩ := hT.existsUnique_path a b
  have he : p=q' := (hz p hp).trans (hz q' hq').symm
  intro w hw
  rw [he,show q'.support = List.map (Subtype.val : P → V) q.support from Walk.support_map f q] at hw
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hw
  exact x.2

theorem path_of_two {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hne : a ≠ c) :
    (Walk.cons hab (Walk.cons hbc Walk.nil)).IsPath := by
  simp [Walk.isPath_def, hab.ne,hbc.ne,hne]

theorem path_of_three {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hac : a≠c) (had : a≠d) (hbd : b≠d) :
    (Walk.cons hab (Walk.cons hbc (Walk.cons hcd Walk.nil))).IsPath := by
  simp [Walk.isPath_def,hab.ne,hbc.ne,hcd.ne,hac,had,hbd]

theorem outside_one {P : Set V} (hT : G.IsTree) (hP : (G.induce P).Connected)
    {a b x : V} (ha : a∈P) (hb : b∈P) (hx : x∉P)
    (hax : G.Adj a x) (hbx : G.Adj b x) : a=b := by
  by_contra hab
  let p : G.Walk a b := Walk.cons hax (Walk.cons hbx.symm Walk.nil)
  exact hx (unique_path_support hT hP ha hb p (path_of_two hax hbx.symm hab) x (by simp [p]))

theorem no_triangle (hT : G.IsTree) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) : False := by
  let p : G.Walk a c := Walk.cons hab (Walk.cons hbc Walk.nil)
  let q : G.Walk a c := Walk.cons hac Walk.nil
  have hp : p.IsPath := path_of_two hab hbc hac.ne
  have hq : q.IsPath := by simp [q,Walk.isPath_def,hac.ne]
  obtain ⟨w,_,hw⟩ := hT.existsUnique_path a c
  have he : p=q := (hw p hp).trans (hw q hq).symm
  have hlen := congrArg Walk.length he
  simp [p,q] at hlen

theorem depth_two_far {P : Set V} (hT : G.IsTree) (hP : (G.induce P).Connected)
    {a x y : V} (ha : a∈P) (hx : x∉P) (hax : G.Adj a x) (hxy : G.Adj x y)
    (hya : y ≠ a) : y ∉ P ∧ ∀ b ∈ P, ¬ G.Adj y b := by
  have hy : y ∉ P := fun hp => hya (outside_one hT hP hp ha hx hxy.symm hax)
  refine ⟨hy,?_⟩
  intro b hb hby
  by_cases he : a=b
  · subst b
    exact no_triangle hT hax hxy hby.symm
  have hax' : a ≠ y := hya.symm
  have hxb : x ≠ b := fun h => hx (h ▸ hb)
  let p : G.Walk a b := Walk.cons hax (Walk.cons hxy (Walk.cons hby Walk.nil))
  exact hx (unique_path_support hT hP ha hb p (path_of_three hax hxy hby hax' he hxb) x (by simp [p]))

theorem depth_two_owner {P : Set V} (hT : G.IsTree) (hP : (G.induce P).Connected)
    {a b x x' y : V} (ha : a∈P) (hb : b∈P) (hx : x∉P) (hx' : x'∉P) (hy : y∉P)
    (hax : G.Adj a x) (hxy : G.Adj x y) (hbx' : G.Adj b x') (hx'y : G.Adj x' y) :
    a = b := by
  by_contra hab
  have hxx' : x ≠ x' := by
    intro h
    subst x'
    exact hab (outside_one hT hP ha hb hx hax hbx')
  have hay : a≠y := fun h => hy (h ▸ ha)
  have hax' : a≠x' := fun h => hx' (h ▸ ha)
  have hxb : x≠b := fun h => hx (h.symm ▸ hb)
  have hyb : y≠b := fun h => hy (h.symm ▸ hb)
  let p : G.Walk a b := Walk.cons hax (Walk.cons hxy (Walk.cons hx'y.symm (Walk.cons hbx'.symm Walk.nil)))
  have hp : p.IsPath := by
    simp [p,Walk.isPath_def,hax.ne,hxy.ne,hx'y.ne.symm,hbx'.ne.symm,hab,hxx',hay,hax',hxb,hyb]
  exact hx (unique_path_support hT hP ha hb p hp x (by simp [p]))

theorem path_dist_eq_len (hT : G.IsTree) {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    G.dist a b = p.length := by
  obtain ⟨q,hq,hlen⟩ := hT.isConnected.exists_path_of_dist a b
  obtain ⟨w,_,hw⟩ := hT.existsUnique_path a b
  have he : p=q := (hw p hp).trans (hw q hq).symm
  rw [he,hlen]

theorem diameter_endpoint_support (hT : G.IsTree) {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) (hd : ∀ x y, G.dist x y ≤ p.length) :
    ∀ x, G.Adj a x → x ∈ p.support := by
  intro x hx
  by_contra hxp
  have hq : (Walk.cons hx.symm p).IsPath := (Walk.cons_isPath_iff hx.symm p).mpr ⟨hp,hxp⟩
  have hlen := path_dist_eq_len hT _ hq
  rw [Walk.length_cons] at hlen
  have hu := hd x b
  omega

theorem endpoint_neighbors (hT : G.IsTree) {a b : V} (p : G.Walk a b)
    (hp : p.IsPath) (hlen : p.length = G.dist a b) (hpos : 0 < p.length)
    (hd : ∀ x y, G.dist x y ≤ p.length) :
    (∀ x, G.Adj a x ↔ x=p.getVert 1) ∧ (∀ x, G.Adj b x ↔ x=p.getVert (p.length-1)) := by
  constructor
  · intro x
    constructor
    · intro hx
      obtain ⟨i,hi,hiL⟩ := Walk.mem_support_iff_exists_getVert.mp
        (diameter_endpoint_support hT p hp hd x hx)
      have ha : G.Adj (p.getVert 0) (p.getVert i) := by simpa [hi] using hx
      have hc := (index_adj hT.isConnected p hlen (by omega : 0 ≤ p.length) hiL).mp ha
      have h1 : i=1 := by omega
      simpa [h1] using hi.symm
    · rintro rfl
      simpa using p.adj_getVert_succ (i:=0) hpos
  · intro x
    constructor
    · intro hx
      have hd' (u v : V) : G.dist u v ≤ p.reverse.length := by simpa using hd u v
      have hmem := diameter_endpoint_support hT p.reverse hp.reverse hd' x hx
      rw [Walk.support_reverse] at hmem
      have hmem' : x ∈ p.support := List.mem_reverse.mp hmem
      obtain ⟨i,hi,hiL⟩ := Walk.mem_support_iff_exists_getVert.mp hmem'
      have ha : G.Adj (p.getVert p.length) (p.getVert i) := by simpa [hi] using hx
      have hc := (index_adj hT.isConnected p hlen (by omega : p.length ≤ p.length) hiL).mp ha
      have h1 : i=p.length-1 := by omega
      simpa [h1] using hi.symm
    · rintro rfl
      have hh := p.adj_getVert_succ (i:=p.length-1) (by omega)
      have he : p.length-1+1=p.length := by omega
      rw [he,Walk.getVert_length] at hh
      exact hh.symm

theorem loss_gap {y j : ℕ} (hp : y=j ∨ y+1=j ∨ y+2=j) :
    j-2 ≤ y ∧ y ≤ j := by omega

noncomputable def pathSet {a b : V} (p : G.Walk a b) : Finset V := by
  classical
  exact p.support.toFinset

@[simp] theorem mem_pathSet {a b : V} (p : G.Walk a b) (v : V) :
    v ∈ pathSet p ↔ v ∈ p.support := by
  classical
  simp [pathSet]

noncomputable def overlap (D P : Finset V) : Finset V := by
  classical
  exact P.filter (fun v => 2 ≤ (D.filter (G.Adj v)).card)

noncomputable def offD (D P : Finset V) : Finset V := by
  classical
  exact D \ P

noncomputable def farD (D P : Finset V) : Finset V := by
  classical
  exact (offD D P).filter (fun v => ∀ w ∈ P, ¬ G.Adj v w)

theorem path_adjacency_cap (hT : G.IsTree) {a b : V}
    (p : G.Walk a b) (hp : p.length = G.dist a b) (v : V) :
    (by classical exact ((pathSet p).filter (G.Adj v)).card ≤ 2) := by
  classical
  let P := pathSet p
  have hh (x : V) : x ∈ P → ∃ i, p.getVert i=x ∧ i≤p.length :=
    fun h => Walk.mem_support_iff_exists_getVert.mp ((mem_pathSet p x).mp h)
  let f := fun x => if h : x ∈ P then Classical.choose (hh x h) else 0
  have hf (x : V) (hx : x ∈ P) : p.getVert (f x)=x ∧ f x≤p.length := by
    simp only [f,dif_pos hx]
    exact Classical.choose_spec (hh x hx)
  by_cases hv : v ∈ P
  · have hCard : (P.filter (G.Adj v)).card ≤ ({f v-1,f v+1} : Finset ℕ).card := by
      apply Finset.card_le_card_of_injOn f
      · intro x hx
        obtain ⟨hxp,hvx⟩ := Finset.mem_filter.mp hx
        have had : G.Adj (p.getVert (f v)) (p.getVert (f x)) := by
          rwa [(hf v hv).1,(hf x hxp).1]
        have he := (index_adj hT.isConnected p hp (hf v hv).2 (hf x hxp).2).mp had
        have hx' : f x=f v-1 ∨ f x=f v+1 := by omega
        simpa using hx'
      · intro x hx y hy he
        have h1 := (hf x (Finset.mem_filter.mp hx).1).1
        have h2 := (hf y (Finset.mem_filter.mp hy).1).1
        exact h1.symm.trans ((congrArg p.getVert he).trans h2)
    exact hCard.trans Finset.card_le_two
  · have hsmall : (P.filter (G.Adj v)).card ≤ 1 := by
      apply Nat.le_of_not_gt
      intro h2
      obtain ⟨x,hx,y,hy,hne⟩ := Finset.one_lt_card.mp h2
      obtain ⟨hxP,hvx⟩ := Finset.mem_filter.mp hx
      obtain ⟨hyP,hvy⟩ := Finset.mem_filter.mp hy
      exact hne (outside_one hT (support_connected p)
        ((mem_pathSet p x).mp hxP) ((mem_pathSet p y).mp hyP)
        (fun h => hv ((mem_pathSet p v).mpr h)) hvx.symm hvy.symm)
    exact hsmall.trans (by decide : 1 ≤ 2)

theorem slack (hT : G.IsTree) {a b : V} (p : G.Walk a b) (hpath : p.IsPath)
    (hp : p.length = G.dist a b) (D : Finset V) (hD : TotalDominates G D) :
    p.length + 1 + (overlap (G:=G) D (pathSet p)).card + (offD D (pathSet p)).card +
        (farD (G:=G) D (pathSet p)).card ≤ 2 * D.card := by
  classical
  let P := pathSet p
  let O := overlap (G:=G) D P
  let B := offD D P
  let F := farD (G:=G) D P
  let x (v : V) := (D.filter (G.Adj v)).card
  let y (v : V) := (P.filter (G.Adj v)).card
  have hflip : (∑ v ∈ P, x v) = ∑ v ∈ D, y v := by
    simp only [x,y,Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases hh : G.Adj v u
    · simp [hh,hh.symm]
    · have hn : ¬ G.Adj u v := fun h => hh h.symm
      simp [hh,hn]
  have hleft : P.card + O.card ≤ ∑ v ∈ P, x v := by
    have h₁ : ∀ v ∈ P, 1 + (if 2 ≤ x v then 1 else 0) ≤ x v := by
      intro v _
      obtain ⟨w,hw,ha⟩ := hD v
      have hh : 0 < x v := Finset.card_pos.mpr ⟨w,Finset.mem_filter.mpr ⟨hw,ha⟩⟩
      by_cases h2 : 2 ≤ x v <;> simp [h2] <;> omega
    have h₂ := Finset.sum_le_sum h₁
    simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_one,
      ← Finset.card_filter] at h₂
    exact h₂
  have hright : (∑ v ∈ D, y v) + B.card + F.card ≤ 2*D.card := by
    have h₁ : ∀ v ∈ D, y v + (if v ∉ P then 1 else 0) +
        (if v ∉ P ∧ (∀ w ∈ P, ¬ G.Adj v w) then 1 else 0) ≤ 2 := by
      intro v _
      by_cases hP : v ∈ P
      · simpa [hP,y,P] using path_adjacency_cap hT p hp v
      · have hY : y v ≤ 1 := by
          apply Nat.le_of_not_gt
          intro h2
          obtain ⟨u,hu,w,hw,hne⟩ := Finset.one_lt_card.mp h2
          obtain ⟨huP,hvu⟩ := Finset.mem_filter.mp hu
          obtain ⟨hwP,hvw⟩ := Finset.mem_filter.mp hw
          have he := outside_one hT (support_connected p)
            ((mem_pathSet p u).mp huP) ((mem_pathSet p w).mp hwP)
            (fun h => hP ((mem_pathSet p v).mpr h)) hvu.symm hvw.symm
          exact hne he
        by_cases hF : ∀ w ∈ P, ¬ G.Adj v w
        · have hy0 : y v = 0 := by
            apply Finset.card_eq_zero.mpr
            ext w
            constructor
            · intro hw
              have hh := Finset.mem_filter.mp hw
              exact False.elim (hF w hh.1 hh.2)
            · simp
          rw [if_pos hP, if_pos ⟨hP,hF⟩, hy0]
        · rw [if_pos hP, if_neg (fun h => hF h.2)]
          omega
    have h₂ := Finset.sum_le_sum h₁
    simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul, ← Finset.card_filter] at h₂
    have hB : B = D.filter (fun v => v ∉ P) := by ext v; simp [B,offD]
    have hF : F = D.filter (fun v => v ∉ P ∧ ∀ w ∈ P, ¬G.Adj v w) := by
      ext v
      simp [F,farD,offD,and_assoc]
    rw [hB,hF,Nat.mul_comm]
    exact h₂
  have hlen : P.card = p.length+1 := by
    simp [P,pathSet,List.toFinset_card_of_nodup hpath.support_nodup]
  rw [hlen,hflip] at hleft
  change p.length + 1 + O.card + B.card + F.card ≤ 2*D.card
  omega

theorem path_vertex_out_neighbor (hT : G.IsTree) {a b : V} (p : G.Walk a b)
    (hp : p.length = G.dist a b) {i : ℕ} (hi : 0 < i) (hi' : i < p.length)
    (hdeg : ¬ S G (p.getVert i)) :
    ∃ x, x ∉ p.support ∧ G.Adj (p.getVert i) x := by
  classical
  by_contra hall
  push_neg at hall
  let u := p.getVert i
  have hc₁ : (nbr G u).card ≤ 2 := by
    have hsub : nbr G u ⊆ (pathSet p).filter (G.Adj u) := by
      intro x hx
      have had := (mem_nbr G).mp hx
      exact Finset.mem_filter.mpr ⟨(mem_pathSet p x).mpr (by by_contra hn; exact hall x hn had), had⟩
    exact (Finset.card_le_card hsub).trans (path_adjacency_cap hT p hp u)
  have hc₂ : 2 ≤ (nbr G u).card := by
    have hbefore := p.adj_getVert_succ (i:=i-1) (by omega)
    have hidx : i-1+1=i := by omega
    rw [hidx] at hbefore
    have hafter := p.adj_getVert_succ hi'
    have he : p.getVert (i-1) ≠ p.getVert (i+1) := by
      intro hh
      have h₁ := dist_index hT.isConnected p hp (by omega : i-1≤p.length)
      have h₂ := dist_index hT.isConnected p hp (by omega : i+1≤p.length)
      rw [hh] at h₁
      omega
    exact Finset.one_lt_card.mpr ⟨_, (mem_nbr G).mpr hbefore.symm,
      _,(mem_nbr G).mpr hafter,he⟩
  exact hdeg (Nat.le_antisymm hc₁ hc₂)

theorem only_neighbour_not_closed {a x : V} (h : ∀ w, G.Adj a w ↔ w=x)
    (hx : x ∉ closedDegreeTwo G) :
    a ∉ closedDegreeTwo G := by
  classical
  have hnbr : nbr G a = {x} := by
    ext w
    simp [h]
  intro hc
  rcases (mem_closed G a).mp hc with hs | ⟨s,hs,had⟩
  · unfold S at hs
    rw [hnbr,Finset.card_singleton] at hs
    omega
  · have he := (h s).mp had
    rw [he] at hs
    exact hx ((mem_closed G x).mpr (Or.inl hs))

theorem charge_components (hT : G.IsTree) {a b : V}
    (p : G.Walk a b) (hpath : p.IsPath) (hp : p.length = G.dist a b)
    (hpos : 0 < p.length) (hdiam : ∀ u v, G.dist u v ≤ p.length)
    (D : Finset V) (hD : TotalDominates G D) :
    countComponents G ≤
      (overlap (G:=G) D (pathSet p)).card + (offD D (pathSet p)).card +
        (farD (G:=G) D (pathSet p)).card + 1 := by
  classical
  let C := closedDegreeTwo G
  let H := G.induce (C : Set V)
  let P := pathSet p
  let O := overlap (G:=G) D P
  let B := offD D P
  let F := farD (G:=G) D P
  let I (i : ℕ) := p.getVert i
  haveI : Finite H.ConnectedComponent :=
    Finite.of_surjective H.connectedComponentMk (fun c => c.exists_rep)
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  change Fintype.card H.ConnectedComponent ≤ O.card+B.card+F.card+1
  let Mark (c : H.ConnectedComponent) (i : ℕ) : Prop :=
    i ≤ p.length ∧ ∃ h : I i ∈ C, H.connectedComponentMk ⟨I i,h⟩=c
  let On (c : H.ConnectedComponent) := ∃ i, Mark c i
  let start (c : H.ConnectedComponent) : ℕ := sInf {i | Mark c i}
  let Later (c : H.ConnectedComponent) := On c ∧ ∃ b, On b ∧ start b < start c
  let src : Finset H.ConnectedComponent := univ.filter (fun c => ¬ On c ∨ Later c)
  have hsrc (c : H.ConnectedComponent) : c∈src ↔ ¬ On c ∨ Later c := by simp [src]
  have first_mark {c : H.ConnectedComponent} (hc : On c) : Mark c (start c) :=
    Nat.sInf_mem hc
  have unique_mark {c d : H.ConnectedComponent} {i : ℕ} (hc : Mark c i) (hd : Mark d i) : c=d := by
    obtain ⟨_,⟨h₁,h₁c⟩⟩ := hc
    obtain ⟨_,⟨h₂,h₂c⟩⟩ := hd
    have he : (⟨I i,h₁⟩ : ↑(C : Set V)) = ⟨I i,h₂⟩ := rfl
    exact h₁c.symm.trans ((congrArg H.connectedComponentMk he).trans h₂c)
  have start_inj {c d : H.ConnectedComponent} (hc : On c) (hd : On d)
      (he : start c = start d) : c=d :=
    unique_mark (first_mark hc) (he.symm ▸ first_mark hd)
  have removed_le_one : ((univ : Finset H.ConnectedComponent) \ src).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro c hc d hd
    have hnc := (Finset.mem_sdiff.mp hc).2
    have hnd := (Finset.mem_sdiff.mp hd).2
    have hOnc : On c := by by_contra h; exact hnc ((hsrc c).mpr (Or.inl h))
    have hOnd : On d := by by_contra h; exact hnd ((hsrc d).mpr (Or.inl h))
    apply start_inj hOnc hOnd
    rcases lt_trichotomy (start c) (start d) with h | h | h
    · exact False.elim (hnd ((hsrc d).mpr (Or.inr ⟨hOnd,c,hOnc,h⟩)))
    · exact h
    · exact False.elim (hnc ((hsrc c).mpr (Or.inr ⟨hOnc,d,hOnd,h⟩)))
  have total_src : Fintype.card H.ConnectedComponent ≤ src.card + 1 := by
    rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ] at removed_le_one
    omega
  have pred_not_closed {c : H.ConnectedComponent} (hc : On c) (hj : 0 < start c) :
      I (start c-1) ∉ C := by
    intro hpred
    obtain ⟨hle,hC,hc'⟩ := first_mark hc
    have ha := p.adj_getVert_succ (i:=start c-1) (by omega)
    have hi : start c - 1 + 1 = start c := by omega
    rw [hi] at ha
    have ha' : H.Adj ⟨I (start c-1),hpred⟩ ⟨I (start c),hC⟩ := ha
    have hMk := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ha'
    have hm : Mark c (start c-1) := ⟨by omega,hpred,hMk.trans hc'⟩
    have hl : start c ≤ start c-1 := Nat.sInf_le hm
    omega
  have gap_setup {c : H.ConnectedComponent} (hc : Later c) :
      3 ≤ start c ∧ start c < p.length ∧ I (start c-1) ∉ C := by
    obtain ⟨hOn,d,hd,hpos'⟩ := hc
    obtain ⟨hjl,hjC,_⟩ := first_mark hOn
    obtain ⟨_,hiC,_⟩ := first_mark hd
    have hpos₁ : 0 < start c := by omega
    have hpred := pred_not_closed hOn hpos₁
    have hdiff : start d ≠ start c-1 := fun h => hpred (h ▸ hiC)
    have hj₂ : 2 ≤ start c := by omega
    have hends := endpoint_neighbors hT p hpath hp hpos hdiam
    have hj₃ : 3 ≤ start c := by
      by_contra h
      have he : start c=2 := by omega
      have hd0 : start d=0 := by omega
      have hA : a ∈ C := by simpa [I,hd0] using hiC
      have hpred₁ : p.getVert 1 ∉ C := by simpa [I,he] using hpred
      exact only_neighbour_not_closed hends.1 hpred₁ hA
    have hjlt : start c < p.length := by
      by_contra h
      have he : start c=p.length := by omega
      have hB : b ∈ C := by simpa [I,he] using hjC
      have hpred₂ : p.getVert (p.length-1) ∉ C := by simpa [I,he] using hpred
      exact only_neighbour_not_closed hends.2 hpred₂ hB
    exact ⟨hj₃,hjlt,hpred⟩
  have gap_endpoint_degree {c : H.ConnectedComponent} (hc : Later c)
      {i : ℕ} (hi : i=start c ∨ i+2=start c) :
      ¬ S G (I i) := by
    obtain ⟨hj₃,hjl,hpred⟩ := gap_setup hc
    intro hS
    have hAd : G.Adj (I (start c-1)) (I i) := by
      apply (index_adj hT.isConnected p hp (by omega : start c-1≤p.length)
        (by omega : i≤p.length)).mpr
      omega
    exact hpred ((mem_closed G _).mpr (Or.inr ⟨I i,hS,hAd⟩))
  have in_path (i : ℕ) : I i ∈ P := (mem_pathSet p _).mpr (p.getVert_mem_support i)
  have idx_distinct {i j : ℕ} (hi : i≤p.length) (hj : j≤p.length) (he : I i=I j) :
      i=j := by
    have h₁ := dist_index hT.isConnected p hp hi
    have h₂ := dist_index hT.isConnected p hp hj
    change p.getVert i=p.getVert j at he
    rw [he] at h₁
    omega
  let firstSlot (c : H.ConnectedComponent) (i : ℕ) : Prop :=
    i+2=start c ∧ I i∈C ∧ I (i-1)∉C
  let livesOn (y : V) : Prop :=
    ∃ c, On c ∧ ∃ h : y ∈ C, H.connectedComponentMk ⟨y,h⟩=c
  let offCase (c : H.ConnectedComponent) (s : V × Fin 3) : Prop :=
    ¬On c ∧ s.2=0 ∧ s.1∈B ∧ ∃ h : s.1∈C, H.connectedComponentMk ⟨s.1,h⟩=c
  let overlapCase (c : H.ConnectedComponent) (s : V × Fin 3) : Prop :=
    Later c ∧ s.2=2 ∧ s.1=I (start c-1) ∧ s.1∈O
  let depthCase (c : H.ConnectedComponent) (s : V × Fin 3) : Prop :=
    Later c ∧ s.1∈F ∧ ∃ i x, (i=start c ∨ i+2=start c) ∧ x∉p.support ∧
      G.Adj (I i) x ∧ G.Adj x s.1 ∧
      ((firstSlot c i ∧ s.2=0 ∧ livesOn s.1) ∨ (¬ firstSlot c i ∧ s.2=1))
  let Good (c : H.ConnectedComponent) (s : V × Fin 3) : Prop :=
    offCase c s ∨ overlapCase c s ∨ depthCase c s
  have book (c : H.ConnectedComponent) (hc : c∈src) : ∃ s, Good c s := by
    rcases (hsrc c).mp hc with hOff | hLate
    · obtain ⟨u,hu⟩ := c.exists_rep
      have hS : ∃ v : ↑(C : Set V), S G v.1 ∧ H.connectedComponentMk v=c := by
        rcases (mem_closed G u.1).mp u.2 with hs | ⟨v,hv,had⟩
        · exact ⟨u,hs,hu⟩
        · let v' : ↑(C : Set V) := ⟨v,(mem_closed G _).mpr (Or.inl hv)⟩
          have had' : H.Adj u v' := had
          exact ⟨v',hv,(SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj had').symm.trans hu⟩
      obtain ⟨v,hv,hvc⟩ := hS
      obtain ⟨y,hy,had⟩ := hD v.1
      have hyC : y ∈ C := (mem_closed G _).mpr (Or.inr ⟨v.1,hv,had.symm⟩)
      have had' : H.Adj v ⟨y,hyC⟩ := had
      have hcomp := (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj had').symm.trans hvc
      have hyP : y∉P := by
        intro hyp
        obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.mp ((mem_pathSet p y).mp hyp)
        have hm : Mark c i := by
          change I i=y at hi
          refine ⟨hil,?_,?_⟩
          · rwa [hi]
          · simpa only [hi] using hcomp
        exact hOff ⟨i,hm⟩
      exact ⟨(y,0),Or.inl ⟨hOff,rfl,Finset.mem_sdiff.mpr ⟨hy,hyP⟩,hyC,hcomp⟩⟩
    · obtain ⟨hj₃,hjl,hgap⟩ := gap_setup hLate
      let j := start c
      have hj₃' : 3 ≤ j := hj₃
      have hjl' : j < p.length := hjl
      by_cases hover : I (j-2) ∈ D ∧ I j ∈ D
      · have hda : G.Adj (I (j-1)) (I (j-2)) := by
          apply (index_adj hT.isConnected p hp (by omega : j-1≤p.length)
            (by omega : j-2≤p.length)).mpr
          omega
        have hdb : G.Adj (I (j-1)) (I j) := by
          apply (index_adj hT.isConnected p hp (by omega : j-1≤p.length)
            (by omega : j≤p.length)).mpr
          omega
        have hne : I (j-2) ≠ I j := by
          intro he
          have hh := idx_distinct (by omega : j-2≤p.length) (by omega : j≤p.length) he
          omega
        have hO : I (j-1) ∈ O := Finset.mem_filter.mpr ⟨in_path _,Finset.one_lt_card.mpr
          ⟨_,Finset.mem_filter.mpr ⟨hover.1,hda⟩,_,Finset.mem_filter.mpr ⟨hover.2,hdb⟩,hne⟩⟩
        exact ⟨(I (j-1),2),Or.inr (Or.inl ⟨hLate,rfl,rfl,hO⟩)⟩
      · have hEndpoint : ∃ i, (i=j ∨ i+2=j) ∧ I i∉D := by
          by_cases hLeft : I (j-2)∈D
          · exact ⟨j,Or.inl rfl,fun h => hover ⟨hLeft,h⟩⟩
          · exact ⟨j-2,Or.inr (by omega),hLeft⟩
        obtain ⟨i,hi,hiD⟩ := hEndpoint
        have hdeg := gap_endpoint_degree hLate hi
        have hix : 0 < i := by omega
        have hiL : i < p.length := by omega
        have get_far {x : V} (hx : x∉p.support) (had : G.Adj (I i) x) :
            ∃ y, y∈F ∧ G.Adj x y := by
          obtain ⟨y,hy,hyx⟩ := hD x
          have hyne : y ≠ I i := fun e => hiD (e ▸ hy)
          have hfar := depth_two_far hT (support_connected p)
            (p.getVert_mem_support i) hx had hyx hyne
          have hyB : y∈B := Finset.mem_sdiff.mpr ⟨hy, fun h => hfar.1 ((mem_pathSet p y).mp h)⟩
          have hyF : y∈F := Finset.mem_filter.mpr ⟨hyB,
            fun w hw => hfar.2 w ((mem_pathSet p w).mp hw)⟩
          exact ⟨y,hyF,hyx⟩
        by_cases hFirst : firstSlot c i
        · have hxS := hFirst.2
          rcases (mem_closed G (I i)).mp hxS.1 with hS | ⟨x,hx,had⟩
          · exact False.elim (hdeg hS)
          · have hxC := (mem_closed G x).mpr (Or.inl hx)
            have hxoff : x∉p.support := by
              intro h
              obtain ⟨k,hk,hkL⟩ := Walk.mem_support_iff_exists_getVert.mp h
              have hh : G.Adj (I i) (I k) := by
                change p.getVert k=x at hk
                rw [show I k=x from hk]
                exact had
              have he := (index_adj hT.isConnected p hp (by omega : i≤p.length) hkL).mp hh
              rcases he with he | he
              · have hf : k=j-1 := by unfold firstSlot at hFirst; omega
                have hg : I (start c-1)=x := by change p.getVert (j-1)=x; simpa [hf] using hk
                exact hgap (hg.symm ▸ hxC)
              · have hf : k=i-1 := by omega
                have hg : I (i-1)=x := by change p.getVert (i-1)=x; simpa [hf] using hk
                exact hxS.2 (hg.symm ▸ hxC)
            obtain ⟨y,hy,hyx⟩ := get_far hxoff had
            have hcomp : livesOn y := by
              have hyC := (mem_closed G y).mpr (Or.inr ⟨x,hx,hyx.symm⟩)
              let c' := H.connectedComponentMk (⟨I i,hxS.1⟩ : ↑(C : Set V))
              have had' : H.Adj ⟨I i,hxS.1⟩ ⟨x,hxC⟩ := had
              have hyx' : H.Adj ⟨x,hxC⟩ ⟨y,hyC⟩ := hyx
              have hc₁ := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj had'
              have hc₂ := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hyx'
              exact ⟨c',⟨i,by omega,hxS.1,rfl⟩,hyC,(hc₁.trans hc₂).symm⟩
            exact ⟨(y,0),Or.inr (Or.inr ⟨hLate,hy,i,x,hi,hxoff,had,hyx,Or.inl ⟨hFirst,rfl,hcomp⟩⟩)⟩
        · obtain ⟨x,hx,had⟩ := path_vertex_out_neighbor hT p hp hix hiL hdeg
          obtain ⟨y,hy,hyx⟩ := get_far hx had
          exact ⟨(y,1),Or.inr (Or.inr ⟨hLate,hy,i,x,hi,hx,had,hyx,Or.inr ⟨hFirst,rfl⟩⟩)⟩
  have mem_comp_unique {c d : H.ConnectedComponent} {v : V}
      (hc : ∃ h : v ∈ C, H.connectedComponentMk ⟨v,h⟩=c)
      (hd : ∃ h : v ∈ C, H.connectedComponentMk ⟨v,h⟩=d) : c=d := by
    obtain ⟨hc,hc'⟩ := hc
    obtain ⟨hd,hd'⟩ := hd
    exact hc'.symm.trans hd'
  have no_off_live {c : H.ConnectedComponent} {v : V} (hc : ¬On c)
      (hv : ∃ h : v ∈ C, H.connectedComponentMk ⟨v,h⟩=c) :
      ¬ livesOn v := by
    rintro ⟨d,hd,hw⟩
    exact hc ((mem_comp_unique hv hw).symm ▸ hd)
  have equal_slot {c d : H.ConnectedComponent} {i : ℕ}
      (hc : Later c) (hd : Later d)
      (hi : i = start c ∨ i+2=start c)
      (hj : i = start d ∨ i+2=start d)
      (same : firstSlot c i ↔ firstSlot d i) : c=d := by
    apply start_inj hc.1 hd.1
    rcases hi with h₁ | h₁ <;> rcases hj with h₂ | h₂
    · omega
    · have hNe : ¬firstSlot c i := by
        intro hh
        have := hh.1
        omega
      have hh : firstSlot d i := by
        refine ⟨h₂, ?_, ?_⟩
        · rw [h₁]
          exact (first_mark hc.1).2.choose
        · rw [h₁]
          exact (gap_setup hc).2.2
      exact (hNe (same.mpr hh)).elim
    · have hNe : ¬firstSlot d i := by
        intro hh
        have := hh.1
        omega
      have hh : firstSlot c i := by
        refine ⟨h₁, ?_, ?_⟩
        · rw [h₂]
          exact (first_mark hd.1).2.choose
        · rw [h₂]
          exact (gap_setup hd).2.2
      exact (hNe (same.mp hh)).elim
    · omega
  have depth_unique {c d : H.ConnectedComponent} {s : V × Fin 3}
      (hc : depthCase c s) (hd : depthCase d s) : c=d := by
    obtain ⟨hc,hs,i,x,hi,hx,hix,hxs,hci⟩ := hc
    obtain ⟨hd,_,j,y,hj,hy,hjy,hys,hdj⟩ := hd
    have hiL : i ≤ p.length := by have h := (gap_setup hc).2.1; omega
    have hjL : j ≤ p.length := by have h := (gap_setup hd).2.1; omega
    have hsP : s.1 ∉ p.support := by
      rw [← mem_pathSet p]
      exact (Finset.mem_sdiff.mp (mem_filter.mp hs).1).2
    have hEq : I i = I j := depth_two_owner hT (support_connected p)
      (p.getVert_mem_support i) (p.getVert_mem_support j) hx hy hsP hix hxs hjy hys
    have hij := idx_distinct hiL hjL hEq
    subst j
    apply equal_slot hc hd hi hj
    rcases hci with ⟨hci,h₀,_⟩ | ⟨hci,h₁⟩ <;>
      rcases hdj with ⟨hdj,h₀',_⟩ | ⟨hdj,h₁'⟩
    · exact iff_of_true hci hdj
    · exact (by omega : False).elim
    · exact (by omega : False).elim
    · exact iff_of_false hci hdj
  have two_not_depth {c : H.ConnectedComponent} {s : V × Fin 3}
      (h : depthCase c s) (e : s.2=2) : False := by
    obtain ⟨_,_,_,_,_,_,_,_,h⟩ := h
    rcases h with ⟨_,h,_⟩ | ⟨_,h⟩ <;> omega
  have zero_depth_live {c : H.ConnectedComponent} {s : V × Fin 3}
      (h : depthCase c s) (e : s.2=0) : livesOn s.1 := by
    obtain ⟨_,_,_,_,_,_,_,_,h⟩ := h
    rcases h with ⟨_,_,h⟩ | ⟨_,h⟩
    · exact h
    · omega
  have good_unique {c d : H.ConnectedComponent} {s : V × Fin 3}
      (hc : Good c s) (hd : Good d s) : c=d := by
    rcases hc with hc | hc | hc <;> rcases hd with hd | hd | hd
    · exact mem_comp_unique hc.2.2.2 hd.2.2.2
    · have h₁ := hc.2.1
      have h₂ := hd.2.1
      omega
    · exact (no_off_live hc.1 hc.2.2.2 (zero_depth_live hd hc.2.1)).elim
    · have h₁ := hc.2.1
      have h₂ := hd.2.1
      omega
    · have hcl := (gap_setup hc.1).2.1
      have hdl := (gap_setup hd.1).2.1
      have hce := (gap_setup hc.1).1
      have hde := (gap_setup hd.1).1
      have he := idx_distinct (i := start c-1) (j := start d-1)
        (by omega) (by omega) (hc.2.2.1.symm.trans hd.2.2.1)
      exact start_inj hc.1.1 hd.1.1 (by omega)
    · exact (two_not_depth hd hc.2.1).elim
    · exact (no_off_live hd.1 hd.2.2.2 (zero_depth_live hc hd.2.1)).elim
    · exact (two_not_depth hc hd.2.1).elim
    · exact depth_unique hc hd
  let dst : Finset (V × Fin 3) := (B.product {0} ∪ F.product {1}) ∪ O.product {2}
  have mem_dst {c : H.ConnectedComponent} {s : V × Fin 3} (hs : Good c s) :
      s ∈ dst := by
    change s ∈ ((B.product {0} ∪ F.product {1}) ∪ O.product {2})
    simp only [mem_union, mem_product, mem_singleton]
    rcases hs with hs | hs | hs
    · exact Or.inl (Or.inl (Finset.mem_product.mpr ⟨hs.2.2.1,mem_singleton.mpr hs.2.1⟩))
    · exact Or.inr (Finset.mem_product.mpr ⟨hs.2.2.2,mem_singleton.mpr hs.2.1⟩)
    · obtain ⟨_,hf,_,_,_,_,_,_,h⟩ := hs
      rcases h with ⟨_,h,_⟩ | ⟨_,h⟩
      · exact Or.inl (Or.inl (Finset.mem_product.mpr ⟨(mem_filter.mp hf).1,mem_singleton.mpr h⟩))
      · exact Or.inl (Or.inr (Finset.mem_product.mpr ⟨hf,mem_singleton.mpr h⟩))
  have cap : src.card ≤ dst.card := by
    apply Finset.card_le_card_of_injOn
      (fun c => if h : c ∈ src then Classical.choose (book c h) else (a,0))
    · intro c hc
      rw [dif_pos hc]
      exact mem_dst (Classical.choose_spec (book c hc))
    · intro c hc d hd h
      have hc' : c ∈ src := hc
      have hd' : d ∈ src := hd
      simp only [dif_pos hc',dif_pos hd'] at h
      exact good_unique (Classical.choose_spec (book c hc))
        (h ▸ Classical.choose_spec (book d hd))
  have cap' := card_union_le (B.product {0} ∪ F.product {1}) (O.product {2} : Finset (V × Fin 3))
  have cap'' := card_union_le (B.product {0} : Finset (V × Fin 3)) (F.product {1})
  have eqB : (B.product ({0} : Finset (Fin 3))).card = B.card := by
    have h := Finset.card_product B ({0} : Finset (Fin 3))
    rw [card_singleton, Nat.mul_one] at h
    exact h
  have eqF : (F.product ({1} : Finset (Fin 3))).card = F.card := by
    have h := Finset.card_product F ({1} : Finset (Fin 3))
    rw [card_singleton, Nat.mul_one] at h
    exact h
  have eqO : (O.product ({2} : Finset (Fin 3))).card = O.card := by
    have h := Finset.card_product O ({2} : Finset (Fin 3))
    rw [card_singleton, Nat.mul_one] at h
    exact h
  rw [eqO] at cap'
  rw [eqB,eqF] at cap'' 
  change src.card ≤ ((B.product {0} ∪ F.product {1}) ∪ O.product {2}).card at cap
  omega


noncomputable def ecc (H : SimpleGraph V) (v : V) : ℕ := univ.sup (H.dist v)
noncomputable def diam (H : SimpleGraph V) : ℕ := univ.sup (ecc H)

/-- Exact arithmetic mean of the eccentricities of all vertices. -/
noncomputable def avgEcc (H : SimpleGraph V) : ℚ :=
  (∑ v : V, (ecc H v : ℚ)) / (Fintype.card V : ℚ)

theorem diameter_strengthening (hT : G.IsTree) (hn : 2 ≤ Fintype.card V) :
    countComponents G + diam G ≤ 2 * totalDominationNumber G := by
  classical
  haveI : Nonempty V := hT.isConnected.nonempty
  obtain ⟨a, _, ha⟩ := exists_mem_eq_sup (univ : Finset V) univ_nonempty (ecc G)
  obtain ⟨b, _, hb⟩ := exists_mem_eq_sup (univ : Finset V) univ_nonempty (G.dist a)
  have hd : diam G = G.dist a b := ha.trans hb
  have hmax (u v : V) : G.dist u v ≤ G.dist a b := by
    rw [← hd]
    exact (le_sup (f := G.dist u) (mem_univ v)).trans (le_sup (f := ecc G) (mem_univ u))
  obtain ⟨x⟩ := ‹Nonempty V›
  obtain ⟨y,hy⟩ := Fintype.exists_ne_of_one_lt_card (by omega) x
  have hpos : 0 < G.dist a b := by
    have hxy := hT.isConnected.pos_dist_of_ne hy.symm
    exact hxy.trans_le (hmax x y)
  obtain ⟨p,hp,hplen⟩ := hT.isConnected.exists_path_of_dist a b
  obtain ⟨D,hD,hN⟩ := exists_min_td G hT.isConnected hn
  have h₁ := slack hT p hp hplen D hD
  have h₂ := charge_components hT p hp hplen (by omega) (fun u v => hplen.symm ▸ hmax u v) D hD
  omega

theorem conjecture242 (hT : G.IsTree) (hn : 2 ≤ Fintype.card V) :
    ((countComponents G : ℚ) + avgEcc G) / 2 ≤ (totalDominationNumber G : ℚ) := by
  classical
  have hc : 0 < (Fintype.card V : ℚ) := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hmean : avgEcc G ≤ (diam G : ℚ) := by
    unfold avgEcc
    apply (div_le_iff₀ hc).mpr
    have h := Finset.sum_le_sum (s := (univ : Finset V)) (fun v _ =>
      show (ecc G v : ℚ) ≤ (diam G : ℚ) by exact_mod_cast
        (le_sup (f := ecc G) (mem_univ v)))
    simpa [mul_comm] using h
  have hN := diameter_strengthening hT hn
  have hR : (countComponents G : ℚ) + (diam G : ℚ) ≤
      2 * (totalDominationNumber G : ℚ) := by exact_mod_cast hN
  linarith

#print axioms conjecture242
end Graffiti242
