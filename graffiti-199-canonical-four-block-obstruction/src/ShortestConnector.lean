import TreeBudget
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

private def chainAdj (i j : Fin 6) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

private lemma chain_rows : ∀ i j : Fin 6, i ≠ j →
    ∃ k : Fin 6, ¬ (chainAdj i k ↔ chainAdj j k) := by
  unfold chainAdj
  decide

private lemma chain_parent : ∀ i : Fin 6, i ≠ 0 →
    ∃ j : Fin 6, chainAdj i j ∧ j < i ∧
      ∀ k : Fin 6, chainAdj i k → k < i → k = j := by
  unfold chainAdj
  decide

def InducedSixPath (G : SimpleGraph V) : Prop :=
  ∃ f : Fin 6 → V, ∀ i j, G.Adj (f i) (f j) ↔ chainAdj i j

theorem InducedSixPath.le_treeNumber [Fintype V] (path : InducedSixPath G) :
    6 ≤ treeNumber G := by
  obtain ⟨f,chart⟩ := path
  have inj : Function.Injective f := by
    intro i j h
    by_contra ne
    obtain ⟨k, hk⟩ := chain_rows i j ne
    exact hk ((chart i k).symm.trans (h ▸ chart j k))
  apply six_le_treeNumber_of_ordering ⟨f, inj⟩
  intro i hi
  obtain ⟨j, ij, lt, unique⟩ := chain_parent i hi
  exact ⟨j, (chart i j).mpr ij, lt, fun k e lk => unique k ((chart i k).mp e) lk⟩

theorem inducedSixPath_of_edges {a b c d e f : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (de : G.Adj d e) (ef : G.Adj e f)
    (ac : ¬ G.Adj a c) (ad : ¬ G.Adj a d) (ae : ¬ G.Adj a e) (af : ¬ G.Adj a f)
    (bd : ¬ G.Adj b d) (be : ¬ G.Adj b e) (bf : ¬ G.Adj b f)
    (ce : ¬ G.Adj c e) (cf : ¬ G.Adj c f) (df : ¬ G.Adj d f) :
    InducedSixPath G := by
  have ca : ¬ G.Adj c a := fun h => ac h.symm
  have da : ¬ G.Adj d a := fun h => ad h.symm
  have ea : ¬ G.Adj e a := fun h => ae h.symm
  have fa : ¬ G.Adj f a := fun h => af h.symm
  have db : ¬ G.Adj d b := fun h => bd h.symm
  have eb : ¬ G.Adj e b := fun h => be h.symm
  have fb : ¬ G.Adj f b := fun h => bf h.symm
  have ec : ¬ G.Adj e c := fun h => ce h.symm
  have fc : ¬ G.Adj f c := fun h => cf h.symm
  have fd : ¬ G.Adj f d := fun h => df h.symm
  let vs : Fin 6 → V := ![a,b,c,d,e,f]
  have v0 : vs ⟨0, by decide⟩ = a := rfl
  have v1 : vs ⟨1, by decide⟩ = b := rfl
  have v2 : vs ⟨2, by decide⟩ = c := rfl
  have v3 : vs ⟨3, by decide⟩ = d := rfl
  have v4 : vs ⟨4, by decide⟩ = e := rfl
  have v5 : vs ⟨5, by decide⟩ = f := rfl
  refine ⟨vs, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) only [v0,v1,v2,v3,v4,v5,chainAdj,iff_true,iff_false] <;>
    first | exact G.loopless _ | assumption | (apply SimpleGraph.Adj.symm; assumption)

private theorem walk_take_length {a b : V} (p : G.Walk a b) (n : ℕ) :
    (p.take n).length ≤ n := by
  induction p generalizing n with
  | nil => simp [Walk.take]
  | cons h p ih =>
    cases n with
    | zero => simp [Walk.take]
    | succ n => exact Nat.succ_le_succ (ih n)

private theorem walk_drop_length {a b : V} (p : G.Walk a b) (n : ℕ) :
    (p.drop n).length ≤ p.length - n := by
  induction p generalizing n with
  | nil => simp [Walk.drop]
  | cons h p ih =>
    cases n with
    | zero => simp [Walk.drop]
    | succ n => simpa [Walk.drop, Walk.length_cons, Nat.succ_sub_succ_eq_sub] using ih n

private theorem geodesic_gap (conn : G.Connected) {a b : V}
    (p : G.Walk a b) (hp : p.length = G.dist a b) {i j : ℕ}
    (h : i+1 < j) (hj : j ≤ p.length) :
    ¬ G.Adj (p.getVert i) (p.getVert j) := by
  intro ij
  have start := (G.dist_le (p.take i)).trans (walk_take_length p i)
  have finish := (G.dist_le (p.drop j)).trans (walk_drop_length p j)
  have edge := dist_eq_one_iff_adj.mpr ij
  have t1 := conn.dist_triangle (u := a) (v := p.getVert i) (w := b)
  have t2 := conn.dist_triangle (u := p.getVert i) (v := p.getVert j) (w := b)
  omega

private theorem p3_entry {A : Set V} {x a b z : V} (xyz : x ∈ A ∧ a ∈ A ∧ b ∈ A)
    (xa : G.Adj x a) (ab : G.Adj a b)
    (entry : G.Adj z x ∨ G.Adj z a ∨ G.Adj z b)
    (oneLow : ¬ (G.Adj z a ∧ G.Adj z b)) :
    ∃ u ∈ A, ∃ v ∈ A, G.Adj z u ∧ G.Adj u v ∧ ¬ G.Adj z v := by
  by_cases za : G.Adj z a
  · exact ⟨a,xyz.2.1,b,xyz.2.2,za,ab,fun zb => oneLow ⟨za,zb⟩⟩
  · by_cases zb : G.Adj z b
    · exact ⟨b,xyz.2.2,a,xyz.2.1,zb,ab.symm,za⟩
    · exact ⟨x,xyz.1,a,xyz.2.1,entry.resolve_right (not_or.mpr ⟨za,zb⟩),xa,za⟩

/-- Two anticomplete induced three-vertex paths force an induced tree on six
vertices if an outside vertex can see at most one of the four marked vertices.
The marked vertices of each path are its middle vertex and one end. -/
theorem inducedSixPath_of_anticomplete_paths (conn : G.Connected)
    {x a b y c e : V}
    (xa : G.Adj x a) (ab : G.Adj a b) (xb : ¬ G.Adj x b)
    (yc : G.Adj y c) (ce : G.Adj c e) (ye : ¬ G.Adj y e)
    (dis : Disjoint ({x,a,b} : Set V) {y,c,e})
    (anti : ∀ u ∈ ({x,a,b} : Set V), ∀ v ∈ ({y,c,e} : Set V), ¬ G.Adj u v)
    (one : ∀ z ∉ ({x,a,b} : Set V), z ∉ ({y,c,e} : Set V) →
      (¬ (G.Adj z a ∧ G.Adj z b)) ∧ (¬ (G.Adj z c ∧ G.Adj z e)) ∧
        ¬ ((G.Adj z a ∨ G.Adj z b) ∧ (G.Adj z c ∨ G.Adj z e))) :
    InducedSixPath G := by
  classical
  let A : Set V := {x,a,b}
  let B : Set V := {y,c,e}
  have xA : x ∈ A := by simp [A]
  have aA : a ∈ A := by simp [A]
  have bA : b ∈ A := by simp [A]
  have yB : y ∈ B := by simp [B]
  have cB : c ∈ B := by simp [B]
  have eB : e ∈ B := by simp [B]
  let meets (n : ℕ) := ∃ u ∈ A, ∃ v ∈ B, G.dist u v = n
  have existsMeet : ∃ n, meets n := ⟨G.dist x y,x,xA,y,yB,rfl⟩
  let d := Nat.find existsMeet
  obtain ⟨u,uA,v,vB,dist_uv⟩ : meets d := Nat.find_spec existsMeet
  have shortest (s) (hs : s ∈ A) (t) (ht : t ∈ B) : d ≤ G.dist s t :=
    Nat.find_min' existsMeet ⟨s,hs,t,ht,rfl⟩
  have d2 : 2 ≤ d := by
    have ne : u ≠ v := fun eq => Set.disjoint_left.mp dis uA (eq ▸ vB)
    have h := conn.one_lt_dist_of_ne_of_not_adj ne (anti u uA v vB)
    omega
  obtain ⟨p,hp⟩ := conn.exists_walk_length_eq_dist u v
  have length_eq : p.length = d := hp.trans dist_uv
  let z := p.getVert
  have start (i : ℕ) : G.dist u (z i) ≤ i :=
    (G.dist_le (p.take i)).trans (walk_take_length p i)
  have finish (i : ℕ) : G.dist (z i) v ≤ d-i := by
    simpa only [length_eq] using (G.dist_le (p.drop i)).trans (walk_drop_length p i)
  have awayA (i : ℕ) (hi : 0 < i) : z i ∉ A := by
    intro ha
    have hs := shortest (z i) ha v vB
    have hf := finish i
    omega
  have awayB (i : ℕ) (hi : i < d) : z i ∉ B := by
    intro hb
    have hs := shortest u uA (z i) hb
    have hf := start i
    omega
  have offA (i : ℕ) (hi : 2 ≤ i) (hd : i ≤ d) {s : V} (hs : s ∈ A) :
      ¬ G.Adj s (z i) := by
    intro edge
    have h := shortest s hs v vB
    have he := dist_eq_one_iff_adj.mpr edge
    have hf := finish i
    have ht := conn.dist_triangle (u := s) (v := z i) (w := v)
    omega
  have offB (i : ℕ) (hi : i+1 < d) {s : V} (hs : s ∈ B) :
      ¬ G.Adj (z i) s := by
    intro edge
    have h := shortest u uA s hs
    have he := dist_eq_one_iff_adj.mpr edge
    have hf := start i
    have ht := conn.dist_triangle (u := u) (v := z i) (w := s)
    omega
  have step (i : ℕ) (hi : i < d) : G.Adj (z i) (z (i+1)) :=
    p.adj_getVert_succ (length_eq.symm ▸ hi)
  have noChord (i j : ℕ) (h : i+1 < j) (hj : j ≤ d) : ¬ G.Adj (z i) (z j) :=
    geodesic_gap conn p hp h (length_eq.symm ▸ hj)
  have entryA : G.Adj (z 1) x ∨ G.Adj (z 1) a ∨ G.Adj (z 1) b := by
    have h : G.Adj (z 1) u := by simpa only [z, Walk.getVert_zero] using (step 0 (by omega)).symm
    rcases (show u = x ∨ u = a ∨ u = b from by simpa [A] using uA) with eq|eq|eq
    · exact Or.inl (eq ▸ h)
    · exact Or.inr (Or.inl (eq ▸ h))
    · exact Or.inr (Or.inr (eq ▸ h))
  have entryB : G.Adj (z (d-1)) y ∨ G.Adj (z (d-1)) c ∨ G.Adj (z (d-1)) e := by
    have end_index : d-1+1 = p.length := by omega
    have h : G.Adj (z (d-1)) v := by
      simpa only [end_index, z, Walk.getVert_length] using step (d-1) (by omega)
    rcases (show v = y ∨ v = c ∨ v = e from by simpa [B] using vB) with eq|eq|eq
    · exact Or.inl (eq ▸ h)
    · exact Or.inr (Or.inl (eq ▸ h))
    · exact Or.inr (Or.inr (eq ▸ h))
  have oneA := one (z 1) (awayA 1 (by omega)) (awayB 1 (by omega))
  have oneB := one (z (d-1)) (awayA _ (by omega)) (awayB _ (by omega))
  obtain ⟨s,sA,t,tA,zs,st,zt⟩ := p3_entry ⟨xA,aA,bA⟩ xa ab entryA oneA.1
  obtain ⟨r,rB,q,qB,zr,rq,zq⟩ := p3_entry ⟨yB,cB,eB⟩ yc ce entryB oneB.2.1
  by_cases h2 : d = 2
  · have index : d-1 = 1 := by omega
    rw [index] at zr zq entryB
    by_cases leftLow : G.Adj (z 1) a ∨ G.Adj (z 1) b
    · have noRight := fun h => oneA.2.2 ⟨leftLow,h⟩
      have zy := entryB.resolve_right noRight
      exact inducedSixPath_of_edges st.symm zs.symm zy yc ce
        (fun h => zt h.symm) (anti t tA y yB) (anti t tA c cB) (anti t tA e eB)
        (anti s sA y yB) (anti s sA c cB) (anti s sA e eB)
        (fun h => noRight (Or.inl h)) (fun h => noRight (Or.inr h)) ye
    · have zx := entryA.resolve_right leftLow
      exact inducedSixPath_of_edges ab.symm xa.symm zx.symm zr rq
        (fun h => xb h.symm) (fun h => leftLow (Or.inr h.symm))
        (anti b bA r rB) (anti b bA q qB)
        (fun h => leftLow (Or.inl h.symm)) (anti a aA r rB) (anti a aA q qB)
        (anti x xA r rB) (anti x xA q qB) zq
  by_cases h3 : d = 3
  · have index : d-1 = 2 := by omega
    rw [index] at zr zq
    exact inducedSixPath_of_edges st.symm zs.symm (step 1 (by omega)) zr rq
      (fun h => zt h.symm) (offA 2 (by omega) (by omega) tA) (anti t tA r rB) (anti t tA q qB)
      (offA 2 (by omega) (by omega) sA) (anti s sA r rB) (anti s sA q qB)
      (offB 1 (by omega) rB) (offB 1 (by omega) qB) zq
  exact inducedSixPath_of_edges st.symm zs.symm (step 1 (by omega)) (step 2 (by omega)) (step 3 (by omega))
    (fun h => zt h.symm) (offA 2 (by omega) (by omega) tA) (offA 3 (by omega) (by omega) tA)
    (offA 4 (by omega) (by omega) tA)
    (offA 2 (by omega) (by omega) sA) (offA 3 (by omega) (by omega) sA)
    (offA 4 (by omega) (by omega) sA)
    (noChord 1 3 (by omega) (by omega)) (noChord 1 4 (by omega) (by omega))
    (noChord 2 4 (by omega) (by omega))

theorem InducedSixPath.of_induce {S : Set V} (path : InducedSixPath (G.induce S)) :
    InducedSixPath G := by
  obtain ⟨f,chart⟩ := path
  exact ⟨fun i => (f i).val,chart⟩

#print axioms InducedSixPath.le_treeNumber
#print axioms inducedSixPath_of_anticomplete_paths
#print axioms InducedSixPath.of_induce

end Graffiti199Depleted.Catalogue
