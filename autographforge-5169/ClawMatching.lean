import Row5169
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace Chain5169
open Finset SimpleGraph Graffiti326 BullCover1125 TriangleMatching1078

variable {W : Type*} [Fintype W] {G : SimpleGraph W}
private abbrev Fits {k : ℕ} (f : Fin k × Bool ↪ W) :=
  ∀ i, G.Adj (f (i,false)) (f (i,true))

omit [Fintype W] in
/-- Exchange a matched endpoint for a free vertex adjacent to its mate. -/
private theorem exchange {k : ℕ} (f : Fin k × Bool ↪ W) (ok : Fits (G:=G) f)
    (i : Fin k) (b : Bool) {x y : W} (hx : x ∉ support f) (hy : y ∉ support f)
    (xy : x ≠ y) (edge : G.Adj x (f (i,!b))) :
    ∃ g : Fin k × Bool ↪ W, Fits (G:=G) g ∧ f (i,b) ∉ support g ∧ y ∉ support g := by
  classical
  let old := f (i,b)
  let perm := Equiv.swap x old
  let g := f.trans perm.toEmbedding
  have used (p : Fin k × Bool) : f p ∈ support f := (Graffiti326.mem_support f).mpr ⟨p.1,p.2,rfl⟩
  have fresh (p) : f p ≠ x := fun eq => hx (eq ▸ used p)
  have keep (p) (ne : p ≠ (i,b)) : g p = f p :=
    Equiv.swap_apply_of_ne_of_ne (fresh p) (fun eq => ne (f.injective eq))
  have replace : g (i,b) = x := Equiv.swap_apply_right x old
  have edges : Fits (G:=G) g := by
    intro j
    by_cases ji : j=i
    · subst j
      cases b with
      | false =>
        rw [replace,keep (i,true) (by simp)]
        exact edge
      | true =>
        rw [replace,keep (i,false) (by simp)]
        exact edge.symm
    · rw [keep (j,false) (fun eq => ji (congrArg Prod.fst eq)),
          keep (j,true) (fun eq => ji (congrArg Prod.fst eq))]
      exact ok j
  have newfree {z : W} (h : Equiv.swap x old z ∉ support f) : z ∉ support g := by
    intro mem
    obtain ⟨a,c,hac⟩ := (Graffiti326.mem_support g).mp mem
    have eq := Equiv.swap_apply_eq_iff.mp (show Equiv.swap x old (f (a,c)) = z from hac)
    exact h (eq ▸ used (a,c))
  exact ⟨g,edges,newfree (by simpa [old] using hx),
    newfree (by rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm xy) (fun e => hy (e ▸ used (i,b)))]; exact hy)⟩

omit [Fintype W] in
private theorem descend (conn : G.Connected) {x y : W} (ne : x ≠ y) :
    ∃ v, G.Adj x v ∧ G.dist v y + 1 = G.dist x y := by
  obtain ⟨p,hp⟩ := conn.exists_walk_length_eq_dist x y
  cases p with
  | nil => exact (ne rfl).elim
  | cons e q =>
    rename_i v
    refine ⟨_,e,?_⟩
    have tri := conn.dist_triangle (u:=x) (v:=v) (w:=y)
    rw [dist_eq_one_iff_adj.mpr e] at tri
    have leq := dist_le q
    simp only [Walk.length_cons] at hp
    omega

/-- Sumner's matching theorem in both parities. Choose, over maximum
matchings, the closest pair of unmatched vertices. A local exchange on the
first two steps of a shortest path strictly shortens their distance. -/
theorem near_perfect (conn : G.Connected) (cl : Free G claw) :
    Fintype.card W ≤ 2*matchingNumber G + 1 := by
  classical
  by_contra! many
  let k := matchingNumber G
  have size (f : Fin k × Bool ↪ W) : (support f).card = 2*k := by
    simp [Graffiti326.support,Nat.mul_comm]
  let costs := {d : ℕ | ∃ f : Fin k × Bool ↪ W, Fits (G:=G) f ∧
    ∃ x y, x ∉ support f ∧ y ∉ support f ∧ x ≠ y ∧ G.dist x y = d}
  obtain ⟨f₀,ok₀⟩ := matchingNumber_attained G
  have room : 1 < ((univ : Finset W) \ support f₀).card := by
    rw [card_sdiff (subset_univ _),card_univ,size f₀]
    dsimp [k]
    omega
  obtain ⟨a,ha,b,hb,ab⟩ := one_lt_card.mp room
  have feasible : costs.Nonempty := ⟨G.dist a b,f₀,ok₀,a,b,(mem_sdiff.mp ha).2,
    (mem_sdiff.mp hb).2,ab,rfl⟩
  obtain ⟨f,ok,x,y,hx,hy,xy,best⟩ := Nat.sInf_mem feasible
  have shortest (g : Fin k × Bool ↪ W) (edges : Fits (G:=G) g) {u : W}
      (hu : u ∉ support g) (hy' : y ∉ support g) (uy : u ≠ y) :
      G.dist x y ≤ G.dist u y := best.le.trans
        (Nat.sInf_le (s:=costs) ⟨g,edges,u,y,hu,hy',uy,rfl⟩)
  obtain ⟨v,xv,step⟩ := descend conn xy
  have usedV : v ∈ support f := by
    apply Classical.byContradiction
    intro free
    have larger := matchingNumber_upper (matching_extend ok hx free xv)
    change k+1 ≤ k at larger
    omega
  obtain ⟨i,b,eq⟩ := (Graffiti326.mem_support f).mp usedV
  subst v
  let v := f (i,b)
  let w := f (i,!b)
  have vw : G.Adj v w := by cases b <;> first | exact ok i | exact (ok i).symm
  have usedW : w ∈ support f := (Graffiti326.mem_support f).mpr ⟨i,!b,rfl⟩
  have vy : v ≠ y := fun e => hy (e ▸ usedV)
  have wy : w ≠ y := fun e => hy (e ▸ usedW)
  have xw : x ≠ w := fun e => hx (e ▸ usedW)
  obtain ⟨z,vz,next⟩ := descend conn vy
  have xz : x ≠ z := by
    intro eqz
    change G.dist v y+1=G.dist x y at step
    rw [←eqz] at next
    omega
  have noxz : ¬G.Adj x z := by
    intro xza
    have dist := conn.dist_triangle (u:=x) (v:=z) (w:=y)
    rw [dist_eq_one_iff_adj.mpr xza] at dist
    change G.dist v y+1=G.dist x y at step
    omega
  have farW : G.dist x y ≤ G.dist w y := by
    obtain ⟨g,edges,free,freeY⟩ := exchange f ok i (!b) hx hy xy (by simpa using xv)
    exact shortest g edges free freeY wy
  by_cases wz : w=z
  · change G.dist v y+1=G.dist x y at step
    rw [wz] at farW
    omega
  rcases claw_neighbors cl xv.symm vz vw xz xw (Ne.symm wz) with impossible | xwa | zwa
  · exact noxz impossible
  · obtain ⟨g,edges,free,freeY⟩ := exchange f ok i b hx hy xy xwa
    have bound := shortest g edges free freeY vy
    omega
  · have dist := conn.dist_triangle (u:=w) (v:=z) (w:=y)
    rw [dist_eq_one_iff_adj.mpr zwa.symm] at dist
    change G.dist v y+1=G.dist x y at step
    omega

end Chain5169
