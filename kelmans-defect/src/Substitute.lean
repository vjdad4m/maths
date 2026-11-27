import ThreePort

open Finset
namespace KelmansCactus.Substitute
open ThreePort

variable {V : Type*} [Fintype V] [DecidableEq V] {G H : SimpleGraph V}

def Closed (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ P, Assemble.LocalPart G P S

structure Mimic (G : SimpleGraph V) (W : Finset V) (p : Fin 3 → V) : Prop where
  leaf : ∀ i, Signature (G:=G) W p (fun j => if j=i then 1 else 0)
  center : ∀ i j, i ≠ j → Signature (G:=G) W p (fun k => if k=i ∨ k=j then 2 else 0)

omit [Fintype V] in
theorem leaf_reserve {W : Finset V} {p : Fin 3 → V} (m : Mimic G W p) (i : Fin 3) :
    p i ∈ W ∧ Closed G (W.erase (p i)) := by
  obtain ⟨F,hF,d,P,hP⟩ := m.leaf i
  have hc : (F i).card = 1 := by simpa using (hF i).1
  have pp : p i ∈ F i := (hF i).2.includes (card_pos.mp (by omega))
  obtain ⟨e,ee⟩ := card_eq_one.mp hc
  have ep : F i = {p i} := by
    have o : p i ∈ ({e} : Finset V) := ee ▸ pp
    simpa [mem_singleton.mp o] using ee
  have uni : univ.biUnion F = {p i} := by
    ext v
    constructor
    · intro hv
      obtain ⟨j,_,jv⟩ := mem_biUnion.mp hv
      by_cases h : j=i
      · subst j; simpa only [ep] using jv
      · have hh : (F j).card = 0 := by simpa [h] using (hF j).1
        rw [card_eq_zero.mp hh] at jv
        exact (not_mem_empty _ jv).elim
    · intro hv
      exact mem_biUnion.mpr ⟨i,mem_univ _,ep.symm ▸ hv⟩
  rw [uni] at hP
  exact ⟨(hF i).2.inside pp,⟨P,by simpa [Finset.sdiff_singleton_eq_erase] using hP⟩⟩

omit [Fintype V] in
theorem center_reserve {W : Finset V} {p : Fin 3 → V} (m : Mimic G W p) {i j : Fin 3} (ne : i≠j) :
    ∃ F K, F.card=2 ∧ K.card=2 ∧ AtPort (G:=G) W (p i) F ∧
      AtPort (G:=G) W (p j) K ∧ Disjoint F K ∧ Closed G (W \ (F∪K)) := by
  obtain ⟨F,hF,d,P,hP⟩ := m.center i j ne
  have ci : (F i).card = 2 := by simpa using (hF i).1
  have cj : (F j).card = 2 := by simpa using (hF j).1
  have hu : univ.biUnion F = F i ∪ F j := by
    ext v
    constructor
    · intro hv
      obtain ⟨k,_,h⟩ := mem_biUnion.mp hv
      by_cases ki : k=i
      · subst k; exact mem_union_left _ h
      by_cases kj : k=j
      · subst k; exact mem_union_right _ h
      · have hc : (F k).card = 0 := by simpa [ki,kj] using (hF k).1
        rw [card_eq_zero.mp hc] at h
        exact (not_mem_empty _ h).elim
    · rintro hv
      rcases mem_union.mp hv with h | h
      · exact mem_biUnion.mpr ⟨i,mem_univ _,h⟩
      · exact mem_biUnion.mpr ⟨j,mem_univ _,h⟩
  rw [hu] at hP
  exact ⟨F i,F j,ci,cj,(hF i).2,(hF j).2,d i j ne,⟨P,hP⟩⟩

omit [Fintype V] in
theorem add_closed {A B : Finset V} (a : Closed G A) (b : Closed G B) (d : Disjoint A B) :
    Closed G (A∪B) := by
  obtain ⟨P,hP⟩ := a
  obtain ⟨Q,hQ⟩ := b
  exact ⟨P∪Q,local_union hP hQ d⟩

omit [Fintype V] in
theorem tile_closed {A : Finset V} (h : KelmansStarter.IsTile G A) : Closed G A :=
  ⟨{A},⟨by simpa using h,by simp,by simp⟩⟩

omit [Fintype V] in
private theorem triple {p q r : V} (pq : G.Adj p q) (qr : G.Adj q r)
    (pr : p ≠ r) : KelmansStarter.IsTile G {p,q,r} := by
  have h : ({p,q,r} : Finset V).card = 3 := by simp [pq.ne,qr.ne,pr]
  exact ⟨h,(Kelmans.tile_iff_path G {p,q,r} h).mpr ⟨p,q,r,pq.ne,pr,qr.ne,pq,qr,rfl⟩⟩

omit [Fintype V] in
theorem glue_leaf {W : Finset V} {p : Fin 3 → V} {i : Fin 3} {y z : V}
    (m : Mimic G W p) (py : G.Adj (p i) y) (yz : G.Adj y z)
    (yn : y ∉ W) (zn : z ∉ W) : Closed G (W ∪ {y,z}) := by
  obtain ⟨wp,cl⟩ := leaf_reserve m i
  have pr : p i ≠ z := fun h => zn (h ▸ wp)
  have cl' := tile_closed (triple py yz pr)
  have dis : Disjoint (W.erase (p i)) ({p i,y,z} : Finset V) := by
    apply disjoint_left.mpr
    intro v vw vt
    obtain ⟨nv,vW⟩ := mem_erase.mp vw
    simp only [mem_insert,mem_singleton] at vt
    rcases vt with rfl | rfl | rfl
    · exact nv rfl
    · exact yn vW
    · exact zn vW
  have out := add_closed cl cl' dis
  convert out using 1
  ext v
  simp only [mem_union,mem_erase,mem_insert,mem_singleton]
  by_cases vp : v = p i
  · subst v; simp [wp]
  · simp [vp,or_assoc]

omit [Fintype V] [DecidableEq V] in
private theorem at_singleton (y : V) : AtPort (G:=G) {y} y {y} :=
  ⟨Subset.rfl,fun _ => mem_singleton_self _,fun _ hv ne => (ne (mem_singleton.mp hv)).elim⟩

omit [Fintype V] in
theorem glue_center {W : Finset V} {p : Fin 3 → V} {i j : Fin 3} {x y : V}
    (m : Mimic G W p) (ne : i≠j) (px : G.Adj (p i) x) (py : G.Adj (p j) y)
    (xn : x ∉ W) (yn : y ∉ W) (nxy : x≠y) : Closed G (W ∪ {x,y}) := by
  obtain ⟨F,K,f2,k2,hF,hK,hFK,cl⟩ := center_reserve m ne
  have fx : Disjoint ({x} : Finset V) F := disjoint_left.mpr fun u ux uf =>
    xn ((mem_singleton.mp ux) ▸ hF.inside uf)
  have ky : Disjoint ({y} : Finset V) K := disjoint_left.mpr fun u uy uk =>
    yn ((mem_singleton.mp uy) ▸ hK.inside uk)
  have fy : Disjoint F ({y} : Finset V) := disjoint_left.mpr fun u uf uy =>
    yn ((mem_singleton.mp uy) ▸ hF.inside uf)
  have xk : Disjoint ({x} : Finset V) K := disjoint_left.mpr fun u ux uk =>
    xn ((mem_singleton.mp ux) ▸ hK.inside uk)
  have xy : Disjoint ({x} : Finset V) ({y} : Finset V) := by simp [nxy.symm]
  have clx := tile_closed (join_one_two (at_singleton (G:=G) x) hF (card_singleton x) f2 fx px.symm)
  have cly := tile_closed (join_one_two (at_singleton (G:=G) y) hK (card_singleton y) k2 ky py.symm)
  have dPorts : Disjoint (({x}:Finset V)∪F) (({y}:Finset V)∪K) := by
    simp only [disjoint_union_left,disjoint_union_right]
    exact ⟨⟨xy,fy⟩,⟨xk,hFK⟩⟩
  have glued := add_closed clx cly dPorts
  have sep : Disjoint (W \ (F∪K)) ((({x}:Finset V)∪F) ∪ (({y}:Finset V)∪K)) := by
    apply disjoint_left.mpr
    intro v vr vs
    obtain ⟨vw,vn⟩ := mem_sdiff.mp vr
    simp only [mem_union,mem_singleton] at vs
    rcases vs with (rfl | vf) | (rfl | vk)
    · exact xn vw
    · exact vn (mem_union_left _ vf)
    · exact yn vw
    · exact vn (mem_union_right _ vk)
  have out := add_closed cl glued sep
  convert out using 1
  ext v
  simp only [mem_union,mem_sdiff,mem_insert,mem_singleton]
  have g₁ : v ∈ F → v ∈ W := fun h => hF.inside h
  have g₂ : v ∈ K → v ∈ W := fun h => hK.inside h
  tauto

#print axioms glue_leaf
#print axioms glue_center

omit [Fintype V] in
theorem remove_tile {P : Finset (Finset V)} {S t : Finset V}
    (h : Assemble.LocalPart G P S) (ht : t ∈ P) :
    Assemble.LocalPart G (P.erase t) (S\t) := by
  refine ⟨fun u hu => h.tile u (mem_erase.mp hu).2,
    fun u hu v hv n => h.disj u (mem_erase.mp hu).2 v (mem_erase.mp hv).2 n,?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,uv⟩ := mem_biUnion.mp hv
    obtain ⟨ne,up⟩ := mem_erase.mp hu
    exact mem_sdiff.mpr ⟨h.tile_sub G up uv, fun tv => disjoint_left.mp (h.disj _ up _ ht ne) uv tv⟩
  · intro hv
    obtain ⟨vs,vt⟩ := mem_sdiff.mp hv
    obtain ⟨u,up,uv⟩ := mem_biUnion.mp (h.cover.symm ▸ vs)
    exact mem_biUnion.mpr ⟨u,mem_erase.mpr ⟨fun e => vt (e ▸ uv),up⟩,uv⟩

omit [Fintype V] in
theorem change_edges {P : Finset (Finset V)} {S : Finset V}
    (h : Assemble.LocalPart H P S)
    (keep : ∀ x ∈ S, ∀ y ∈ S, H.Adj x y → G.Adj x y) :
    Assemble.LocalPart G P S := by
  refine ⟨?_,h.disj,h.cover⟩
  intro t ht
  obtain ⟨card,c,ct,star⟩ := h.tile t ht
  have sub := h.tile_sub H ht
  exact ⟨card,c,ct,fun v hv ne => keep c (sub ct) v (sub hv) (star v hv ne)⟩

omit [Fintype V] in
private theorem enclosed_member {r x : V} {S : Finset V} (h : x ∈ insert r S) (ne : x ≠ r) :
    x ∈ S := by
  exact (mem_insert.mp h).resolve_left ne

omit [Fintype V] in
/-- At any chosen root, replace the one old vertex by a brick with the six
mimic signatures. Only the two paths of the original tile through the root
need to be considered: an old leaf uses a width-one port, and a center uses
two disjoint width-two ports. Retain all old edges away from the root. -/
theorem replace_one {U W : Finset V} {r : V} {p : Fin 3 → V} {slot : V → Fin 3}
    (before : Closed H (insert r U)) (m : Mimic G W p)
    (outside : r ∉ U) (sep : Disjoint U W)
    (keep : ∀ x ∈ U, ∀ y ∈ U, H.Adj x y → G.Adj x y)
    (link : ∀ x ∈ U, H.Adj r x → G.Adj (p (slot x)) x)
    (slots : ∀ x ∈ U, ∀ y ∈ U, H.Adj r x → H.Adj r y → x ≠ y → slot x ≠ slot y) :
    Closed G (U∪W) := by
  obtain ⟨P,hP⟩ := before
  have rr : r ∈ P.biUnion id := hP.cover.symm ▸ mem_insert_self _ _
  obtain ⟨t,ht,htr⟩ := mem_biUnion.mp rr
  change r ∈ t at htr
  have tile := hP.tile t ht
  have sub := hP.tile_sub H ht
  have tOut : t.erase r ⊆ U := by
    intro x hx
    obtain ⟨ne,xt⟩ := mem_erase.mp hx
    exact enclosed_member (sub xt) ne
  have oldOut : (insert r U) \ t ⊆ U := by
    intro x hx
    obtain ⟨xs,nxt⟩ := mem_sdiff.mp hx
    apply enclosed_member xs
    rintro rfl
    exact nxt htr
  have rest := change_edges (G:=G) (remove_tile hP ht)
    (fun x hx y hy => keep x (oldOut hx) y (oldOut hy))
  have newTile : Closed G (W∪t.erase r) := by
    obtain ⟨a,b,c,nab,nac,nbc,ab,bc,he⟩ := (Kelmans.tile_iff_path H t tile.1).mp tile.2
    have ra : a ∈ t := by simp [he]
    have rb : b ∈ t := by simp [he]
    have rc : c ∈ t := by simp [he]
    rw [he] at htr
    simp only [mem_insert,mem_singleton] at htr
    have nW (v : V) (h : v ∈ U) : v ∉ W := disjoint_left.mp sep h
    rcases htr with rr | rr | rr
    · subst r
      have bu := enclosed_member (sub rb) nab.symm
      have cu := enclosed_member (sub rc) nac.symm
      rw [he,erase_insert (by simp [nab,nac])]
      exact glue_leaf m (link b bu ab) (keep b bu c cu bc) (nW b bu) (nW c cu)
    · subst r
      have au := enclosed_member (sub ra) nab
      have cu := enclosed_member (sub rc) nbc.symm
      have ere : ({a,b,c}:Finset V).erase b = {a,c} := by
        ext v
        simp only [mem_erase,mem_insert,mem_singleton]
        constructor
        · rintro ⟨hn,h | h | h⟩
          · exact Or.inl h
          · exact (hn h).elim
          · exact Or.inr h
        · rintro (rfl | rfl)
          · exact ⟨nab,Or.inl rfl⟩
          · exact ⟨nbc.symm,Or.inr (Or.inr rfl)⟩
      rw [he,ere]
      exact glue_center m (slots a au c cu ab.symm bc nac)
        (link a au ab.symm) (link c cu bc) (nW a au) (nW c cu) nac
    · subst r
      have au := enclosed_member (sub ra) nac
      have bu := enclosed_member (sub rb) nbc
      have ere : ({a,b,c}:Finset V).erase c = {b,a} := by
        ext v
        simp only [mem_erase,mem_insert,mem_singleton]
        constructor
        · rintro ⟨hn,h | h | h⟩
          · exact Or.inr h
          · exact Or.inl h
          · exact (hn h).elim
        · rintro (rfl | rfl)
          · exact ⟨nbc,Or.inr (Or.inl rfl)⟩
          · exact ⟨nac,Or.inl rfl⟩
      rw [he,ere]
      exact glue_leaf m (link b bu bc.symm) (keep b bu a au ab.symm) (nW b bu) (nW a au)
  have d : Disjoint ((insert r U) \ t) (W∪t.erase r) := by
    apply disjoint_left.mpr
    intro x hx hy
    rcases mem_union.mp hy with ww | ww
    · exact disjoint_left.mp sep (oldOut hx) ww
    · exact (mem_sdiff.mp hx).2 (mem_erase.mp ww).2
  have out := add_closed ⟨_,rest⟩ newTile d
  convert out using 1
  ext v
  simp only [mem_union,mem_sdiff,mem_insert,mem_erase]
  by_cases vr : v=r
  · subst v; simp [htr,outside]
  · simp [vr,or_assoc,or_left_comm]
    have go : v ∈ t → v ∈ U := fun hx => enclosed_member (sub hx) vr
    tauto

/-- A growth step carries its incidence data. This is independent of the
number of vertices or steps, and may be chained with different bricks. -/
structure Step (base result : SimpleGraph V × Finset V) where
  outside : Finset V
  brick : Finset V
  root : V
  ports : Fin 3 → V
  slot : V → Fin 3
  old_vertices : base.2 = insert root outside
  new_vertices : result.2 = outside ∪ brick
  outside_root : root ∉ outside
  disjoint : Disjoint outside brick
  mimic : Mimic result.1 brick ports
  preserve : ∀ x ∈ outside, ∀ y ∈ outside, base.1.Adj x y → result.1.Adj x y
  link : ∀ x ∈ outside, base.1.Adj root x → result.1.Adj (ports (slot x)) x
  distinct_slots : ∀ x ∈ outside, ∀ y ∈ outside,
    base.1.Adj root x → base.1.Adj root y → x ≠ y → slot x ≠ slot y

inductive Expansion (start : SimpleGraph V × Finset V) :
    SimpleGraph V × Finset V → Prop where
  | base : Expansion start start
  | next {u v} : Expansion start u → Step u v → Expansion start v

omit [Fintype V] in
theorem expansion_preserves_factor {u v : SimpleGraph V × Finset V}
    (start : Closed u.1 u.2) (history : Expansion u v) : Closed v.1 v.2 := by
  induction history with
  | base => exact start
  | next _ step ih =>
    rw [step.old_vertices] at ih
    rw [step.new_vertices]
    exact replace_one ih step.mimic step.outside_root step.disjoint
      step.preserve step.link step.distinct_slots

#print axioms replace_one
#print axioms expansion_preserves_factor
end KelmansCactus.Substitute
