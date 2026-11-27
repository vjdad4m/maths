import Substitute
import Mathlib.Data.Finset.Preimage

open Finset
namespace KelmansCactus.AtomicBridge.DominoRepair
open Substitute Assemble

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev p : V ⊕ Fin 3 := .inr 0
abbrev q : V ⊕ Fin 3 := .inr 1
abbrev r : V ⊕ Fin 3 := .inr 2

omit [Fintype V] in
private theorem third {X : Type*} [DecidableEq X] {t : Finset X} {x y : X}
    (sz : t.card = 3) (mx : x ∈ t) (my : y ∈ t) (xy : x ≠ y) :
    ∃ z, z ∈ t ∧ z ≠ x ∧ z ≠ y ∧ t = {x,y,z} := by
  have sub : ({x,y}:Finset X) ⊆ t := by
    intro v m
    simp only [mem_insert,mem_singleton] at m
    rcases m with rfl|rfl <;> assumption
  have le := card_sdiff_add_card_eq_card sub
  have two : ({x,y}:Finset X).card = 2 := by simp [xy]
  rw [sz,two] at le
  have one : (t \ {x,y}).card = 1 := by omega
  obtain ⟨z,hz⟩ := card_eq_one.mp one
  have zm : z ∈ t \ {x,y} := hz.symm ▸ mem_singleton_self z
  obtain ⟨zt,zn⟩ := mem_sdiff.mp zm
  have zx : z ≠ x := fun h => zn (by simp [h])
  have zy : z ≠ y := fun h => zn (by simp [h])
  refine ⟨z,zt,zx,zy,?_⟩
  ext w
  simp only [mem_insert,mem_singleton]
  by_cases wx : w=x
  · subst w; simp [mx]
  by_cases wy : w=y
  · subst w; simp [my]
  constructor
  · intro wt
    have ww : w ∈ t \ {x,y} := mem_sdiff.mpr ⟨wt,by simp [wx,wy]⟩
    have wz : w=z := mem_singleton.mp (hz ▸ ww)
    exact Or.inr (Or.inr wz)
  · rintro (e|e|e)
    · exact (wx e).elim
    · exact (wy e).elim
    · exact e.symm ▸ zt

private def oldIn : V ↪ (V ⊕ Fin 3) := ⟨Sum.inl, Sum.inl_injective⟩

omit [Fintype V] in
private theorem pullback {G : SimpleGraph V} {H : SimpleGraph (V ⊕ Fin 3)}
    {P : Finset (Finset (V ⊕ Fin 3))} {S : Finset V}
    (sound : ∀ u v, H.Adj (.inl u) (.inl v) → G.Adj u v)
    (h : LocalPart H P (S.map oldIn)) : Closed G S := by
  classical
  let e : V ↪ (V ⊕ Fin 3) := oldIn
  let f (t : Finset (V ⊕ Fin 3)) := t.preimage e e.injective.injOn
  have restore (t : Finset (V ⊕ Fin 3)) (ht : t ∈ P) : (f t).map e = t := by
    ext v
    constructor
    · intro mem
      obtain ⟨w, hw, rfl⟩ := mem_map.mp mem
      exact mem_preimage.mp hw
    · intro hv
      obtain ⟨w, _, rfl⟩ := mem_map.mp (h.tile_sub H ht hv)
      exact mem_map.mpr ⟨w, mem_preimage.mpr hv, rfl⟩
  refine ⟨P.image f, ⟨?_, ?_, ?_⟩⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
    obtain ⟨card, a, ha, star⟩ := h.tile t ht
    obtain ⟨c, _, rfl⟩ := mem_map.mp (h.tile_sub H ht ha)
    refine ⟨?_, c, mem_preimage.mpr ha, ?_⟩
    · rw [← card_map (s := f t) e, restore t ht]
      exact card
    · intro w hw ne
      exact sound _ _ (star _ (mem_preimage.mp hw) (fun eq => ne (e.injective eq)))
  · intro s hs t ht ne
    obtain ⟨s', hs', rfl⟩ := mem_image.mp hs
    obtain ⟨t', ht', rfl⟩ := mem_image.mp ht
    apply disjoint_left.mpr
    intro w ws wt
    exact disjoint_left.mp (h.disj _ hs' _ ht' (fun eq => ne (congrArg f eq)))
      (mem_preimage.mp ws) (mem_preimage.mp wt)
  · ext w
    constructor
    · intro hw
      obtain ⟨t,ht,wt⟩ := mem_biUnion.mp hw
      obtain ⟨u,hu,rfl⟩ := mem_image.mp ht
      have wu : w ∈ f u := wt
      have ew : e w ∈ u := mem_preimage.mp wu
      obtain ⟨v,hv,eq⟩ := mem_map.mp (h.tile_sub H hu ew)
      exact oldIn.injective eq ▸ hv
    · intro wS
      have hw : e w ∈ P.biUnion id := h.cover.symm ▸ mem_map.mpr ⟨w,wS,rfl⟩
      obtain ⟨t, ht, wt⟩ := mem_biUnion.mp hw
      have wp : w ∈ f t := mem_preimage.mpr wt
      exact mem_biUnion.mpr ⟨f t, mem_image_of_mem f ht, wp⟩

private theorem finish {G : SimpleGraph V} {H : SimpleGraph (V ⊕ Fin 3)}
    {P : Finset (Finset (V ⊕ Fin 3))} {S : Finset V} {T : Finset (V ⊕ Fin 3)}
    (sound : ∀ u v, H.Adj (.inl u) (.inl v) → G.Adj u v)
    (rest : LocalPart H P T)
    (cover : ∀ x : V ⊕ Fin 3, x ∈ T ↔ ∃ v ∈ S, Sum.inl v = x)
    (repair : Closed G (univ \ S)) : KelmansStarter.HasP3Factor G := by
  have eq : T = S.map oldIn := by
    ext x
    rw [cover,mem_map]
    rfl
  have part := pullback sound (eq ▸ rest)
  have sep : Disjoint S (univ \ S) := disjoint_left.mpr
    (fun _ a b => (mem_sdiff.mp b).2 a)
  have h := add_closed part repair sep
  have all : S ∪ (univ \ S) = (univ : Finset V) := by
    ext v; simp
  rw [all] at h
  obtain ⟨tiles,ok⟩ := h
  exact ⟨tiles,ok.tile,ok.disj,ok.cover⟩

omit [Fintype V] in
private theorem mandatory {X : Type*} [DecidableEq X] {H : SimpleGraph X}
    {t : Finset X} {v w : X} (h : KelmansStarter.IsTile H t) (hv : v ∈ t)
    (only : ∀ x ∈ t, H.Adj v x → x=w) :
    ∃ z, z ≠ v ∧ z ≠ w ∧ H.Adj w z ∧ t = {v,w,z} := by
  obtain ⟨sz,c,cm,star⟩ := h
  have cv : c ≠ v := by
    intro ce
    subst c
    have sub : t ⊆ {v,w} := by
      intro x xm
      by_cases xv : x=v
      · simp [xv]
      · simp [only x xm (star x xm xv),mem_insert,mem_singleton]
    have low := card_le_card sub
    have hi : ({v,w}:Finset X).card ≤ 2 := by rcases (card_pair_eq_one_or_two : ({v,w}:Finset X).card = 1 ∨ ({v,w}:Finset X).card = 2) with e|e <;> omega
    omega
  have cw := only c cm (star _ hv cv.symm).symm
  subst c
  obtain ⟨z,zm,zv,zw,eq⟩ := third sz hv cm cv.symm
  exact ⟨z,zv,zw,star _ zm zw,eq⟩

omit [Fintype V] in
private theorem triple_closed {G : SimpleGraph V} {a b c : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (ac : a ≠ c) :
    Closed G ({a,b,c}:Finset V) := by
  apply tile_closed
  refine ⟨by simp [ab.ne,bc.ne,ac],b,by simp,?_⟩
  intro x hx ne
  simp only [mem_insert,mem_singleton] at hx
  rcases hx with rfl|rfl|rfl
  · exact ab.symm
  · exact (ne rfl).elim
  · exact bc

/-- Residual repair after the domino construction. Its external contacts are
p-a, p-b, r-a; internal gadget edges lie on p-q-r. The forgotten old
edge a-b repairs either mixed case. The old host edges may be a
subgraph of the old target graph. -/
theorem factor_of_residual
    (G : SimpleGraph V) (H : SimpleGraph (V ⊕ Fin 3))
    {a b : V} (ab : G.Adj a b)
    (old : ∀ u v, H.Adj (.inl u) (.inl v) → G.Adj u v)
    (p_adj : ∀ z, H.Adj p z → z=q ∨ z=Sum.inl a ∨ z=Sum.inl b)
    (q_adj : ∀ z, H.Adj q z → z=p ∨ z=r)
    (r_adj : ∀ z, H.Adj r z → z=q ∨ z=Sum.inl a)
    (has : KelmansStarter.HasP3Factor H) : KelmansStarter.HasP3Factor G := by
  classical
  have pq : (p : V ⊕ Fin 3) ≠ q := fun h => (by decide : (0 : Fin 3) ≠ 1) (Sum.inr.inj h)
  have qr : (q : V ⊕ Fin 3) ≠ r := fun h => (by decide : (1 : Fin 3) ≠ 2) (Sum.inr.inj h)
  have pr : (p : V ⊕ Fin 3) ≠ r := fun h => (by decide : (0 : Fin 3) ≠ 2) (Sum.inr.inj h)
  obtain ⟨P,ht,hd,hcov⟩ := has
  have localP : LocalPart H P univ := ⟨ht,hd,hcov⟩
  have contains (x : V ⊕ Fin 3) : ∃ t ∈ P,x ∈ t :=
    mem_biUnion.mp (hcov.symm ▸ mem_univ x)
  have conflict {s t : Finset (V ⊕ Fin 3)} (sm : s ∈ P) (tm : t ∈ P)
      {x : V ⊕ Fin 3} (xs : x ∈ s) (xt : x ∈ t) : s=t := by
    by_contra ne
    exact disjoint_left.mp (hd s sm t tm ne) xs xt
  have fin (n : Fin 3) : n=0 ∨ n=1 ∨ n=2 := by fin_cases n <;> simp
  obtain ⟨t,tm,qt⟩ := contains q
  have tile := ht t tm
  have one_of : p ∈ t ∨ r ∈ t := by
    by_contra! none
    obtain ⟨sz,c,cm,star⟩ := tile
    by_cases cq : c=q
    · subst c
      have sub : t ⊆ {q} := by
        intro v vt
        by_cases vq : v=q
        · exact mem_singleton.mpr vq
        · rcases q_adj _ (star _ vt vq) with e|e
          · exact (none.1 (e ▸ vt)).elim
          · exact (none.2 (e ▸ vt)).elim
      have count := card_le_card sub
      simp [sz] at count
    · rcases q_adj _ (star _ qt (fun e => cq e.symm)).symm with e|e
      · exact none.1 (e ▸ cm)
      · exact none.2 (e ▸ cm)
  by_cases pt : p ∈ t
  · by_cases rt : r ∈ t
    · obtain ⟨z,_,_,_,hz⟩ := third tile.1 pt qt pq
      have rz : r=z := by
        have mem : r ∈ ({p,q,z}:Finset (V ⊕ Fin 3)) := hz ▸ rt
        simp only [mem_insert,mem_singleton] at mem
        exact (mem.resolve_left pr.symm).resolve_left qr.symm
      have eq : t = {p,q,r} := rz.symm ▸ hz
      apply finish old (remove_tile localP tm) (S := univ)
      · intro x
        cases x with
        | inl v => simp [eq,p,q,r]
        | inr n =>
          rcases fin n with n0|n1|n2 <;> subst n <;> simp [eq,p,q,r]
      · simpa using (show Closed G ∅ from ⟨∅,by constructor <;> simp⟩)
    · obtain ⟨z,zt,zp,zq,te⟩ := third tile.1 pt qt pq
      have qedge : H.Adj p z := by
        obtain ⟨sz,c,cm,star⟩ := tile
        by_cases cq : c=q
        · subst c
          rcases q_adj _ (star _ zt zq) with ep|er
          · exact (zp ep).elim
          · exact (rt (er ▸ zt)).elim
        · rcases q_adj _ (star _ qt (fun e => cq e.symm)).symm with ep|er
          · subst c; exact star _ zt zp
          · exact (rt (er ▸ cm)).elim
      have zb : z = Sum.inl b := by
        rcases p_adj _ qedge with e|e|e
        · exact (zq e).elim
        · obtain ⟨u,um,ru⟩ := contains r
          have ne : u ≠ t := fun k => rt (k ▸ ru)
          have qu : q ∉ u := fun m => ne (conflict um tm m qt)
          obtain ⟨w,_,_,_,ue⟩ := mandatory (ht u um) ru
            (w := Sum.inl a) (fun x xm e => (r_adj _ e).resolve_left (fun k=>qu (k ▸ xm)))
          have au : Sum.inl a ∈ u := by simp [ue]
          exact (ne (conflict um tm au (e ▸ zt))).elim
        · exact e
      subst z
      obtain ⟨u,um,ru⟩ := contains r
      have ne : u ≠ t := fun k => rt (k ▸ ru)
      have qu : q ∉ u := fun m => ne (conflict um tm m qt)
      obtain ⟨w,wr,wa,aw,ue⟩ := mandatory (ht u um) ru (w := Sum.inl a)
        (fun x xm e => (r_adj _ e).resolve_left (fun k=>qu (k ▸ xm)))
      have wm : w ∈ u := by simp [ue]
      have wb : w ≠ Sum.inl b := fun e => ne (conflict um tm wm (e.symm ▸ zt))
      have we : ∃ v, w=Sum.inl v := by
        cases w with
        | inl v => exact ⟨v,rfl⟩
        | inr n =>
          rcases fin n with n0|n1|n2 <;> subst n
          · exact (ne (conflict um tm wm pt)).elim
          · exact (qu wm).elim
          · exact (wr rfl).elim
      obtain ⟨v,rfl⟩ := we
      have va : v ≠ a := fun e => wa (congrArg Sum.inl e)
      have vb : v ≠ b := fun e => wb (congrArg Sum.inl e)
      have rep := triple_closed ab.symm (old _ _ aw) vb.symm
      have um' : u ∈ P.erase t := mem_erase.mpr ⟨ne,um⟩
      let S := (univ : Finset V) \ {b,a,v}
      apply finish old (remove_tile (remove_tile localP tm) um') (S := S)
      · intro x
        rw [te,ue]
        cases x with
        | inl i => simp [S,p,q,r, and_assoc]
        | inr n => rcases fin n with n0|n1|n2 <;> subst n <;> simp [p,q,r]
      · have s : (univ : Finset V) \ S = {b,a,v} := by simp [S]
        exact s.symm ▸ rep
  · have rt : r ∈ t := one_of.resolve_left pt
    obtain ⟨z,zt,zr,zq,te⟩ := third tile.1 rt qt qr.symm
    have qedge : H.Adj r z := by
      obtain ⟨sz,c,cm,star⟩ := tile
      by_cases cq : c=q
      · subst c
        rcases q_adj _ (star _ zt zq) with ep|er
        · exact (pt (ep ▸ zt)).elim
        · exact (zr er).elim
      · rcases q_adj _ (star _ qt (fun e => cq e.symm)).symm with ep|er
        · exact (pt (ep ▸ cm)).elim
        · subst c; exact star _ zt zr
    have za : z = Sum.inl a := (r_adj _ qedge).resolve_left zq
    subst z
    obtain ⟨u,um,pu⟩ := contains p
    have ne : u ≠ t := fun k => pt (k ▸ pu)
    have qu : q ∉ u := fun m => ne (conflict um tm m qt)
    have au : Sum.inl a ∉ u := fun m => ne (conflict um tm m zt)
    obtain ⟨w,wp,wb,bw,ue⟩ := mandatory (ht u um) pu (w := Sum.inl b)
      (fun x xm e => ((p_adj _ e).resolve_left (fun k=>qu (k ▸ xm))).resolve_left
        (fun k=>au (k ▸ xm)))
    have wm : w ∈ u := by simp [ue]
    have wa : w ≠ Sum.inl a := fun e => au (e ▸ wm)
    have we : ∃ v, w=Sum.inl v := by
      cases w with
      | inl v => exact ⟨v,rfl⟩
      | inr n =>
        rcases fin n with n0|n1|n2 <;> subst n
        · exact (wp rfl).elim
        · exact (qu wm).elim
        · exact (ne (conflict um tm wm rt)).elim
    obtain ⟨v,rfl⟩ := we
    have va : v ≠ a := fun e => wa (congrArg Sum.inl e)
    have vb : v ≠ b := fun e => wb (congrArg Sum.inl e)
    have rep := triple_closed ab (old _ _ bw) va.symm
    have um' : u ∈ P.erase t := mem_erase.mpr ⟨ne,um⟩
    let S := (univ : Finset V) \ {a,b,v}
    apply finish old (remove_tile (remove_tile localP tm) um') (S := S)
    · intro x
      rw [te,ue]
      cases x with
      | inl i => simp [S,p,q,r,and_assoc]
      | inr n => rcases fin n with n0|n1|n2 <;> subst n <;> simp [p,q,r]
    · have s : (univ : Finset V) \ S = {a,b,v} := by simp [S]
      exact s.symm ▸ rep

#print axioms factor_of_residual
end KelmansCactus.AtomicBridge.DominoRepair
