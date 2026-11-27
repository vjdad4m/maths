import ThetaFiveTransferLocal
import ThetaLocalRoute

open SimpleGraph Finset
namespace KelmansCactus.AtomicBridge.ThetaFiveRing
open SquareCap (FactorOn factor_map)
open ThetaLocalRoute (Ring route route_injective)
open ThetaFiveTransferLocal (Patch mapped_local_refill)
noncomputable section

abbrev Lane := Bool×Bool

def site (s i : Bool) : Ring := if s then if i then 5 else 2 else if i then 4 else 1

def atMode (s i : Bool) : Fin 4 :=
  if s then if i then 2 else 3 else if i then 1 else 0

private theorem mode_site : ∀ s i : Bool,
    route (atMode s i) 1=site s i ∧ route (atMode s i) 2=site (!s) i ∧
    route (atMode s i) 5=site (!s) (!i) := by decide

private theorem cyclic_route : ∀ k : Fin 4, ∀ a b : Ring,
    a+1=b ∨ b+1=a →
      route k a+1=route k b ∨ route k b+1=route k a := by decide

variable {V : Type*}

abbrev outer (v : V) : V⊕Fin 7 := .inl v
abbrev ring (i : Ring) : V⊕Fin 7 := .inr i.castSucc

def ringMap (V : Type*) : Ring↪(V⊕Fin 7) :=
  ⟨ring,by
    intro a b h
    change (Sum.inr a.castSucc : V⊕Fin 7) = Sum.inr b.castSucc at h
    exact Fin.ext (congrArg (fun z : Fin 7=>z.val) (Sum.inr_injective h))⟩

def allRing (V : Type*) [DecidableEq V] : Finset (V⊕Fin 7) := univ.map (ringMap V)

structure Shape (H : SimpleGraph (V⊕Fin 7)) (p : Lane↪V) : Prop where
  cycle : ∀ a b : Ring,a+1=b ∨ b+1=a → H.Adj (ring a) (ring b)
  wire : ∀ s i : Bool,H.Adj (ring (site s i)) (outer (p (s,i)))

private def put (k : Fin 4) (a b c : V) (x : Patch) : V⊕Fin 7 :=
  if r : x.val<6 then ring (route k ⟨x.val,r⟩)
  else if x=6 then outer a else if x=7 then outer b else outer c

@[simp] private theorem put0 (k : Fin 4) (a b c : V) :
    put k a b c 0 = ring (route k 0) := by
  rw [put,dif_pos (by decide : (0:Patch).val<6)]; rfl

@[simp] private theorem put1 (k : Fin 4) (a b c : V) :
    put k a b c 1 = ring (route k 1) := by
  rw [put,dif_pos (by decide : (1:Patch).val<6)]; rfl

@[simp] private theorem put2 (k : Fin 4) (a b c : V) :
    put k a b c 2 = ring (route k 2) := by
  rw [put,dif_pos (by decide : (2:Patch).val<6)]; rfl

@[simp] private theorem put3 (k : Fin 4) (a b c : V) :
    put k a b c 3 = ring (route k 3) := by
  rw [put,dif_pos (by decide : (3:Patch).val<6)]; rfl

@[simp] private theorem put4 (k : Fin 4) (a b c : V) :
    put k a b c 4 = ring (route k 4) := by
  rw [put,dif_pos (by decide : (4:Patch).val<6)]; rfl

@[simp] private theorem put5 (k : Fin 4) (a b c : V) :
    put k a b c 5 = ring (route k 5) := by
  rw [put,dif_pos (by decide : (5:Patch).val<6)]; rfl

@[simp] private theorem put6 (k : Fin 4) (a b c : V) :
    put k a b c 6 = outer a := by
  simp [put,show ¬(6:Patch).val<6 from by decide]

@[simp] private theorem put7 (k : Fin 4) (a b c : V) :
    put k a b c 7 = outer b := by
  simp [put,show ¬(7:Patch).val<6 from by decide]

@[simp] private theorem put8 (k : Fin 4) (a b c : V) :
    put k a b c 8 = outer c := by
  simp [put,show ¬(8:Patch).val<6 from by decide]

private theorem put_inj (k : Fin 4) {a b c : V} (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    Function.Injective (put k a b c) := by
  intro x y e
  by_cases h : x.val<6 <;> by_cases j : y.val<6
  · simp only [put,dif_pos h,dif_pos j] at e
    have ee : (ringMap V) (route k ⟨x.val,h⟩) = (ringMap V) (route k ⟨y.val,j⟩) := e
    exact Fin.ext (congrArg (fun z : Ring=>z.val) (route_injective k ((ringMap V).injective ee)))
  · simp only [put,dif_pos h,dif_neg j] at e
    split at e
    · exact Sum.noConfusion e
    · split at e <;> exact Sum.noConfusion e
  · simp only [put,dif_neg h,dif_pos j] at e
    split at e
    · exact Sum.noConfusion e
    · split at e <;> exact Sum.noConfusion e
  · have remain (z : Patch) (zv : ¬ z.val<6) : z=6∨z=7∨z=8 := by
      have eh : ∀ z : Patch, ¬ z.val<6 → z=6∨z=7∨z=8 := by decide
      exact eh z zv
    rcases remain x h with rfl|rfl|rfl <;> rcases remain y j with rfl|rfl|rfl
    all_goals
      simp only [put6,put7,put8,Sum.inl.injEq] at e
      first | rfl | contradiction | exact (ab e.symm).elim | exact (ac e.symm).elim | exact (bc e.symm).elim

private def emb (k : Fin 4) {a b c : V} (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    Patch↪(V⊕Fin 7) := ⟨put k a b c,put_inj k ab ac bc⟩

variable [DecidableEq V]

private theorem image_emb (k : Fin 4) {a b c : V} (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    (univ : Finset Patch).map (emb k ab ac bc) = allRing V ∪ {outer a,outer b,outer c} := by
  ext z
  constructor
  · intro hz
    obtain ⟨x,_,rfl⟩ := mem_map.mp hz
    by_cases hv : x.val<6
    · apply mem_union_left
      exact mem_map.mpr ⟨route k ⟨x.val,hv⟩,by simp,by simp [emb,put,hv,ringMap]⟩
    · have eh : ∀ x : Patch, ¬ x.val<6 → x=6∨x=7∨x=8 := by decide
      apply mem_union_right
      rcases eh x hv with rfl|rfl|rfl <;> simp [emb]
  · intro hz
    rcases mem_union.mp hz with left | right
    · obtain ⟨i,_,rfl⟩ := mem_map.mp left
      have surj := (Finite.injective_iff_bijective.mp (route_injective k)).2
      obtain ⟨j,hj⟩ := surj i
      let x : Patch := ⟨j.val,by have hl:=j.isLt; omega⟩
      exact mem_map.mpr ⟨x,by simp,by
        have lt : x.val<6 := j.isLt
        simpa [emb,put,lt,x,ringMap] using congrArg (ring (V:=V)) hj⟩
    · simp only [mem_insert,mem_singleton] at right
      rcases right with rfl|rfl|rfl
      · exact mem_map.mpr ⟨6,by simp,by simp [emb]⟩
      · exact mem_map.mpr ⟨7,by simp,by simp [emb]⟩
      · exact mem_map.mpr ⟨8,by simp,by simp [emb]⟩

private theorem cap_routed {H : SimpleGraph (V⊕Fin 7)} {p : Lane↪V}
    (d : Shape H p) (s i : Bool) (mode : Fin 3)
    {a b c : V} (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (wire : a=p (s,i))
    (extra :
      (mode=0 ∧ b=p ((!s),i) ∧ c=p ((!s),(!i))) ∨
      (mode=1 ∧ b=p ((!s),i) ∧ H.Adj (outer b) (outer c)) ∨
      (mode=2 ∧ b=p ((!s),(!i)) ∧ H.Adj (outer b) (outer c))) :
    FactorOn H (allRing V ∪ {outer a,outer b,outer c}) := by
  rw [←image_emb (atMode s i) ab ac bc]
  apply mapped_local_refill mode
  intro x y edge
  have e1 := (mode_site s i).1
  have e2 := (mode_site s i).2.1
  have e5 := (mode_site s i).2.2
  have r01 := d.cycle _ _ (cyclic_route (atMode s i) 0 1 (by decide))
  have r12 := d.cycle _ _ (cyclic_route (atMode s i) 1 2 (by decide))
  have r23 := d.cycle _ _ (cyclic_route (atMode s i) 2 3 (by decide))
  have r34 := d.cycle _ _ (cyclic_route (atMode s i) 3 4 (by decide))
  have r45 := d.cycle _ _ (cyclic_route (atMode s i) 4 5 (by decide))
  have r50 := d.cycle _ _ (cyclic_route (atMode s i) 5 0 (by decide))
  have w1 := d.wire s i
  rcases extra with ⟨rfl,bv,cv⟩|⟨rfl,bv,ext⟩|⟨rfl,bv,ext⟩
  · have w2 := d.wire (!s) i
    have w5 := d.wire (!s) (!i)
    simp [ThetaFiveTransferLocal.edges,ThetaFiveTransferLocal.ringEdges] at edge

    rcases edge with h|h|h|h|h|h|h|h|h
    all_goals
      have xx := h.1
      have yy := h.2
      subst x; subst y
      first
      | simpa [emb] using r01
      | simpa [emb] using r12
      | simpa [emb] using r23
      | simpa [emb] using r34
      | simpa [emb] using r45
      | simpa [emb] using r50
      | simpa [emb,e1,wire] using w1
      | simpa [emb,e2,bv] using w2
      | simpa [emb,e5,cv] using w5
  · have w2 := d.wire (!s) i
    simp [ThetaFiveTransferLocal.edges,ThetaFiveTransferLocal.ringEdges] at edge
    rcases edge with h|h|h|h|h|h|h|h|h
    all_goals
      have xx := h.1
      have yy := h.2
      subst x; subst y
      first
      | simpa [emb] using r01
      | simpa [emb] using r12
      | simpa [emb] using r23
      | simpa [emb] using r34
      | simpa [emb] using r45
      | simpa [emb] using r50
      | simpa [emb,e1,wire] using w1
      | simpa [emb,e2,bv] using w2
      | simpa [emb] using ext
  · have w5 := d.wire (!s) (!i)
    simp [ThetaFiveTransferLocal.edges,ThetaFiveTransferLocal.ringEdges] at edge
    rcases edge with h|h|h|h|h|h|h|h|h
    all_goals
      have xx := h.1
      have yy := h.2
      subst x; subst y
      first
      | simpa [emb] using r01
      | simpa [emb] using r12
      | simpa [emb] using r23
      | simpa [emb] using r34
      | simpa [emb] using r45
      | simpa [emb] using r50
      | simpa [emb,e1,wire] using w1
      | simpa [emb,e5,bv] using w5
      | simpa [emb] using ext

theorem refill_both_contacts {H : SimpleGraph (V⊕Fin 7)} {p : Lane↪V}
    (d : Shape H p) (s i : Bool) :
    FactorOn H (allRing V ∪
      {outer (p (s,i)),outer (p ((!s),i)),outer (p ((!s),(!i)) )}) := by
  have ss : s≠(!s) := by cases s <;> decide
  have ii : i≠(!i) := by cases i <;> decide
  exact cap_routed d s i 0 (fun h=>ss (congrArg Prod.fst (p.injective h)))
    (fun h=>ss (congrArg Prod.fst (p.injective h)))
    (fun h=>ii (congrArg Prod.snd (p.injective h))) rfl (Or.inl ⟨rfl,rfl,rfl⟩)

theorem refill_neighbor {H : SimpleGraph (V⊕Fin 7)} {p : Lane↪V}
    (d : Shape H p) (s i j : Bool) {w : V}
    (fresh : p (s,i)≠w)
    (e : H.Adj (outer (p ((!s),j))) (outer w)) :
    FactorOn H (allRing V ∪ {outer (p (s,i)),outer (p ((!s),j)),outer w}) := by
  have ss : s≠(!s) := by cases s <;> decide
  have ab : p (s,i)≠p ((!s),j) := fun h=>ss (congrArg Prod.fst (p.injective h))
  have bc : p ((!s),j)≠w := fun h=>e.ne (congrArg (outer (V:=V)) h)
  by_cases eq : j=i
  · subst j
    exact cap_routed d s i 1 ab fresh bc rfl (Or.inr (Or.inl ⟨rfl,rfl,e⟩))
  · have q : j=(!i) := by cases j <;> cases i <;> simp_all
    subst j
    exact cap_routed d s i 2 ab fresh bc rfl (Or.inr (Or.inr ⟨rfl,rfl,e⟩))

#print axioms refill_both_contacts
#print axioms refill_neighbor
end
end KelmansCactus.AtomicBridge.ThetaFiveRing
