import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteVacancyRails
open SquareCap (FactorOn IsTile HasFactor)
variable {V : Type*} [DecidableEq V]

theorem factor_single {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {S : Finset V} (h : IsTile G S) : FactorOn G S := by
  refine ⟨{S},?_,?_,by simp⟩
  · intro A ha
    obtain rfl := mem_singleton.mp ha
    exact h
  · intro A ha B hb ne
    exact (ne ((mem_singleton.mp ha).trans (mem_singleton.mp hb).symm)).elim

theorem factor_disjUnion {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {S T : Finset V} (hs : FactorOn G S) (ht : FactorOn G T)
    (d : Disjoint S T) : FactorOn G (S ∪ T) := by
  obtain ⟨P,p,q,r⟩ := hs
  obtain ⟨Q,u,v,w⟩ := ht
  have pq {A B : Finset V} (ha : A ∈ P) (hb : B ∈ Q) : Disjoint A B := by
    apply disjoint_left.mpr
    intro x xa xb
    exact disjoint_left.mp d (r ▸ mem_biUnion.mpr ⟨A,ha,xa⟩) (w ▸ mem_biUnion.mpr ⟨B,hb,xb⟩)
  refine ⟨P∪Q,?_,?_,?_⟩
  · intro A ha
    exact (mem_union.mp ha).elim (p A) (u A)
  · intro A ha B hb ne
    rcases mem_union.mp ha with hp|hq <;> rcases mem_union.mp hb with kp|kq
    · exact q A hp B kp ne
    · exact pq hp kq
    · exact (pq kp hq).symm
    · exact v A hq B kq ne
  · ext x
    rw [←r,←w,mem_union]
    constructor
    · intro hx
      obtain ⟨A,ha,hax⟩ := mem_biUnion.mp hx
      exact (mem_union.mp ha).elim (fun hp => Or.inl (mem_biUnion.mpr ⟨A,hp,hax⟩))
        (fun hq => Or.inr (mem_biUnion.mpr ⟨A,hq,hax⟩))
    · intro hx
      rcases hx with hp | hq
      · obtain ⟨A,ha,hm⟩ := mem_biUnion.mp hp
        exact mem_biUnion.mpr ⟨A,mem_union.mpr (Or.inl ha),hm⟩
      · obtain ⟨A,ha,hm⟩ := mem_biUnion.mp hq
        exact mem_biUnion.mpr ⟨A,mem_union.mpr (Or.inr ha),hm⟩


theorem tile_path (G : SimpleGraph V) {a b c : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (ac : a≠c) :
    IsTile G ({a,b,c}:Finset V) := by
  refine ⟨by simp [ab.ne,bc.ne,ac],b,by simp,?_⟩
  intro d ds db
  simp only [mem_insert,mem_singleton] at ds
  rcases ds with rfl|rfl|rfl
  · exact ab.symm
  · contradiction
  · exact bc

/-- Straight vacancy rail through vertex-disjoint P3 tiles. The rail
omits its incoming hole from its tile support and returns one
outgoing hole. The two inner vertices of each step form a genuine
edge; an arbitrary number of steps is allowed. -/
inductive Rail (G : SimpleGraph V) : V → V → Finset V → Prop
  | stop (h : V) : Rail G h h ∅
  | step {h a b c e : V} {K : Finset V}
      (ha : G.Adj h a) (ab : G.Adj a b) (bc : G.Adj b c)
      (hb : h≠b) (hc : h≠c) (ac : a≠c)
      (apart : Disjoint ({h,a,b,c}:Finset V) K)
      (tail : Rail G c e K) :
      Rail G h e (({a,b,c}:Finset V)∪K)

theorem Rail.rotate {G : SimpleGraph V} {h e : V} {S : Finset V}
    (rail : Rail G h e S) :
    h∉S ∧ e∈S∪{h} ∧ FactorOn G ((S∪{h})\{e}) := by
  induction rail with
  | stop h =>
    refine ⟨not_mem_empty _,by simp,?_⟩
    have no : ((∅:Finset V)∪{h})\{h}=∅ := by simp
    rw [no]
    exact ⟨∅,by simp,by simp,by simp⟩
  | @step h a b c e K ha ab bc hb hc ac apart tail ih =>
    obtain ⟨_,inside,pack⟩ := ih
    let T : Finset V := {h,a,b}
    let R : Finset V := K∪{c}
    have localApart : Disjoint T R := by
      rw [disjoint_left]
      intro x xt xr
      have t : x∈({h,a,b,c}:Finset V) := by
        simp only [T,mem_insert,mem_singleton] at xt ⊢
        tauto
      rcases mem_union.mp xr with kk|eq
      · exact disjoint_left.mp apart t kk
      · have last := mem_singleton.mp eq
        simp only [T,mem_insert,mem_singleton] at xt
        rcases xt with e1|e1|e1
        · exact hc (e1.symm.trans last)
        · exact ac (e1.symm.trans last)
        · exact bc.ne (e1.symm.trans last)
    have hOutside : h∉({a,b,c}:Finset V)∪K := by
      intro hm
      rcases mem_union.mp hm with ht|hk
      · simp [ha.ne,hb,hc] at ht
      · exact disjoint_left.mp apart (by simp) hk
    have joined : (({a,b,c}:Finset V)∪K)∪{h}=T∪R := by
      ext x
      simp only [T,R,mem_union,mem_insert,mem_singleton]
      tauto
    refine ⟨hOutside,by rw [joined]; exact mem_union_right _ inside,?_⟩
    rw [joined]
    have Re : e∈R := inside
    have eT : e∉T := fun et=>disjoint_left.mp localApart et Re
    have newPack := factor_disjUnion (factor_single (tile_path G ha ab hb)) pack
      (Disjoint.mono_right sdiff_subset localApart)
    have unionEq : T∪(R\{e})=(T∪R)\{e} := by
      ext x
      simp only [mem_union,mem_sdiff,mem_singleton]
      constructor
      · rintro (xt|⟨xr,nh⟩)
        · exact ⟨Or.inl xt,fun hx=>eT (hx ▸ xt)⟩
        · exact ⟨Or.inr xr,nh⟩
      · rintro ⟨(xt|xr),ne⟩
        · exact Or.inl xt
        · exact Or.inr ⟨xr,ne⟩
    change FactorOn G (T∪(R\{e})) at newPack
    rwa [unionEq] at newPack

#print axioms Rail.rotate
end KelmansCactus.AtomicBridge.RemoteVacancyRails
