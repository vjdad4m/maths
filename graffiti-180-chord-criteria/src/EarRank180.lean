import Exchange180

set_option warningAsError true
namespace Converse180
open Finset SimpleGraph Graffiti177 Rooted180
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
noncomputable def without (v : V) := within (TwoColor G) (univ.erase v)

omit [Fintype V] [DecidableEq V] in
private theorem ear_colored (N A : Finset V) (i : Indep G A) (f : Bool)
    (out : f=true → Disjoint A N) :
    Indep (ear G N) (A.disjSum (if f then univ else ∅)) := by
  classical
  rintro (v|v) hv (w|w) hw ne e
  · exact i _ (inl_mem_disjSum.mp hv) _ (inl_mem_disjSum.mp hw)
      (fun h => ne (congrArg Sum.inl h)) e
  · have on : f=true := by cases f <;> simp_all
    exact disjoint_left.mp (out on) (inl_mem_disjSum.mp hv) e
  · have on : f=true := by cases f <;> simp_all
    exact disjoint_left.mp (out on) (inl_mem_disjSum.mp hw) e
  · exact e.elim

private theorem lower_rank (x y : V) : without G x+1 ≤ bipartiteNum (ear G {x,y}) := by
  classical
  have empty : TwoColor G ∅ := ⟨∅,∅,by simp,by simp,by simp [Indep],by simp [Indep]⟩
  obtain ⟨S,hs,eq⟩ := exists_mem_eq_sup (s := (univ.erase x).powerset.filter (TwoColor G)) (f:=card)
    ⟨∅,mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),empty⟩⟩
  obtain ⟨sub,col⟩ := mem_filter.mp hs
  have out := mem_powerset.mp sub
  obtain ⟨A,B,dis,sel,ai,bi⟩ := col
  have xa : x ∉ A := fun h => (mem_erase.mp (out (sel ▸ mem_union_left B h))).1 rfl
  have xb : x ∉ B := fun h => (mem_erase.mp (out (sel ▸ mem_union_right A h))).1 rfl
  let f := decide (y ∉ A)
  have da : f=true → Disjoint A {x,y} := by
    intro h
    have ya : y ∉ A := of_decide_eq_true h
    exact disjoint_left.mpr (fun v va vn => by
      rcases mem_insert.mp vn with e|e
      · exact xa (e ▸ va)
      · exact ya ((mem_singleton.mp e) ▸ va))
  have db : (!f)=true → Disjoint B {x,y} := by
    intro h
    have ya : y ∈ A := by by_contra no; simp [f,no] at h
    exact disjoint_left.mpr (fun v vb vn => by
      rcases mem_insert.mp vn with e|e
      · exact xb (e ▸ vb)
      · exact disjoint_left.mp dis ya ((mem_singleton.mp e) ▸ vb))
  have one := ear_colored G {x,y} A ai f da
  have two := ear_colored G {x,y} B bi (!f) db
  have sep : Disjoint (A.disjSum (if f then (univ : Finset Unit) else ∅))
      (B.disjSum (if !f then univ else ∅)) := by
    apply disjoint_left.mpr
    rintro (v|v) hv kv
    · exact disjoint_left.mp dis (inl_mem_disjSum.mp hv) (inl_mem_disjSum.mp kv)
    · cases h : f <;> simp [h] at hv kv
  have b := bip_bound (ear G {x,y}) one two sep
  have count := card_union_of_disjoint dis
  rw [sel] at count
  change without G x=S.card at eq
  rw [eq,count]
  cases h : f <;> simpa [h,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using b

theorem triangle_rank_exchange (x y : V) (xy : G.Adj x y) :
    bipartiteNum (ear G {x,y}) = max (without G x) (without G y)+1 := by
  classical
  have lo := lower_rank G x y
  have hi := lower_rank G y x
  rw [show ({y,x}:Finset V)={x,y} from pair_comm _ _] at hi
  apply le_antisymm _ (by omega)
  apply Finset.sup_le
  intro S h
  let R := pull Sum.inl S
  let H := ear G {x,y}
  have col : TwoColor H S := (mem_filter.mp h).2
  have rest : TwoColor G R := restrict_color G H Sum.inl Sum.inl_injective (fun e => e) col
  have count := split_card S
  have one := card_le_univ (pull (Sum.inr : Unit → V ⊕ Unit) S)
  rw [Fintype.card_unit] at one
  have rank (v) (no : v ∉ R) : R.card ≤ without G v :=
    le_sup (f:=card) (mem_filter.mpr ⟨mem_powerset.mpr (fun t ht =>
      mem_erase.mpr ⟨fun e => no (e ▸ ht),mem_univ _⟩),rest⟩)
  by_cases z : Sum.inr () ∈ S
  · have forbidden : x ∉ R ∨ y ∉ R := by
      by_contra! both
      have xe := mem_pull.mp both.1
      have ye := mem_pull.mp both.2
      obtain ⟨A,B,dis,sel,ai,bi⟩ := col
      rw [← sel] at xe ye z
      have bad (K : Finset (V ⊕ Unit)) (ind : Indep H K) :
          ¬ (Sum.inl x ∈ K ∧ Sum.inl y ∈ K) ∧
          ¬ (Sum.inl x ∈ K ∧ Sum.inr () ∈ K) ∧
          ¬ (Sum.inl y ∈ K ∧ Sum.inr () ∈ K) := by
        refine ⟨fun h => ind _ h.1 _ h.2 (fun e => xy.ne (Sum.inl.inj e)) xy,
          fun h => ind _ h.1 _ h.2 (fun e => Sum.noConfusion e) ?_,
          fun h => ind _ h.1 _ h.2 (fun e => Sum.noConfusion e) ?_⟩
        · exact mem_insert_self _ _
        · exact mem_insert_of_mem (mem_singleton_self _)
      have a := bad A ai
      have b := bad B bi
      simp only [mem_union] at xe ye z
      rcases xe with ha|ha <;> rcases ye with hb|hb <;> rcases z with hz|hz
      all_goals first | exact a.1 ⟨ha,hb⟩ | exact b.1 ⟨ha,hb⟩ |
        exact a.2.1 ⟨ha,hz⟩ | exact b.2.1 ⟨ha,hz⟩ |
        exact a.2.2 ⟨hb,hz⟩ | exact b.2.2 ⟨hb,hz⟩
    change S.card=R.card+_ at count
    rcases forbidden with nx|ny
    · have := rank x nx; omega
    · have := rank y ny; omega
  · have empty : pull (Sum.inr : Unit → V ⊕ Unit) S = ∅ := by
      ext v; cases v; simpa using z
    rw [empty,card_empty,Nat.add_zero] at count
    have base : R.card ≤ bipartiteNum G := le_sup (f:=card) (mem_filter.mpr ⟨mem_univ _,rest⟩)
    have rem := restrict_bipartite G (univ.erase x)
    have one' : (univ : Finset V) \ univ.erase x = {x} := by ext v; simp
    rw [one',card_singleton] at rem
    change bipartiteNum G ≤ without G x+1 at rem
    change S.card=R.card at count
    omega

#print axioms triangle_rank_exchange
end Converse180
