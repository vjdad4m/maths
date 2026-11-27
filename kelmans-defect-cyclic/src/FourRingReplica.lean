import FourRingPhase
import ReplicaCyclicCut

open Finset SimpleGraph
namespace KelmansCactus.FourRingReplica
open ThreePort Substitute PathSlides FourRingBudget FourRingCap FourRingPhase
noncomputable section
variable {U J : Type*}

abbrev Piece (r : Bool→U) := {v : U // v≠r false ∧ v≠r true}
abbrev Host (J : Type*) (r : Bool→U) := J×Piece r

/-- The four distinct surviving neighbors of an adjacent root pair,
with two ordered ports at either root. -/
structure Layout (A : SimpleGraph U) (r : Bool→U) where
  rootEdge : A.Adj (r false) (r true)
  port : Slot ↪ Piece r
  conn : ∀ s,A.Adj (r s.1) (port s).val
  exactPort : ∀ b (v : Piece r), A.Adj (r b) v.val → ∃ c,port (b,c)=v

namespace Layout
variable {A : SimpleGraph U} {r : Bool→U}
variable (L : Layout A r)
variable (next : Equiv.Perm J)

def p (i : J) (s : Slot) : Host J r := (i,L.port s)

def mate (t : J×Slot) : J×Slot :=
  if t.2.1 then (next t.1,(false,t.2.2)) else (next.symm t.1,(true,t.2.2))

theorem mate_sq : Function.Involutive (mate next) := by
  rintro ⟨i,b,c⟩
  cases b <;> simp [mate]

def q (i : J) (s : Slot) : Host J r := L.p (mate next (i,s)).1 (mate next (i,s)).2

theorem port_inj_on_host : Function.Injective (fun t : J×Slot=>L.p t.1 t.2) := by
  intro x y e
  exact Prod.ext (congrArg (fun u : Host J r=>u.1) e)
    (L.port.injective (congrArg (fun u : Host J r=>u.2) e))

theorem mate_inj_on_host : Function.Injective (fun t : J×Slot=>L.q next t.1 t.2) :=
  L.port_inj_on_host.comp (mate_sq next).injective

theorem reverse_seam (i : J) (b : Bool) :
    L.p (next i) (false,b)=L.q next i (true,b) ∧
      L.q next (next i) (false,b)=L.p i (true,b) := by
  simp [q,mate]

theorem q_not_cell (fixed : ∀ i,next i≠i) (i : J) (s : Slot) :
    (L.q next i s).1≠i := by
  obtain ⟨b,c⟩ := s
  cases b
  · intro eq
    have e : next.symm i=i := eq
    have cancel := congrArg next e
    exact fixed i (by simpa using cancel.symm)
  · exact fixed i

def graph (fixed : ∀i,next i≠i) : SimpleGraph (Host J r) where
  Adj x y := (x.1=y.1 ∧ A.Adj x.2.val y.2.val) ∨
    ∃ s : J×Slot,L.p s.1 s.2=x ∧ L.q next s.1 s.2=y
  symm := by
    rintro x y (⟨e,adj⟩|⟨s,a,b⟩)
    · exact Or.inl ⟨e.symm,adj.symm⟩
    · exact Or.inr ⟨mate next s,b,by simpa only [q,mate_sq next s] using a⟩
  loopless := by
    rintro x (⟨_,adj⟩|⟨s,a,b⟩)
    · exact A.loopless _ adj
    · exact L.q_not_cell next fixed s.1 s.2 (congrArg Prod.fst (b.trans a.symm))

instance (fixed : ∀i,next i≠i) : DecidableRel (L.graph next fixed).Adj := Classical.decRel _

theorem internal {fixed : ∀i,next i≠i} {x y : Host J r} (same : x.1=y.1) :
    (L.graph next fixed).Adj x y ↔ A.Adj x.2.val y.2.val := by
  constructor
  · rintro (⟨_,a⟩|⟨s,ex,ey⟩)
    · exact a
    · exact (L.q_not_cell next fixed s.1 s.2
        ((congrArg Prod.fst ey).trans (same.symm.trans (congrArg Prod.fst ex).symm))).elim
  · exact fun a=>Or.inl ⟨same,a⟩

theorem graph_cross {fixed : ∀i,next i≠i} {x y : Host J r} (different : x.1≠y.1) :
    (L.graph next fixed).Adj x y ↔ ∃ s : J×Slot,L.p s.1 s.2=x ∧ L.q next s.1 s.2=y :=
  or_iff_right (fun h=>different h.1)

variable [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J]

def cell (i : J) : Finset (Host J r) := univ.filter (fun x=>x.1=i)

@[simp] theorem mem_cell {x : Host J r} {i : J} :
    x∈cell i ↔ x.1=i := by simp [cell]

theorem cellDisjoint : (↑(univ : Finset J) : Set J).PairwiseDisjoint (cell (r:=r)) := by
  intro i _ j _ ne
  apply disjoint_left.mpr
  intro x xi xj
  exact ne ((mem_cell.mp xi).symm.trans (mem_cell.mp xj))

theorem cellSeam (fixed : ∀i,next i≠i) (i : J) :
    Seam (G:=L.graph next fixed) (cell i) (L.p i) (L.q next i) := by
  refine ⟨fun _=>mem_cell.mpr rfl,fun s h=>L.q_not_cell next fixed i s (mem_cell.mp h),
    ?_,?_,?_⟩
  · intro a b e
    have t : (i,a)=(i,b) := L.port_inj_on_host e
    exact congrArg (fun t : J×Slot=>t.2) t
  · intro a b e
    have t : (i,a)=(i,b) := L.mate_inj_on_host next e
    exact congrArg (fun t : J×Slot=>t.2) t
  · intro x xi y yOut
    have xx := mem_cell.mp xi
    have diff : x.1≠y.1 := fun eq=>yOut (mem_cell.mpr (eq.symm.trans xx))
    rw [L.graph_cross next diff]
    constructor
    · rintro ⟨⟨k,s⟩,a,b⟩
      have eq : k=i := (congrArg Prod.fst a).trans xx
      exact ⟨s,eq ▸ a,eq ▸ b⟩
    · rintro ⟨s,a,b⟩
      exact ⟨(i,s),a,b⟩

include L in
omit [Fintype J] [DecidableEq J] in
theorem piece_card : Fintype.card (Piece r)=Fintype.card U-2 := by
  classical
  let S : Finset U := {r false,r true}
  have setEq (x : U) : (x≠r false ∧ x≠r true) ↔ x∉S := by simp [S]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight setEq),
    Fintype.card_subtype_compl (fun x=>x∈S),Fintype.card_coe]
  have s : S.card=2 := by simp [S,L.rootEdge.ne]
  rw [s]

include L in
omit [DecidableEq J] in
theorem host_card : Fintype.card (Host J r)=Fintype.card J*(Fintype.card U-2) := by
  rw [Fintype.card_prod,L.piece_card]

include L in
theorem cell_card (i : J) : (cell (r:=r) i).card=Fintype.card U-2 := by
  let e : Piece r ↪ Host J r := ⟨fun v=>(i,v),fun _ _ eq=>congrArg Prod.snd eq⟩
  have h : cell (r:=r) i=(univ:Finset (Piece r)).map e := by
    ext v
    rw [mem_cell]
    constructor
    · intro vi
      exact mem_map.mpr ⟨v.2,mem_univ _,Prod.ext vi.symm rfl⟩
    · rintro m
      obtain ⟨u,_,e⟩ := mem_map.mp m
      exact (congrArg Prod.fst e).symm
  rw [h,card_map,card_univ,L.piece_card]

#print axioms cellSeam
#print axioms host_card
end Layout
end
end KelmansCactus.FourRingReplica
