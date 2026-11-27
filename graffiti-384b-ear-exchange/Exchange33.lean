import FrontierEar33

namespace Graffiti384b.EarExchange33
open Finset SimpleGraph CliquePivot33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- A minimum set from which its root can be exchanged for a new leaf. -/
def Exchange (a : V) (D : Finset V) : Prop :=
  TwoDominates H D ∧ D.card=gamma H ∧ a∈D ∧ nbr H a D=1 ∧
    ∀ v,v∉D → H.Adj v a → 3≤nbr H v D

omit [Fintype V] in
private theorem count_insert (a v : V) {S : Finset V} (out : a∉S) :
    nbr H v (insert a S)=nbr H v S + (if H.Adj v a then 1 else 0) := by
  classical
  unfold nbr
  by_cases edge : H.Adj v a
  · rw [filter_insert,if_pos edge,card_insert_of_not_mem (fun m => out (mem_filter.mp m).1),if_pos edge]
  · simp [filter_insert,edge]

/-- At equality in the half-order bound, an allowed saving at one root
is equivalent to a local condition in an ordinary minimum 2-dominating set. -/
theorem exchange_iff (a : V) (half : 2*gamma H=Fintype.card V) :
    (¬Tight H {a}) ↔ ∃ D,Exchange H a D := by
  classical
  constructor
  · intro notT
    unfold Tight at notT
    push_neg at notT
    obtain ⟨S,good,small⟩ := notT
    have ssmall : S.card<gamma H := by omega
    have notDom : ¬TwoDominates H S := fun h => (not_lt_of_ge (show gamma H≤S.card from Nat.sInf_le ⟨_,h,rfl⟩)) ssmall
    have other (v : V) (ne : v≠a) (out : v∉S) : 2≤nbr H v S := by
      simpa [ne] using good v out
    have aout : a∉S := by
      intro m
      exact notDom (fun v out => other v (fun eq => out (eq ▸ m)) out)
    have one : nbr H a S=1 := by
      have lo := good a aout
      simp at lo
      have hi : ¬2≤nbr H a S := by
        intro h
        apply notDom
        intro v out
        by_cases eq : v=a
        · exact eq ▸ h
        · exact other v eq out
      omega
    let D := insert a S
    have dom : TwoDominates H D := by
      intro v out
      have absent : v≠a ∧ v∉S := by simpa [D] using out
      exact (other v absent.1 absent.2).trans (by rw [show D=insert a S from rfl,count_insert H a v aout]; omega)
    have dcard : D.card=S.card+1 := card_insert_of_not_mem aout
    have low : gamma H≤D.card := Nat.sInf_le ⟨_,dom,rfl⟩
    refine ⟨D,dom,by omega,mem_insert_self ..,?_,?_⟩
    · rw [show D=insert a S from rfl,count_insert H a a aout,if_neg (H.loopless a),Nat.add_zero,one]
    · intro v out edge
      have h := other v edge.ne (fun m => out (mem_insert_of_mem m))
      rw [show D=insert a S from rfl,count_insert H a v aout,if_pos edge]
      omega
  · rintro ⟨D,dom,sz,m,one,protect⟩ tight
    let S := D.erase a
    have aout : a∉S := not_mem_erase a D 
    have recover : insert a S=D := insert_erase m
    have counts (v : V) := (congrArg (nbr H v) recover).symm.trans (count_insert H a v aout)
    have good : Relaxed H {a} S := by
      intro v out
      by_cases eq : v=a
      · subst v
        have count := counts a
        rw [if_neg (H.loopless a),Nat.add_zero] at count
        simp [← count,one] 
      · have vd : v∉D := fun vm => out (mem_erase.mpr ⟨eq,vm⟩)
        have cd := counts v
        by_cases edge : H.Adj v a
        · have h := protect v vd edge
          rw [if_pos edge] at cd
          simp [eq]; omega
        · have h := dom v vd
          rw [if_neg edge,Nat.add_zero] at cd
          simpa [eq,← cd]
    have lb := tight S good
    have changeSize : S.card=D.card-1 := card_erase_of_mem m
    have pos := card_pos.mpr (show D.Nonempty from ⟨a,m⟩)
    omega

end Graffiti384b.EarExchange33
#print axioms Graffiti384b.EarExchange33.exchange_iff
