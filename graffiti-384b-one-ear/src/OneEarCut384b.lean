import Recolor34_384b
import LowSample384b

namespace Graffiti384b.OneEar
open Finset SimpleGraph LowSample
open private Repair.full_nbr from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Remove the three internal edges of the ear triangle. -/
def opened (K : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ¬(u∈K ∧ v∈K)
  symm := fun _ _ h => ⟨h.1.symm,fun both => h.2 both.symm⟩
  loopless := fun _ h => h.1.ne rfl

instance (K : Finset V) : DecidableRel (opened G K).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem separated {e a b : V} (only : twos G={e}) (q : (types G).card≤(nonleaves G).card)
    (ear : G.neighborFinset e={a,b}) (ab : G.Adj a b)
    (apart : ¬(opened G {e,a,b}).Reachable a b) : gamma G≤bound G := by
  classical
  let K : Finset V := {e,a,b}
  let H := opened G K
  have ea : G.Adj e a := (G.mem_neighborFinset _ _).mp (ear ▸ mem_insert_self ..)
  have eb : G.Adj e b := (G.mem_neighborFinset _ _).mp (ear ▸ mem_insert_of_mem (mem_singleton_self _))
  have ek : e∈K := mem_insert_self ..
  have ak : a∈K := mem_insert_of_mem (mem_insert_self ..)
  have bk : b∈K := mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  have iso {v : V} (edge : H.Adj e v) : False := by
    have vm := (G.mem_neighborFinset _ _).mpr edge.1
    rw [ear] at vm
    exact edge.2 ⟨ek,mem_insert_of_mem vm⟩
  obtain ⟨A,_,_,left,right⟩ := PinnedColor34.cut H ∅ ∅ (by simp)
  let opp (v : V) := if v∈A then Aᶜ else A
  have balance (v : V) : H.degree v ≤ 2*nbr H v (opp v) := by
    have total := Repair.full_nbr H v A
    by_cases va : v∈A
    · have h := left v va (by simp)
      simp only [opp,if_pos va]; omega
    · have h := right v (mem_compl.mpr va) (by simp)
      simp only [opp,if_neg va]; omega
  let ref (v : V) := if H.Reachable a v then a else b
  let S := univ.filter (fun v => v≠e ∧ (v∈A ↔ ref v∈A))
  have sm {v : V} : v∈S ↔ v≠e ∧ (v∈A ↔ ref v∈A) := by simp [S]
  have as' : a∈S := sm.mpr ⟨ea.ne.symm,by simp [ref,Reachable.refl]⟩
  have bs' : b∈S := sm.mpr ⟨eb.ne.symm,by simp [ref,apart,H,K]⟩
  have es : e∉S := fun m => (sm.mp m).1 rfl
  have across {u v : V} (adj : H.Adj u v) (ov : v∈opp u) : (v∈S ↔ u∉S) := by
    have ue : u≠e := fun eq => iso (eq ▸ adj)
    have ve : v≠e := fun eq => iso (eq ▸ adj.symm)
    have reach : H.Reachable a u ↔ H.Reachable a v :=
      ⟨fun r => r.trans adj.reachable,fun r => r.trans adj.symm.reachable⟩
    have fixed : ref u=ref v := by simp only [ref,reach]
    rw [sm,sm]
    simp only [ue,ve,true_and,fixed]
    by_cases ua : u∈A
    · have va : v∉A := mem_compl.mp (show v∈Aᶜ by simpa [opp,ua] using ov)
      simp [ua,va,ue,ve]
    · have va : v∈A := by simpa [opp,ua] using ov
      simp [ua,va,ue,ve]
  let outside (v : V) := if v∈S then Sᶜ else S
  have inc (v : V) : (opp v).filter (H.Adj v)⊆(outside v).filter (G.Adj v) := by
    intro i im
    obtain ⟨ic,vi⟩ := mem_filter.mp im
    apply mem_filter.mpr ⟨?_,vi.1⟩
    have h := across vi ic
    by_cases vs : v∈S <;> simp [outside,vs,h]
  have nonEar {v : V} (vn : v∈nonleaves G) (ve : v≠e) : 3≤G.degree v := by
    by_cases vh : v∈high G
    · exact (mem_filter.mp vh).2
    · have vm : v∈twos G := mem_sdiff.mpr ⟨vn,vh⟩
      exact (ve (mem_singleton.mp (only ▸ vm))).elim
  have atAnchor (v : V) (vn : v∈nonleaves G) (vs : v∈S) (ev : G.Adj e v) (vk : v∈K) :
      2≤nbr G v (outside v) := by
    have vd := nonEar vn ev.ne.symm
    have hd : 0<H.degree v := by
      apply Nat.pos_of_ne_zero
      intro zero
      have nc : (H.neighborFinset v).card=0 := by rw [card_neighborFinset_eq_degree]; omega
      have cover : G.neighborFinset v⊆K.erase v := by
        intro i im
        have vi := (G.mem_neighborFinset _ _).mp im
        apply mem_erase.mpr ⟨vi.ne.symm,?_⟩
        apply Classical.byContradiction
        intro out
        have edge : H.Adj v i := ⟨vi,fun both => out both.2⟩
        have bad := (H.mem_neighborFinset _ _).mpr edge
        rw [card_eq_zero.mp nc] at bad
        exact Finset.not_mem_empty _ bad
      have cap := card_le_card cover
      rw [card_neighborFinset_eq_degree,card_erase_of_mem vk] at cap
      have kc : K.card=3 := by simp [K,ea.ne,eb.ne,ab.ne]
      omega
    have bal := balance v
    obtain ⟨i,im⟩ := card_pos.mp (show 0<((opp v).filter (H.Adj v)).card by change 0<nbr H v (opp v); omega)
    have vi := (mem_filter.mp im).2
    have ie : i≠e := fun eq => iso (eq ▸ vi.symm)
    exact PinnedColor34.two G ie vi.1 ev.symm (mem_filter.mp (inc v im)).1 (by simp [outside,vs,es])
  have good (v : V) (vn : v∈nonleaves G) : 2≤nbr G v (outside v) := by
    by_cases ve : v=e
    · subst v
      simpa [outside,es] using PinnedColor34.two G ab.ne ea eb as' bs'
    by_cases va : v=a
    · subst v; exact atAnchor a vn as' ea ak
    by_cases vb : v=b
    · subst v; exact atAnchor b vn bs' eb bk
    have vk : v∉K := by simp [K,ve,va,vb]
    have eq : H.neighborFinset v = G.neighborFinset v := by
      ext i; simp [H,opened,vk]
    have de : H.degree v=G.degree v := by simpa only [card_neighborFinset_eq_degree] using congrArg Finset.card eq
    have min := nonEar vn ve
    have bal := balance v
    have low : 2 ≤ nbr H v (opp v) := by omega
    exact low.trans (card_le_card (inc v))
  exact PinnedColor34.both G S q (fun v vn vs => by simpa [outside,vs] using good v vn)
    (fun v vn vs => by simpa [outside,mem_compl.mp vs] using good v vn)
end Graffiti384b.OneEar
#print axioms Graffiti384b.OneEar.separated
