import CleanFinish
namespace Graffiti384b.LeafPath
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Delete a leaf and its degree-two neighbor at exact cost one, with the
other endpoint required in the remaining 2-dominating set. -/
theorem deletion {l e b : V} (leaf : G.neighborFinset l={e}) (ear : G.neighborFinset e={l,b})
    (lb : l≠b) (k : ℕ) :
    gamma G≤k+1 ↔ ∃ R : Finset V,R⊆({l,e}:Finset V)ᶜ ∧ b∈R ∧ R.card≤k ∧
      ∀ w∈({l,e}:Finset V)ᶜ,w∉R → 2≤nbr G w R := by
  classical
  have le : G.Adj l e := (G.mem_neighborFinset ..).mp (leaf ▸ mem_singleton_self _)
  have eb : G.Adj e b := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_of_mem (mem_singleton_self _))
  have one : G.degree l=1 := by rw [←card_neighborFinset_eq_degree,leaf,card_singleton]
  constructor
  · intro upper
    have available : {j : ℕ | ∃ D, TwoDominates G D ∧ D.card=j}.Nonempty := ⟨_,univ,by simp [TwoDominates],rfl⟩
    obtain ⟨D,dom,dsize⟩ := Nat.sInf_mem available
    change D.card=gamma G at dsize
    have lm : l∈D := by
      by_contra off
      have d := dom l off
      have cap := card_le_card (show D.filter (G.Adj l)⊆G.neighborFinset l from fun _ m => (G.mem_neighborFinset ..).mpr (mem_filter.mp m).2)
      rw [card_neighborFinset_eq_degree,one] at cap; change nbr G l D≤1 at cap; omega
    have cover : b∈D ∨ e∈D := by
      by_cases bm : b∈D
      · exact Or.inl bm
      right; by_contra off
      have small : D.filter (G.Adj e)⊆{l} := by
        intro i im
        have nm := (G.mem_neighborFinset ..).mpr (mem_filter.mp im).2
        rw [ear,mem_insert,mem_singleton] at nm
        exact mem_singleton.mpr (nm.resolve_right (fun z => bm (z ▸ (mem_filter.mp im).1)))
      have cap := card_le_card small
      rw [card_singleton] at cap
      have d := dom e off
      change nbr G e D≤1 at cap; omega
    let S := (D.erase l).erase e
    let R := insert b S
    have inc : R⊆({l,e}:Finset V)ᶜ := by
      intro i im; rcases mem_insert.mp im with rfl|m
      · simp [lb.symm,eb.ne.symm]
      · have ie := (mem_erase.mp m).1
        have il := (mem_erase.mp (mem_erase.mp m).2).1
        simp [ie,il]
    refine ⟨R,inc,mem_insert_self ..,?_,?_⟩
    · have del := card_erase_of_mem lm
      rcases cover with bm|em
      · have bs : b∈S := mem_erase.mpr ⟨eb.ne.symm,mem_erase.mpr ⟨lb.symm,bm⟩⟩
        have sub : S⊆D.erase l := erase_subset ..
        have sc := card_le_card sub
        dsimp only [R]; rw [insert_eq_of_mem bs]; omega
      · have ee : e∈D.erase l := mem_erase.mpr ⟨le.ne.symm,em⟩
        have sc : S.card=(D.erase l).card-1 := card_erase_of_mem ee
        have rc : R.card≤S.card+1 := card_insert_le ..
        have ep := card_pos.mpr (show (D.erase l).Nonempty from ⟨e,ee⟩)
        omega
    · intro w wc out
      have wl : w≠l := fun eq => mem_compl.mp wc (eq ▸ mem_insert_self ..)
      have we : w≠e := fun eq => mem_compl.mp wc (eq ▸ mem_insert_of_mem (mem_singleton_self _))
      have wb : w≠b := fun eq => out (eq ▸ mem_insert_self ..)
      have wd : w∉D := fun wm => out (mem_insert_of_mem (mem_erase.mpr ⟨we,mem_erase.mpr ⟨wl,wm⟩⟩))
      apply (dom w wd).trans (card_le_card ?_)
      intro i im
      obtain ⟨id',wi⟩ := mem_filter.mp im
      apply mem_filter.mpr; refine ⟨mem_insert_of_mem (mem_erase.mpr ⟨?_,mem_erase.mpr ⟨?_,id'⟩⟩),wi⟩
      · rintro rfl
        have nm := (G.mem_neighborFinset ..).mpr wi.symm
        rw [ear,mem_insert,mem_singleton] at nm; exact nm.elim wl wb
      · rintro rfl
        have nm := (G.mem_neighborFinset ..).mpr wi.symm
        rw [leaf,mem_singleton] at nm; exact we nm
  · rintro ⟨R,_,br,sz,ok⟩
    let D := insert l R
    have dom : TwoDominates G D := by
      intro w out
      by_cases we : w=e
      · subst w
        have inc : ({l,b}:Finset V)⊆D.filter (G.Adj e) :=
          insert_subset (mem_filter.mpr ⟨mem_insert_self ..,le.symm⟩)
            (singleton_subset_iff.mpr (mem_filter.mpr ⟨mem_insert_of_mem br,eb⟩))
        simpa only [card_pair lb] using card_le_card inc
      · have wl : w≠l := fun eq => out (eq ▸ mem_insert_self ..)
        exact (ok w (by simp [wl,we]) (fun wm => out (mem_insert_of_mem wm))).trans
          (card_le_card (filter_subset_filter _ (subset_insert ..)))
    have opt := Nat.sInf_le (s:={j : ℕ | ∃ D,TwoDominates G D ∧ D.card=j}) ⟨D,dom,rfl⟩
    exact opt.trans ((card_insert_le ..).trans (Nat.add_le_add_right sz 1))
end Graffiti384b.LeafPath
#print axioms Graffiti384b.LeafPath.deletion
