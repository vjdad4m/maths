import FlankAttachment

namespace Graffiti199Depleted.PathOn

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {z : V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]
variable (p : PathOn G {v | v ≠ z})

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem before_adj_after (i : p.EdgePosition) : G.Adj (p.before i) (p.after i) := by
  have chain := p.chain
  rw [p.split_at_edge i,List.append_assoc] at chain
  exact chain.right_of_append.rel_head

omit [Fintype V] in
theorem before_mem_terminalFlanks (i : p.EdgePosition) (hi : G.Adj z (p.after i)) :
    p.before i ∈ p.terminalFlanks :=
  Finset.mem_insert_of_mem ((p.mem_predecessors).mpr ⟨i,hi,rfl⟩)

/-- With three independent neighbors of an omitted vertex, a predecessor
cannot be private to its own neighbor if that neighbor has no other
contact among the terminal flanks. -/
theorem predecessor_requires_other_contact (noTrace : ¬ Catalogue.Traceable G)
    (budget : Catalogue.treeNumber G ≤ 5) {k a b : V}
    (ka : k ≠ a) (kb : k ≠ b) (ab : a ≠ b)
    (zk : G.Adj z k) (za : G.Adj z a) (zb : G.Adj z b)
    (offKA : ¬ G.Adj k a) (offKB : ¬ G.Adj k b) (offAB : ¬ G.Adj a b)
    (i : p.EdgePosition) (ik : p.after i = k) :
    (∃ w ∈ p.terminalFlanks, w ≠ p.before i ∧ G.Adj w k) ∨
      G.Adj (p.before i) a ∨ G.Adj (p.before i) b := by
  classical
  by_cases shared : ∃ w ∈ p.terminalFlanks, w ≠ p.before i ∧ G.Adj w k
  · exact Or.inl shared
  · right
    by_contra no
    have offA : ¬ G.Adj (p.before i) a := fun h => no (Or.inl h)
    have offB : ¬ G.Adj (p.before i) b := fun h => no (Or.inr h)
    let pk := p.before i
    have pkW : pk ∈ p.terminalFlanks := p.before_mem_terminalFlanks i (ik.symm ▸ zk)
    have pkEdge : G.Adj pk k := ik ▸ p.before_adj_after i
    have onlyK (w : V) (hw : w ∈ p.terminalFlanks) (wk : G.Adj w k) : w = pk :=
      Classical.byContradiction fun h => shared ⟨w,hw,h,wk⟩
    obtain ⟨j,ja⟩ := p.neighbor_has_position noTrace za
    obtain ⟨l,lb⟩ := p.neighbor_has_position noTrace zb
    let pa := p.before j
    let pb := p.before l
    have firstSecond : pa ≠ pb := by
      intro eq
      have ij : j = l := p.before_injective eq
      exact ab (ja.symm.trans ((congrArg p.after ij).trans lb))
    have privateAt (v : V) (j : p.EdgePosition) (jv : p.after j = v)
        (ne : k ≠ v) (zv : G.Adj z v) (offKV : ¬ G.Adj k v)
        (offV : ¬ G.Adj pk v) :
        ∀ w ∈ p.terminalFlanks, G.Adj w v → w = p.before j := by
      let q := p.before j
      have pkq : pk ≠ q := by
        intro eq
        have eqj : i = j := p.before_injective eq
        exact ne (ik.symm.trans ((congrArg p.after eqj).trans jv))
      have qW : q ∈ p.terminalFlanks := p.before_mem_terminalFlanks j (jv.symm ▸ zv)
      have qAdj : G.Adj q v := jv ▸ p.before_adj_after j
      have qOffK : ¬ G.Adj q k := fun e => pkq (onlyK q qW e).symm
      intro w hw wv
      by_contra wrong
      have wNotPk : pk ≠ w := fun eq => offV (eq.symm ▸ wv)
      have agree := p.remaining_flank_agrees noTrace budget ne zk zv offKV pkW qW hw
        pkq wNotPk (Ne.symm wrong) (fun h => offV (h.mp pkEdge)) (fun h => qOffK (h.mpr qAdj))
      exact wNotPk (onlyK w hw (agree.mpr wv)).symm
    have privateA := privateAt a j ja ka za offKA offA
    have privateB := privateAt b l lb kb zb offKB offB
    have paW : pa ∈ p.terminalFlanks := p.before_mem_terminalFlanks j (ja.symm ▸ za)
    have pbW : pb ∈ p.terminalFlanks := p.before_mem_terminalFlanks l (lb.symm ▸ zb)
    have paEdge : G.Adj pa a := ja ▸ p.before_adj_after j
    have pbEdge : G.Adj pb b := lb ▸ p.before_adj_after l
    have pkpa : pk ≠ pa := fun eq => offA (Eq.mp (congrArg (fun w : V => G.Adj w a) eq.symm) paEdge)
    have pkpb : pk ≠ pb := fun eq => offB (Eq.mp (congrArg (fun w : V => G.Adj w b) eq.symm) pbEdge)
    let A : Finset V := {k,a,b}
    have size : A.card = 3 := by
      have off : k ∉ ({a,b} : Finset V) := by simp [ka,kb]
      change (insert k ({a,b} : Finset V)).card = 3
      rw [Finset.card_insert_of_not_mem off,Finset.card_pair ab]
    have sub : A ⊆ G.neighborFinset z := by
      intro x hx
      apply (G.mem_neighborFinset _ _).mpr
      rcases (show x = k ∨ x = a ∨ x = b by simpa [A] using hx) with rfl|rfl|rfl
      · exact zk
      · exact za
      · exact zb
    have ind (x : V) (hx : x ∈ A) (y : V) (hy : y ∈ A) : ¬ G.Adj x y := by
      rcases (show x = k ∨ x = a ∨ x = b by simpa [A] using hx) with xk|xa|xb <;>
        rcases (show y = k ∨ y = a ∨ y = b by simpa [A] using hy) with yk|ya|yb <;>
        subst x <;> subst y
      · exact G.loopless k
      · exact offKA
      · exact offKB
      · exact fun e => offKA e.symm
      · exact G.loopless a
      · exact offAB
      · exact fun e => offKB e.symm
      · exact fun e => offAB e.symm
      · exact G.loopless b
    have paUnique : pa ∈ p.uniqueAttachments A := (p.mem_uniqueAttachments _ _).mpr ⟨paW,by
      refine ⟨a,⟨by simp [A],paEdge⟩,?_⟩
      rintro w ⟨hw,e⟩
      rcases (show w = k ∨ w = a ∨ w = b by simpa [A] using hw) with rfl|rfl|rfl
      · exact (pkpa (onlyK pa paW e).symm).elim
      · rfl
      · exact (firstSecond (privateB pa paW e)).elim⟩
    have pbUnique : pb ∈ p.uniqueAttachments A := (p.mem_uniqueAttachments _ _).mpr ⟨pbW,by
      refine ⟨b,⟨by simp [A],pbEdge⟩,?_⟩
      rintro w ⟨hw,e⟩
      rcases (show w = k ∨ w = a ∨ w = b by simpa [A] using hw) with rfl|rfl|rfl
      · exact (pkpb (onlyK pb pbW e).symm).elim
      · exact (firstSecond (privateA pb pbW e).symm).elim
      · rfl⟩
    have two : 1 < (p.uniqueAttachments A).card :=
      Finset.one_lt_card.mpr ⟨pa,paUnique,pb,pbUnique,firstSecond⟩
    have cap := p.unique_attachment_bound noTrace budget A sub ind
    omega

#print axioms predecessor_requires_other_contact

end Graffiti199Depleted.PathOn
