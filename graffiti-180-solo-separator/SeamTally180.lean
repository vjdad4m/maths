import PairSeparator180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
private theorem loss {X : Finset V} (c : ↥X) (D : Finset ↥X) (Z : Finset V)
    (all : ∀ v∈D, v=c ∧ c.val∈Z) : D.card ≤ weight c.val Z := by
  classical
  by_cases h : c.val∈Z
  · have le : D ⊆ {c} := fun v hv => mem_singleton.mpr (all v hv).1
    simpa [weight,h] using card_le_card le
  · have nil : D=∅ := eq_empty_iff_forall_not_mem.mpr (fun v hv => h (all v hv).2)
    simp [nil,weight,h]

/-- The leaf loss at an articulation is paid by its two marking indicators. -/
theorem seam_leaf_tally {c : V} {S T : Finset V} (s : Split G c S T) (hc : G.Connected)
    (r : ↥S) (P A : Finset V) :
    weightedLeaves (side G S) (eligible (pull (fun v : ↥S => v.val) A) (pull (fun v : ↥S => v.val) P) r) +
      weightedLeaves (side G T) (eligible (pull (fun v : ↥T => v.val) A) (pull (fun v : ↥T => v.val) P) ⟨c,s.both.2⟩) ≤
      weightedLeaves G (eligible A P r.val)+weight c A+weight c P := by
  classical
  let t : ↥T := ⟨c,s.both.2⟩
  let l : ↥S := ⟨c,s.both.1⟩
  let U := eligible A P r.val
  let L (F : Finset V) := pull (fun v : ↥S => v.val) F
  let R (F : Finset V) := pull (fun v : ↥T => v.val) F
  let E := eligible (L A) (L P) r
  let F := eligible (R A) (R P) t
  have offL (v : ↥S) (hv : v∈E) : v.val∈U := by
    rw [eligible_iff] at hv ⊢
    exact ⟨hv.1.imp mem_pull.mp mem_pull.mp,hv.2.imp (fun h eq => h (Subtype.ext eq))
      (fun h => ⟨mem_pull.mp h.1,mem_pull.mp h.2⟩)⟩
  have dl := restrict_leaves (side G S) E (L (U.erase c))
  have dr := restrict_leaves (side G T) F (R (U.erase c))
  have ll := loss l (E \ L (U.erase c)) (A ∪ P) (fun v hv => by
    obtain ⟨ve,no⟩ := mem_sdiff.mp hv
    have inU := offL v ve
    have eq : v.val=c := Classical.byContradiction (fun ne => no (mem_pull.mpr (mem_erase.mpr ⟨ne,inU⟩)))
    refine ⟨Subtype.ext eq,?_⟩
    change c∈A∪P
    rw [← eq]
    exact mem_union.mpr (eligible_iff.mp inU).1)
  have lr := loss t (F \ R (U.erase c)) (A ∩ P) (fun v hv => by
    obtain ⟨ve,no⟩ := mem_sdiff.mp hv
    have info := eligible_iff.mp ve
    have eq : v.val=c := by
      apply Classical.byContradiction
      intro ne
      have vr : v.val≠r.val := fun h => ne (s.common (h.symm ▸ r.property) v.property)
      apply no
      apply mem_pull.mpr
      apply mem_erase.mpr
      exact ⟨ne,eligible_iff.mpr ⟨info.1.imp mem_pull.mp mem_pull.mp,Or.inl vr⟩⟩
    have vt : v=t := Subtype.ext eq
    obtain ⟨a,p⟩ := info.2.resolve_left (not_not.mpr vt)
    exact ⟨vt,mem_inter.mpr ⟨mem_pull.mp a,mem_pull.mp p⟩⟩)
  have leaves := s.leaf_join hc U
  change weightedLeaves (side G S) (L (U.erase c))+weightedLeaves (side G T) (R (U.erase c)) ≤ _ at leaves
  have count : weight l.val (A ∪ P)+weight t.val (A ∩ P)=weight c A+weight c P := by
    by_cases a : c∈A <;> by_cases p : c∈P <;> simp [l,t,weight,a,p]
  change weightedLeaves (side G S) E + weightedLeaves (side G T) F ≤
    weightedLeaves G U+weight c A+weight c P
  omega

private def Proper (H : SimpleGraph V) (A : Finset V) (f : V → Bool) : Prop :=
  ∀ ⦃v w⦄, v∈A → w∈A → H.Adj v w → f v ≠ f w

omit [Fintype V] in
private theorem normalize {H : SimpleGraph V} {A : Finset V} (hc : TwoColor H A) (x : V) :
    ∃ f, f x = false ∧ Proper H A f := by
  classical
  obtain ⟨B,C,dis,rfl,ib,ic⟩ := hc
  let f (v : V) := decide (v∈B)
  have good : Proper H (B ∪ C) f := by
    intro v w hv hw e eq
    by_cases a : v∈B
    · have b : w∈B := by by_contra h; simp [f,a,h] at eq
      exact ib _ a _ b e.ne e
    · have b : w∉B := by intro h; simp [f,a,h] at eq
      exact ic _ ((mem_union.mp hv).resolve_left a) _ ((mem_union.mp hw).resolve_left b) e.ne e
  cases h : f x
  · exact ⟨f,h,good⟩
  · exact ⟨fun v => !(f v),by simp [h],fun {_ _} hv hw e eq => good hv hw e (Bool.not_inj eq)⟩

omit [Fintype V] in
private theorem color_of_proper {H : SimpleGraph V} {A : Finset V} {f : V → Bool} (ok : Proper H A f) :
    TwoColor H A := by
  classical
  refine ⟨A.filter (fun v => f v=false),A.filter (fun v => f v=true),?_,?_,?_,?_⟩
  · exact disjoint_left.mpr (fun v hv hk => Bool.false_ne_true ((mem_filter.mp hv).2.symm.trans (mem_filter.mp hk).2))
  · ext v; cases h : f v <;> simp [h]
  all_goals
    intro v hv w hw _ e
    exact ok (mem_filter.mp hv).1 (mem_filter.mp hw).1 e ((mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm)

/-- Glue arbitrary selected bipartite sets, retaining the seam only when
both sides selected it. The membership formula preserves common pins. -/
theorem seam_color {c : V} {S T : Finset V} (s : Split G c S T) (A : Finset ↥S) (B : Finset ↥T)
    (ha : TwoColor (side G S) A) (hb : TwoColor (side G T) B) :
    ∃ X : Finset V,TwoColor G X ∧ A.card+B.card≤X.card+1 ∧
      ∀ v,v∈X ↔ (v∈S → v∈push A) ∧ (v∈T → v∈push B) := by
  classical
  let l : ↥S := ⟨c,s.both.1⟩
  let t : ↥T := ⟨c,s.both.2⟩
  obtain ⟨f,fc,fa⟩ := normalize ha l
  obtain ⟨g,gc,gb⟩ := normalize hb t
  let F (v : V) := if v∈S then f (s.proj v) else g (s.flip.proj v)
  have fl (v : ↥S) : F v.val=f v := by simp only [F,if_pos v.property,s.proj_in]
  have fr (v : ↥T) : F v.val=g v := by
    by_cases vs : v.val∈S
    · have eq : v=t := Subtype.ext (s.common vs v.property)
      subst v
      rw [show F t.val=f l from fl l,fc,gc]
    · simp only [F,if_neg vs,s.flip.proj_in]
  let X := univ.filter (fun v => (v∈S → v∈push A) ∧ (v∈T → v∈push B))
  have ok : Proper G X F := by
    intro v w hv hw e
    have hv' := (mem_filter.mp hv).2
    have hw' := (mem_filter.mp hw).2
    rcases s.edges e with h|h
    · rw [fl ⟨v,h.1⟩,fl ⟨w,h.2⟩]
      exact fa ((in_push ⟨v,h.1⟩).mp (hv'.1 h.1)) ((in_push ⟨w,h.2⟩).mp (hw'.1 h.2)) e
    · rw [fr ⟨v,h.1⟩,fr ⟨w,h.2⟩]
      exact gb ((in_push ⟨v,h.1⟩).mp (hv'.2 h.1)) ((in_push ⟨w,h.2⟩).mp (hw'.2 h.2)) e
  refine ⟨X,color_of_proper ok,?_,fun v => by simp [X]⟩
  let D := (push A).erase c ∪ (push B).erase c
  have dX : D = X.erase c := by
    ext v
    by_cases ne : v=c
    · simp [D,ne]
    · have exclusive : v∈S → v∈T → False := fun h k => ne (s.common h k)
      rcases s.either v with h|h
      · have nt : v ∉ T := exclusive h
        have nb : v ∉ push B := fun k => nt (push_sub _ k)
        simp [D,X,ne,h,nt,nb]
      · have ns : v∉S := fun k => exclusive k h
        have na : v ∉ push A := fun k => ns (push_sub _ k)
        simp [D,X,ne,h,ns,na]
  have dcard := card_union_of_disjoint (s.trim_disj A B)
  change D.card = _ at dcard
  rw [dX] at dcard
  have a := card_trim (push A) c
  have b := card_trim (push B) c
  have z := card_trim X c
  rw [card_push] at a
  rw [card_push] at b
  have cx : c∈X ↔ c∈push A ∧ c∈push B := by simp [X,s.both.1,s.both.2]
  by_cases ca : c ∈ push A <;> by_cases cb : c ∈ push B <;>
    simp only [weight,cx,ca,cb,
      and_self,if_true,if_false,and_false,false_and] at a b z <;> omega

#print axioms seam_leaf_tally
#print axioms seam_color
end Minimal180.PairRepair
