import OddSquare28

namespace Graffiti384b.HighSquare28
open Finset SimpleGraph HighEar Core28 Four28
open private HighSquare28.absorb_cut from OddSquare28
open private Four28.ear_one Four28.core_data from FourFrontier28
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The fourth vertex s touches one cubic h. When both other contacts
r,t of h see s, a matching from the ear endpoints to r,t supplies the
second opposite neighbor of each pin. The other cubic must miss s. -/
theorem matched_saving {e a b s h k r t : V} (n : Fintype.card V=28)
    (pos : ∀ w,0<trianglesAt H w) (fi : Function.Injective (trianglesAt H))
    (ab : H.Adj a b) (en : H.neighborFinset e={a,b}) (sm : s∈additional H e a b)
    (scores : (trianglesAt H h=2 ∧ trianglesAt H k=3) ∨ (trianglesAt H h=3 ∧ trianglesAt H k=2))
    (ks : ¬H.Adj k s) (kdiff : k≠s) (hoff : h∉({e,a,b}:Finset V))
    (hs : H.Adj h s) (hr : H.Adj h r) (ht : H.Adj h t) (sr : H.Adj s r) (st : H.Adj s t)
    (rt : r≠t) (off : Disjoint ({a,b}:Finset V) {r,t}) (ar : H.Adj a r) (bt : H.Adj b t) : gamma H≤13 := by
  classical
  let A : Finset V := {h,a,b}
  let B : Finset V := {e,r,t}
  have ham : h≠a := fun eq => hoff (by simp [eq])
  have hbm : h≠b := fun eq => hoff (by simp [eq])
  have hem : h≠e := fun eq => hoff (by simp [eq])
  have ea : H.Adj e a := (H.mem_neighborFinset ..).mp (en ▸ mem_insert_self ..)
  have eb : H.Adj e b := (H.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  have no : ¬H.Adj e h := by
    intro ed
    exact hoff (mem_insert_of_mem (en ▸ (H.mem_neighborFinset ..).mpr ed))
  have er : e≠r := fun eq => no (eq.symm ▸ hr.symm)
  have et : e≠t := fun eq => no (eq.symm ▸ ht.symm)
  obtain ⟨se,as',bs⟩ := (additional_mem H).mp sm
  have lhs (w : V) (wa : H.Adj w a) (wb : H.Adj w b) : 2≤nbr H w A :=
    PinnedColor34.two H ab.ne wa wb (by simp [A]) (by simp [A])
  have rhs (w : V) (wr : H.Adj w r) (wt : H.Adj w t) : 2≤nbr H w B :=
    PinnedColor34.two H rt wr wt (by simp [B]) (by simp [B])
  have sep : Disjoint A B := by
    apply disjoint_left.mpr
    intro z za zb
    rcases mem_insert.mp za with zh|zpair
    · rw [zh] at zb
      rcases (show h=e ∨ h=r ∨ h=t by simpa [B] using zb) with k|k|k
      · exact hem k
      · exact hr.ne k
      · exact ht.ne k
    · rcases mem_insert.mp zb with ze|zrt
      · rw [ze] at zpair; simp [ea.ne,eb.ne] at zpair
      · exact disjoint_left.mp off zpair zrt
  have fr : EarFrame33.Frame H A B := by
    refine ⟨sep,?_,?_⟩
    · intro w wm
      rcases (show w=h ∨ w=a ∨ w=b by simpa [A] using wm) with wh|wa|wb
      · rw [wh]; exact rhs _ hr ht
      · rw [wa]; exact PinnedColor34.two H er ea.symm ar (by simp [B]) (by simp [B])
      · rw [wb]; exact PinnedColor34.two H et eb.symm bt (by simp [B]) (by simp [B])
    · intro w wm
      rcases (show w=e ∨ w=r ∨ w=t by simpa [B] using wm) with we|wr|wt
      · rw [we]; exact lhs _ ea eb
      · rw [wr]; exact PinnedColor34.two H ham hr.symm ar.symm (by simp [A]) (by simp [A])
      · rw [wt]; exact PinnedColor34.two H hbm ht.symm bt.symm (by simp [A]) (by simp [A])
  have so : s∉A∪B := by simp [A,B,hs.ne.symm,as'.ne.symm,bs.ne.symm,se,sr.ne,st.ne]
  apply HighSquare28.absorb_cut H n fr so kdiff (lhs s as'.symm bs.symm) (rhs s sr st) ?_ (Or.inl ks)
  intro w wm
  have we : w≠e := fun eq => wm (by simp [eq,B])
  have wh : w≠h := fun eq => wm (by simp [eq,A])
  have sear := Four28.ear_one H ab.ne en pos
  have n1 : trianglesAt H w≠1 := fun eq => we (fi (eq.trans sear.symm))
  have high := Repair.triangles_le_choose H w
  have pw := pos w
  have dg : 3≤H.degree w := by
    apply Nat.le_of_not_gt; intro low
    have cap := high.trans (Nat.choose_le_choose 2 (Nat.le_of_lt_succ low : H.degree w≤2))
    rw [Nat.choose_self] at cap; omega
  refine ⟨dg,?_⟩
  intro wk
  have eh : trianglesAt H w≠trianglesAt H h := fun eq => wh (fi eq)
  have ek : trianglesAt H w≠trianglesAt H k := fun eq => wk (fi eq)
  apply Nat.le_of_not_gt; intro low
  have cap := high.trans (Nat.choose_le_choose 2 (Nat.le_of_lt_succ low : H.degree w≤3))
  change trianglesAt H w≤3 at cap
  rcases scores with ⟨a,b⟩|⟨a,b⟩ <;> omega

/-- In the disjoint-cubic frontier this forbids a matching of the two
ear endpoints to the other two neighbors of a cubic touching s,
whenever those neighbors also touch s and are outside the endpoints. -/
theorem matching_restriction (ty : (types H).card=29) (nl : (nonleaves H).card=28) (bad : bound H<gamma H) :
    let J := triangleEdges (H.induce (nonleaves H:Set V))
    J.CliqueFree 5 → ∀ e a b s h k r t,J.Adj a b → J.neighborFinset e={a,b} →
    s∈additional J e a b →
    ((trianglesAt J h=2 ∧ trianglesAt J k=3) ∨ (trianglesAt J h=3 ∧ trianglesAt J k=2)) →
    Disjoint (J.neighborFinset h) (J.neighborFinset k) → h∉({e,a,b}:Finset _) →
    J.Adj h s → J.Adj h r → J.Adj h t → J.Adj s r → J.Adj s t → r≠t →
    Disjoint ({a,b}:Finset _) {r,t} → ¬(J.Adj a r ∧ J.Adj b t) := by
  classical
  dsimp only
  intro free e a b s h k r t ab en sm scores dis hoff hs hr ht sr st rt off pair
  let J := triangleEdges (H.induce (nonleaves H:Set V))
  obtain ⟨n,pos,fi,half,_⟩ := Four28.core_data H ty nl bad
  obtain ⟨_,_,_,hard,_⟩ := forced_pair H ty nl bad free e a b ab en
  have count := (hard s sm).2
  change 4≤trianglesAt J s at count
  change (trianglesAt J h=2 ∧ trianglesAt J k=3) ∨ (trianglesAt J h=3 ∧ trianglesAt J k=2) at scores
  have kd : k≠s := by intro eq; subst s; rcases scores with ⟨_,c⟩|⟨_,c⟩ <;> omega
  have ks : ¬J.Adj k s := fun adj => disjoint_left.mp dis ((J.mem_neighborFinset ..).mpr hs) ((J.mem_neighborFinset ..).mpr adj)
  exact (Nat.not_succ_le_self 13) (half.trans (matched_saving J n pos fi ab en sm scores ks kd hoff
    hs hr ht sr st rt off pair.1 pair.2))

/-- For the score-three cubic every pair of its neighbors is adjacent.
Hence the two remaining neighbors of v automatically touch s. -/
theorem full_cubic_matching (ty : (types H).card=29) (nl : (nonleaves H).card=28) (bad : bound H<gamma H) :
    let J := triangleEdges (H.induce (nonleaves H:Set V))
    J.CliqueFree 5 → ∀ e a b s u v,J.Adj a b → J.neighborFinset e={a,b} →
    s∈additional J e a b → trianglesAt J u=2 → J.degree v=3 → trianglesAt J v=3 →
    Disjoint (J.neighborFinset u) (J.neighborFinset v) → v∉({e,a,b}:Finset _) → J.Adj v s →
    let R := (J.neighborFinset v).erase s
    Disjoint ({a,b}:Finset _) R → ¬∃ r∈R,∃ t∈R,r≠t ∧ J.Adj a r ∧ J.Adj b t := by
  dsimp only
  intro free e a b s u v ab en sm su dv sv dis vo vs sep witness
  let J := triangleEdges (H.induce (nonleaves H:Set V))
  obtain ⟨r,rm,t,tm,rt,ar,bt⟩ := witness
  obtain ⟨rs,vr⟩ := mem_erase.mp rm
  obtain ⟨ts,vt⟩ := mem_erase.mp tm
  have vR := (J.mem_neighborFinset ..).mp vr
  have vT := (J.mem_neighborFinset ..).mp vt
  have sr := EarAnchor.full_neighbors J dv sv vs vR rs.symm
  have st := EarAnchor.full_neighbors J dv sv vs vT ts.symm
  exact matching_restriction H ty nl bad free e a b s v u r t ab en sm (Or.inr ⟨sv,su⟩) dis.symm
    vo vs vR vT sr st rt (sep.mono_right (insert_subset rm (singleton_subset_iff.mpr tm))) ⟨ar,bt⟩

end Graffiti384b.HighSquare28
#print axioms Graffiti384b.HighSquare28.matched_saving
#print axioms Graffiti384b.HighSquare28.matching_restriction
#print axioms Graffiti384b.HighSquare28.full_cubic_matching
