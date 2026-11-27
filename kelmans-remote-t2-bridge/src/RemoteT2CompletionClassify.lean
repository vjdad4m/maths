import RemoteT2PairCounts
import RemoteT2SideCompletionCuts

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteT2CompletionClassify
open SquareCap (SmallTrivial boundary)
open PentagonCap (SmallFourTrivial)
open RemoteT2PairCounts (extend innerCut row mismatch OutsideTwo extended_boundary outside_cut_balance extended_lower)
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
def OutsideThree (c : V→Bool) (x y : V) (b : Bool) : Prop :=
  ∃ u v w : V,u≠x∧u≠y∧v≠x∧v≠y∧w≠x∧w≠y∧u≠v∧u≠w∧v≠w∧c u=b∧c v=b∧c w=b

omit [DecidableRel G.Adj] in
private theorem lower_together (small : SmallFourTrivial G) (c : V→Bool)
    {x y : V} (s t : Bool) (st : s≠t) (two : OutsideTwo c x y s) (three : OutsideThree c x y t) :
    5≤(boundary G (extend c x y s s)).card := by
  by_contra! low
  obtain ⟨q,delete⟩ := small (extend c x y s s) (by omega)
  by_cases eq : q=s
  · subst q
    obtain ⟨a,b,ax,ay,bx,by',ab,ha,hb⟩ := two
    have ne := delete a b x (by simp [extend,ax,ay,ha]) (by simp [extend,bx,by',hb])
      (by simp [extend])
    exact ne.elim ab (fun z=>z.elim ax bx)
  · have qt : q=t := by cases q <;> cases s <;> cases t <;> simp_all
    subst q
    obtain ⟨a,b,d,ax,ay,bx,by',dx,dy,ab,ad,bd,ha,hb,hd⟩ := three
    exact (delete a b d (by simp [extend,ax,ay,ha]) (by simp [extend,bx,by',hb])
      (by simp [extend,dx,dy,hd])).elim ab (fun z=>z.elim ad bd)

omit [DecidableRel G.Adj] in
private theorem three_of_two_all (c : V→Bool) {x y : V}
    (sz : 7 ≤ Fintype.card V) (pos : OutsideTwo c x y true) (neg : OutsideTwo c x y false) :
    OutsideThree c x y true ∨ OutsideThree c x y false := by
  classical
  obtain ⟨a,b,ax,ay,bx,by',ab,ha,hb⟩ := pos
  obtain ⟨d,e,dx,dy,ex,ey,de,hd,he⟩ := neg
  let S : Finset V := {x,y,a,b,d,e}
  have ub : S.card≤6 := by
    dsimp [S]
    calc
      _ ≤ ({y,a,b,d,e} : Finset V).card+1 := Finset.card_insert_le _ _
      _ ≤ ({a,b,d,e} : Finset V).card+2 := by have := Finset.card_insert_le y ({a,b,d,e}:Finset V); omega
      _ ≤ ({b,d,e} : Finset V).card+3 := by have := Finset.card_insert_le a ({b,d,e}:Finset V); omega
      _ ≤ ({d,e} : Finset V).card+4 := by have := Finset.card_insert_le b ({d,e}:Finset V); omega
      _ ≤ ({e} : Finset V).card+5 := by have := Finset.card_insert_le d ({e}:Finset V); omega
      _ = 6 := by simp
  have lt : S.card < (Finset.univ : Finset V).card := by simp only [Finset.card_univ]; omega
  have ex : ∃ w : V, w∉S := by
    by_contra! all
    have eq : S=Finset.univ := by
      ext z
      simp [all z]
    rw [eq] at lt
    omega
  obtain ⟨w,hw⟩ := ex
  have nw : w≠x ∧ w≠y ∧ w≠a ∧ w≠b ∧ w≠d ∧ w≠e := by simpa [S] using hw
  cases cw : c w
  · exact Or.inr ⟨d,e,w,dx,dy,ex,ey,nw.1,nw.2.1,de,nw.2.2.2.2.1.symm,nw.2.2.2.2.2.symm,hd,he,cw⟩
  · exact Or.inl ⟨a,b,w,ax,ay,bx,by',nw.1,nw.2.1,ab,nw.2.2.1.symm,nw.2.2.2.1.symm,ha,hb,cw⟩

/-- Removing the marked adjacent pair in a cyclic-five graph of order at least seven
leaves at least three edges across every cut with at least two surviving vertices
on both shores. In particular, omitting one further edge cannot turn such a cut into
a bridge. -/
theorem cyclic_five_outside_cut_three (small : SmallTrivial G) (cyc5 : SmallFourTrivial G)
    (sz : 7 ≤ Fintype.card V) (c : V→Bool) {x y : V} (xy : G.Adj x y)
    (cx : G.degree x=3) (cy : G.degree y=3)
    (pos : OutsideTwo c x y true) (neg : OutsideTwo c x y false) :
    3≤(innerCut G c x y).card := by
  have k := outside_cut_balance G small c xy cx cy pos neg
  by_contra! low
  have eq : (innerCut G c x y).card=2 := by omega
  obtain ⟨xf,xt,yf,yt⟩ := k.2 eq
  rcases three_of_two_all c sz pos neg with T|F
  · have z := lower_together G cyc5 c false true (by decide) neg T
    rw [extended_boundary G c xy,eq,xf,yf] at z
    simp [mismatch] at z
  · have z := lower_together G cyc5 c true false (by decide) pos F
    rw [extended_boundary G c xy,eq,xt,yt] at z
    simp [mismatch] at z

private theorem row_zero_of_pair (c : V→Bool) {x y a b : V}
    (ports : (G.neighborFinset x).erase y={a,b}) (eq : c a=c b) :
    (row G c x y (c a)).card=0 := by
  unfold row
  rw [ports]
  have ex : ({a,b}:Finset V).filter (fun v=>c v≠c a)=∅ := by
    ext w
    simp only [mem_filter,mem_insert,mem_singleton,not_mem_empty,iff_false]
    rintro ⟨rfl|rfl,h⟩
    · exact h rfl
    · exact h eq.symm
  rw [ex,card_empty]

/-- Exact cut-count obstruction to the same-side completion in the cyclic-four
case. Every offending cut has surviving width three and splits x from y, with
neither of the two surviving port pairs split. The extended original cut then
has width four and crosses the marked edge xy. -/
theorem same_side_low_iff (small : SmallTrivial G) (c : V→Bool)
    {x y a b d e : V} (xy : G.Adj x y) (cx : G.degree x=3) (cy : G.degree y=3)
    (X : (G.neighborFinset x).erase y={a,b}) (Y : (G.neighborFinset y).erase x={d,e})
    (pos : OutsideTwo c x y true) (neg : OutsideTwo c x y false) :
    (innerCut G c x y).card+mismatch (c a) (c b)+mismatch (c d) (c e)≤3 ↔
      (innerCut G c x y).card=3 ∧ c a=c b ∧ c d=c e ∧ c a≠c d := by
  constructor
  · intro low
    have k := outside_cut_balance G small c xy cx cy pos neg
    have notTwo : (innerCut G c x y).card≠2 := by
      intro eq
      obtain ⟨xf,xt,yf,yt⟩ := k.2 eq
      have ab : c a≠c b := by
        intro same
        have z := row_zero_of_pair G c X same
        cases ea : c a <;> rw [ea] at z <;> omega
      have de : c d≠c e := by
        intro same
        have z := row_zero_of_pair G c Y same
        cases ed : c d <;> rw [ed] at z <;> omega
      simp [eq,mismatch,ab,de] at low
    have width : (innerCut G c x y).card=3 := by omega
    have ab : c a=c b := by
      by_contra h
      simp [width,mismatch,h] at low
      omega
    have de : c d=c e := by
      by_contra h
      simp [width,mismatch,ab,h] at low
    refine ⟨width,ab,de,?_⟩
    intro same
    have w := extended_lower G small c x y pos neg (c a) (c d)
    rw [extended_boundary G c xy,width,row_zero_of_pair G c X ab,row_zero_of_pair G c Y de] at w
    simp [mismatch,same] at w
  · rintro ⟨r,ab,de,_⟩
    simp [r,mismatch,ab,de]

theorem same_side_low_ext_width_four (small : SmallTrivial G) (c : V→Bool)
    {x y a b d e : V} (xy : G.Adj x y) (cx : G.degree x=3) (cy : G.degree y=3)
    (X : (G.neighborFinset x).erase y={a,b}) (Y : (G.neighborFinset y).erase x={d,e})
    (pos : OutsideTwo c x y true) (neg : OutsideTwo c x y false)
    (low : (innerCut G c x y).card+mismatch (c a) (c b)+mismatch (c d) (c e)≤3) :
    (boundary G (extend c x y (c a) (c d))).card=4 :=
  by
    obtain ⟨r,ab,de,ne⟩ := (same_side_low_iff G small c xy cx cy X Y pos neg).mp low
    rw [extended_boundary G c xy,r,row_zero_of_pair G c X ab,row_zero_of_pair G c Y de]
    simp [mismatch,ne]

#print axioms cyclic_five_outside_cut_three
#print axioms same_side_low_iff
#print axioms same_side_low_ext_width_four
end
end KelmansCactus.AtomicBridge.RemoteT2CompletionClassify
