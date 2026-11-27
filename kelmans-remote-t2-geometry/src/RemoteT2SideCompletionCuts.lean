import RemoteT2PairCounts
import PentagonCap

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteT2SideCompletionCuts
open SquareCap (SmallTrivial boundary)
open PentagonCap (SmallFourTrivial)
open RemoteT2PairCounts (extend innerCut row mismatch OutsideTwo extended_boundary outside_cut_balance extended_lower)
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
private theorem mixed_lower (small : SmallFourTrivial G) (c : V→Bool)
    {x y : V} (xy : x≠y) (pos : OutsideTwo c x y true) (neg : OutsideTwo c x y false)
    {a b : Bool} (split : a≠b) :
    5≤(boundary G (extend c x y a b)).card := by
  by_contra! low
  obtain ⟨q,delete⟩ := small (extend c x y a b) (by omega)
  have old : OutsideTwo c x y q := by cases q <;> assumption
  obtain ⟨u,v,ux,uy,vx,vy,uv,hu,hv⟩ := old
  have existsK : ∃ z : V,(z=x∨z=y)∧extend c x y a b z=q := by
    by_cases aq : a=q
    · exact ⟨x,Or.inl rfl,by simp [extend,aq]⟩
    · have bq : b=q := by cases a <;> cases b <;> cases q <;> simp_all
      exact ⟨y,Or.inr rfl,by simp [extend,xy.symm,bq]⟩
  obtain ⟨z,hz,same⟩ := existsK
  have uz : u≠z := hz.elim (fun e=>e.symm ▸ ux) (fun e=>e.symm ▸ uy)
  have vz : v≠z := hz.elim (fun e=>e.symm ▸ vx) (fun e=>e.symm ▸ vy)
  have choose := delete u v z (by simp [extend,ux,uy,hu]) (by simp [extend,vx,vy,hv]) same
  exact choose.elim uv (fun h=>h.elim uz vz)

private theorem same_color_gives_empty_row (c : V→Bool) {x y a b : V}
    (ports : (G.neighborFinset x).erase y={a,b}) (eq : c a=c b) :
    (row G c x y (c a)).card=0 := by
  unfold row
  rw [ports]
  have e : ({a,b}:Finset V).filter (fun v=>c v≠c a)=∅ := by
    ext w
    simp only [mem_filter,mem_insert,mem_singleton,not_mem_empty,iff_false]
    rintro ⟨rfl|rfl,h⟩
    · exact h rfl
    · exact h eq.symm
  rw [e,card_empty]

/-- This is the precise lower bound for homotopically deleting an
adjacent edge in a cyclic-five graph: the two replacement edges join
the two surviving neighbors of x and, separately, those of y. For
any two-sided nontrivial surviving cut, the repaired width is ≥4. -/
theorem same_side_completion_cut (small : SmallTrivial G) (cyc5 : SmallFourTrivial G)
    (c : V→Bool) {x y a b d e : V} (xy : G.Adj x y) (cx : G.degree x=3) (cy : G.degree y=3)
    (X : (G.neighborFinset x).erase y={a,b}) (Y : (G.neighborFinset y).erase x={d,e})
    (pos : OutsideTwo c x y true) (neg : OutsideTwo c x y false) :
    4≤(innerCut G c x y).card+mismatch (c a) (c b)+mismatch (c d) (c e) := by
  have balanced := outside_cut_balance G small c xy cx cy pos neg
  by_cases exactly : (innerCut G c x y).card=2
  · have h := balanced.2 exactly
    have ab : c a≠c b := by
      intro eq
      have z := same_color_gives_empty_row G c X eq
      cases ea : c a <;> rw [ea] at z
      · omega
      · omega
    have de : c d≠c e := by
      intro eq
      have z := same_color_gives_empty_row G c Y eq
      cases ed : c d <;> rw [ed] at z
      · omega
      · omega
    simp [exactly,mismatch,ab,de]
  · by_cases lo : 4≤(innerCut G c x y).card
    · omega
    · by_cases ab : c a=c b
      · by_cases de : c d=c e
        · have xZero := same_color_gives_empty_row G c X ab
          have yZero := same_color_gives_empty_row G c Y de
          by_cases same : c a=c d
          · have w := extended_lower G small c x y pos neg (c a) (c d)
            rw [extended_boundary G c xy,xZero,yZero] at w
            simp [mismatch,same] at w
            omega
          · have w := mixed_lower G cyc5 c xy.ne pos neg same
            rw [extended_boundary G c xy,xZero,yZero] at w
            simp [mismatch,same] at w
            omega
        · have n : mismatch (c d) (c e)=1 := by simp [mismatch,de]
          omega
      · have n : mismatch (c a) (c b)=1 := by simp [mismatch,ab]
        omega

#print axioms same_side_completion_cut
end
end KelmansCactus.AtomicBridge.RemoteT2SideCompletionCuts
