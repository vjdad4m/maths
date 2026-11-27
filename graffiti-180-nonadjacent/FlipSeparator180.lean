import PairTests180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [DecidableEq V]

/-- Paths confined to S, including paths of length zero. -/
def Joined (G : SimpleGraph V) (S : Finset V) (x y : V) : Prop :=
  ∃ xm : x∈S,∃ ym : y∈S,(side G S).Reachable ⟨x,xm⟩ ⟨y,ym⟩

omit [DecidableEq V] in
theorem joined_self (G : SimpleGraph V) (S : Finset V) {x : V} (xm : x∈S) : Joined G S x x :=
  ⟨xm,xm,Reachable.refl _⟩

omit [DecidableEq V] in
theorem joined_step (G : SimpleGraph V) (S : Finset V) {x y z : V} (path : Joined G S x y)
    (zm : z∈S) (ed : G.Adj y z) : Joined G S x z := by
  obtain ⟨xm,ym,h⟩ := path
  exact ⟨xm,zm,h.trans (Adj.reachable (G:=side G S) (u:=⟨y,ym⟩) (v:=⟨z,zm⟩) ed)⟩

omit [DecidableEq V] in
theorem joined_constant (G : SimpleGraph V) (S : Finset V) (s : V→Bool)
    (same : ∀ x∈S,∀ y∈S,G.Adj x y → s x=s y) {x y : V} (h : Joined G S x y) : s x=s y := by
  obtain ⟨xm,ym,⟨w⟩⟩ := h
  have equal {u v : ↥S} (p : (side G S).Walk u v) : s u.val=s v.val := by
    induction p with
    | nil => rfl
    | @cons u v _ ed _ ih => exact (same u.val u.property v.val v.property ed).trans ih
  exact equal w

/-- A surviving outside vertex requests precisely the flip that makes
its color different from the designated color of a retained endpoint. -/
def Demand (G : SimpleGraph V) (T : Finset V) (c d : V→Bool) (w : Bool) (x : V) : Prop :=
  ∃ t∈T,G.Adj t x ∧ (c x == d t)=w

def Compatible (G : SimpleGraph V) (S T : Finset V) (c d : V→Bool) : Prop :=
  ∀ x y,Demand G T c d true x → Demand G T c d false y → ¬Joined G S x y

private theorem flipped_edge {cx cy dx dy : Bool} (cc : cx≠cy) (dd : dx≠dy) :
    (cx != dx)=(cy != dy) := by cases cx <;> cases cy <;> cases dx <;> cases dy <;> simp_all

private theorem opposite {a b v : Bool} (diff : b≠v) : (a != v)=(a == b) := by
  cases a <;> cases b <;> cases v <;> simp_all

/-- An exact test for extending a fixed proper coloring of S up to
independent flips in the surviving components. Endpoint colors are fixed.
A common neighbor can witness an incompatibility by a length-zero path. -/
theorem extension_iff (G : SimpleGraph V) (S T : Finset V) (c d : V→Bool)
    (dis : Disjoint S T) (old : ProperOn G S c) (tips : ProperOn G T d) :
    (∃ e,ProperOn G (S∪T) e ∧ ∀ t∈T,e t=d t) ↔ Compatible G S T c d := by
  classical
  constructor
  · rintro ⟨e,ok,agree⟩ x y ⟨a,atp,ax,pos⟩ ⟨b,bt,by',neg⟩ path
    have xs := path.choose
    have ys := path.choose_spec.choose
    have fixed := joined_constant G S (fun v => c v != e v)
      (fun i im j jm ij => flipped_edge (old i im j jm ij) (ok i (mem_union_left _ im) j (mem_union_left _ jm) ij)) path
    have first := ok a (mem_union_right _ atp) x (mem_union_left _ xs) ax
    have last := ok b (mem_union_right _ bt) y (mem_union_left _ ys) by'
    rw [agree a atp] at first
    rw [agree b bt] at last
    change (c x != e x)=(c y != e y) at fixed
    rw [opposite first,opposite last,pos,neg] at fixed
    contradiction
  · intro compat
    let flip (x : V) : Bool := decide (∃ z,Demand G T c d true z ∧ Joined G S z x)
    have sync (x : V) (xm : x∈S) (y : V) (ym : y∈S) (ed : G.Adj x y) : flip x=flip y := by
      have iff : (∃ z,Demand G T c d true z ∧ Joined G S z x) ↔
          ∃ z,Demand G T c d true z ∧ Joined G S z y := by
        constructor <;> rintro ⟨z,force,path⟩
        · exact ⟨z,force,joined_step G S path ym ed⟩
        · exact ⟨z,force,joined_step G S path xm ed.symm⟩
      simp only [flip,iff]
    let e (x : V) := if x∈T then d x else if flip x then !(c x) else c x
    have cross (x : V) (xm : x∈S) (t : V) (tm : t∈T) (ed : G.Adj t x) : e t≠e x := by
      have xt := disjoint_left.mp dis xm
      by_cases eq : c x=d t
      · have force : Demand G T c d true x := ⟨t,tm,ed,by simp [eq]⟩
        have hit : flip x=true := decide_eq_true ⟨x,force,joined_self G S xm⟩
        simp [e,tm,xt,hit,eq]
      · have force : Demand G T c d false x := ⟨t,tm,ed,by cases h : c x <;> cases k : d t <;> simp_all⟩
        have miss : flip x=false := decide_eq_false (fun ⟨z,yes,path⟩ => compat z x yes force path)
        simpa [e,tm,xt,miss] using Ne.symm eq
    refine ⟨e,?_,fun t tm => by simp [e,tm]⟩
    intro x xm y ym ed
    rcases mem_union.mp xm with xs|xt <;> rcases mem_union.mp ym with ys|yt
    · have fx := sync x xs y ys ed
      have diff := old x xs y ys ed
      have nx := disjoint_left.mp dis xs
      have ny := disjoint_left.mp dis ys
      cases h : flip y <;> simpa [e,nx,ny,fx,h] using diff
    · exact (cross x xs y yt ed.symm).symm
    · exact cross y ys x xt ed
    · simpa [e,xt,yt] using tips x xt y yt ed

#print axioms joined_constant
#print axioms extension_iff
end Minimal180.PairRepair
