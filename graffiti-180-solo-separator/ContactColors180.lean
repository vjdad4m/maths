import ComponentPorts180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [DecidableEq V]

/-- Constant terminal contacts in a proper coloring determine one
feasible relative color, even when the part is disconnected. -/
theorem contact_color (G : SimpleGraph V) (a b : V) (ab : a≠b) (na : ¬G.Adj a b)
    (S : Finset V) (ao : a∉S) (bo : b∉S) (c : V→Bool) (cp : ProperOn G S c) (i j : Bool)
    (ac : ∀ x∈S,G.Adj a x → c x=i) (bc : ∀ x∈S,G.Adj b x → c x=j) :
    TerminalColor G a b S (j==i) := by
  classical
  let e (x : V) := if x=a then true else if x=b then (j==i) else (c x != i)
  have ea : e a=true := by simp [e]
  have eb : e b=(j==i) := by simp [e,ab.symm]
  have es (x : V) (xm : x∈S) : e x=(c x != i) := by
    have xa : x≠a := fun h => ao (h ▸ xm)
    have xb : x≠b := fun h => bo (h ▸ xm)
    simp [e,xa,xb]
  have ax (x : V) (xm : x∈S) (ed : G.Adj a x) : e a≠e x := by rw [ea,es x xm,ac x xm ed];simp
  have bx (x : V) (xm : x∈S) (ed : G.Adj b x) : e b≠e x := by
    rw [eb,es x xm,bc x xm ed];cases j <;> cases i <;> decide
  refine ⟨e,?_,ea,eb⟩
  intro x xm y ym ed
  have classify (z : V) (zm : z∈({a,b}:Finset V)∪S) : z=a ∨ z=b ∨ z∈S := by
    simpa only [mem_union,mem_insert,mem_singleton,or_assoc] using zm
  rcases classify x xm with rfl|rfl|xs <;> rcases classify y ym with rfl|rfl|ys
  · exact (ed.ne rfl).elim
  · exact (na ed).elim
  · exact ax y ys ed
  · exact (na ed.symm).elim
  · exact (ed.ne rfl).elim
  · exact bx y ys ed
  · exact (ax x xs ed.symm).symm
  · exact (bx x xs ed.symm).symm
  · rw [es x xs,es y ys]
    have no := cp x xs y ys ed
    cases h : c x <;> cases k : c y <;> cases i <;> simp_all

/-- If the other tip sees a monochromatic part, either relative tip
color can be realized. Delete the appropriate one of the center's two
oppositely colored neighbors and keep every other vertex of the part. -/
theorem flexible_contact (G : SimpleGraph V) (a b : V) (ab : a≠b) (na : ¬G.Adj a b)
    (C K : Finset V) (ao : a∉C) (bo : b∉C) (c : V→Bool) (cp : ProperOn G C c)
    (u v : V) (uc : u∈C) (vc : v∈C) (uk : u∉K) (vk : v∉K) (diff : c u≠c v)
    (neigh : ∀ x∈C,G.Adj a x → x=u ∨ x=v) (j : Bool) (bc : ∀ x∈C,G.Adj b x → c x=j)
    (t : Bool) : ∃ x∈C,x∉K ∧ TerminalColor G a b (C.erase x) t := by
  classical
  have make (s z : V) (cover : ∀ x∈C,G.Adj a x → x=s ∨ x=z) :
      TerminalColor G a b (C.erase s) (j==c z) :=
    contact_color G a b ab na _ (fun h => ao (mem_of_mem_erase h)) (fun h => bo (mem_of_mem_erase h)) c
      (fun x xm y ym => cp x (mem_of_mem_erase xm) y (mem_of_mem_erase ym)) (c z) j
      (fun x xm ed => congrArg c ((cover x (mem_of_mem_erase xm) ed).resolve_left (mem_erase.mp xm).1))
      (fun x xm => bc x (mem_of_mem_erase xm))
  by_cases eq : (j==c v)=t
  · exact ⟨u,uc,uk,eq ▸ make u v neigh⟩
  · have other : (j==c u)=t := by cases j <;> cases t <;> cases q : c u <;> cases s : c v <;> simp_all
    exact ⟨v,vc,vk,other ▸ make v u (fun x xm ed => (neigh x xm ed).symm)⟩

#print axioms contact_color
#print axioms flexible_contact
end Minimal180.PairRepair
