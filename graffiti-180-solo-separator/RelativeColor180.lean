import ComponentPorts180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [DecidableEq V]

/-- In each surviving connected component, the contacts of a fixed
terminal must see just one side of the bipartition. -/
def MonoAt (G : SimpleGraph V) (S : Finset V) (a : V) (c : V→Bool) : Prop :=
  ∀ x y,G.Adj a x → G.Adj a y → Joined G S x y → c x=c y

/-- Every component meeting both tips constrains their relative color.
The value is true precisely when its two contact colors coincide. -/
def RelativeCheck (G : SimpleGraph V) (S : Finset V) (a b : V) (c : V→Bool) (t : Bool) : Prop :=
  MonoAt G S a c ∧ MonoAt G S b c ∧
    ∀ x y,G.Adj a x → G.Adj b y → Joined G S x y → (c x==c y)=t

omit [DecidableEq V] in
private theorem joined_reverse (G : SimpleGraph V) (S : Finset V) {x y : V} (h : Joined G S x y) :
    Joined G S y x := by obtain ⟨xm,ym,p⟩ := h;exact ⟨ym,xm,p.symm⟩

omit [DecidableEq V] in
private theorem opposite_request {i j u v : Bool} (h : (i==u)=true) (k : (j==v)=false) :
    (i==j)≠(u==v) := by cases i <;> cases j <;> cases u <;> cases v <;> simp_all

private theorem same_relative {i j u v z w m n : Bool} (f : (i != u)=(j != v)) (am : m≠u) (bn : n≠v)
    (hm : m=z) (hn : n=w) : (i==j)=(z==w) := by
  subst z;subst w
  exact (show ∀ i j u v m n : Bool,(i != u)=(j != v) → m≠u → n≠v → (i==j)=(m==n) by decide) i j u v m n f am bn

omit [DecidableEq V] in
private theorem flip_edge {a b i j : Bool} (ab : a≠b) (ij : i≠j) : (a != i)=(b != j) := by
  cases a <;> cases b <;> cases i <;> cases j <;> simp_all

/-- Exact test for the relative color after independent component flips.
There is no quantification over new colorings. -/
theorem terminal_iff_contacts (G : SimpleGraph V) (a b : V) (ab : a≠b) (na : ¬G.Adj a b)
    (S : Finset V) (ao : a∉S) (bo : b∉S) (c : V→Bool) (cp : ProperOn G S c) (t : Bool) :
    TerminalColor G a b S t ↔ RelativeCheck G S a b c t := by
  classical
  let X : Finset V := {a,b}
  let d (v : V) := if v=a then true else t
  have da : d a=true := by simp [d]
  have db : d b=t := by simp [d,ab.symm]
  have sep : Disjoint S X := disjoint_left.mpr (fun x xm h => by
    rcases mem_insert.mp h with xa|xb
    · exact ao (xa ▸ xm)
    · exact bo ((mem_singleton.mp xb) ▸ xm))
  have ind := pair_indep G na
  have ext := extension_iff G S X c d sep cp (fun x xm y ym ed => (ind x xm y ym ed.ne ed).elim)
  constructor
  · rintro ⟨e,ok,ea,eb⟩
    have law (m n : V) (mm : m∈X) (nm : n∈X) (x y : V) (mx : G.Adj m x) (ny : G.Adj n y)
        (path : Joined G S x y) : (c x==c y)=(e m==e n) := by
      have sync := joined_constant G S (fun z => c z != e z) (fun i im j jm ed =>
        flip_edge (cp i im j jm ed) (ok i (mem_union_right _ im) j (mem_union_right _ jm) ed)) path
      exact same_relative sync (ok m (mem_union_left _ mm) x (mem_union_right _ path.choose) mx)
        (ok n (mem_union_left _ nm) y (mem_union_right _ path.choose_spec.choose) ny) rfl rfl
    have ma : a∈X := mem_insert_self ..
    have mb : b∈X := mem_insert_of_mem (mem_singleton_self _)
    refine ⟨fun x y ax ay j => ?_,fun x y bx by' j => ?_,fun x y ax by' j => ?_⟩
    · simpa using law a a ma ma x y ax ay j
    · simpa using law b b mb mb x y bx by' j
    · simpa [ea,eb] using law a b ma mb x y ax by' j
  · rintro ⟨monoA,monoB,relative⟩
    have fit : Compatible G S X c d := by
      rintro x y ⟨u,um,ux,on⟩ ⟨v,vm,vy,off⟩ path
      have deny := opposite_request on off
      rcases mem_insert.mp um with ua|ub <;> rcases mem_insert.mp vm with va|vb
      · subst u;subst v;apply deny;simp [monoA x y ux vy path]
      · subst u;obtain rfl := mem_singleton.mp vb
        apply deny;simpa [da,db] using relative x y ux vy path
      · obtain rfl := mem_singleton.mp ub;subst v
        apply deny
        have eq := relative y x vy ux (joined_reverse G S path)
        simpa [da,db] using ((Bool.beq_comm (a:=c x) (b:=c y)).trans eq)
      · obtain rfl := mem_singleton.mp ub;obtain rfl := mem_singleton.mp vb
        apply deny;simp [monoB x y ux vy path]
    obtain ⟨e,ok,agree⟩ := ext.mpr fit
    refine ⟨e,?_,(agree a (mem_insert_self ..)).trans da,(agree b (mem_insert_of_mem (mem_singleton_self _))).trans db⟩
    simpa only [union_comm S X] using ok

/-- Once each tip has coherent contacts, the complete absence of paths
between their contacts is equivalent to availability of both signs. -/
theorem both_signs_iff (G : SimpleGraph V) (a b : V) (ab : a≠b) (na : ¬G.Adj a b)
    (S : Finset V) (ao : a∉S) (bo : b∉S) (c : V→Bool) (cp : ProperOn G S c) :
    (∀ t,TerminalColor G a b S t) ↔ MonoAt G S a c ∧ MonoAt G S b c ∧
      ∀ x y,G.Adj a x → G.Adj b y → ¬Joined G S x y := by
  have rule := terminal_iff_contacts G a b ab na S ao bo c cp
  constructor
  · intro all
    obtain ⟨am,bm,off⟩ := (rule false).mp (all false)
    obtain ⟨_,_,on⟩ := (rule true).mp (all true)
    exact ⟨am,bm,fun x y ax by' j => Bool.noConfusion ((off x y ax by' j).symm.trans (on x y ax by' j))⟩
  · rintro ⟨am,bm,separate⟩ t
    exact (rule t).mpr ⟨am,bm,fun x y ax by' j => (separate x y ax by' j).elim⟩

#print axioms terminal_iff_contacts
#print axioms both_signs_iff
end Minimal180.PairRepair
