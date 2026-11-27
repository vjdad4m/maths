import PortPath189
namespace Graffiti189LongestPath.TwoCut
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.FourCut.Three
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

structure TwoSides (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) where
  con : G.Connected
  ab : a≠b
  d2 : ∀ x, (DistanceTwo G x).card≤4
  H : Bool → Finset V
  dis : Disjoint (H false) (H true)
  off : ∀ i, a∉H i ∧ b∉H i
  all : ∀ x, x=a ∨ x=b ∨ ∃ i,x∈H i
  closed : ∀ i, ∀ x∈H i, ∀ y, G.Adj x y → y=a ∨ y=b ∨ y∈H i
  joined : ∀ i, ∀ x∈H i, ∀ y∈H i, ∃ q : G.Walk x y, ∀ z∈q.support, z∈H i
  hitb : ∀ i, ∃ x∈H i,G.Adj b x
  ports_four : ∀ i, ((H i).filter (G.Adj a)).card=4

namespace TwoSides
noncomputable section
variable {a b : V} (S : TwoSides G a b)
def Ports (i : Bool) := (S.H i).filter (G.Adj a)
def Inner (i : Bool) := S.H i \ S.Ports i
theorem ports_card (i : Bool) : (S.Ports i).card=4 := S.ports_four i

private theorem disjoint_sides {i j : Bool} (ij : i≠j) : Disjoint (S.H i) (S.H j) := by
  cases i <;> cases j
  · exact (ij rfl).elim
  · exact S.dis
  · exact S.dis.symm
  · exact (ij rfl).elim

theorem every_port_universal {i : Bool} {x : V} (xi : x∈S.Ports i) :
    (∀ y∈S.H i,x=y ∨ G.Adj x y) ∧ G.Adj b x ∧
      ∀ y∈S.H (!i), G.Adj b y → y∈S.Ports (!i) := by
  have xH := (mem_filter.mp xi).1
  have ax := (mem_filter.mp xi).2
  have ij : i ≠ !i := by cases i <;> decide
  have dis := S.disjoint_sides ij
  have foreign {y : V} (yH : y∈S.H (!i)) : x≠y ∧ ¬G.Adj x y := by
    have no : y∉S.H i := fun h => disjoint_left.mp dis h yH
    exact ⟨fun e => no (e ▸ xH),fun adj =>
      (S.closed i x xH y adj).elim (fun e => (S.off (!i)).1 (e ▸ yH))
        (fun h => h.elim (fun e => (S.off (!i)).2 (e ▸ yH)) no)⟩
  have sub : S.Ports (!i) ⊆ DistanceTwo G x := by
    intro y yp
    obtain ⟨yh,ay⟩ := mem_filter.mp yp
    obtain ⟨ne,no⟩ := foreign yh
    exact Sides.mem_d2.mpr (Sides.dist_two S.con ne no ax.symm ay)
  have eq : DistanceTwo G x=S.Ports (!i) :=
    (eq_of_subset_of_card_le sub (by rw [S.ports_card]; exact S.d2 x)).symm
  have no_inside {y : V} (yH : y∈S.H i) : y∉DistanceTwo G x := by
    rw [eq]
    exact fun e => disjoint_left.mp dis yH (mem_filter.mp e).1
  have uni (y : V) (yH : y∈S.H i) : x=y ∨ G.Adj x y := by
    obtain ⟨w,ws⟩ := S.joined i x xH y yH
    have prop {u v : V} (q : G.Walk u v) (qs : ∀ w∈q.support,w∈S.H i)
        (xu : x=u ∨ G.Adj x u) : x=v ∨ G.Adj x v := by
      induction q with
      | nil => exact xu
      | @cons u w v uw q ih =>
        apply ih (fun z hz => qs z (by simp [hz]))
        rcases xu with eq|xu
        · exact Or.inr (eq.symm ▸ uw)
        by_cases xw : x=w
        · exact Or.inl xw
        by_cases ad : G.Adj x w
        · exact Or.inr ad
        exact (no_inside (qs w (by simp)) (Sides.mem_d2.mpr (Sides.dist_two S.con xw ad xu uw))).elim
    exact prop w ws (Or.inl rfl)
  have bx : G.Adj b x := by
    by_cases bx : G.Adj b x
    · exact bx
    obtain ⟨y,yH,by'⟩ := S.hitb i
    rcases uni y yH with xy|xy
    · exact (bx (xy.symm ▸ by')).elim
    · have ne : x≠b := fun e => (S.off i).2 (e ▸ xH)
      have bd := Sides.mem_d2.mpr (Sides.dist_two S.con ne (fun e => bx e.symm) xy by'.symm)
      rw [eq] at bd
      exact ((S.off (!i)).2 (mem_filter.mp bd).1).elim
  refine ⟨uni,bx,?_⟩
  intro y yH by'
  obtain ⟨ne,no⟩ := foreign yH
  have dy := Sides.mem_d2.mpr (Sides.dist_two S.con ne no bx.symm by')
  rwa [eq] at dy

private theorem inner_sub (i : Bool) : S.Inner i⊆DistanceTwo G a := by
  intro x xi
  obtain ⟨xH,notP⟩ := mem_sdiff.mp xi
  obtain ⟨y,yp⟩ := card_pos.mp (show 0<(S.Ports i).card by rw [S.ports_card]; decide)
  have yx : y≠x := fun e => notP (e ▸ yp)
  have adj := ((S.every_port_universal yp).1 x xH).resolve_left yx
  have ax : ¬G.Adj a x := fun e => notP (mem_filter.mpr ⟨xH,e⟩)
  have ne : a≠x := fun e => (S.off i).1 (e.symm ▸ xH)
  exact Sides.mem_d2.mpr (Sides.dist_two S.con ne ax (mem_filter.mp yp).2 adj)

theorem inner_card_sum : (S.Inner false).card+(S.Inner true).card≤4 := by
  have dis : Disjoint (S.Inner false) (S.Inner true) := S.dis.mono sdiff_subset sdiff_subset
  have cnt := card_le_card (union_subset (S.inner_sub false) (S.inner_sub true))
  rw [card_union_of_disjoint dis] at cnt
  exact cnt.trans (S.d2 a)

private theorem path_in (i : Bool) (small : (S.Inner i).card≤4) :
    ∃ x∈S.Ports i, ∃ y, ∃ p : G.Walk x y,
      p.IsPath ∧ (∀ z,z∈p.support ↔ z∈S.H i) ∧ ((S.Inner i).card<4 → y∈S.Ports i) := by
  have dis : Disjoint (S.Ports i) (S.Inner i) := disjoint_left.mpr
    (fun _ hp hi => (mem_sdiff.mp hi).2 hp)
  have peq : S.Ports i∪S.Inner i = S.H i := by
    ext z
    simp only [Inner,mem_union,mem_sdiff]
    have sub : S.Ports i⊆S.H i := filter_subset _ _
    constructor
    · rintro (h|⟨h,_⟩)
      · exact sub h
      · exact h
    · intro h
      by_cases p : z∈S.Ports i
      · exact Or.inl p
      · exact Or.inr ⟨h,p⟩
  have c := S.ports_card i
  obtain ⟨x,xp,y,p,hp,ps,yp⟩ := path_from_universal_ports (G:=G) (S.Ports i) (S.Inner i) dis
    (by omega) (by omega) (by
      intro x xx y yy ne
      rw [peq] at yy
      exact ((S.every_port_universal xx).1 y yy).resolve_left ne)
  exact ⟨x,xp,y,p,hp,by simpa only [peq] using ps,fun h => yp (by omega)⟩

private theorem assemble {i j : Bool} (ij : i≠j) (few : (S.Inner i).card<4) (other : (S.Inner j).card≤4) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsPath ∧ ∀ y,y∈p.support := by
  obtain ⟨x,xp,y,p,hp,ps,yp⟩ := S.path_in i (by omega)
  obtain ⟨z,zp,w,q,hq,qs,_⟩ := S.path_in j other
  have bx := (S.every_port_universal xp).2.1
  have ya := (mem_filter.mp (yp few)).2.symm
  have az := (mem_filter.mp zp).2
  let right : G.Walk y w := .cons ya (.cons az q)
  let middle := p.append right
  have ms : middle.support = p.support ++ a :: q.support := by simp [middle,right,support_append]
  have aoff : a∉q.support := fun e => (S.off j).1 ((qs _).mp e)
  have mpath : middle.IsPath := by
    apply Walk.IsPath.mk'
    rw [ms,List.nodup_append]
    refine ⟨hp.support_nodup,List.nodup_cons.mpr ⟨aoff,hq.support_nodup⟩,?_⟩
    intro u up uq
    rcases List.mem_cons.mp uq with rfl|uq
    · exact (S.off i).1 ((ps _).mp up)
    · exact disjoint_left.mp (S.disjoint_sides ij) ((ps _).mp up) ((qs _).mp uq)
  have bnot : b∉middle.support := by
    rw [ms,List.mem_append,List.mem_cons]
    rintro (ip|ba|jp)
    · exact (S.off i).2 ((ps _).mp ip)
    · exact S.ab ba.symm
    · exact (S.off j).2 ((qs _).mp jp)
  refine ⟨b,w,.cons bx middle,mpath.cons bnot,?_⟩
  intro u
  simp only [support_cons,List.mem_cons,ms,List.mem_append,ps,qs]
  rcases S.all u with ea|eb|⟨k,ku⟩
  · exact Or.inr (Or.inr (Or.inl ea))
  · exact Or.inl eb
  · by_cases ki : k=i
    · exact Or.inr (Or.inl (ki ▸ ku))
    · have kj : k=j := by cases i <;> cases j <;> cases k <;> simp_all
      exact Or.inr (Or.inr (Or.inr (kj ▸ ku)))

include S

/-- If one cut vertex has four neighbors in both components, then under the
distance-two bound the graph is traceable. No even-distance cap is needed. -/
theorem traceable : ∃ u v : V, ∃ p : G.Walk u v, p.IsPath ∧ ∀ y,y∈p.support := by
  have cnt := S.inner_card_sum
  by_cases h : (S.Inner false).card<4
  · exact S.assemble (show false≠true by decide) h (by omega)
  · exact S.assemble (show true≠false by decide) (by omega) (by omega)

#print axioms traceable
end
end TwoSides
end Graffiti189LongestPath.TwoCut
