import AffineBase
import FourRingCyclicGeometry

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.AffineHost
open AffineBase FourRingBudget FourRingReplica FourRingReplica.Layout FourRingCutAux
noncomputable section
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {A : SimpleGraph U} {r : Bool→U}
variable (L : Layout A r)

abbrev V (r : Bool→U) := Sum (Point×Piece r) Line
abbrev cell (i : Point) (x : Piece r) : V r := .inl (i,x)
abbrev control (l : Line) : V r := .inr l

def graph : SimpleGraph (V r) where
  Adj x y := match x,y with
    | .inl (i,a), .inl (j,b) => i=j ∧ A.Adj a.val b.val
    | .inl (i,a), .inr l => ∃ s, L.port s=a ∧ route i s=l
    | .inr l, .inl (i,a) => ∃ s, L.port s=a ∧ route i s=l
    | .inr _, .inr _ => False
  symm := by
    rintro ((⟨i,x⟩)|l) ((⟨j,y⟩)|k) h
    · exact ⟨h.1.symm,h.2.symm⟩
    · exact h
    · exact h
    · exact h
  loopless := by
    rintro ((⟨i,x⟩)|l) h
    · exact A.loopless _ h.2
    · exact h

instance : DecidableRel (graph L).Adj := Classical.decRel _

omit [Fintype U] [DecidableEq U] in
theorem separate {i j : Point} {x y : Piece r}
    (h : (graph L).Adj (cell i x) (cell j y)) : i=j := h.1

omit [Fintype U] [DecidableEq U] in
theorem inside {i : Point} {x y : Piece r}
    (h : (graph L).Adj (cell i x) (cell i y)) : (minor A r).Adj x y := h.2

omit [Fintype U] [DecidableEq U] in
theorem attach (i : Point) (s : Slot) :
    (graph L).Adj (cell i (L.port s)) (control (route i s)) := ⟨s,rfl,rfl⟩

private abbrev OnLine (l : Line) := {i : Point // i∈univ.filter (fun i=>Incident i l)}

omit [Fintype U] [DecidableEq U] in
private theorem point_has_slot (i : Point) (l : Line)
    (h : i∈univ.filter (fun i=>Incident i l)) : ∃ s,route i s=l :=
  (incident_iff i l).mp (mem_filter.mp h).2

omit [Fintype U] [DecidableEq U] in
private def slotFor {l : Line} (i : OnLine l) : Slot :=
  (point_has_slot i.val l i.property).choose

omit [Fintype U] [DecidableEq U] in
private theorem slotFor_route {l : Line} (i : OnLine l) : route i.val (slotFor i)=l :=
  (point_has_slot i.val l i.property).choose_spec

omit [Fintype U] [DecidableEq U] in
private def lineNeighbor (l : Line) (i : OnLine l) : (graph L).neighborSet (control l) :=
  ⟨cell i.val (L.port (slotFor i)),⟨slotFor i,rfl,slotFor_route i⟩⟩

omit [Fintype U] [DecidableEq U] in
private theorem lineNeighbor_bij (l : Line) : Function.Bijective (lineNeighbor L l) := by
  constructor
  · intro i j e
    have eq := congrArg Subtype.val e
    have xy := Sum.inl.inj eq
    exact Subtype.ext (congrArg Prod.fst xy)
  · rintro ⟨⟨i,x⟩|k,h⟩
    · obtain ⟨s,sx,sl⟩ := h
      have inc : Incident i l := (incident_iff i l).mpr ⟨s,sl⟩
      let p : OnLine l := ⟨i,mem_filter.mpr ⟨mem_univ _,inc⟩⟩
      have eq : slotFor p=s := route_injective i ((slotFor_route p).trans sl.symm)
      refine ⟨p,Subtype.ext ?_⟩
      change cell i (L.port (slotFor p))=cell i x
      rw [eq,sx]
    · exact h.elim

theorem control_degree (l : Line) : (graph L).degree (control l)=3 := by
  classical
  have ec := Fintype.card_congr (Equiv.ofBijective _ (lineNeighbor_bij L l))
  rw [card_neighborSet_eq_degree,Fintype.card_coe,card_points_on_line] at ec
  exact ec.symm

variable [DecidableRel A.Adj]

omit [Fintype U] [DecidableEq U] [DecidableRel A.Adj] in
private theorem reverse_cap_neighbor (x : Piece r)
    (y : A.neighborSet x.val) {k : Bool} (e : y.val=r k) :
    A.Adj (r k) x.val := by
  rw [←e]
  exact (show A.Adj x.val y.val from y.property).symm

private def liftAdjacent (i : Point) (x : Piece r)
    (y : A.neighborSet x.val) : (graph L).neighborSet (cell i x) := by
  classical
  by_cases a : y.val=r false
  · have e : A.Adj (r false) x.val := reverse_cap_neighbor x y a
    let s := (L.exactPort false x e).choose
    have sp : L.port (false,s)=x := (L.exactPort false x e).choose_spec
    exact ⟨control (route i (false,s)),⟨(false,s),sp,rfl⟩⟩
  · by_cases b : y.val=r true
    · have e : A.Adj (r true) x.val := reverse_cap_neighbor x y b
      let s := (L.exactPort true x e).choose
      have sp : L.port (true,s)=x := (L.exactPort true x e).choose_spec
      exact ⟨control (route i (true,s)),⟨(true,s),sp,rfl⟩⟩
    · exact ⟨cell i ⟨y.val,a,b⟩,⟨rfl,y.property⟩⟩

omit [Fintype U] [DecidableRel A.Adj] in
private theorem liftAdjacent_internal (i : Point) (x : Piece r)
    (y : A.neighborSet x.val) (a : y.val≠r false) (b : y.val≠r true) :
    (liftAdjacent L i x y).val=cell i ⟨y.val,a,b⟩ := by
  simp [liftAdjacent,a,b]

omit [Fintype U] [DecidableRel A.Adj] in
private theorem liftAdjacent_port (i : Point) (x : Piece r) (s : Slot)
    (px : L.port s=x) (y : A.neighborSet x.val) (ry : y.val=r s.1) :
    (liftAdjacent L i x y).val=control (route i s) := by
  classical
  obtain ⟨b,t⟩ := s
  cases b
  · have a : y.val=r false := ry
    unfold liftAdjacent
    simp only [dif_pos a]
    have eq : (L.exactPort false x (reverse_cap_neighbor x y a)).choose=t := by
      have h := (L.exactPort false x (reverse_cap_neighbor x y a)).choose_spec
      exact congrArg Prod.snd (L.port.injective (h.trans px.symm))
    rw [eq]
  · have b : y.val=r true := ry
    have a : y.val≠r false := fun e=>L.rootEdge.ne (e.symm.trans b)
    unfold liftAdjacent
    simp only [dif_neg a,dif_pos b]
    have eq : (L.exactPort true x (reverse_cap_neighbor x y b)).choose=t := by
      have h := (L.exactPort true x (reverse_cap_neighbor x y b)).choose_spec
      exact congrArg Prod.snd (L.port.injective (h.trans px.symm))
    rw [eq]

omit [Fintype U] [DecidableRel A.Adj] in
private theorem liftAdjacent_bij (i : Point) (x : Piece r) : Function.Bijective (liftAdjacent L i x) := by
  classical
  have root_case (v : A.neighborSet x.val) (k : Bool) (rs : v.val=r k) :
      ∃ s : Slot,s.1=k ∧ L.port s=x ∧ (liftAdjacent L i x v).val=control (route i s) := by
    have vX : A.Adj (r k) x.val := reverse_cap_neighbor x v rs
    obtain ⟨t,h⟩ := L.exactPort k x vX
    exact ⟨(k,t),rfl,h,liftAdjacent_port L i x (k,t) h v rs⟩
  have classes (u : A.neighborSet x.val) :
      (∃ a : Piece r,u.val=a.val ∧ (liftAdjacent L i x u).val=cell i a) ∨
      (∃ s : Slot,u.val=r s.1 ∧ L.port s=x ∧ (liftAdjacent L i x u).val=control (route i s)) := by
    by_cases h : ∃ k,u.val=r k
    · obtain ⟨k,e⟩ := h
      obtain ⟨s,sk,sx,sl⟩ := root_case u k e
      exact Or.inr ⟨s,by rwa [sk],sx,sl⟩
    · push_neg at h
      exact Or.inl ⟨⟨u.val,h false,h true⟩,rfl,liftAdjacent_internal L i x u (h false) (h true)⟩
  constructor
  · intro u v e
    have d := congrArg Subtype.val e
    apply Subtype.ext
    rcases classes u with ⟨a,ua,la⟩|⟨s,us,_,ls⟩ <;>
      rcases classes v with ⟨b,vb,lb⟩|⟨t,vt,_,lt⟩
    · rw [la,lb] at d
      have xy := congrArg Prod.snd (Sum.inl.inj d)
      exact ua.trans ((congrArg Subtype.val xy).trans vb.symm)
    · rw [la,lt] at d
      cases d
    · rw [ls,lb] at d
      cases d
    · rw [ls,lt] at d
      have x := route_injective i (Sum.inr.inj d)
      exact us.trans ((congrArg (fun s : Slot=>r s.1) x).trans vt.symm)
  · rintro ⟨⟨j,y⟩|l,h⟩
    · obtain ⟨eq,ed⟩ := h
      subst j
      exact ⟨⟨y.val,ed⟩,Subtype.ext (liftAdjacent_internal L i x _ y.property.1 y.property.2)⟩
    · obtain ⟨s,sx,sl⟩ := h
      have edge : A.Adj x.val (r s.1) := sx ▸ (L.conn s).symm
      let y : A.neighborSet x.val := ⟨r s.1,edge⟩
      refine ⟨y,Subtype.ext ?_⟩
      exact (liftAdjacent_port L i x s sx y rfl).trans (congrArg control sl)

theorem cell_degree (i : Point) (x : Piece r) : (graph L).degree (cell i x)=A.degree x.val := by
  classical
  have ec := Fintype.card_congr (Equiv.ofBijective _ (liftAdjacent_bij L i x))
  rw [card_neighborSet_eq_degree,card_neighborSet_eq_degree] at ec
  exact ec.symm

theorem cubic (cub : ∀ x,A.degree x=3) :
    ∀ v,(graph L).degree v=3 := by
  rintro (⟨i,x⟩|l)
  · rw [show Sum.inl (i,x)=cell i x from rfl,cell_degree,cub]
  · exact control_degree L l

include L in
omit [DecidableRel A.Adj] in
theorem card_host : Fintype.card (V r)=9*(Fintype.card U-2)+12 := by
  rw [Fintype.card_sum,Fintype.card_prod,L.piece_card]
  rfl

#print axioms cubic
#print axioms card_host
end
end KelmansCactus.AtomicBridge.AffineHost
