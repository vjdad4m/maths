import FourRingReplicaCap

open Finset SimpleGraph
namespace KelmansCactus.FourRingReplica.Layout
open FourRingBudget
noncomputable section
variable {U J : Type*} {A : SimpleGraph U} {r : Bool→U}
variable (L : Layout A r)
variable (next : Equiv.Perm J) (fixed : ∀i,next i≠i)

private def sideOf (u : Piece r) : Bool := by
  classical
  exact if ∃ b,L.port (false,b)=u then false else true

private theorem sideOf_port (s : Slot) : L.sideOf (L.port s)=s.1 := by
  classical
  obtain ⟨b,c⟩ := s
  cases b
  · simp only [sideOf,if_pos (show ∃ d,L.port (false,d)=L.port (false,c) from ⟨c,rfl⟩)]
  · have n : ¬∃ d,L.port (false,d)=L.port (true,c) := by
      rintro ⟨d,e⟩
      exact Bool.false_ne_true (congrArg Prod.fst (L.port.injective e))
    simp only [sideOf,if_neg n]

variable [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J]

/-- At each port its single external edge replaces exactly one of
the deleted root edges; all other neighbors are unchanged. -/
theorem cubic [DecidableRel A.Adj] (deg : ∀ v,A.degree v=3) (x : Host J r) :
    (L.graph next fixed).degree x=3 := by
  classical
  let f : (L.graph next fixed).neighborSet x → A.neighborSet x.2.val := fun y =>
    if same : y.val.1=x.1 then
      ⟨y.val.2.val,(L.internal next (fixed:=fixed) same.symm).mp y.property⟩
    else
      ⟨r (L.sideOf x.2),by
        obtain ⟨s,e,_⟩ := (L.graph_cross next (fixed:=fixed) (Ne.symm same)).mp y.property
        have v : L.port s.2=x.2 := congrArg (fun z : Host J r=>z.2) e
        have orig : A.Adj x.2.val (r s.2.1) :=
          congrArg (fun t : Piece r=>t.val) v ▸ (L.conn s.2).symm
        have side : L.sideOf x.2=s.2.1 := v ▸ L.sideOf_port s.2
        rw [side]
        exact orig⟩
  have fIn (y : (L.graph next fixed).neighborSet x) (h : y.val.1=x.1) :
      (f y).val=y.val.2.val := by simp [f,h]
  have fOut (y : (L.graph next fixed).neighborSet x) (h : y.val.1≠x.1) :
      (f y).val=r (L.sideOf x.2) := by simp [f,h]
  have noRoot (y : Piece r) (b : Bool) : y.val≠r b := by
    cases b
    · exact y.property.1
    · exact y.property.2
  have inj : Function.Injective f := by
    intro y z eq
    have v : (f y).val=(f z).val := congrArg (fun t : A.neighborSet x.2.val=>t.val) eq
    by_cases yy : y.val.1=x.1
    · by_cases zz : z.val.1=x.1
      · rw [fIn y yy,fIn z zz] at v
        exact Subtype.ext (Prod.ext (yy.trans zz.symm) (Subtype.ext v))
      · rw [fIn y yy,fOut z zz] at v
        exact (noRoot y.val.2 _ v).elim
    · by_cases zz : z.val.1=x.1
      · rw [fOut y yy,fIn z zz] at v
        exact (noRoot z.val.2 _ v.symm).elim
      · obtain ⟨s,xs,ys⟩ := (L.graph_cross next (fixed:=fixed) (Ne.symm yy)).mp y.property
        obtain ⟨t,xt,zt⟩ := (L.graph_cross next (fixed:=fixed) (Ne.symm zz)).mp z.property
        have e := L.port_inj_on_host (xs.trans xt.symm)
        exact Subtype.ext (ys.symm.trans (e ▸ zt))
  have surj : Function.Surjective f := by
    intro z
    by_cases rootCase : ∃ b,z.val=r b
    · obtain ⟨b,zb⟩ := rootCase
      have vz : A.Adj x.2.val z.val := z.property
      have e : A.Adj (r b) x.2.val := by simpa only [zb] using vz.symm
      obtain ⟨k,kp⟩ := L.exactPort b x.2 e
      have same : L.p x.1 (b,k)=x := Prod.ext rfl kp
      have h : (L.graph next fixed).Adj x (L.q next x.1 (b,k)) := Or.inr ⟨(x.1,b,k),same,rfl⟩
      let y : (L.graph next fixed).neighborSet x := ⟨L.q next x.1 (b,k),h⟩
      have out := fOut y (L.q_not_cell next fixed x.1 (b,k))
      have side : L.sideOf x.2=b := kp ▸ L.sideOf_port (b,k)
      exact ⟨y,Subtype.ext (out.trans ((congrArg r side).trans zb.symm))⟩
    · let u : Piece r := ⟨z.val,fun e=>rootCase ⟨false,e⟩,fun e=>rootCase ⟨true,e⟩⟩
      let y : Host J r := (x.1,u)
      have h : (L.graph next fixed).Adj x y :=
        (L.internal next (fixed:=fixed) (x:=x) (y:=y) rfl).mpr z.property
      exact ⟨⟨y,h⟩,Subtype.ext (fIn ⟨y,h⟩ rfl)⟩
  rw [←card_neighborSet_eq_degree,Fintype.card_of_bijective ⟨inj,surj⟩,card_neighborSet_eq_degree]
  exact deg _

#print axioms cubic
end
end KelmansCactus.FourRingReplica.Layout
