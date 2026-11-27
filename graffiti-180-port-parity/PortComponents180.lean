import NearestPort180
import CoreSplit180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every component of the old induced set D meets an attachment port. -/
def PortComponents (G : SimpleGraph V) (N D : Finset V) : Prop :=
  ∀ x : ↥(D : Set V), ∃ y : ↥(D : Set V), y.val∈N ∧ (G.induce (D : Set V)).Reachable x y

omit [Fintype V] in
theorem con_lift_iff (G : SimpleGraph V) (N D : Finset V) :
    Con (ear G N) (lift D true) ↔ PortComponents G N D := by
  classical
  let H := ear G N
  let K := G.induce (D : Set V)
  let L := H.induce (lift D true : Set (V⊕Unit))
  let r : ↥(lift D true : Set (V⊕Unit)) := ⟨.inr (),by simp⟩
  let inc : K →g L := ⟨fun x => ⟨.inl x.val,(inl_lift ..).mpr x.property⟩,fun e => e⟩
  constructor
  · intro hc x
    let f (v : V⊕Unit) := Sum.elim (fun w => if h : w∈D then decide (K.Reachable x ⟨w,h⟩) else false) (fun _ => false) v
    by_contra! no
    have old {w} (wd : w∈D) : f (.inl w)=decide (K.Reachable x ⟨w,wd⟩) := dif_pos wd
    have port {w} (wd : w∈D) (wn : w∈N) : f (.inl w)=false := by
      rw [old wd]; exact decide_eq_false (no ⟨w,wd⟩ wn)
    have stable : OnEdges H (lift D true) f := by
      rintro (u|z) hu (v|t) hv e
      · have a := (inl_lift ..).mp hu
        have b := (inl_lift ..).mp hv
        have edge : K.Adj ⟨u,a⟩ ⟨v,b⟩ := e
        rw [old a,old b,decide_eq_decide]
        exact ⟨fun h => h.trans edge.reachable,fun h => h.trans edge.symm.reachable⟩
      · exact port ((inl_lift ..).mp hu) e
      · exact (port ((inl_lift ..).mp hv) e).symm
      · rfl
    have eq := ((connected_cuts H _).mp hc).2 f stable (.inl x.val) ((inl_lift ..).mpr x.property) (.inr ()) (by simp)
    rw [old x.property] at eq
    change decide (K.Reachable x x)=false at eq
    simp [Reachable.refl] at eq
  · intro hit
    apply (connected_iff_exists_forall_reachable L).mpr
    refine ⟨r,fun z => ?_⟩
    rcases z with ⟨w,hw⟩
    rcases w with w|u
    · let x : ↥(D:Set V) := ⟨w,(inl_lift ..).mp hw⟩
      obtain ⟨y,port,path⟩ := hit x
      have edge : L.Adj r (inc y) := port
      exact edge.reachable.trans (path.symm.map inc)
    · cases u; exact Reachable.refl _

omit [Fintype V] [DecidableEq V] in
theorem dominates_lift (G : SimpleGraph V) (N D : Finset V) (x : V) :
    Dominates (ear G N) (lift D true) (.inl x) ↔ x∈N ∨ Dominates G D x := by
  constructor
  · rintro ⟨y,hm,edge⟩
    rcases y with y|u
    · exact Or.inr ⟨y,(inl_lift ..).mp hm,edge⟩
    · exact Or.inl edge
  · rintro (h|⟨y,d,e⟩)
    · exact ⟨.inr (),by simp,h⟩
    · exact ⟨.inl y,(inl_lift ..).mpr d,e⟩

#print axioms con_lift_iff
#print axioms dominates_lift
end Minimal180.PortParity
