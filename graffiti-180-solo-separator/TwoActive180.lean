import Inactive180
import ContactColors180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two active regions and the union of all other remainder components. -/
structure TwoRegions (G : SimpleGraph V) (a b : V) (C D O : Finset V) : Prop where
  partition : univ\({a,b}:Finset V)=(C∪D)∪O
  apart : Disjoint C D
  other : Disjoint (C∪D) O
  cross : ∀ x∈C,∀ y∈D,¬G.Adj x y
  out : ∀ x∈C∪D,∀ y∈O,¬G.Adj x y
  inactive : ∀ x∈O,¬G.Adj a x

def DropColor (G : SimpleGraph V) (a b : V) (K S : Finset V) (t : Bool) : Prop :=
  ∃ x∈S,x∉K ∧ TerminalColor G a b (S.erase x) t

private theorem other_closed (G : SimpleGraph V) (a b : V) (C D O : Finset V) (h : TwoRegions G a b C D O) :
    ClosedIn G (univ\{a,b}) O := by
  intro x xr y yr ed
  rw [h.partition] at xr yr
  constructor
  · intro xo
    exact (mem_union.mp yr).resolve_left (fun yc => h.out y yc x xo ed.symm)
  · intro yo
    exact (mem_union.mp xr).resolve_left (fun xc => h.out x xc y yo ed)

private theorem rank_of_pair (G : SimpleGraph V) (a b : V) (ab : a≠b) (bi : TwoColor G (univ\{a,b})) :
    Fintype.card V≤bipartiteNum G+2 := by
  have lower := size_bip G bi
  have sum := card_sdiff_add_card_eq_card (subset_univ ({a,b}:Finset V))
  rw [card_pair ab,card_univ] at sum;omega

/-- At the exact degree-four, budget-two marking there is no constraint
from the inactive region. The two masks of possible colors may
still be incompatible; this equivalence tests their actual intersection. -/
theorem two_active_iff (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (a b : V) (ab : a≠b) (na : ¬G.Adj a b)
    (bi : TwoColor G (univ\{a,b})) (am : a∈A) (pm : a∈parity G r p) (deg : G.degree a=4)
    (two : allowance G r p A=2) (C D O : Finset V) (h : TwoRegions G a b C D O)
    (lc : ¬TwoColor G (insert a C)) (rc : ¬TwoColor G (insert a D)) :
    Protected G r p A ↔ ∃ t : Bool,DropColor G a b (A∩insert r (parity G r p)) C t ∧
      DropColor G a b (A∩insert r (parity G r p)) D t := by
  have os : O⊆univ\({a,b}:Finset V) := h.partition ▸ subset_union_right
  have oc := inactive_free G gc hn (rank_of_pair G a b ab bi) r p A ai a b ab na am pm
    (by omega) O os (other_closed G a b C D O h) h.inactive
  rw [two_region_iff G gc hn r p A ai a b (mem_inter.mpr ⟨am,mem_insert_of_mem pm⟩)
    C D O h.partition h.apart h.other h.cross h.out lc rc two]
  exact ⟨fun ⟨t,ll,rr,_⟩ => ⟨t,ll,rr⟩,fun ⟨t,ll,rr⟩ => ⟨t,ll,rr,oc t⟩⟩

/-- A single-protected nonroot case settles if one active region sees
the other tip in one color, while in the second region removing one
unprotected vertex makes both tips' remaining contacts monochromatic.
The color classes and the removable vertex are explicit inputs. -/
theorem solo_flexible_repair (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (a b : V) (ab : a≠b)
    (bi : TwoColor G (univ\{a,b})) (ar : a≠r) (ak : a∈A∩insert r (parity G r p))
    (bk : b∉A∩insert r (parity G r p)) (C D O : Finset V) (h : TwoRegions G a b C D O)
    (c : V→Bool) (cp : ProperOn G (univ\{a,b}) c) (lc : MixedAt G a C c) (rc : MixedAt G a D c)
    (u v : V) (uc : u∈C) (vc : v∈C) (au : G.Adj a u) (av : G.Adj a v) (diff : c u≠c v)
    (cover : ∀ w∈C,G.Adj a w → w=u ∨ w=v) (col : Bool) (one : ∀ w∈C,G.Adj b w → c w=col)
    (z : V) (zd : z∈D) (zk : z∉A∩insert r (parity G r p)) (i j : Bool)
    (ac : ∀ w∈D.erase z,G.Adj a w → c w=i) (bc : ∀ w∈D.erase z,G.Adj b w → c w=j) :
    Protected G r p A := by
  classical
  by_contra bad
  have rig := solo_rigidity G gc hn r p A ai bad a b ab bi ak bk
  have na := (pair_obstruction G gc hn r p A ai bad a b ab bi).1
  have am := (mem_inter.mp ak).1
  have pm := (mem_insert.mp (mem_inter.mp ak).2).resolve_left ar
  have cs : C⊆univ\({a,b}:Finset V) := h.partition ▸ (subset_union_left.trans subset_union_left)
  have ds : D⊆univ\({a,b}:Finset V) := h.partition ▸ (subset_union_right.trans subset_union_left)
  have ca : a∉C := fun m => (mem_sdiff.mp (cs m)).2 (mem_insert_self ..)
  have cb : b∉C := fun m => (mem_sdiff.mp (cs m)).2 (mem_insert_of_mem (mem_singleton_self _))
  have da : a∉D := fun m => (mem_sdiff.mp (ds m)).2 (mem_insert_self ..)
  have db : b∉D := fun m => (mem_sdiff.mp (ds m)).2 (mem_insert_of_mem (mem_singleton_self _))
  have cproper : ProperOn G C c := fun x xm y ym => cp x (cs xm) y (cs ym)
  have dproper : ProperOn G D c := fun x xm y ym => cp x (ds xm) y (ds ym)
  have free (w : V) (ed : G.Adj a w) : w∉A∩insert r (parity G r p) := fun wm =>
    ai a am w (mem_inter.mp wm).1 ed.ne ed
  apply bad
  apply (two_active_iff G gc hn r p A ai a b ab na bi am pm rig.1 rig.2.1 C D O h
    ((mixed_iff G a C c ca cproper).mp lc) ((mixed_iff G a D c da dproper).mp rc)).mpr
  refine ⟨j==i,flexible_contact G a b ab na C _ ca cb c cproper u v uc vc (free u au) (free v av)
    diff cover col one _,z,zd,zk,?_⟩
  exact contact_color G a b ab na _ (fun m => da (mem_of_mem_erase m)) (fun m => db (mem_of_mem_erase m))
    c (fun x xm y ym => dproper x (mem_of_mem_erase xm) y (mem_of_mem_erase ym)) i j ac bc

#print axioms two_active_iff
#print axioms solo_flexible_repair
end Minimal180.PairRepair
