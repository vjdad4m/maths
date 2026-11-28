import HighDichotomy189
import MultiPinRotation189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath Graffiti189LongestPath.Rigidity
open Graffiti189LongestPath.OneSlack Graffiti189LongestPath.OneSlack.MultiRotation
open Graffiti189LongestPath.Normalize
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.pin_pos from Rigidity189
open private Graffiti189LongestPath.OneSlack.first_eq_if_no_pair
  Graffiti189LongestPath.OneSlack.cardinal_flankVertices
  Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
open private Graffiti189LongestPath.OneSlack.MultiRotation.chord_forces_first_fringe
  Graffiti189LongestPath.OneSlack.MultiRotation.rigidity_of_tight
  Graffiti189LongestPath.OneSlack.MultiRotation.same_support_pin_count
  Graffiti189LongestPath.OneSlack.MultiRotation.reverse_longest
  Graffiti189LongestPath.OneSlack.MultiRotation.pin_reverse from MultiPinRotation189
set_option warningAsError true
namespace Graffiti189LongestPath.LockedPins
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A separated double porter on a normalized path has locked pin edges:
rotation at a chord from the initial endpoint can never pivot on a pin. -/
theorem no_start_pin_chord (hc : G.Connected) (k : Nat) (hk : 3≤k)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x y : V} {p : G.Walk a b} (hp : EdgeMinAvoid (k+2) p) (hx : x∉p.support)
    (hy : y∉p.support) (xy : G.Adj x y) (high : k+2≤G.degree x)
    (two : (Pins p x).card=2) (sep : PairedPins p x=∅)
    {i : Nat} (hi : i∈Pins p x) (ii : 2≤i) : ¬G.Adj a (p.getVert i) := by
  classical
  have max := hp.1.1
  by_cases inner : ∀ j∈Pins p x, 2≤j
  · obtain ⟨d2,_,bb⟩ := double_porter_saturated_one_slack hc k max hx two (cap x) conn hy xy
    have bcard : (External G (OmittedStar p x)).card=k := by
      rcases bb with h|h
      · exact h.2
      · simp [sep] at h
    have first := Graffiti189LongestPath.OneSlack.first_eq_if_no_pair
      (p:=p) (x:=x) sep
    have rigid := Graffiti189LongestPath.OneSlack.MultiRotation.rigidity_of_tight hc max hx (by
      rw [Graffiti189LongestPath.OneSlack.cardinal_flankVertices max,flank_count_exact max hx,
        Graffiti189LongestPath.OneSlack.card_pinVertices max,first,bcard,d2,two])
    exact Graffiti189LongestPath.OneSlack.MultiRotation.chord_forces_first_fringe hc max hx hi inner rigid
  intro chord
  push_neg at inner
  obtain ⟨j,hj,hlt⟩ := inner
  have hpositive := Graffiti189LongestPath.Rigidity.pin_pos max hx hj
  have j1 : j=1 := by omega
  subst j
  have ei := (Graffiti189LongestPath.pin_data hi).1
  have ei' : i-1+1=i := by omega
  obtain ⟨q,hq,same,ql,mp⟩ := rotate_start_map max (i-1) (by omega)
    (by simpa only [ei'] using chord)
  have qo : x∉q.support := fun h => hx ((same x).mpr h)
  have es : q.support.toFinset=p.support.toFinset := by
    ext u
    simpa only [List.mem_toFinset] using (same u).symm
  have qmin : EdgeMinAvoid (k+2) q := by
    refine ⟨⟨hq,?_⟩,?_⟩
    · intro u v r h
      rw [es]
      exact hp.1.2 u v r h
    · intro u v r h z hz ho hqz
      exact hp.2 u v r h z hz ho ((same z).mpr hqz)
  have leftE : q.getVert (i-2)=p.getVert 1 := by
    have e := mp (i-2) (by omega)
    rw [if_pos (by omega : i-2≤i-1),show i-1-(i-2)=1 by omega] at e
    exact e
  have rightE : q.getVert i=p.getVert i := by
    have e := mp i (by omega)
    rw [if_neg (by omega : ¬i≤i-1)] at e
    exact e
  have kl : i-2 ∈ Pins q x :=
    mem_filter.mpr ⟨mem_range.mpr (by omega),leftE.symm ▸ (Graffiti189LongestPath.pin_data hj).2⟩
  have kr : i ∈ Pins q x :=
    mem_filter.mpr ⟨mem_range.mpr (by omega),rightE.symm ▸ (Graffiti189LongestPath.pin_data hi).2⟩
  exact (normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn qmin qo high _ kl).2
    (show i-2+2∈Pins q x by rwa [show i-2+2=i by omega])
#print axioms no_start_pin_chord

theorem no_end_pin_chord (hc : G.Connected) (k : Nat) (hk : 3≤k)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b x y : V} {p : G.Walk a b} (hp : EdgeMinAvoid (k+2) p) (hx : x∉p.support)
    (hy : y∉p.support) (xy : G.Adj x y) (high : k+2≤G.degree x)
    (two : (Pins p x).card=2)
    {i : Nat} (hi : i∈Pins p x) (ii : i+2≤p.length) : ¬G.Adj b (p.getVert i) := by
  have rp := Graffiti189LongestPath.OneSlack.MultiRotation.reverse_longest hp.1.1
  have same (z : V) : z∈p.support ↔ z∈p.reverse.support := by simp
  have c := Graffiti189LongestPath.OneSlack.MultiRotation.same_support_pin_count hp.1.1 rp hx same
  have eq : p.reverse.support.toFinset=p.support.toFinset := by
    ext u
    simpa only [List.mem_toFinset] using (same u).symm
  have normal : EdgeMinAvoid (k+2) p.reverse := by
    refine ⟨⟨rp,?_⟩,?_⟩
    · intro u v w hw
      rw [eq]
      exact hp.1.2 u v w hw
    · intro u v w hw z hz ho hq
      exact hp.2 u v w hw z hz ho ((same z).mpr hq)
  have xrev : x∉p.reverse.support := fun e => hx ((same x).mpr e)
  have yrev : y∉p.reverse.support := fun e => hy ((same y).mpr e)
  have sep : PairedPins p.reverse x=∅ := eq_empty_iff_forall_not_mem.mpr (by
    intro t ht
    obtain ⟨ht,u,hu,eq|eq⟩ := mem_filter.mp ht
    · exact (normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn normal xrev high u hu).2
        (eq.symm ▸ ht)
    · exact (normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn normal xrev high t ht).2
        (eq.symm ▸ hu))
  have pr := Graffiti189LongestPath.OneSlack.MultiRotation.pin_reverse hp.1.1 hx hi
  have n := no_start_pin_chord hc k hk cap conn normal xrev yrev xy high
    (by omega : (Pins p.reverse x).card=2) sep pr (by omega)
  rw [getVert_reverse,show p.length-(p.length-i)=i by omega] at n
  exact n

#print axioms no_end_pin_chord
end Graffiti189LongestPath.LockedPins
