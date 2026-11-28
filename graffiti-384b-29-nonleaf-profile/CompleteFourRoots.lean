import SatelliteBound

namespace Graffiti384b.PrivatePatch
open Finset SimpleGraph Four29 LowSample
open private Remaining29.account from Remaining29
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem ordered_finish {e f a b : V} (t : (types G).card=29) (q : (nonleaves G).card=29) (h : (high G).card=27)
    (bad : bound G<gamma G) (de : G.degree e=2) (df : G.degree f=2) (ef : e≠f)
    (aw : a∈roots G e f) (bw : b∈roots G e f) (ab : a≠b)
    (wa : Weak G (roots G e f) (triangleContacts G e f) a) (wb : Weak G (roots G e f) (triangleContacts G e f) b)
    (only : ∀v∈roots G e f,Weak G (roots G e f) (triangleContacts G e f) v → v=a ∨ v=b)
    (order : trianglesAt G a<trianglesAt G b) : False := by
  classical
  let W := roots G e f
  let C := triangleContacts G e f
  have D := data_of_failure G t h q bad de df ef
  obtain ⟨sep,_,no3⟩ := root_shape G t q h bad de df ef
  obtain ⟨U,S,au,bs,dis,uc,sc⟩ := carriers G D de df sep no3 aw bw ab wa wb order
  obtain ⟨wc,we,ec,es,touch⟩ := shape_sets G D de df
  obtain ⟨P,Q,wp,eq',apart,right,left,one,free⟩ := assemble G wc we ec es touch
  have frame : TwoGaps G P Q a b := by
    refine ⟨apart,wp aw,wp bw,one a aw,one b bw,?_,right⟩
    intro v vm va vb
    apply left v vm
    by_cases vw : v∈W
    · exact Or.inr (fun weak => (only v vw weak).elim va vb)
    · exact Or.inl vw
  have H : Board G e f a b P Q U S := ⟨D,by omega,bad,frame,
    mem_union_right _ (eq' (mem_insert_self ..)),
    mem_union_right _ (eq' (mem_insert_of_mem (mem_singleton_self _))),dis,
    (free a aw wa).mono_left au.inside,(free b bw wb).mono_left bs.inside,
    fun _ m => (mem_filter.mp (au.inside m)).2.1,fun _ m => (mem_filter.mp (bs.inside m)).2.1,
    au.paired,bs.paired,card_pos.mp (by omega),card_pos.mp (by omega)⟩
  apply H.impossible G aw bw wp
  · have cp : C⊆pool G e f := filter_subset ..
    exact union_subset (au.inside.trans ((filter_subset ..).trans cp)) (bs.inside.trans ((filter_subset ..).trans cp))
  · rw [card_union_of_disjoint dis,uc,sc]

/-- The full 29-type, 29-nonleaf, 27-high profile, with no contact,
ordering, degree-two-label or connectivity hypotheses. -/
theorem exact_profile (t : (types G).card=29) (q : (nonleaves G).card=29) (h : (high G).card=27) :
    gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt; intro bad
  have count := Remaining29.account G
  obtain ⟨e,f,ef,ears⟩ := card_eq_two.mp (show (twos G).card=2 by omega)
  have de := LowSample.two_degree G (show e∈twos G from ears ▸ mem_insert_self ..)
  have df := LowSample.two_degree G (show f∈twos G from ears ▸ mem_insert_of_mem (mem_singleton_self _))
  obtain ⟨a,aw,b,bw,ab,wa,wb,only,_⟩ := private_front G t q h bad de df ef
  have D := data_of_failure G t h q bad de df ef
  have diff : trianglesAt G a≠trianglesAt G b := fun eq => ab (D.scoreInj (D.highRoots aw) (D.highRoots bw) eq)
  rcases lt_or_gt_of_ne diff with lt|gt
  · exact ordered_finish G t q h bad de df ef aw bw ab wa wb only lt
  · exact ordered_finish G t q h bad de df ef bw aw ab.symm wb wa (fun v vw w => (only v vw w).symm) gt

theorem fifteen_omissions (t : (types G).card=29) (q : (nonleaves G).card=29) (h : (high G).card=27) :
    gamma G≤Fintype.card V-15 := by simpa [bound,t] using exact_profile G t q h
/-- Removing the high-vertex count in the same nonleaf profile uses the earlier bound for at least 28 high vertices. -/
theorem twenty_nine_nonleaves (t : (types G).card=29) (q : (nonleaves G).card=29) :
    gamma G≤Fintype.card V-15 := by
  have cap := type_bound G
  by_cases h : 28≤(high G).card
  · exact Remaining29.exact_above_minimum G t q.ge h
  · exact fifteen_omissions G t q (by omega)
end Graffiti384b.PrivatePatch
#print axioms Graffiti384b.PrivatePatch.exact_profile
#print axioms Graffiti384b.PrivatePatch.fifteen_omissions
#print axioms Graffiti384b.PrivatePatch.twenty_nine_nonleaves
