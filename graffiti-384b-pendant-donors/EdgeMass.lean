import ForcedDonors

namespace Graffiti384b.Donor
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Sample sets for which the recipient has one seed neighbor and the donor
is deficient. In applications both endpoints are fixed outside the seeds. -/
def pairTrials (F X : Finset V) (b : ℕ) (u v : V) :=
  (X.powersetCard b).filter (fun k => nbr G u (F∪k)=1 ∧ v∈deficient G (F∪k))

omit [Fintype V] in
private theorem add_contacts (F : Finset V) {X k : Finset V} (fx : Disjoint F X) (ks : k⊆X) (u : V) :
    nbr G u (F∪k)=nbr G u F+nbr G u k := by
  unfold nbr
  rw [filter_union,card_union_of_disjoint ((fx.mono_right ks).mono (filter_subset ..) (filter_subset ..))]

/-- Count a pair with zero fixed contacts at the recipient. After conditioning
on its unique sampled neighbor, every remaining seed must avoid its neighborhood.
The donor may already have any number of fixed contacts. -/
theorem zero_fixed (F X : Finset V) (fx : Disjoint F X) (u v : V)
    (zero : nbr G u F=0) {b : ℕ} (pos : 0<b) :
    (pairTrials G F X (b+1) u v).card =
      ∑ t∈X.filter (G.Adj u), loss G (insert t F) (X.filter (fun z => ¬G.Adj u z)) b v := by
  classical
  let U := X.filter (G.Adj u)
  let T := X.filter (fun z => ¬G.Adj u z)
  let Q := pairTrials G F X (b+1) u v
  have data {k : Finset V} (km : k∈Q) : k⊆X ∧ k.card=b+1 ∧ nbr G u k=1 ∧ v∈deficient G (F∪k) := by
    obtain ⟨kc,recv,don⟩ := mem_filter.mp km
    obtain ⟨sub,sz⟩ := mem_powersetCard.mp kc
    rw [add_contacts G F fx sub,zero,Nat.zero_add] at recv
    exact ⟨sub,sz,recv,don⟩
  have single {k : Finset V} (km : k∈Q) : (U.filter (fun t => t∈k)).card=1 := by
    have dk := data km
    have eq : U.filter (fun t => t∈k)=k.filter (G.Adj u) := by
      ext x
      simp only [U,mem_filter]
      exact ⟨fun a => ⟨a.2,a.1.2⟩,fun a => ⟨⟨dk.1 a.1,a.2⟩,a.1⟩⟩
    rw [eq]; exact dk.2.2.1
  have fibre (t : V) (tm : t∈U) :
      (Q.filter (fun k => t∈k)).card=loss G (insert t F) T b v := by
    obtain ⟨tx,ut⟩ := mem_filter.mp tm
    have tt : t∉T := fun m => (mem_filter.mp m).2 ut
    have sep : Disjoint (insert t F) T := disjoint_left.mpr (fun z zf zt =>
      (mem_insert.mp zf).elim (fun eq => tt (eq ▸ zt)) (fun f => disjoint_left.mp fx f (mem_filter.mp zt).1))
    rw [←loss_exact G (insert t F) T sep pos v]
    have join (k : Finset V) : insert t F∪k=F∪insert t k := by ext z; simp [or_assoc,or_left_comm,or_comm]
    refine card_bij' (fun k _ => k.erase t) (fun k _ => insert t k) ?_ ?_ ?_ ?_
    · intro k m
      obtain ⟨km,tk⟩ := mem_filter.mp m
      obtain ⟨sub,sz,count,vd⟩ := data km
      have near : k.filter (G.Adj u)={t} := by
        apply Eq.symm
        exact eq_of_subset_of_card_le (singleton_subset_iff.mpr (mem_filter.mpr ⟨tk,ut⟩))
          (by change (k.filter (G.Adj u)).card=1 at count; simp [count])
      refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_,by rw [card_erase_of_mem tk,sz]; omega⟩,?_⟩
      · intro z ze
        obtain ⟨nt,zk⟩ := mem_erase.mp ze
        exact mem_filter.mpr ⟨sub zk,fun uz => nt (mem_singleton.mp (near ▸ mem_filter.mpr ⟨zk,uz⟩))⟩
      · simpa only [join,insert_erase tk] using vd
    · intro k m
      obtain ⟨kp,vd⟩ := mem_filter.mp m
      obtain ⟨kt,sz⟩ := mem_powersetCard.mp kp
      have nt : t∉k := fun hm => tt (kt hm)
      have sub : insert t k⊆X := insert_subset tx (kt.trans (filter_subset ..))
      have near : (insert t k).filter (G.Adj u)={t} := by
        ext z
        constructor
        · intro zm
          obtain ⟨ins,adj⟩ := mem_filter.mp zm
          exact mem_singleton.mpr ((mem_insert.mp ins).resolve_right (fun zk => (mem_filter.mp (kt zk)).2 adj))
        · rintro zm
          obtain rfl := mem_singleton.mp zm
          exact mem_filter.mpr ⟨mem_insert_self ..,ut⟩
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powersetCard.mpr ⟨sub,by rw [card_insert_of_not_mem nt,sz]⟩,?_,?_⟩,mem_insert_self ..⟩
      · rw [add_contacts G F fx sub,zero]; simp [nbr,near]
      · rwa [←join]
    · intro k m; exact insert_erase (mem_filter.mp m).2
    · intro k m
      have sub := (mem_powersetCard.mp (mem_filter.mp m).1).1
      exact erase_insert (fun tk => tt (sub tk))
  calc
    Q.card = ∑k∈Q,∑t∈U,(if t∈k then 1 else 0 : ℕ) := by
      simp only [sum_boole,Nat.cast_id]
      rw [sum_congr rfl (fun k km => single km)]
      simp
    _ = ∑t∈U,(Q.filter (fun k => t∈k)).card := by rw [sum_comm]; simp
    _ = _ := sum_congr rfl fibre

/-- With one fixed contact at the recipient, the whole sample must avoid its
neighbors. The donor's exact conditional loss counts the usable samples. -/
theorem one_fixed (F X : Finset V) (fx : Disjoint F X) (u v : V)
    (one : nbr G u F=1) {b : ℕ} (pos : 0<b) :
    (pairTrials G F X b u v).card=loss G F (X.filter (fun z => ¬G.Adj u z)) b v := by
  classical
  let T := X.filter (fun z => ¬G.Adj u z)
  rw [←loss_exact G F T (fx.mono_right (filter_subset ..)) pos v]
  congr 1
  ext k
  constructor
  · intro m
    obtain ⟨kp,recv,vd⟩ := mem_filter.mp m
    obtain ⟨sub,sz⟩ := mem_powersetCard.mp kp
    rw [add_contacts G F fx sub,one] at recv
    have empty : k.filter (G.Adj u)=∅ := card_eq_zero.mp (show nbr G u k=0 by omega)
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨fun z zk => mem_filter.mpr ⟨sub zk,fun uz =>
      not_mem_empty z (empty ▸ mem_filter.mpr ⟨zk,uz⟩)⟩,sz⟩,vd⟩
  · intro m
    obtain ⟨kp,vd⟩ := mem_filter.mp m
    obtain ⟨kt,sz⟩ := mem_powersetCard.mp kp
    have sub := kt.trans (show T⊆X from filter_subset ..)
    have empty : k.filter (G.Adj u)=∅ := eq_empty_of_forall_not_mem (fun z m =>
      (mem_filter.mp (kt (mem_filter.mp m).1)).2 (mem_filter.mp m).2)
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨sub,sz⟩,by rw [add_contacts G F fx sub,one]; simp [nbr,empty],vd⟩

end Graffiti384b.Donor
#print axioms Graffiti384b.Donor.zero_fixed
#print axioms Graffiti384b.Donor.one_fixed
