import SharedRanks
import EarTriangle
import CleanFinish
namespace Graffiti384b.Shared
open Finset SimpleGraph
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Two independent ears are omitted in every sample when their high anchors
fit on three pins. The third ear supplies the additional 346104 omissions. -/
theorem three_pins (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {e f a b z : V} (ef : e≠f) (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (thin : G.neighborFinset a∩G.neighborFinset b={e})
    (az : a≠z) (bz : b≠z) (pins : ({a,b,z}:Finset V)⊆high G)
    (df : G.degree f=2) (other : G.neighborFinset f⊆{a,b,z})
    (ind : ∀ u v,G.degree u=2 → G.degree v=2 → ¬G.Adj u v) : gamma G≤bound G := by
  classical
  by_contra! bad
  obtain ⟨hs,es⟩ := Cover31.residual G t q bad
  obtain ⟨inj,floor,_,_⟩ := Repair.maximal_diversity G (by omega)
  let J : Finset V := {a,b,z}
  let X := high G\J
  let E := LowSample.twos G
  let O : Finset V := {e,f}
  have de : G.degree e=2 := by rw [←card_neighborFinset_eq_degree,ear,card_pair ab]
  have mE {v : V} (d : G.degree v=2) : v∈E := mem_sdiff.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun h => by have := (mem_filter.mp h).2; omega⟩
  have oe : O⊆E := insert_subset (mE de) (singleton_subset_iff.mpr (mE df))
  have jo : Disjoint J E := disjoint_left.mpr (fun _ jm em => (mem_sdiff.mp em).2 (pins jm))
  have xe : Disjoint X E := disjoint_left.mpr (fun _ m ed => (mem_sdiff.mp ed).2 (mem_sdiff.mp m).1)
  have xj : Disjoint X J := disjoint_left.mpr (fun _ m => (mem_sdiff.mp m).2)
  have xs : X.card=26 := by dsimp only [X]; rw [card_sdiff pins,hs]; simp [J,ab,az,bz]
  have os : O.card=2 := card_pair ef
  have inJ (w : V) (wo : w∈O) : G.neighborFinset w⊆J := by
    rcases mem_insert.mp wo with rfl|eq
    · rw [ear]; intro i m; simpa [J] using (show i=a ∨ i=b ∨ i=z from by simpa using (mem_insert.mp m).imp_right (fun h => Or.inl (mem_singleton.mp h)))
    · rw [mem_singleton.mp eq]; exact other
  have safe (w : V) (wo : w∈O) : 2≤nbr G w (X∪O)ᶜ := by
    have inc : G.neighborFinset w⊆(X∪O)ᶜ.filter (G.Adj w) := by
      intro i m; have jm := inJ w wo m
      exact mem_filter.mpr ⟨mem_compl.mpr (fun p => (mem_union.mp p).elim
        (fun ix => disjoint_left.mp xj ix jm) (fun io => disjoint_left.mp jo jm (oe io))),(G.mem_neighborFinset ..).mp m⟩
    have h := card_le_card inc
    rwa [card_neighborFinset_eq_degree,LowSample.two_degree G (oe wo)] at h
  have away (i : V) (ix : i∈X) (w : V) (wo : w∈O) (iw : G.Adj i w) : False :=
    disjoint_left.mp xj ix (inJ w wo ((G.mem_neighborFinset ..).mpr iw.symm))
  let B := fun v : V => (26-nbr G v X).choose (9-nbr G v X)
  have zero (w : V) (wo : w∈O) : nbr G w X=0 := by
    apply card_eq_zero.mpr; apply eq_empty_iff_forall_not_mem.mpr
    intro i m; exact away i (mem_filter.mp m).1 w wo (mem_filter.mp m).2.symm
  have two (w : V) (we : w∈E) := LowSample.two_degree G we
  have gains : 2*3124550+346104≤∑ w∈E,B w := by
    have fix (w : V) (wo : w∈O) : B w=3124550 := by dsimp only [B]; rw [zero w wo]; decide
    have each (w : V) (wh : w∈E\O) : 346104≤B w := by
      have cnt : nbr G w X≤G.degree w := by
        rw [←card_neighborFinset_eq_degree]
        exact card_le_card (fun i m => (G.mem_neighborFinset ..).mpr (mem_filter.mp m).2)
      rw [two w (mem_sdiff.mp wh).1] at cnt
      let d := nbr G w X
      change 346104≤(26-d).choose (9-d)
      have le : d≤2 := cnt
      rcases (show d=0 ∨ d=1 ∨ d=2 by omega) with h|h|h <;> rw [h] <;> decide
    have sum := sum_le_sum each
    have count : (E\O).card=1 := by rw [card_sdiff oe,os]; change (LowSample.twos G).card-2=1; omega
    have so : (∑ w∈O,B w)=2*3124550 := by rw [sum_congr rfl fix,sum_const,os,smul_eq_mul]
    simp only [sum_const,count,one_smul] at sum
    have add := sum_sdiff oe (f:=B)
    omega
  let A : Finset V := {a,b}
  let hits := X.filter (fun w => 0<nbr G w J)
  let m := hits.card
  have plus {k : V} (kj : k∈J) : X.filter (G.Adj k)⊆hits := by
    intro i im; exact mem_filter.mpr ⟨(mem_filter.mp im).1,card_pos.mpr ⟨k,mem_filter.mpr ⟨kj,(mem_filter.mp im).2.symm⟩⟩⟩
  have eh : e∉high G := (mem_sdiff.mp (mE de)).2
  have common {w : V} (aw : G.Adj a w) (bw : G.Adj b w) : w=e := by
    have wm : w∈G.neighborFinset a∩G.neighborFinset b := mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr aw,(G.mem_neighborFinset ..).mpr bw⟩
    rwa [thin,mem_singleton] at wm
  have dis : Disjoint (X.filter (G.Adj a)) (X.filter (G.Adj b)) := disjoint_left.mpr (by
    intro i am bm
    have eq := common (mem_filter.mp am).2 (mem_filter.mp bm).2
    exact eh (eq ▸ (mem_sdiff.mp (mem_filter.mp am).1).1))
  have xy : nbr G a X+nbr G b X≤m := by
    have h := card_le_card (union_subset (plus (show a∈J by simp [J])) (plus (show b∈J by simp [J])))
    rwa [card_union_of_disjoint dis] at h
  have partition {i : V} (ih : i∈high G) (ix : i∉X) : i=a ∨ i=b ∨ i=z := by
    have im : i∈J := by by_contra no; exact ix (mem_sdiff.mpr ⟨ih,no⟩)
    simpa [J] using im
  have anchor (p r : V) (pr : p=a ∧ r=b ∨ p=b ∧ r=a) :
      trianglesAt G p≤3+(nbr G p X+1).choose 2 := by
    have size : nbr G p (X∪{z})≤nbr G p X+1 := by
      unfold nbr; rw [filter_union]
      exact (card_union_le ..).trans (Nat.add_le_add_left ((card_le_card (filter_subset ..)).trans_eq (card_singleton z)) _)
    rw [←es]; apply score_cap G p (X∪{z}) _ size
    intro i j pi pj ij ih jh
    by_cases ix : i∈X
    · exact mem_union_left _ ix
    rcases pr with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · rcases partition ih ix with eq|eq|eq
      · exact False.elim (pi.ne eq.symm)
      · subst i; exact False.elim (eh (common pj ij ▸ jh))
      · exact mem_union_right _ (mem_singleton.mpr eq)
    · rcases partition ih ix with eq|eq|eq
      · subst i; exact False.elim (eh (common ij pj ▸ jh))
      · exact False.elim (pi.ne eq.symm)
      · exact mem_union_right _ (mem_singleton.mpr eq)
  have sc : trianglesAt G z≤3+(m+1).choose 2 := by
    have zw : z∈(insert e A)ᶜ := by
      have ze : z≠e := fun eq => eh (eq ▸ pins (show z∈J by simp [J]))
      simp [A,ze,az.symm,bz.symm]
    have one := (PortRepair29.thin_degrees G ear thin z zw).1
    have size : nbr G z (X∪A)≤m+1 := by
      unfold nbr; rw [filter_union]
      exact (card_union_le ..).trans (Nat.add_le_add (card_le_card (plus (show z∈J by simp [J]))) one)
    rw [←es]; apply score_cap G z (X∪A) _ size
    intro i j zi _ _ ih _
    by_cases ix : i∈X
    · exact mem_union_left _ ix
    rcases partition ih ix with eq|eq|eq
    · exact mem_union_right _ (mem_insert.mpr (Or.inl eq))
    · exact mem_union_right _ (mem_insert_of_mem (mem_singleton.mpr eq))
    · exact False.elim (zi.ne eq.symm)
  have hx : insert a (insert b (insert z X))⊆high G := insert_subset (pins (by simp [J])) (insert_subset
    (pins (by simp [J])) (insert_subset (pins (by simp [J])) sdiff_subset))
  have cap := shared_pool G n X O ab az bz xs os (xe.mono_right oe) safe away sdiff_subset xj
    (inj.mono (show ((insert a (insert b (insert z X)):Finset V):Set V)⊆high G from hx))
    (fun i im => floor i (hx im)) E xe two (fun i im j jm => ind i j (two i im) (two j jm))
    gains _ _ m xy rfl (anchor a b (Or.inl ⟨rfl,rfl⟩)) (anchor b a (Or.inr ⟨rfl,rfl⟩)) sc
  rw [bound,n,t] at bad; omega
end Graffiti384b.Shared
#print axioms Graffiti384b.Shared.three_pins
