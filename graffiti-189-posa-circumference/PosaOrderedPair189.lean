import PosaTracks189
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.PosaSpine Graffiti189LongestPath.PosaTracks
set_option warningAsError true
set_option maxHeartbeats 6000000
namespace Graffiti189LongestPath.PosaOrderedPair
variable {V ι : Type*} [DecidableEq V] {G : SimpleGraph V}

def splitTracks : List ι → List ι × List ι
  | [] => ([],[])
  | a :: xs => (a :: (splitTracks xs).2,(splitTracks xs).1)

theorem tracks_mem {xs : List ι} (a : ι) :
    a∈(splitTracks xs).1 ∨ a∈(splitTracks xs).2 ↔ a∈xs := by
  induction xs with
  | nil => simp [splitTracks]
  | cons b xs ih =>
    simp only [splitTracks,List.mem_cons]
    tauto

theorem tracks_disjoint {xs : List ι} (nodup : xs.Nodup) :
    List.Disjoint (splitTracks xs).1 (splitTracks xs).2 := by
  induction xs with
  | nil => simp [splitTracks]
  | cons a xs ih =>
    have h := List.nodup_cons.mp nodup
    intro y left right
    change y∈a::(splitTracks xs).2 at left
    change y∈(splitTracks xs).1 at right
    rcases List.mem_cons.mp left with eq|left
    · exact h.1 (eq ▸ (tracks_mem y).mp (Or.inl right))
    · exact ih h.2 right left

theorem tracks_separated (S : Finset ι) (l r : ι → Nat) (N : Nat)
    {c : Nat} {xs : List ι} (h : PosaGreedy189.Trace S l r N c xs) :
    (splitTracks xs).1.Pairwise (fun x y => r x≤l y) ∧
      (splitTracks xs).2.Pairwise (fun x y => r x≤l y) := by
  induction h with
  | stop => simp [splitTracks]
  | @step c a xs ha tail ih =>
    refine ⟨List.pairwise_cons.mpr ⟨?_,ih.2⟩,ih.1⟩
    intro b hb
    cases xs with
    | nil => simp [splitTracks] at hb
    | cons x tt =>
      change b∈(splitTracks tt).1 at hb
      have bm := (tracks_mem b).mp (Or.inl hb)
      exact (PosaGreedy189.Trace.step ha tail).later_separated (pre:=[]) bm

/-- A pair of ordered simple paths, forming a genuine cycle: they share
only the endpoints, and at least one has an internal vertex. -/
structure OrderedPair {a b : V} (p : G.Walk a b) where
  left : G.Walk a b
  right : G.Walk a b
  leftPath : left.IsPath
  rightPath : right.IsPath
  leftOrder : Ordered p left
  rightOrder : Ordered p right
  only : ∀ z∈left.support,z∈right.support → z=a ∨ z=b
  internal_exact : ∃ z,(z∈left.support ∨ z∈right.support) ∧ z≠a ∧ z≠b

/-- Checked greedy interval chains realize an ordered two-route cycle in
the graph, using labelled off-spine disjoint detours. -/
theorem exists_ordered_pair {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (n : 2≤p.length) (S : Finset ι) (l r : ι → Nat)
    (D : ∀ j∈S,Detour p (l j) (r j))
    (offDisj : ∀ i (hi : i∈S) j (hj : j∈S), i≠j →
      ∀ z∈(D i hi).walk.support,z∈(D j hj).walk.support → z∈p.support)
    (bridge : ∀ i,0<i → i<p.length → ∃ j∈S,l j<i ∧ i<r j) :
    Nonempty (OrderedPair p) := by
  classical
  obtain ⟨j,js,j0,tr⟩ := PosaGreedy189.exists_spanning_chain n
    (fun d hd => (D d hd).bound) bridge
  let A := (splitTracks (j::js)).1
  let B := (splitTracks (j::js)).2
  have trN : (j::js).Nodup :=
    tr.pairwise_increasing.imp (by intro x y xy e; exact (Nat.lt_irrefl _) (e ▸ xy.1))
  have ds : List.Disjoint A B := tracks_disjoint trN
  have sp := tracks_separated S l r p.length tr
  have AA (i : ι) (hi : i∈A) := tr.mem_source_right ((tracks_mem i).mp (Or.inl hi))
  have BB (i : ι) (hi : i∈B) := tr.mem_source_right ((tracks_mem i).mp (Or.inr hi))
  obtain ⟨P⟩ := make_track p S l r D hp offDisj A 0 (by omega)
    (fun i h => (AA i h).1) sp.1 (fun _ _ => Nat.zero_le _)
  obtain ⟨Q⟩ := make_track p S l r D hp offDisj B 0 (by omega)
    (fun i h => (BB i h).1) sp.2 (fun _ _ => Nat.zero_le _)
  have only : ∀ z∈P.walk.support,z∈Q.walk.support → z=a ∨ z=b := by
    intro z zp zq
    by_cases h : z∈p.support
    · obtain ⟨i,e,il⟩ := mem_support_iff_exists_getVert.mp h
      by_cases e0 : i=0
      · exact Or.inl (e.symm.trans (e0 ▸ p.getVert_zero))
      by_cases en : i=p.length
      · exact Or.inr (e.symm.trans (en ▸ p.getVert_length))
      obtain ⟨d,dm,dl,dr⟩ := tr.covers (by omega : 1≤i) (by omega : i<p.length)
      rcases (tracks_mem d).mpr dm with da|db
      · exact (P.skip i il d da dl dr (e.symm ▸ zp)).elim
      · exact (Q.skip i il d db dl dr (e.symm ▸ zq)).elim
    obtain ⟨u,uA,uS,ui⟩ := P.exterior z zp h
    obtain ⟨v,vB,vS,vi⟩ := Q.exterior z zq h
    have ne : u≠v := fun e => ds uA (e.symm ▸ vB)
    exact (h (offDisj u uS v vS ne z ui vi)).elim
  have jr : 1<r j := (tr.mem_source_right List.mem_cons_self).2
  have ju : r j≤p.length := (D j (tr.mem_source_right List.mem_cons_self).1).bound
  have inside : ∃ z,(z∈P.walk.support ∨ z∈Q.walk.support) ∧ z≠a ∧ z≠b := by
    have goes (i : Nat) (ip : 0<i) (il : i<p.length) :
        p.getVert i≠a ∧ p.getVert i≠b := by
      constructor
      · intro eq
        have e := hp.getVert_injOn (Nat.le_of_lt il) (by omega : 0≤p.length)
          (eq.trans p.getVert_zero.symm)
        omega
      · intro eq
        have e := hp.getVert_injOn (Nat.le_of_lt il) (by simp)
          (eq.trans p.getVert_length.symm)
        omega
    by_cases hit : r j<p.length
    · have jA : j∈A := List.mem_cons_self
      exact ⟨_,Or.inl (P.hits j jA).2,goes _ (by omega) hit⟩
    have final : r j=p.length := by omega
    have empty : js=[] := by
      cases ee : js with
      | nil => rfl
      | cons d rest =>
        have m : d∈js := ee.symm ▸ List.mem_cons_self
        have lt := (List.pairwise_cons.mp tr.pairwise_increasing).1 d m
        have dN := (D d (tr.mem_source_right (List.mem_cons_of_mem _ m)).1).bound
        omega
    have noB : B=[] := by simp [B,empty,splitTracks]
    have lit := Q.complete 1 (by omega) (by omega) (by simp [noB])
    exact ⟨_,Or.inr lit,goes _ (by omega) (by omega)⟩
  let PP := P.walk.copy p.getVert_zero p.getVert_length
  let QQ := Q.walk.copy p.getVert_zero p.getVert_length
  have po : Ordered p PP := by simpa [PP,Ordered,length_copy,getVert_copy] using P.ordered
  have qo : Ordered p QQ := by simpa [QQ,Ordered,length_copy,getVert_copy] using Q.ordered
  refine ⟨⟨PP,QQ,by simpa [PP] using P.simple,by simpa [QQ] using Q.simple,
    po,qo,?_,?_⟩⟩
  · simpa only [PP,QQ,support_copy] using only
  · simpa only [PP,QQ,support_copy] using inside

#print axioms exists_ordered_pair
end Graffiti189LongestPath.PosaOrderedPair
