import LocalFrontier
namespace Graffiti384b.RichRoot.Examples
open Finset SimpleGraph
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def neighbors : Fin 13 → Finset (Fin 13)
  | 0 => {1,2,3,4,6,7,8,9,10}
  | 1 => {0,2,4,6,9,10}
  | 2 => {0,1,5,6,7,8,9}
  | 3 => {0,4,7,10}
  | 4 => {0,1,3,5,6,7,8,9,10}
  | 5 => {2,4,6,7,8,9}
  | 6 => {0,1,2,4,5,8,9,10}
  | 7 => {0,2,3,4,5,9,10}
  | 8 => {0,2,4,5,6,9,10}
  | 9 => {0,1,2,4,5,6,7,8,10,11,12}
  | 10 => {0,1,3,4,6,7,8,9,11}
  | 11 => {9,10}
  | 12 => {9}

def adjacentRoot : SimpleGraph (Fin 13) where
  Adj u v := v∈neighbors u
  symm := fun _ _ h => (show ∀u v : Fin 13,v∈neighbors u → u∈neighbors v by decide) _ _ h
  loopless := (show ∀v : Fin 13,v∉neighbors v by decide)
instance : DecidableRel adjacentRoot.Adj := fun u v => inferInstanceAs (Decidable (v∈neighbors u))

theorem adjacent_profile : (nonleaves adjacentRoot).card=12 ∧ (types adjacentRoot).card=13 ∧
    trianglesAt adjacentRoot 9=28 ∧ trianglesAt adjacentRoot 11=1 ∧ adjacentRoot.Adj 9 10 ∧
    adjacentRoot.Adj 9 11 ∧ adjacentRoot.Adj 10 11 ∧ adjacentRoot.degree 12=1 ∧ bound adjacentRoot=6 := by decide

theorem adjacent_certificate : gamma adjacentRoot≤bound adjacentRoot := by
  let S := exchangePool adjacentRoot 9 11 10
  have rich : ∀v∈S,2≤trianglesAt (inside adjacentRoot S) v := by decide
  apply path_exchange adjacentRoot (r:=9) (e:=11) (b:=10) (z:=12)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  apply Or.inl
  constructor
  · exact ⟨fun v vm => Nat.zero_lt_of_lt (rich v vm),fun x xm _ _ low _ _ => by
      have two := rich x xm; change trianglesAt (inside adjacentRoot S) x=1 at low; omega⟩
  · exact Or.inl (Or.inl (by decide))

def coreNeighbors : Fin 9 → Finset (Fin 9)
  | 0 => {5,6,7,8}
  | 1 => {5,6,8}
  | 2 => {6,7,8}
  | 3 => {7,8}
  | 4 => ∅
  | 5 => {0,1,7,8}
  | 6 => {0,1,2,7,8}
  | 7 => {0,2,3,5,6,8}
  | 8 => {0,1,2,3,5,6,7}

def rooted (r : Fin 9) : SimpleGraph (Fin 9) where
  Adj u v := v∈coreNeighbors u ∨ (u=4 ∧ v=r ∧ r≠4) ∨ (u=r ∧ v=4 ∧ r≠4)
  symm := by
    intro u v adj
    rcases adj with h|⟨h,k,d⟩|⟨h,k,d⟩
    · exact Or.inl ((show ∀u v : Fin 9,v∈coreNeighbors u → u∈coreNeighbors v by decide) _ _ h)
    · exact Or.inr (Or.inr ⟨k,h,d⟩)
    · exact Or.inr (Or.inl ⟨k,h,d⟩)
  loopless := fun u adj => by
    rcases adj with h|⟨a,b,d⟩|⟨a,b,d⟩
    · exact (show ∀u : Fin 9,u∉coreNeighbors u by decide) u h
    · exact d (b.symm.trans a)
    · exact d (a.symm.trans b)
instance (r : Fin 9) : DecidableRel (rooted r).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _)))

theorem remote_certificate : gamma (rooted 0)≤bound (rooted 0) := by
  let G := rooted 0
  let S := rootPool G 0
  have pos : ∀v∈S,0<trianglesAt (inside G S) v := by decide
  have uniq : ∀v∈S,trianglesAt (inside G S) v=1 → v=3 := by decide
  apply root_exchange G (r:=0) (z:=4) (by decide) (by decide) (by decide)
    (Or.inl ⟨⟨pos,fun x xm y ym vx vy _ => (uniq x xm vx).trans (uniq y ym vy).symm⟩,Or.inl (Or.inr ⟨5,by decide,by decide⟩)⟩)

/-- Even the precise necessary contact pattern can occur in an equality graph. -/
theorem tight_shore_example :
    let G := rooted 2
    let S := rootPool G 2
    let L : Finset (Fin 9) := {5,6,7,8}
    let R : Finset (Fin 9) := {0,1,3}
    (types G).card=9 ∧ (nonleaves G).card=8 ∧ trianglesAt G 2=3 ∧ G.Adj 2 4 ∧ G.degree 4=1 ∧
    HasResidualPalette G S ∧ Split (triangleEdges G S) S L R ∧
    S.filter (G.Adj 2)⊆L ∧ L.card=R.card+1 ∧ gamma G=bound G := by
  let G := rooted 2
  let S := rootPool G 2
  have pos : ∀v∈S,0<trianglesAt (inside G S) v := by decide
  have uniq : ∀v∈S,trianglesAt (inside G S) v=1 → v=3 := by decide
  have ex : ∃D : Finset (Fin 9), TwoDominates G D ∧ D.card=4 :=
    ⟨{1,4,7,8},(by decide : ∀v : Fin 9,v∉({1,4,7,8}:Finset (Fin 9)) → 2≤nbr G v {1,4,7,8}),by decide⟩
  have exactScore : gamma G=4 := by
    apply le_antisymm (Nat.sInf_le ex) (le_csInf ⟨4,ex⟩ ?_)
    rintro k ⟨D,good,rfl⟩
    by_contra! small
    let bad := (univ : Finset (Fin 9)).powerset.filter (fun X => X.card<4 ∧ ∀v,v∉X → 2≤nbr G v X)
    have empty : bad=∅ := by decide
    have mem : D∈bad := mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),small,good⟩
    exact not_mem_empty _ (empty ▸ mem)
  refine ⟨by decide,by decide,by decide,by decide,by decide,
    ⟨pos,fun x xm y ym vx vy _ => (uniq x xm vx).trans (uniq y ym vy).symm⟩,?_,by decide,by decide,
    exactScore.trans (by decide)⟩
  exact ⟨by decide,by decide,by decide,by decide⟩

private theorem connected_of_two_steps {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n)
    (h : ∀v,v=r ∨ G.Adj r v ∨ ∃w,G.Adj r w ∧ G.Adj w v) : G.Connected := by
  apply (connected_iff_exists_forall_reachable G).mpr
  refine ⟨r,fun v => ?_⟩
  rcases h v with rfl|adj|⟨w,rw,wv⟩
  · exact Reachable.refl _
  · exact adj.reachable
  · exact rw.reachable.trans wv.reachable

theorem connected_examples : adjacentRoot.Connected ∧ (rooted 0).Connected ∧ (rooted 2).Connected :=
  ⟨connected_of_two_steps _ 9 (by decide),connected_of_two_steps _ 8 (by decide),connected_of_two_steps _ 8 (by decide)⟩

end Graffiti384b.RichRoot.Examples
#print axioms Graffiti384b.RichRoot.Examples.adjacent_profile
#print axioms Graffiti384b.RichRoot.Examples.adjacent_certificate
#print axioms Graffiti384b.RichRoot.Examples.remote_certificate
#print axioms Graffiti384b.RichRoot.Examples.tight_shore_example

#print axioms Graffiti384b.RichRoot.Examples.connected_examples
