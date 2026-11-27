import RootQuartet
import StarContacts

open private six_le_treeNumber_of_five_independent_neighbors from CubicEdgeCuts
open private shore_anticomplete from CubicPortThreeShores

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V]
variable {D : Finset V} {X Y : Set V} {r a b : V}

/-- Across a three-cut, a port with both a contact and a noncontact in the
opposite component restricts independent neighbors of a second port on
the first side that miss the first port. -/
theorem card_private_contacts_le_two
    (budget : treeNumber G ≤ 5) (conn : ConnectivityAtLeast G 3) (cut : D.card = 3)
    (offX : ∀ v ∈ D, v ∉ X) (offY : ∀ v ∈ D, v ∉ Y)
    (boundX : ShoreBoundary G D X) (boundY : ShoreBoundary G D Y)
    (apart : Disjoint X Y) (connY : (G.induce Y).Connected)
    (rD : r ∈ D) (aD : a ∈ D) (ra : r ≠ a) (missing : ∃ y ∈ Y, ¬ G.Adj r y)
    (U : Finset V)
    (contact : ∀ u ∈ U, u ∈ X ∧ G.Adj a u ∧ ¬ G.Adj r u)
    (ind : ∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v) : U.card ≤ 2 := by
  classical
  by_contra! many
  obtain ⟨T,sub,card⟩ := Finset.exists_subset_card_eq (show 3 ≤ U.card by omega)
  let e : Fin 3 ≃ ↥T := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe,card])).symm
  let v (i : Fin 3) : V := (e i).val
  have mem (i : Fin 3) : v i ∈ U := sub (e i).property
  have ainj (i j : Fin 3) (h : i ≠ j) : v i ≠ v j :=
    fun eq => h (e.injective (Subtype.ext eq))
  have offa (i : Fin 3) : a ≠ v i := (contact _ (mem i)).2.1.ne
  have nd : [a,v 0,v 1,v 2].Nodup := by
    simp [offa,ainj (0 : Fin 3) 1 (by decide),ainj (0 : Fin 3) 2 (by decide),
      ainj (1 : Fin 3) 2 (by decide)]
  have edge (i : Fin 3) : G.Adj a (v i) := (contact _ (mem i)).2.1
  have no (i j : Fin 3) : ¬ G.Adj (v i) (v j) := ind _ (mem i) _ (mem j)
  obtain ⟨f,eq0,eq1,eq2,eq3,root⟩ := four_ordering nd (edge 0)
    (Or.inl ⟨(edge 1).symm,no 1 0⟩) (Or.inl ⟨(edge 2).symm,no 2 0,no 2 1⟩)
  have leaf (i : Fin 4) (hi : i ≠ 0) : f i ∈ U := by
    fin_cases i
    · exact (hi rfl).elim
    · change f (1 : Fin 4) ∈ U
      exact eq1.symm ▸ mem 0
    · change f (2 : Fin 4) ∈ U
      exact eq2.symm ▸ mem 1
    · change f (3 : Fin 4) ∈ U
      exact eq3.symm ▸ mem 2
  have anti {x y : V} (hx : x ∈ X) (hy : y ∈ Y) : ¬ G.Adj x y :=
    shore_anticomplete offY boundX apart hx hy
  have yDistinct {y : V} (hy : y ∈ Y) (i : Fin 4) : y ≠ f i := by
    intro eq
    by_cases z : i = 0
    · subst i
      rw [eq0] at eq
      exact offY a aD (eq ▸ hy)
    · exact Set.disjoint_left.mp apart (contact _ (leaf i z)).1 (eq ▸ hy)
  have yNonleaf {y : V} (hy : y ∈ Y) (i : Fin 4) (hi : i ≠ 0) : ¬ G.Adj (f i) y :=
    anti (contact _ (leaf i hi)).1 hy
  have ySome : Y.Nonempty := by obtain ⟨y,hy,_⟩ := missing; exact ⟨y,hy⟩
  have aSome := contact_of_shore conn cut.le offY boundY ySome aD
  have rSome := contact_of_shore conn cut.le offY boundY ySome rD
  by_cases aMissing : ∃ y ∈ Y, ¬ G.Adj a y
  · obtain ⟨y,hy,z,hz,ay,yz,az⟩ := two_step_into_shore connY.preconnected aSome aMissing
    have noTail (i : Fin 4) : ¬ G.Adj (f i) z := by
      by_cases eq : i = 0
      · subst i
        simpa only [eq0] using az
      · exact yNonleaf hz i eq
    have six := six_le_treeNumber_of_rooted_four_and_tail f root yz (eq0.symm ▸ ay)
      (yDistinct hy) (yDistinct hz) noTail (yNonleaf hy)
    omega
  have aComplete (y : V) (hy : y ∈ Y) : G.Adj a y :=
    Classical.byContradiction fun h => aMissing ⟨y,hy,h⟩
  by_cases ar : G.Adj a r
  · obtain ⟨y,hy,ry⟩ := missing
    have yT : y ∉ T :=
      fun h => Set.disjoint_left.mp apart (contact _ (sub h)).1 hy
    have rT : r ∉ T := fun h => offX r rD (contact _ (sub h)).1
    have ryNe : r ≠ y := fun e => offY r rD (e ▸ hy)
    let S := insert r (insert y T)
    have cS : S.card = 5 := by simp [S,yT,rT,ryNe,card]
    have edges (u : V) (hu : u ∈ S) : G.Adj a u := by
      simp only [S,Finset.mem_insert] at hu
      rcases hu with rfl|rfl|h
      · exact ar
      · exact aComplete _ hy
      · exact (contact _ (sub h)).2.1
    have stable (u : V) (hu : u ∈ S) (w : V) (hw : w ∈ S) : ¬ G.Adj u w := by
      simp only [S,Finset.mem_insert] at hu hw
      rcases hu with rfl|rfl|hu <;> rcases hw with rfl|rfl|hw
      · exact G.loopless _
      · exact ry
      · exact (contact _ (sub hw)).2.2
      · exact fun h => ry h.symm
      · exact G.loopless _
      · exact fun h => anti (contact _ (sub hw)).1 hy h.symm
      · exact fun h => (contact _ (sub hu)).2.2 h.symm
      · exact anti (contact _ (sub hu)).1 hy
      · exact ind _ (sub hu) _ (sub hw)
    have six := six_le_treeNumber_of_five_independent_neighbors S a cS.ge edges stable
    omega
  · obtain ⟨y,hy,ry⟩ := rSome
    have rDistinct (i : Fin 4) : r ≠ f i := by
      intro e
      by_cases z : i = 0
      · subst i
        exact ra (e.trans eq0)
      · exact offX r rD (e.symm ▸ (contact _ (leaf i z)).1)
    have noTail (i : Fin 4) : ¬ G.Adj (f i) r := by
      by_cases h : i = 0
      · subst i
        simpa only [eq0] using ar
      · exact fun e => (contact _ (leaf i h)).2.2 e.symm
    have six := six_le_treeNumber_of_rooted_four_and_tail f root ry.symm
      (eq0.symm ▸ aComplete y hy) (yDistinct hy) rDistinct noTail (yNonleaf hy)
    omega

/-- At most two disjoint private blocks of the first shore can have
a single contact among the neighbors of the distinguished cut vertex.
The blocks can be arbitrary nonempty sets with the stated boundary. -/
theorem private_sets_le_two [DecidableEq V] {n : Nat}
    (budget : treeNumber G ≤ 5) (conn : ConnectivityAtLeast G 3) (cut : D.card = 3)
    (offX : ∀ v ∈ D, v ∉ X) (offY : ∀ v ∈ D, v ∉ Y)
    (boundX : ShoreBoundary G D X) (boundY : ShoreBoundary G D Y)
    (apart : Disjoint X Y) (connY : (G.induce Y).Connected)
    (rD : r ∈ D) (aD : a ∈ D) (bD : b ∈ D) (ra : r ≠ a)
    (missing : ∃ y ∈ Y, ¬ G.Adj r y)
    (C : Fin n → Set V) (p : Fin n → V) (nonempty : ∀ i, (C i).Nonempty)
    (blocks : ∀ i u, u ∈ C i → u ∈ X ∧ ¬ G.Adj r u)
    (rContact : ∀ i, G.Adj r (p i))
    (disjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (boundary : ∀ i, ShoreBoundary G ({a,b,p i} : Finset V) (C i)) : n ≤ 2 := by
  classical
  by_contra! large
  let Q (i : Fin n) : Finset V := {a,b,p i}
  have qoff (i : Fin n) : ∀ v ∈ Q i, v ∉ C i := by
    intro v hv hc
    have inside := blocks i v hc
    simp only [Q,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl|rfl
    · exact offX _ aD inside.1
    · exact offX _ bD inside.1
    · exact inside.2 (rContact i)
  have qcard (i : Fin n) : (Q i).card ≤ 3 := by
    unfold Q
    have h1 := Finset.card_insert_le a ({b,p i} : Finset V)
    have h2 := Finset.card_insert_le b ({p i} : Finset V)
    simp only [Finset.card_singleton] at h2
    omega
  have aContact (i : Fin n) : ∃ u ∈ C i, G.Adj a u :=
    contact_of_shore conn (qcard i) (qoff i) (boundary i) (nonempty i)
      (Finset.mem_insert_self _ _)
  choose c mem edge using aContact
  have n3 : 3 ≤ n := by omega
  let j (i : Fin 3) : Fin n := ⟨i.val,lt_of_lt_of_le i.isLt n3⟩
  have ji : Function.Injective j := fun _ _ eq =>
    Fin.ext (congrArg (Fin.val : Fin n → Nat) eq)
  let f : Fin 3 ↪ V := ⟨fun i => c (j i),by
    intro i k eq
    change c (j i) = c (j k) at eq
    by_cases same : i = k
    · exact same
    · exact (Set.disjoint_left.mp (disjoint _ _ (fun h => same (ji h))) (mem (j i))
        (eq.symm ▸ mem (j k))).elim⟩
  let U : Finset V := Finset.univ.map f
  have cl (u : V) (hu : u ∈ U) : ∃ i : Fin n, u ∈ C i ∧ G.Adj a u := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hu
    exact ⟨j i,mem (j i),edge (j i)⟩
  have qout (i j : Fin n) {v : V} (hv : v ∈ C j) : v ∉ Q i := by
    have inside := blocks j v hv
    simp only [Q,Finset.mem_insert,Finset.mem_singleton]
    rintro (rfl|rfl|rfl)
    · exact offX _ aD inside.1
    · exact offX _ bD inside.1
    · exact inside.2 (rContact i)
  have ind (u : V) (hu : u ∈ U) (v : V) (hv : v ∈ U) : ¬ G.Adj u v := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨k,_,rfl⟩ := Finset.mem_map.mp hv
    by_cases eq : i = k
    · subst k
      exact G.loopless _
    intro e
    have apart := Set.disjoint_left.mp (disjoint _ _ (fun h => eq (ji h)))
    exact qout (j i) (j k) (mem (j k)) (boundary (j i) _ (mem (j i)) _
      (fun hvi => apart hvi (mem (j k))) e)
  have cap := card_private_contacts_le_two budget conn cut offX offY boundX boundY apart
    connY rD aD ra missing U (by
      intro u hu
      obtain ⟨i,hi,he⟩ := cl u hu
      exact ⟨(blocks i u hi).1,he,(blocks i u hi).2⟩) ind
  have uc : U.card = 3 := by simp [U]
  omega

#print axioms card_private_contacts_le_two
#print axioms private_sets_le_two

end Graffiti199Depleted.Catalogue
