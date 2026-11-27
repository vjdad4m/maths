import Reuse
import Bridge

open Finset
namespace KelmansCactus.PortSwitch

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

omit [Fintype V] in
/-- Partition a (possibly proper) vertex set from a list of chains whose
flattening is repetition-free, when their lengths are all multiples of three. -/
theorem tile_chains (paths : List (List V)) (hn : paths.flatten.Nodup)
    (hch : ∀ P ∈ paths, P.Chain' G.Adj)
    (hdiv : ∀ P ∈ paths, P.length % 3 = 0) :
    ∃ k, Kelmans.Tiles G k paths.flatten.toFinset := by
  induction paths with
  | nil => exact ⟨0,Kelmans.Tiles.empty⟩
  | cons P Q ih =>
    change (P++Q.flatten).Nodup at hn
    have dis : Disjoint P.toFinset Q.flatten.toFinset :=
      disjoint_left.mpr fun _ hp hq =>
        List.disjoint_of_nodup_append hn (List.mem_toFinset.mp hp) (List.mem_toFinset.mp hq)
    obtain ⟨k,hk⟩ := ih hn.of_append_right
      (fun R hR => hch R (List.mem_cons_of_mem _ hR))
      (fun R hR => hdiv R (List.mem_cons_of_mem _ hR))
    have hr := hdiv P (by simp)
    have hP := Kelmans.tiles_of_chain G (P.length/3) P hn.of_append_left (hch P (by simp)) (by omega)
    refine ⟨P.length / 3 + k,?_⟩
    simpa only [List.flatten_cons,List.toFinset_append] using Kelmans.tiles_union G hP hk dis

theorem factor_chains (paths : List (List V)) (len : paths.flatten.length = Fintype.card V)
    (cov : ∀ v : V, v ∈ paths.flatten)
    (hch : ∀ P ∈ paths, P.Chain' G.Adj)
    (hdiv : ∀ P ∈ paths, P.length % 3 = 0) :
    KelmansStarter.HasP3Factor G := by
  have hfull : paths.flatten.toFinset = univ := by
    ext v
    simp [cov v]
  have hcard : paths.flatten.toFinset.card = paths.flatten.length := by rw [hfull,card_univ,len]
  have hn : paths.flatten.Nodup :=
    (Multiset.toFinset_card_eq_card_iff_nodup (m := (↑paths.flatten : Multiset V))).mp hcard
  obtain ⟨k,hk⟩ := tile_chains G paths hn hch hdiv
  rw [hfull] at hk
  exact Kelmans.partition_of_tiles G hk

private theorem card_gap {P : Finset (Finset V)} {D : Finset V}
    (hf : Factor G P) (pure : ∀ t ∈ P, ¬ Mixed D t) : D.card % 3 = 0 := by
  have hD : 3 ∣ ∑ t ∈ P, (t ∩ D).card :=
    Finset.dvd_sum (fun t ht => pure_dvd (pure t ht) (hf.tile t ht).1)
  rw [sum_inter hf D] at hD
  exact Nat.mod_eq_zero_of_dvd hD

private theorem covers_port {P : Finset (Finset V)} {A : Finset V} {p q : V}
    (hf : Factor G P) (ex : OnlyExit (G:=G) A p q)
    (hq : q ∉ A) (residue : A.card % 3 = 2) :
    ∃ t ∈ P, q ∈ t ∧ t ⊆ insert q A := by
  obtain ⟨t,ht,mt⟩ := (bridge_crossing_iff ex hf).mpr (by omega : A.card % 3 ≠ 0)
  have hcard := bridge_residue ex hf ht mt
  have tile3 := (hf.tile t ht).1
  have qt := (ports_mem ex (hf.tile t ht) mt).2
  have hs : (t \ A).card = 1 := by
    have eq := card_sdiff_add_card_inter t A
    omega
  have eq : t \ A = {q} := by
    symm
    apply eq_of_subset_of_card_le
    · intro z hz
      rcases mem_singleton.mp hz with rfl
      exact mem_sdiff.mpr ⟨qt,hq⟩
    · rw [hs,card_singleton]
  refine ⟨t,ht,qt,?_⟩
  intro v hv
  by_cases ha : v ∈ A
  · exact mem_insert_of_mem ha
  · have he : v ∈ t \ A := mem_sdiff.mpr ⟨hv,ha⟩
    rw [eq] at he
    rcases mem_singleton.mp he with rfl
    exact mem_insert_self _ _

/-- A gap whose only exits reach the two ports protected by residue-two
leaves has no mixed tile, and hence its order is divisible by three. This
does not assume the gap itself is a path or the leaves are Hamiltonian. -/
theorem gap_zero {A B D : Finset V} {a b x y : V}
    (ha : OnlyExit (G:=G) A a x) (hb : OnlyExit (G:=G) B b y)
    (ra : A.card % 3 = 2) (rb : B.card % 3 = 2) (hx : x ∉ A) (hy : y ∉ B)
    (hxd : x ∉ D) (hyd : y ∉ D)
    (dA : Disjoint D A) (dB : Disjoint D B)
    (ex : ∀ u ∈ D, ∀ v ∉ D, G.Adj u v → v = x ∨ v = y)
    (fact : KelmansStarter.HasP3Factor G) : D.card % 3 = 0 := by
  obtain ⟨P,ht,hd,hcov⟩ := fact
  have hf : Factor G P := ⟨ht,hd,hcov⟩
  obtain ⟨tx,hxt,xt,hxs⟩ := covers_port G hf ha hx ra
  obtain ⟨ty,hyt,yt,hys⟩ := covers_port G hf hb hy rb
  apply card_gap G hf
  intro t ht' hm
  obtain ⟨⟨u,hu,ud⟩,⟨v,hv,vd⟩⟩ := hm
  obtain ⟨c,hc,hadj⟩ := (hf.tile t ht').2
  have hport : x ∈ t ∨ y ∈ t := by
    by_cases cd : c ∈ D
    · have ne : v ≠ c := by rintro rfl; contradiction
      rcases ex c cd v vd (hadj v hv ne) with rfl | rfl
      · exact Or.inl hv
      · exact Or.inr hv
    · have ne : u ≠ c := by rintro rfl; contradiction
      rcases ex u ud c cd (hadj u hu ne).symm with rfl | rfl
      · exact Or.inl hc
      · exact Or.inr hc
  rcases hport with h | h
  · have eq : t = tx := by
      by_contra ne
      exact disjoint_left.mp (hf.disj t ht' tx hxt ne) h xt
    rcases mem_insert.mp (hxs (eq ▸ hu)) with rfl | ua
    · exact hxd ud
    · exact disjoint_left.mp dA ud ua
  · have eq : t = ty := by
      by_contra ne
      exact disjoint_left.mp (hf.disj t ht' ty hyt ne) h yt
    rcases mem_insert.mp (hys (eq ▸ hu)) with rfl | ub
    · exact hyd ud
    · exact disjoint_left.mp dB ud ub

/-- Sufficiency for the 2-mod-3 case, via attaching each port to its outer
path and then tiling both middle open arcs independently. -/
theorem factor_with_clear_arcs {a b x y : V} {L R A B : List V}
    (hl : (L++[a]).Chain' G.Adj) (hr : (b::R).Chain' G.Adj)
    (hA : A.Chain' G.Adj) (hB : B.Chain' G.Adj)
    (ha : G.Adj a x) (hb : G.Adj y b)
    (rL : L.length % 3 = 1) (rR : R.length % 3 = 1)
    (rA : A.length % 3 = 0) (rB : B.length % 3 = 0)
    (len : L.length + R.length + A.length + B.length + 4 = Fintype.card V)
    (cov : ∀ v : V, v ∈ L ∨ v = a ∨ v ∈ R ∨ v = b ∨ v = x ∨ v = y ∨ v ∈ A ∨ v ∈ B) :
    KelmansStarter.HasP3Factor G := by
  have left : (L ++ [a,x]).Chain' G.Adj :=
    List.chain'_append_cons_cons.mpr ⟨hl,ha,List.chain'_singleton _⟩
  have right : (y :: b :: R).Chain' G.Adj := hr.cons hb
  apply factor_chains G [L++[a,x],y::b::R,A,B]
  · simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.length_append,
      List.length_cons,List.length_nil]
    omega
  · intro v
    have hv := cov v
    simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false]
    tauto
  · intro C hC
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl
    exacts [left,right,hA,hB]
  · intro C hC
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl
    · simp; omega
    · simp; omega
    · exact rA
    · exact rB

omit [Fintype V] in
private theorem finset_disj {A B : List V} (h : A.Disjoint B) :
    Disjoint A.toFinset B.toFinset :=
  disjoint_left.mpr fun _ ha hb => h (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)

/-- Exact criterion for the tree-of-three residue-two cycles. Each outer
cycle is supplied as an attachment-ended Hamiltonian path, and A, B are
the two open arcs of the central cycle after removing its ports x and y.
The exit assumptions say no extra connector/chord bypasses this cut.
The cyclic distances between x and y are one plus the open arc lengths. -/
theorem factor_three_twos_iff {a b x y : V} {L R A B : List V}
    (hl : (L++[a]).Chain' G.Adj) (hr : (b::R).Chain' G.Adj)
    (hA : A.Chain' G.Adj) (hB : B.Chain' G.Adj)
    (ha : G.Adj a x) (hb : G.Adj y b)
    (rL : L.length % 3 = 1) (rR : R.length % 3 = 1)
    (len : L.length + R.length + A.length + B.length + 4 = Fintype.card V)
    (cov : ∀ v : V, v ∈ L ∨ v = a ∨ v ∈ R ∨ v = b ∨ v = x ∨ v = y ∨ v ∈ A ∨ v ∈ B)
    (exL : OnlyExit (G:=G) (L++[a]).toFinset a x)
    (exR : OnlyExit (G:=G) (b::R).toFinset b y)
    (exA : ∀ u ∈ A.toFinset, ∀ v ∉ A.toFinset, G.Adj u v → v = x ∨ v = y)
    (exB : ∀ u ∈ B.toFinset, ∀ v ∉ B.toFinset, G.Adj u v → v = x ∨ v = y) :
    KelmansStarter.HasP3Factor G ↔ A.length % 3 = 0 ∧ B.length % 3 = 0 := by
  constructor
  · intro fact
    let Ps : List (List V) := [L++[a], b::R, [x,y], A, B]
    have hfull : Ps.flatten.toFinset = univ := by
      ext v
      have hv := cov v
      simp only [Ps,List.flatten_cons,List.flatten_nil,List.append_nil,
        List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,mem_univ,iff_true]
      tauto
    have hlen : Ps.flatten.length = Fintype.card V := by
      simp only [Ps,List.flatten_cons,List.flatten_nil,List.append_nil,
        List.length_append,List.length_cons,List.length_nil]
      omega
    have hcard : Ps.flatten.toFinset.card = Ps.flatten.length := by rw [hfull,card_univ,hlen]
    have hn : Ps.flatten.Nodup :=
      (Multiset.toFinset_card_eq_card_iff_nodup (m := (↑Ps.flatten : Multiset V))).mp hcard
    obtain ⟨hn,hdis⟩ := List.nodup_flatten.mp hn
    change List.Pairwise List.Disjoint [L++[a], b::R, [x,y], A, B] at hdis
    obtain ⟨dL,hd⟩ := List.pairwise_cons.mp hdis
    obtain ⟨dR,hd⟩ := List.pairwise_cons.mp hd
    obtain ⟨dports,_⟩ := List.pairwise_cons.mp hd
    have xL : x ∉ (L++[a]).toFinset := by
      intro hx
      exact dL [x,y] (by simp) (List.mem_toFinset.mp hx) (by simp)
    have yR : y ∉ (b::R).toFinset := by
      intro hy
      exact dR [x,y] (by simp) (List.mem_toFinset.mp hy) (by simp)
    have eL : (L++[a]).toFinset.card % 3 = 2 := by
      rw [List.toFinset_card_of_nodup (hn _ (by simp [Ps]))]
      simpa using (show (L.length+1)%3 = 2 by omega)
    have eR : (b::R).toFinset.card % 3 = 2 := by
      rw [List.toFinset_card_of_nodup (hn _ (by simp [Ps]))]
      change (R.length+1)%3 = 2
      omega
    have go : ∀ D ∈ [A,B],
        (∀ u ∈ D.toFinset, ∀ v ∉ D.toFinset, G.Adj u v → v = x ∨ v = y) →
        D.length % 3 = 0 := by
      intro D dm exD
      have xD : x ∉ D.toFinset := fun h => dports D dm (by simp) (List.mem_toFinset.mp h)
      have yD : y ∉ D.toFinset := fun h => dports D dm (by simp) (List.mem_toFinset.mp h)
      have dA : Disjoint D.toFinset (L++[a]).toFinset :=
        (finset_disj (dL D (by simp [dm]))).symm
      have dB : Disjoint D.toFinset (b::R).toFinset :=
        (finset_disj (dR D (by simp [dm]))).symm
      have res := gap_zero G exL exR eL eR xL yR xD yD dA dB exD fact
      rwa [List.toFinset_card_of_nodup (hn D (by simp [Ps,dm]))] at res
    exact ⟨go A (by simp) exA,go B (by simp) exB⟩
  · rintro ⟨rA,rB⟩
    exact factor_with_clear_arcs G hl hr hA hB ha hb rL rR rA rB len cov

#print axioms factor_three_twos_iff

private def Cyclic (P : List V) : Prop :=
  P.Chain' G.Adj ∧ ∀ x ∈ P.getLast?, ∀ y ∈ P.head?, G.Adj x y

omit [Fintype V] [DecidableEq V] in
private theorem split_at {P : List V} {x : V} (hx : x ∈ P) :
    ∃ Q R : List V, P = Q ++ x :: R := by
  induction P with
  | nil => simp at hx
  | cons a A ih =>
    rcases List.mem_cons.mp hx with rfl | hm
    · exact ⟨[],A,rfl⟩
    · obtain ⟨Q,R,hq⟩ := ih hm
      exact ⟨a::Q,R,by rw [hq]; rfl⟩

omit [Fintype V] [DecidableEq V] in
private theorem cyc_start {P : List V} {x : V} (hc : Cyclic G P) (hx : x ∈ P) :
    ∃ R, (x::R).Chain' G.Adj ∧ (x::R).Perm P := by
  obtain ⟨A,B,h⟩ := split_at hx
  subst P
  rcases hc with ⟨hc,hcl⟩
  by_cases ha : A = []
  · subst A
    exact ⟨B,hc,List.Perm.refl _⟩
  · have hB : (x::B) ≠ [] := by simp
    have hjoin : ((x::B) ++ A).Chain' G.Adj := by
      apply hc.right_of_append.append hc.left_of_append
      intro u hu v hv
      apply hcl u _ v _
      · rw [List.getLast?_append_of_ne_nil _ hB]; exact hu
      · rw [List.head?_append_of_ne_nil _ ha]; exact hv
    exact ⟨B++A,hjoin,@List.perm_append_comm V (x::B) A⟩

omit [Fintype V] [DecidableEq V] in
private theorem cyc_end {P : List V} {x : V} (hc : Cyclic G P) (hx : x ∈ P) :
    ∃ R, (R++[x]).Chain' G.Adj ∧ (R++[x]).Perm P := by
  have hrev : Cyclic G P.reverse := by
    refine ⟨List.chain'_reverse.mpr (hc.1.imp fun _ _ e => e.symm),?_⟩
    intro u hu v hv
    rw [List.getLast?_reverse] at hu
    rw [List.head?_reverse] at hv
    exact (hc.2 v hv u hu).symm
  obtain ⟨R,hr,hR⟩ := cyc_start G hrev (List.mem_reverse.mpr hx)
  have h1 : (R.reverse++[x]).Chain' G.Adj := by
    simpa using (List.chain'_reverse.mpr (hr.imp fun _ _ e => e.symm))
  have h2 : (R.reverse++[x]).Perm P := by
    have h : (x::R).reverse.Perm P := ((List.reverse_perm _).trans hR).trans (List.reverse_perm _)
    simpa only [List.reverse_cons] using h
  exact ⟨R.reverse,h1,h2⟩

omit [Fintype V] [DecidableEq V] in
private theorem cycle_join {a a' b b' : V} {A B : List V}
    (hA : ((a::A)++[a']).Chain' G.Adj) (hB : ((b::B)++[b']).Chain' G.Adj)
    (e : G.Adj a' b) (f : G.Adj b' a) :
    Cyclic G ((a::A) ++ a' :: b :: (B++[b'])) := by
  constructor
  · exact List.chain'_append_cons_cons.mpr ⟨hA,e,hB⟩
  · intro x hx y hy
    have hl : (((a::A) ++ a' :: b :: (B++[b'])).getLast?) = some b' := by
      rw [List.getLast?_append_cons]
      simp only [List.getLast?_cons_cons,List.getLast?_cons,List.getLast?_concat,Option.getD_some]
    have hh : (((a::A) ++ a' :: b :: (B++[b'])).head?) = some a := rfl
    rw [hl] at hx
    rw [hh] at hy
    simpa using (show G.Adj x y from by
      have hx' : b' = x := by simpa using hx
      have hy' : a = y := by simpa using hy
      subst x
      subst y
      exact f)

/-- Alternating 4-cycle switch. If two links between two residue-two cycles
line up with an internal edge on each cycle, the links merge the two cycles
into a residue-one cycle. The resulting cycle pairs with a third residue-two
cycle at any specified attachment. Paths A and B omit the internal edges
being switched out; e and f are the two links switched in. -/
theorem rescue_by_switch {a a' b b' z c : V} {A B C : List V}
    (hA : ((a::A)++[a']).Chain' G.Adj) (hB : ((b::B)++[b']).Chain' G.Adj)
    (hC : (c::C).Chain' G.Adj)
    (e : G.Adj a' b) (f : G.Adj b' a) (g : G.Adj z c)
    (port : z ∈ (a::A) ++ a' :: b :: (B++[b']))
    (rA : A.length % 3 = 0) (rB : B.length % 3 = 0) (rC : C.length % 3 = 1)
    (len : A.length + B.length + C.length + 5 = Fintype.card V)
    (cov : ∀ v : V, v ∈ (a::A) ++ a' :: b :: (B++[b']) ∨ v ∈ c::C) :
    KelmansStarter.HasP3Factor G := by
  obtain ⟨R,hr,hperm⟩ := cyc_end G (cycle_join G hA hB e f) port
  have hh : (R ++ z :: c :: C).Chain' G.Adj :=
    List.chain'_append_cons_cons.mpr ⟨hr,g,hC⟩
  have hlen := hperm.length_eq
  simp only [List.length_append,List.length_cons,List.length_nil] at hlen
  apply factor_chains G [R ++ z :: c :: C]
  · simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.length_append,
      List.length_cons]
    omega
  · intro v
    rcases cov v with hm | hm
    · have hR := hperm.mem_iff.mpr hm
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hR
      simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.mem_append,List.mem_cons]
      tauto
    · simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.mem_append,List.mem_cons]
      exact Or.inr (Or.inr (List.mem_cons.mp hm))
  · intro Q hQ
    have he : Q = R ++ z :: c :: C := by simpa using hQ
    simpa [he] using hh
  · intro Q hQ
    have he : Q = R ++ z :: c :: C := by simpa using hQ
    subst Q
    simp only [List.length_append,List.length_cons]
    omega

#print axioms rescue_by_switch
#print axioms gap_zero
#print axioms factor_with_clear_arcs
end KelmansCactus.PortSwitch
