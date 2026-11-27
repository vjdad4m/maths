import SeamProtected180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem seam_degree_lt {a : V} {S T : Finset V} (s : Split G a S T) (hc : G.Connected) :
    (side G S).degree ⟨a,s.both.1⟩ < G.degree a := by
  classical
  let l : ↥S := ⟨a,s.both.1⟩
  let t : ↥T := ⟨a,s.both.2⟩
  let B := push ((side G S).neighborFinset l)
  have sub : B⊆G.neighborFinset a := by
    intro x xm
    obtain ⟨v,vm,rfl⟩ := mem_map.mp xm
    exact (G.mem_neighborFinset _ _).mpr (((side G S).mem_neighborFinset _ _).mp vm)
  obtain ⟨v,ed⟩ := exists_adj (side G T) (s.flip.connectedL hc) s.flip.largeL t
  have notin : v.val∉B := fun m => ed.ne (Subtype.ext (s.common (push_sub _ m) v.property).symm)
  have strict : B⊂G.neighborFinset a := Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun eq =>
    notin (eq ▸ (G.mem_neighborFinset _ _).mpr (show G.Adj a v.val from ed))⟩
  have count := card_lt_card strict
  simpa only [B,card_push,card_neighborFinset_eq_degree] using count

private theorem wing_good {a b r : V} {S T : Finset V} (s : Split G a S T) (gc : G.Connected)
    (r' : ↥S) (q : Bool) (A P : Finset V) (ai : Indep G A) (ab : a≠b) (bi : TwoColor G (univ\{a,b}))
    (four : G.degree a=4) (aa : a∈A) (ap : a∈P) (bk : b∉A∩insert r P)
    (root : r'.val=r ∨ r'.val=a) (par : pull (fun v : ↥S => v.val) P=parity (side G S) r' q) :
    Protected (side G S) r' q (pull (fun v : ↥S => v.val) A) := by
  classical
  let L := side G S
  let l : ↥S := ⟨a,s.both.1⟩
  let M := pull (fun v : ↥S => v.val) A
  have mi : Indep L M := fun x xm y ym ne ed => ai _ (mem_pull.mp xm) _ (mem_pull.mp ym)
    (fun eq => ne (Subtype.ext eq)) ed
  obtain ⟨paint,proper⟩ := (color_function ..).mp bi
  by_cases bs : b∈S
  · let z : ↥S := ⟨b,bs⟩
    have ne : l≠z := fun eq => ab (congrArg Subtype.val eq)
    have col : TwoColor L (univ\{l,z}) := by
      have away (x : ↥S) (xm : x∈univ\{l,z}) : x.val∈univ\({a,b}:Finset V) := by
        obtain ⟨_,miss⟩ := mem_sdiff.mp xm
        refine mem_sdiff.mpr ⟨mem_univ _,fun h => miss ?_⟩
        rcases mem_insert.mp h with e|m
        · exact mem_insert.mpr (Or.inl (Subtype.ext e))
        · exact mem_insert_of_mem (mem_singleton.mpr (Subtype.ext (mem_singleton.mp m)))
      exact (color_function ..).mpr ⟨fun x => paint x.val,fun x xm y ym => proper _ (away x xm) _ (away y ym)⟩
    have pin : l∈M∩insert r' (parity L r' q) := mem_inter.mpr ⟨mem_pull.mpr aa,
      mem_insert_of_mem (par ▸ mem_pull.mpr ap)⟩
    have free : z∉M∩insert r' (parity L r' q) := by
      intro zm
      obtain ⟨za,alt⟩ := mem_inter.mp zm
      apply bk
      refine mem_inter.mpr ⟨mem_pull.mp za,?_⟩
      rcases mem_insert.mp alt with e|h
      · have vr : b=r'.val := congrArg Subtype.val e
        rcases root with rr|ra
        · exact mem_insert.mpr (Or.inl (vr.trans rr))
        · exact (ab (vr.trans ra).symm).elim
      · exact mem_insert_of_mem (mem_pull.mp (par.symm ▸ h))
    by_contra bad
    have eq := (solo_rigidity L (s.connectedL gc) s.largeL r' q M mi bad l z ne col pin free).1
    have lt := seam_degree_lt s gc
    change (side G S).degree ⟨a,s.both.1⟩=4 at eq
    omega
  · have col : TwoColor L (univ.erase l) := by
      have away (x : ↥S) (xm : x∈univ.erase l) : x.val∈univ\({a,b}:Finset V) := by
        refine mem_sdiff.mpr ⟨mem_univ _,fun h => ?_⟩
        rcases mem_insert.mp h with e|m
        · exact (mem_erase.mp xm).1 (Subtype.ext e)
        · exact bs ((mem_singleton.mp m) ▸ x.property)
      exact (color_function ..).mpr ⟨fun x => paint x.val,fun x xm y ym => proper _ (away x xm) _ (away y ym)⟩
    have lower : (univ.erase l).card≤bipartiteNum L := le_sup (f:=card) (mem_filter.mpr ⟨mem_univ _,col⟩)
    have count := card_erase_add_one (mem_univ l)
    rw [card_univ] at count
    have sizes : Fintype.card ↥(S : Set V)=Fintype.card ↥S := Fintype.card_congr (Equiv.refl _)
    exact protected_rank_one L (s.connectedL gc) s.largeL (by omega) r' q M mi

/-- If removing the sole protected nonroot transversal tip separates the
graph, the protected witness always exists. No balance assumption is needed. -/
theorem solo_cut_protected (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (a b : V) (ab : a≠b)
    (bi : TwoColor G (univ\{a,b})) (ak : a∈A∩insert r (parity G r p)) (bk : b∉A∩insert r (parity G r p))
    (ar : a≠r) (S T : Finset V) (s : Split G a S T) : Protected G r p A := by
  classical
  by_contra bad
  have four := (solo_rigidity G gc hn r p A ai bad a b ab bi ak bk).1
  have ap := (mem_insert.mp (mem_inter.mp ak).2).resolve_left ar
  have orient {L R : Finset V} (split : Split G a L R) (hr : r∈L) : Protected G r p A := by
    let w : ↥L := ⟨r,hr⟩
    have par := seam_parities split gc w p
    apply protected_join split gc w p A
    · exact wing_good split gc w p A _ ai ab bi four (mem_inter.mp ak).1 ap bk (Or.inl rfl) par.1
    · exact wing_good split.flip gc ⟨a,split.both.2⟩ _ A _ ai ab bi four (mem_inter.mp ak).1 ap bk (Or.inr rfl) par.2
  rcases s.either r with l|t
  · exact bad (orient s l)
  · exact bad (orient s.flip t)

#print axioms seam_degree_lt
#print axioms solo_cut_protected
end Minimal180.PairRepair
