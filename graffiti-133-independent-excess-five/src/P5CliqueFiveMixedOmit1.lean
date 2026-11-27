import P5CliqueMixedPairKernel133

namespace Graffiti133P5CliqueArms.MixedPairCertificate
open SimpleGraph Graffiti133 Graffiti133Camby
set_option maxRecDepth 140000
set_option maxHeartbeats 20000000

def fivePairOmitModel1 : Model 17 := ⟨[(4,5),(4,6),(4,7),(4,8),(5,6),(5,7),(5,8),(5,15),(5,16),(6,7),(6,8),(6,13),(6,14),(7,8),(7,11),(7,12),(9,11),(9,12),(9,14),(9,15),(9,16),(10,12),(10,13),(10,14),(10,16),(11,16),(12,15),(12,16),(13,15),(13,16),(14,15)], ![41072,2448,70304,17728,1539,5,6153,24582,98314,20,24,66,68,129,136,257,260]⟩
def fivePairOmitRows1 : List (Row 17) := [⟨0,1140891660,Sum.inr ![4,0,15,8,3,14,7,2,12]⟩,
⟨1073741824,0,Sum.inl ![3,8,15,14]⟩,
⟨536870912,0,Sum.inl ![2,7,13,16]⟩,
⟨134217728,536911884,Sum.inr ![4,0,13,7,14,3,8,16,12]⟩,
⟨67108864,0,Sum.inl ![0,6,12,15]⟩,
⟨33554432,0,Sum.inl ![1,8,16,11]⟩,
⟨16777216,0,Sum.inl ![3,8,16,10]⟩,
⟨142606336,18920960,Sum.inr ![0,6,12,16,8,1,7,14,10]⟩,
⟨4194304,0,Sum.inl ![0,4,10,13]⟩,
⟨2097152,0,Sum.inl ![3,6,12,10]⟩,
⟨135266304,0,Sum.inl ![2,9,16,12]⟩,
⟨524288,0,Sum.inl ![0,4,9,15]⟩,
⟨262144,0,Sum.inl ![2,7,14,9]⟩,
⟨268566528,67668486,Sum.inr ![3,6,12,9,4,1,7,13,15]⟩,
⟨134348800,0,Sum.inl ![2,9,12,16]⟩,
⟨1179648,0,Sum.inl ![2,12,9,16]⟩,
⟨65536,0,Sum.inl ![1,4,9,11]⟩,
⟨0,331795,Sum.inr ![5,2,9,4,1,11,6,3,14]⟩,
⟨268435456,536078,Sum.inr ![4,9,2,7,13,15,8,3,6]⟩,
⟨134250496,0,Sum.inl ![2,7,12,16]⟩,
⟨1081344,134619148,Sum.inr ![0,4,9,16,8,3,14,7,12]⟩,
⟨163840,0,Sum.inl ![2,7,12,9]⟩,
⟨16384,50339852,Sum.inr ![0,4,10,3,8,16,2,7,11]⟩,
⟨1064960,33890316,Sum.inr ![0,4,9,16,8,3,14,7,11]⟩,
⟨49152,0,Sum.inl ![6,11,7,12]⟩,
⟨8192,0,Sum.inl ![2,7,8,16]⟩,
⟨1073745920,0,Sum.inl ![0,6,14,15]⟩,
⟨8392704,0,Sum.inl ![3,6,14,10]⟩,
⟨36864,0,Sum.inl ![6,12,7,14]⟩,
⟨20480,0,Sum.inl ![6,11,7,14]⟩,
⟨268437504,0,Sum.inl ![0,6,13,15]⟩,
⟨34816,0,Sum.inl ![6,12,7,13]⟩,
⟨18432,0,Sum.inl ![6,11,7,13]⟩,
⟨6144,0,Sum.inl ![6,13,7,14]⟩,
⟨1024,0,Sum.inl ![0,6,8,15]⟩,
⟨512,0,Sum.inl ![0,6,7,13]⟩,
⟨536871168,0,Sum.inl ![0,5,16,13]⟩,
⟨134217984,0,Sum.inl ![2,5,16,12]⟩,
⟨1048832,0,Sum.inl ![2,5,16,9]⟩,
⟨33024,134226029,Sum.inr ![4,0,5,16,8,3,14,7,12]⟩,
⟨128,69206035,Sum.inr ![1,4,10,3,6,12,2,5,15]⟩,
⟨268435584,0,Sum.inl ![0,5,15,13]⟩,
⟨384,0,Sum.inl ![5,15,8,16]⟩,
⟨64,0,Sum.inl ![0,5,8,15]⟩,
⟨32,0,Sum.inl ![0,5,7,13]⟩,
⟨16,0,Sum.inl ![2,5,6,12]⟩,
⟨8,0,Sum.inl ![0,4,8,15]⟩,
⟨4,0,Sum.inl ![0,4,7,13]⟩,
⟨2,0,Sum.inl ![1,4,6,11]⟩,
⟨1,0,Sum.inl ![2,5,4,9]⟩]
def fivePairOmitTree1 : Tree := .fork 15 (.fork 2 (.fork 13 (.fork 3 (.fork 12 (.fork 1 (.fork 27 (.fork 11 (.fork 26 (.fork 0 (.fork 4 (.fork 7 (.fork 9 (.fork 16 (.fork 18 (.leaf 17) (.leaf 12)) (.leaf 16)) (.leaf 35)) (.fork 8 (.fork 9 (.fork 16 (.fork 18 (.leaf 17) (.leaf 12)) (.leaf 16)) (.leaf 35)) (.leaf 42))) (.leaf 45)) (.leaf 49)) (.leaf 4)) (.fork 0 (.fork 4 (.fork 7 (.fork 14 (.fork 8 (.fork 16 (.fork 18 (.leaf 17) (.leaf 12)) (.leaf 16)) (.fork 16 (.fork 18 (.leaf 17) (.leaf 12)) (.leaf 16))) (.leaf 32)) (.fork 8 (.fork 14 (.fork 26 (.fork 16 (.fork 18 (.leaf 17) (.leaf 12)) (.leaf 16)) (.leaf 4)) (.leaf 32)) (.leaf 42))) (.leaf 45)) (.leaf 49))) (.fork 8 (.fork 9 (.fork 11 (.fork 26 (.fork 0 (.fork 4 (.fork 10 (.fork 16 (.fork 17 (.fork 18 (.leaf 17) (.leaf 12)) (.leaf 14)) (.leaf 16)) (.leaf 34)) (.leaf 45)) (.leaf 49)) (.leaf 4)) (.fork 0 (.fork 4 (.fork 14 (.fork 21 (.fork 26 (.fork 7 (.fork 10 (.fork 16 (.fork 17 (.fork 18 (.leaf 17) (.leaf 12)) (.leaf 14)) (.leaf 16)) (.leaf 34)) (.leaf 40)) (.leaf 4)) (.leaf 9)) (.leaf 32)) (.leaf 45)) (.leaf 49))) (.leaf 35)) (.leaf 37))) (.leaf 48)) (.fork 11 (.fork 1 (.fork 8 (.fork 26 (.fork 9 (.fork 14 (.fork 17 (.fork 30 (.leaf 0) (.leaf 1)) (.fork 19 (.fork 27 (.fork 28 (.fork 30 (.leaf 0) (.leaf 1)) (.leaf 13)) (.leaf 14)) (.leaf 11))) (.leaf 29)) (.leaf 35)) (.leaf 4)) (.fork 20 (.fork 26 (.fork 7 (.fork 9 (.fork 19 (.fork 27 (.fork 30 (.leaf 0) (.leaf 1)) (.leaf 37)) (.leaf 11)) (.leaf 35)) (.leaf 42)) (.leaf 4)) (.leaf 38))) (.leaf 48)) (.leaf 33))) (.leaf 46)) (.leaf 25)) (.leaf 47)) (.fork 2 (.fork 3 (.fork 12 (.fork 13 (.fork 27 (.fork 0 (.fork 1 (.fork 8 (.fork 11 (.fork 18 (.fork 4 (.fork 14 (.fork 17 (.fork 7 (.fork 9 (.fork 10 (.fork 16 (.leaf 17) (.leaf 16)) (.leaf 34)) (.leaf 35)) (.fork 9 (.fork 10 (.fork 16 (.leaf 17) (.leaf 16)) (.leaf 34)) (.leaf 35))) (.leaf 21)) (.leaf 24)) (.leaf 45)) (.leaf 12)) (.leaf 31)) (.fork 11 (.fork 18 (.fork 20 (.fork 4 (.fork 7 (.fork 5 (.fork 6 (.leaf 39) (.leaf 43)) (.leaf 44)) (.leaf 42)) (.leaf 45)) (.leaf 38)) (.leaf 12)) (.leaf 31))) (.leaf 48)) (.leaf 49)) (.leaf 19)) (.leaf 25)) (.leaf 28)) (.leaf 46)) (.leaf 47))

theorem five_pair_omit_1_forbidden {V : Type*} {G : SimpleGraph V}
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (m : Nat) (e : Fin 17→V) (eI : Function.Injective e)
    (fit : ∀ x y,G.Adj (e x) (e y)↔edge fivePairOmitModel1 m x y=true) : False := by
  apply actual_model_forbidden (by decide) h4 h9 fivePairOmitModel1 fivePairOmitRows1 fivePairOmitTree1 _ _ m e eI fit
  · decide
  · decide

#print axioms five_pair_omit_1_forbidden
end Graffiti133P5CliqueArms.MixedPairCertificate
