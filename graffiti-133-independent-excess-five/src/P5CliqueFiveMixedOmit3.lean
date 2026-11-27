import P5CliqueMixedPairKernel133

namespace Graffiti133P5CliqueArms.MixedPairCertificate
open SimpleGraph Graffiti133 Graffiti133Camby
set_option maxRecDepth 140000
set_option maxHeartbeats 20000000

def fivePairOmitModel3 : Model 17 := ⟨[(4,5),(4,6),(4,7),(4,8),(5,6),(5,7),(5,8),(5,15),(5,16),(6,7),(6,8),(7,8),(7,13),(7,14),(8,11),(8,12),(9,12),(9,13),(9,14),(9,15),(9,16),(10,11),(10,12),(10,14),(10,16),(11,13),(11,14),(12,13),(13,16),(14,15),(14,16)], ![32880,10640,82592,5440,1539,6149,24585,6,98314,20,24,34,40,66,68,257,260]⟩
def fivePairOmitRows3 : List (Row 17) := [⟨0,402653459,Sum.inr ![4,1,13,6,3,12,5,2,16]⟩,
⟨1073741824,67109139,Sum.inr ![4,1,11,5,12,3,6,14,16]⟩,
⟨536870912,0,Sum.inl ![0,6,14,15]⟩,
⟨268435456,0,Sum.inl ![1,8,16,13]⟩,
⟨134217728,0,Sum.inl ![3,6,13,12]⟩,
⟨67108864,0,Sum.inl ![2,5,11,14]⟩,
⟨16777216,0,Sum.inl ![3,8,16,10]⟩,
⟨8388608,0,Sum.inl ![3,6,14,10]⟩,
⟨1077936128,25199952,Sum.inr ![1,8,16,14,6,0,5,12,10]⟩,
⟨2097152,0,Sum.inl ![1,4,10,11]⟩,
⟨1074790400,0,Sum.inl ![2,9,16,14]⟩,
⟨34603008,268583241,Sum.inr ![3,8,16,9,4,0,5,11,13]⟩,
⟨524288,0,Sum.inl ![0,4,9,15]⟩,
⟨1074003968,0,Sum.inl ![2,9,14,16]⟩,
⟨1310720,0,Sum.inl ![2,14,9,16]⟩,
⟨131072,0,Sum.inl ![1,4,9,13]⟩,
⟨65536,0,Sum.inl ![2,5,12,9]⟩,
⟨134250496,0,Sum.inl ![1,8,12,13]⟩,
⟨4227072,0,Sum.inl ![3,8,12,10]⟩,
⟨33570816,0,Sum.inl ![1,8,11,13]⟩,
⟨49152,0,Sum.inl ![5,11,8,12]⟩,
⟨1073750016,0,Sum.inl ![2,7,14,16]⟩,
⟨67117056,0,Sum.inl ![1,7,14,11]⟩,
⟨270336,0,Sum.inl ![2,7,14,9]⟩,
⟨4096,285214732,Sum.inr ![0,4,10,3,8,16,2,7,13]⟩,
⟨33558528,0,Sum.inl ![1,7,13,11]⟩,
⟨12288,0,Sum.inl ![6,13,7,14]⟩,
⟨2048,0,Sum.inl ![2,7,8,16]⟩,
⟨1024,0,Sum.inl ![0,6,8,15]⟩,
⟨512,0,Sum.inl ![1,7,6,13]⟩,
⟨0,624652,Sum.inr ![7,2,9,4,0,15,8,3,12]⟩,
⟨1073742080,0,Sum.inl ![2,5,16,14]⟩,
⟨33554432,148571,Sum.inr ![4,9,2,5,11,13,6,3,8]⟩,
⟨4194304,8422491,Sum.inr ![6,14,2,5,12,10,4,1,8]⟩,
⟨1048832,0,Sum.inl ![2,5,16,9]⟩,
⟨262400,1074855955,Sum.inr ![1,4,9,14,6,3,12,5,16]⟩,
⟨33024,0,Sum.inl ![5,12,8,16]⟩,
⟨16640,0,Sum.inl ![5,11,8,16]⟩,
⟨8448,1073742391,Sum.inr ![4,1,7,14,6,3,12,5,16]⟩,
⟨128,545259539,Sum.inr ![1,4,10,3,6,14,2,5,15]⟩,
⟨262272,537460755,Sum.inr ![1,4,9,14,6,3,12,5,15]⟩,
⟨32896,0,Sum.inl ![5,12,8,15]⟩,
⟨16512,0,Sum.inl ![5,11,8,15]⟩,
⟨384,0,Sum.inl ![5,15,8,16]⟩,
⟨64,0,Sum.inl ![0,5,8,15]⟩,
⟨32,0,Sum.inl ![1,7,5,11]⟩,
⟨16,0,Sum.inl ![2,5,6,14]⟩,
⟨8,0,Sum.inl ![0,4,8,15]⟩,
⟨4,0,Sum.inl ![2,7,4,9]⟩,
⟨2,0,Sum.inl ![1,4,6,13]⟩,
⟨1,0,Sum.inl ![1,4,5,11]⟩]
def fivePairOmitTree3 : Tree := .fork 8 (.fork 0 (.fork 4 (.fork 1 (.fork 15 (.fork 3 (.fork 6 (.fork 30 (.fork 14 (.fork 28 (.fork 2 (.fork 10 (.fork 11 (.fork 12 (.fork 16 (.fork 17 (.fork 18 (.fork 23 (.fork 19 (.leaf 30) (.leaf 12)) (.leaf 7)) (.fork 19 (.leaf 30) (.leaf 12))) (.leaf 15)) (.leaf 16)) (.fork 13 (.fork 16 (.fork 17 (.fork 19 (.leaf 30) (.leaf 12)) (.leaf 15)) (.leaf 16)) (.leaf 26))) (.leaf 27)) (.leaf 28)) (.leaf 48)) (.leaf 3)) (.fork 2 (.fork 7 (.fork 11 (.fork 12 (.fork 10 (.fork 13 (.fork 16 (.fork 19 (.leaf 30) (.leaf 12)) (.leaf 16)) (.fork 16 (.fork 18 (.fork 19 (.leaf 30) (.leaf 12)) (.leaf 23)) (.leaf 16))) (.leaf 28)) (.fork 13 (.fork 28 (.fork 10 (.fork 16 (.fork 19 (.leaf 30) (.leaf 12)) (.leaf 16)) (.leaf 28)) (.leaf 3)) (.leaf 26))) (.leaf 27)) (.leaf 42)) (.leaf 48))) (.fork 10 (.fork 13 (.fork 14 (.fork 23 (.fork 28 (.fork 2 (.fork 11 (.fork 16 (.fork 17 (.fork 18 (.fork 24 (.fork 25 (.fork 19 (.leaf 30) (.leaf 12)) (.leaf 32)) (.leaf 6)) (.leaf 13)) (.leaf 15)) (.leaf 16)) (.leaf 27)) (.leaf 48)) (.leaf 3)) (.leaf 7)) (.fork 23 (.fork 2 (.fork 7 (.fork 11 (.fork 24 (.fork 28 (.fork 12 (.fork 16 (.fork 18 (.fork 19 (.leaf 30) (.leaf 12)) (.leaf 13)) (.leaf 16)) (.leaf 24)) (.leaf 3)) (.leaf 6)) (.leaf 27)) (.leaf 42)) (.leaf 48)) (.leaf 7))) (.leaf 21)) (.leaf 28))) (.leaf 44)) (.leaf 47)) (.fork 14 (.fork 3 (.fork 13 (.fork 28 (.fork 6 (.fork 7 (.fork 17 (.fork 20 (.fork 27 (.leaf 0) (.leaf 4)) (.fork 25 (.fork 27 (.leaf 0) (.leaf 4)) (.leaf 11))) (.leaf 15)) (.leaf 41)) (.leaf 44)) (.leaf 3)) (.fork 18 (.fork 28 (.fork 6 (.fork 12 (.fork 17 (.fork 26 (.fork 27 (.leaf 0) (.leaf 4)) (.leaf 5)) (.leaf 15)) (.leaf 26)) (.leaf 44)) (.leaf 3)) (.leaf 23))) (.leaf 47)) (.leaf 20))) (.leaf 49)) (.leaf 46)) (.leaf 50)) (.fork 0 (.fork 1 (.fork 4 (.fork 15 (.fork 30 (.fork 3 (.fork 2 (.fork 7 (.fork 13 (.fork 6 (.fork 10 (.fork 11 (.fork 14 (.fork 16 (.fork 20 (.fork 12 (.fork 17 (.fork 19 (.leaf 30) (.leaf 12)) (.leaf 15)) (.fork 17 (.fork 19 (.leaf 30) (.leaf 12)) (.leaf 15))) (.leaf 34)) (.leaf 16)) (.leaf 37)) (.leaf 27)) (.leaf 28)) (.leaf 44)) (.fork 6 (.fork 10 (.fork 11 (.fork 12 (.fork 14 (.fork 16 (.fork 18 (.fork 5 (.fork 9 (.leaf 38) (.leaf 29)) (.leaf 45)) (.leaf 23)) (.leaf 16)) (.leaf 37)) (.leaf 26)) (.leaf 27)) (.leaf 28)) (.leaf 44))) (.leaf 43)) (.leaf 48)) (.leaf 47)) (.leaf 31)) (.leaf 36)) (.leaf 46)) (.leaf 49)) (.leaf 50))

theorem five_pair_omit_3_forbidden {V : Type*} {G : SimpleGraph V}
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (m : Nat) (e : Fin 17→V) (eI : Function.Injective e)
    (fit : ∀ x y,G.Adj (e x) (e y)↔edge fivePairOmitModel3 m x y=true) : False := by
  apply actual_model_forbidden (by decide) h4 h9 fivePairOmitModel3 fivePairOmitRows3 fivePairOmitTree3 _ _ m e eI fit
  · decide
  · decide

#print axioms five_pair_omit_3_forbidden
end Graffiti133P5CliqueArms.MixedPairCertificate
