module
public import RKCert.Dirk15SparseSample

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def axes7K5 : OrderedAxes 7 5 21 :=
  codedAxes 7 5 21 (by decide) #[18056, 22152, 26248, 22664, 26760, 27272, 22728, 26824, 27336, 27400, 22736, 26832, 27344, 27408, 27416, 22737, 26833, 27345, 27409, 27417, 27418]
    (by decide +kernel) (by decide +kernel) (by decide)

end RKCert.FixedPolynomial.FixedReplay
