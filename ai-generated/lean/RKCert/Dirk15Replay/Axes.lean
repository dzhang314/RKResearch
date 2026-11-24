module
public import RKCert.Dirk15SparseSample

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def axes5K1 : OrderedAxes 5 1 5 := singleAxes 5

def axes5K2 : OrderedAxes 5 2 10 :=
  codedAxes 5 2 10 (by decide) #[8, 16, 24, 32, 17, 25, 33, 26, 34, 35]
    (by decide +kernel) (by decide +kernel) (by decide)

def axes5K3 : OrderedAxes 5 3 10 :=
  codedAxes 5 3 10 (by decide) #[136, 200, 264, 208, 272, 280, 209, 273, 281, 282]
    (by decide +kernel) (by decide +kernel) (by decide)

def axes5K4 : OrderedAxes 5 4 5 :=
  codedAxes 5 4 5 (by decide) #[1672, 2184, 2248, 2256, 2257]
    (by decide +kernel) (by decide +kernel) (by decide)

def axes6K1 : OrderedAxes 6 1 6 := singleAxes 6

def axes6K2 : OrderedAxes 6 2 15 :=
  codedAxes 6 2 15 (by decide) #[8, 16, 24, 32, 40, 17, 25, 33, 41, 26, 34, 42, 35, 43, 44]
    (by decide +kernel) (by decide +kernel) (by decide)

def axes6K3 : OrderedAxes 6 3 20 :=
  codedAxes 6 3 20 (by decide) #[136, 200, 264, 328, 208, 272, 336, 280, 344, 352, 209, 273, 337, 281, 345, 353, 282, 346, 354, 355]
    (by decide +kernel) (by decide +kernel) (by decide)

def axes6K4 : OrderedAxes 6 4 15 :=
  codedAxes 6 4 15 (by decide) #[1672, 2184, 2696, 2248, 2760, 2824, 2256, 2768, 2832, 2840, 2257, 2769, 2833, 2841, 2842]
    (by decide +kernel) (by decide +kernel) (by decide)

def axes7K1 : OrderedAxes 7 1 7 := singleAxes 7

def axes7K2 : OrderedAxes 7 2 21 :=
  codedAxes 7 2 21 (by decide) #[8, 16, 24, 32, 40, 48, 17, 25, 33, 41, 49, 26, 34, 42, 50, 35, 43, 51, 44, 52, 53]
    (by decide +kernel) (by decide +kernel) (by decide)

def axes7K3 : OrderedAxes 7 3 35 :=
  codedAxes 7 3 35 (by decide) #[136, 200, 264, 328, 392, 208, 272, 336, 400, 280, 344, 408, 352, 416, 424, 209, 273, 337, 401, 281, 345, 409, 353, 417, 425, 282, 346, 410, 354, 418, 426, 355, 419, 427, 428]
    (by decide +kernel) (by decide +kernel) (by decide)

def axes7K4 : OrderedAxes 7 4 35 :=
  codedAxes 7 4 35 (by decide) #[1672, 2184, 2696, 3208, 2248, 2760, 3272, 2824, 3336, 3400, 2256, 2768, 3280, 2832, 3344, 3408, 2840, 3352, 3416, 3424, 2257, 2769, 3281, 2833, 3345, 3409, 2841, 3353, 3417, 3425, 2842, 3354, 3418, 3426, 3427]
    (by decide +kernel) (by decide +kernel) (by decide)

end RKCert.FixedPolynomial.FixedReplay
