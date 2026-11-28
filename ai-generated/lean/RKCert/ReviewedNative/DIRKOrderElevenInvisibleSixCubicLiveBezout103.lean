/-! Kernel replay of the standalone ascending-coefficient GF(103) Bézout
certificate for the explicit degree-276 γ=5 cofactor. Exact coefficient
ingress and degree preservation are separate arithmetic replays.
-/
namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixCubicLiveBezout103

set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

def F : List Nat := [
  84, 66, 37, 25, 8, 2, 60, 41, 95, 94, 9, 80, 83, 16, 53, 53, 80, 24, 75, 90, 101, 7, 56, 39,
  101, 83, 3, 20, 61, 79, 55, 65, 26, 7, 21, 50, 56, 37, 52, 61, 75, 69, 96, 95, 14, 68, 66, 20,
  59, 35, 66, 27, 68, 52, 87, 72, 97, 32, 26, 97, 2, 56, 57, 57, 45, 94, 73, 87, 40, 61, 95, 28,
  79, 22, 24, 57, 23, 34, 58, 22, 73, 75, 24, 25, 100, 88, 58, 87, 84, 97, 75, 56, 51, 15, 87, 96,
  6, 66, 71, 72, 93, 71, 21, 9, 102, 37, 99, 63, 68, 80, 60, 43, 24, 63, 68, 76, 84, 44, 45, 59,
  57, 3, 29, 20, 28, 35, 42, 80, 91, 76, 34, 57, 1, 15, 39, 73, 93, 43, 85, 67, 20, 84, 27, 20,
  9, 43, 6, 26, 56, 7, 82, 58, 61, 4, 56, 78, 26, 85, 24, 30, 13, 45, 3, 84, 31, 90, 86, 49,
  0, 49, 20, 13, 79, 59, 95, 57, 65, 34, 23, 70, 59, 79, 12, 38, 19, 16, 102, 58, 24, 66, 30, 64,
  69, 87, 97, 96, 35, 22, 16, 74, 79, 26, 44, 7, 58, 77, 88, 80, 60, 32, 18, 98, 10, 36, 81, 48,
  1, 11, 93, 50, 56, 71, 22, 31, 59, 89, 36, 3, 73, 81, 29, 39, 36, 17, 64, 23, 30, 67, 24, 101,
  4, 51, 1, 65, 5, 52, 0, 17, 27, 97, 99, 28, 91, 29, 99, 30, 75, 42, 25, 42, 0, 83, 18, 67,
  82, 33, 31, 51, 53, 64, 18, 96, 64, 14, 58, 63, 1
]

def G : List Nat := [
  61, 79, 60, 69, 15, 90, 6, 40, 66, 75, 64, 29, 27, 14, 22, 17, 99, 81, 92, 9, 15, 6, 90, 64,
  45, 54, 74, 98, 33, 8, 87, 43, 66, 19, 23, 62, 20, 7, 56, 61, 30, 99, 100, 48, 91, 69, 49, 67,
  19, 97, 25, 100, 1, 63, 62, 30, 72, 83, 36, 39, 74, 40, 47, 23, 39, 3, 46, 66, 42, 8, 77, 29,
  30, 102, 36, 41, 78, 86, 46, 6, 39, 62, 81, 21, 70, 55, 100, 89, 46, 4, 87, 39, 40, 82, 22, 19,
  79, 23, 15, 22, 3, 38, 69, 69, 73, 22, 99, 50, 26, 56, 78, 67, 82, 31, 64, 39, 64, 73, 17, 35,
  78, 56, 80, 94, 44, 72, 100, 87, 23, 10, 28, 44, 59, 73, 45, 29, 40, 102, 58, 22, 24, 35, 41, 76,
  14, 15, 78, 44, 30, 37, 69, 19, 98, 48, 87, 8, 9, 85, 60, 22, 35, 7, 99, 51, 58, 69, 50, 37,
  23, 69, 75, 15, 54, 82, 21, 63, 80, 98, 92, 12, 30, 7, 64, 24, 92, 91, 21, 58, 36, 42, 63, 57,
  50, 53, 3, 11, 7, 100, 84, 27, 77, 91, 98, 54, 47, 95, 79, 73, 36, 20, 24, 81, 53, 95, 30, 10,
  86, 54, 82, 74, 74, 45, 16, 87, 11, 98, 22, 2, 86, 49, 93, 49, 11, 51, 35, 24, 44, 16, 13, 60,
  49, 47, 89, 87, 79, 30, 57, 74, 5, 37, 8, 50, 64, 35, 92, 31, 63, 36, 9, 30, 47, 44, 73, 82,
  11, 15, 69, 43, 50, 38, 87, 34, 35, 36, 38, 29
]

def U : List Nat := [
  1, 21, 56, 31, 51, 66, 56, 6, 74, 55, 59, 22, 89, 85, 72, 56, 21, 92, 34, 7, 101, 38, 37, 0,
  79, 29, 78, 70, 4, 12, 5, 78, 48, 82, 47, 55, 0, 52, 27, 78, 43, 27, 18, 100, 100, 93, 54, 52,
  102, 60, 12, 86, 7, 22, 89, 39, 97, 78, 56, 97, 20, 75, 100, 100, 70, 19, 59, 73, 11, 46, 95, 85,
  28, 28, 68, 60, 55, 91, 77, 51, 14, 66, 39, 21, 32, 10, 90, 55, 11, 9, 36, 90, 65, 69, 16, 36,
  55, 58, 1, 86, 8, 87, 62, 10, 47, 12, 81, 11, 35, 17, 87, 84, 87, 9, 62, 20, 26, 69, 96, 48,
  4, 53, 46, 16, 13, 23, 12, 78, 48, 5, 29, 66, 59, 2, 76, 19, 55, 13, 97, 67, 68, 44, 69, 63,
  76, 99, 9, 91, 87, 84, 5, 50, 57, 34, 48, 91, 10, 52, 1, 75, 102, 88, 3, 35, 76, 4, 19, 17,
  10, 51, 102, 15, 48, 3, 37, 35, 28, 15, 1, 19, 59, 94, 28, 78, 39, 63, 60, 68, 23, 64, 24, 19,
  1, 95, 74, 21, 89, 37, 2, 42, 4, 83, 95, 13, 69, 46, 75, 16, 28, 26, 17, 3, 99, 101, 29, 71,
  6, 55, 76, 34, 91, 49, 1, 66, 74, 11, 95, 44, 57, 39, 84, 58, 86, 24, 13, 68, 95, 53, 23, 73,
  93, 96, 77, 35, 9, 15, 76, 32, 8, 89, 44, 24, 39, 1, 23, 85, 48, 23, 36, 37, 52, 65, 42, 46,
  42, 82, 26, 10, 41, 40, 70, 49, 52, 35, 27
]

def V : List Nat := [
  78, 102, 20, 98, 84, 78, 69, 26, 78, 45, 59, 95, 34, 95, 50, 47, 20, 13, 4, 1, 4, 88, 35, 67,
  85, 6, 68, 41, 15, 37, 64, 65, 74, 94, 8, 2, 21, 73, 82, 22, 31, 24, 2, 79, 19, 22, 78, 21,
  7, 96, 27, 12, 76, 43, 42, 32, 10, 64, 2, 93, 42, 7, 59, 43, 97, 86, 69, 37, 30, 98, 90, 74,
  77, 34, 10, 65, 25, 95, 1, 42, 32, 84, 70, 1, 23, 6, 31, 80, 63, 67, 71, 45, 80, 53, 12, 44,
  25, 0, 82, 23, 99, 14, 35, 60, 19, 61, 56, 21, 82, 81, 47, 11, 16, 81, 82, 82, 10, 90, 65, 70,
  33, 97, 44, 53, 46, 61, 59, 77, 58, 5, 35, 53, 61, 11, 63, 11, 47, 56, 18, 53, 92, 10, 39, 80,
  13, 19, 80, 53, 38, 73, 56, 93, 72, 73, 5, 71, 14, 18, 59, 92, 93, 81, 62, 39, 53, 28, 79, 83,
  10, 30, 66, 43, 46, 51, 68, 68, 54, 32, 53, 98, 61, 19, 102, 0, 85, 101, 64, 39, 98, 98, 84, 19,
  54, 73, 17, 12, 19, 0, 21, 21, 48, 60, 67, 24, 99, 39, 97, 43, 4, 18, 23, 74, 20, 28, 77, 80,
  65, 72, 53, 34, 51, 55, 96, 48, 49, 71, 86, 17, 15, 6, 29, 21, 74, 41, 39, 25, 83, 84, 86, 11,
  14, 35, 36, 86, 94, 14, 20, 41, 38, 15, 98, 72, 97, 42, 20, 45, 44, 24, 52, 46, 61, 99, 23, 15,
  72, 92, 43, 46, 85, 6, 63, 37, 15, 53, 92, 63
]

def conv (f g : List Nat) (n : Nat) : Nat :=
  let r := List.replicate (n+1-g.length) 0 ++ (g.take (n+1)).reverse
  ((f.take (n+1)).zip r).foldl (fun s q => s+q.1*q.2) 0

def check (n : Nat) : Bool :=
  (conv F U n + conv G V n) % 103 == if n=0 then 1 else 0

theorem maxDegreeBound : F.length + U.length ≤ 552 ∧ G.length + V.length ≤ 552 := by decide

theorem block0 : (List.range 16).all (fun j => check (0+j)) = true := by decide

theorem block16 : (List.range 16).all (fun j => check (16+j)) = true := by decide

theorem block32 : (List.range 16).all (fun j => check (32+j)) = true := by decide

theorem block48 : (List.range 16).all (fun j => check (48+j)) = true := by decide

theorem block64 : (List.range 16).all (fun j => check (64+j)) = true := by decide

theorem block80 : (List.range 16).all (fun j => check (80+j)) = true := by decide

theorem block96 : (List.range 16).all (fun j => check (96+j)) = true := by decide

theorem block112 : (List.range 16).all (fun j => check (112+j)) = true := by decide

theorem block128 : (List.range 16).all (fun j => check (128+j)) = true := by decide

theorem block144 : (List.range 16).all (fun j => check (144+j)) = true := by decide

theorem block160 : (List.range 16).all (fun j => check (160+j)) = true := by decide

theorem block176 : (List.range 16).all (fun j => check (176+j)) = true := by decide

theorem block192 : (List.range 16).all (fun j => check (192+j)) = true := by decide

theorem block208 : (List.range 16).all (fun j => check (208+j)) = true := by decide

theorem block224 : (List.range 16).all (fun j => check (224+j)) = true := by decide

theorem block240 : (List.range 16).all (fun j => check (240+j)) = true := by decide

theorem block256 : (List.range 16).all (fun j => check (256+j)) = true := by decide

theorem block272 : (List.range 16).all (fun j => check (272+j)) = true := by decide

theorem block288 : (List.range 16).all (fun j => check (288+j)) = true := by decide

theorem block304 : (List.range 16).all (fun j => check (304+j)) = true := by decide

theorem block320 : (List.range 16).all (fun j => check (320+j)) = true := by decide

theorem block336 : (List.range 16).all (fun j => check (336+j)) = true := by decide

theorem block352 : (List.range 16).all (fun j => check (352+j)) = true := by decide

theorem block368 : (List.range 16).all (fun j => check (368+j)) = true := by decide

theorem block384 : (List.range 16).all (fun j => check (384+j)) = true := by decide

theorem block400 : (List.range 16).all (fun j => check (400+j)) = true := by decide

theorem block416 : (List.range 16).all (fun j => check (416+j)) = true := by decide

theorem block432 : (List.range 16).all (fun j => check (432+j)) = true := by decide

theorem block448 : (List.range 16).all (fun j => check (448+j)) = true := by decide

theorem block464 : (List.range 16).all (fun j => check (464+j)) = true := by decide

theorem block480 : (List.range 16).all (fun j => check (480+j)) = true := by decide

theorem block496 : (List.range 16).all (fun j => check (496+j)) = true := by decide

theorem block512 : (List.range 16).all (fun j => check (512+j)) = true := by decide

theorem block528 : (List.range 16).all (fun j => check (528+j)) = true := by decide

theorem block544 : (List.range 7).all (fun j => check (544+j)) = true := by decide

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixCubicLiveBezout103
