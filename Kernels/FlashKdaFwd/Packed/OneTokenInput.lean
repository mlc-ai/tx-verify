-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Workspace
public import Lemmas.Tcgen05.MemFloat

@[expose] public section
namespace FlashKda.Packed.OneToken
open PTX Workspace Sequence
noncomputable section

def problem : Problem where
  sequences := 1
  heads := 1
  length _ := 1
  query _ _ _ _ := 0
  key _ _ _ _ := 0
  logDecay _ _ _ _ := 0
  betaLogit _ _ _ := 0
  value _ _ _ _ := 0
  initial _ _ _ _ := 0
  scale := 1
  outputBase := 524288
  stateBase := 589824

def bases : Bases := ⟨131072,196608,262144,393216,65536⟩

def tile := coefficients (suffix (problem.tokens 0 0 0) 0) (liveRows 1 0) 1

def lane (n d : Nat) (h : 0 < d) : Fin d := ⟨n % d,Nat.mod_lt n h⟩

def matrixBytes {r c : Nat} (hr : 0 < r) (hc : 0 < c) (f : Fin r → Fin c → ℝ)
    (offset : Nat) : Byte :=
  (.float .bf16 (f (lane (offset/(2*c)) r hr) (lane (offset/2) c hc)),offset%2)

def memory (l : Loc) : Option (Option Byte) :=
  if l.space ≠ .global ∨ l.cta ≠ 0 ∨ l.addr < 65536 ∨ 655360 ≤ l.addr then
    if l.space = .shared ∧ l.cta = 0 ∧ l.addr < 98432 then some none else none
  else some (some (if l.addr < 65544 then
    (Proof.b64 0).byteAt (l.addr-65536)
  else if l.addr < 65552 then (Proof.b64 1).byteAt (l.addr-65544)
  else if l.addr < 139264 then matrixBytes (by decide) (by decide) tile.decayedKey (l.addr-131072)
  else if l.addr < 147456 then matrixBytes (by decide) (by decide) tile.decayedQuery (l.addr-139264)
  else if l.addr < 155648 then matrixBytes (by decide) (by decide) tile.restoredKey (l.addr-147456)
  else if l.addr < 156672 then
    (.float .f32 (tile.totalDecay (lane ((l.addr-155648)/4) 128 (by decide))),l.addr%4)
  else if l.addr < 157696 then matrixBytes (by decide) (by decide) tile.inverse (l.addr-156672)
  else if l.addr < 158720 then matrixBytes (by decide) (by decide) tile.score (l.addr-157696)
  else if l.addr < 393216 then (.float .bf16 0,l.addr%2)
  else (.float .f32 0,l.addr%4)))

private theorem matrix_slot {r c : Nat} (hr : 0 < r) (hc : 0 < c) (f : Fin r → Fin c → ℝ)
    (t : Fin r) (k : Fin c) {b : Nat} (hb : b < 2) :
    matrixBytes hr hc f ((2*c)*t.val+2*k.val+b) = (.float .bf16 (f t k),b) := by
  have h : 2*k.val+b < 2*c := by omega
  have row : ((2*c)*t.val+2*k.val+b)/(2*c) = t.val := by
    rw [Nat.add_assoc,Nat.mul_add_div (by omega),Nat.div_eq_of_lt h,Nat.add_zero]
  have col : ((2*c)*t.val+2*k.val+b)/2 = c*t.val+k.val := by rw [Nat.mul_assoc]; omega
  have x : lane (((2*c)*t.val+2*k.val+b)/(2*c)) r hr = t :=
    Fin.ext (by simp [lane,row,Nat.mod_eq_of_lt t.isLt])
  have y : lane (((2*c)*t.val+2*k.val+b)/2) c hc = k := Fin.ext (by
    simp [lane,col,Nat.mod_eq_of_lt k.isLt])
  simp only [matrixBytes,x,y,Prod.mk.injEq,true_and]
  rw [Nat.mul_assoc]
  omega

private theorem rows (r c : Nat) (hr : 0 < r) (hc : 0 < c) (f : Fin r → Fin c → ℝ) (a : Nat)
    (mem : ∀ n < 2*c*r, memory ⟨.global,0,a+n⟩ = some (some (matrixBytes hr hc f n)))
    (t : Fin r) (k : Fin c) :
    memFloat .bf16 memory ⟨.global,0,a+(2*c*t.val+2*k.val)⟩ = .ok (f t k) := by
  apply memFloat_float
  intro b hb
  change b < 2 at hb
  change memory ⟨.global,0,(a+_)+b⟩ = _
  rw [Nat.add_assoc,mem _ (by nlinarith [t.isLt,k.isLt])]
  exact congrArg (fun x => some (some x)) (matrix_slot hr hc f t k hb)

set_option maxHeartbeats 2000000 in
private theorem recorded : Recorded problem bases memory 0 0 0 tile := by
  change (∀ (t : Fin 16) (k : Fin 128), memFloat .bf16 memory
      ⟨.global,0,131072+(256*t.val+2*k.val)⟩ = .ok (tile.decayedKey t k)) ∧
    (∀ (t : Fin 16) (k : Fin 128), memFloat .bf16 memory
      ⟨.global,0,139264+(256*t.val+2*k.val)⟩ = .ok (tile.decayedQuery t k)) ∧
    (∀ (t : Fin 16) (k : Fin 128), memFloat .bf16 memory
      ⟨.global,0,147456+(256*t.val+2*k.val)⟩ = .ok (tile.restoredKey t k)) ∧
    (∀ k : Fin 128, memFloat .f32 memory ⟨.global,0,155648+4*k.val⟩ = .ok (tile.totalDecay k)) ∧
    (∀ t j : Fin 16, memFloat .bf16 memory
      ⟨.global,0,156672+(32*t.val+2*j.val)⟩ = .ok (tile.inverse t j)) ∧
    (∀ t j : Fin 16, memFloat .bf16 memory
      ⟨.global,0,157696+(32*t.val+2*j.val)⟩ = .ok (tile.score t j))
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  case refine_1 => apply rows 16 128 (by decide) (by decide) tile.decayedKey 131072
                   intro n hn
                   simp only [memory,ne_eq,not_true_eq_false,false_or]
                   split_ifs <;> first | omega | simp
  case refine_2 => apply rows 16 128 (by decide) (by decide) tile.decayedQuery 139264
                   intro n hn
                   simp only [memory,ne_eq,not_true_eq_false,false_or]
                   split_ifs <;> first | omega | simp
  case refine_3 => apply rows 16 128 (by decide) (by decide) tile.restoredKey 147456
                   intro n hn
                   simp only [memory,ne_eq,not_true_eq_false,false_or]
                   split_ifs <;> first | omega | simp
  case refine_5 => apply rows 16 16 (by decide) (by decide) tile.inverse 156672
                   intro n hn
                   simp only [memory,ne_eq,not_true_eq_false,false_or]
                   split_ifs <;> first | omega | simp
  case refine_6 => apply rows 16 16 (by decide) (by decide) tile.score 157696
                   intro n hn
                   simp only [memory,ne_eq,not_true_eq_false,false_or]
                   split_ifs <;> first | omega | simp
  intro k
  apply memFloat_float
  intro b hb
  change b < 4 at hb
  let a := 155648+4*k.val+b
  change memory ⟨.global,0,a⟩ = some (some (.float .f32 (tile.totalDecay k),b))
  have lo : 155648 ≤ a := by dsimp [a]; omega
  have hi : a < 156672 := by dsimp [a]; omega
  have coord : lane ((a-155648)/4) 128 (by decide) = k := Fin.ext (by simp [a,lane]; omega)
  have frac : a%4 = b := by dsimp [a]; omega
  simp [memory,show ¬a < 65536 by omega,show ¬655360 ≤ a by omega,show ¬a < 65544 by omega,
    show ¬a < 65552 by omega,show ¬a < 139264 by omega,show ¬a < 147456 by omega,
    show ¬a < 155648 by omega,hi,coord,frac]

set_option maxHeartbeats 1500000 in
theorem inputs : Inputs problem bases memory := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro s hs h hh i hi
    have s0 : s = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hs)
    have h0 : h = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hh)
    norm_num [Batches.tiles,problem] at hi
    have i0 : i = 0 := by omega
    subst s h i
    exact recorded
  · intro s hs b hb
    change s ≤ 1 at hs
    interval_cases s
    · have bound : 65536+b < 65544 := by omega
      simp [bases,memory,Batches.firstToken,problem,Proof.b64,bound,show 65536+b < 655360 by omega]
    · have lo : ¬65544+b < 65544 := by omega
      have hi : 65544+b < 65552 := by omega
      simp [bases,memory,Batches.firstToken,problem,Proof.b64,lo,hi,show 65536 ≤ 65544+b by omega,
        show 65544+b < 655360 by omega]
  all_goals
    intro s hs h hh
    have s0 : s = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hs)
    have h0 : h = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hh)
    subst s h
  · intro t ht v
    have t0 : t = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ht)
    subst t
    apply memFloat_float
    intro b hb
    change b < 2 at hb
    change memory ⟨.global,0,196608+2*v.val+b⟩ = some (some (.float .bf16 0,b))
    simp only [memory,ne_eq,not_true_eq_false,false_or]
    split_ifs <;> first | omega | congr 3; omega
  · intro t ht
    have t0 : t = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ht)
    subst t
    apply memFloat_float
    intro b hb
    change b < 2 at hb
    change memory ⟨.global,0,262144+b⟩ = some (some (.float .bf16 0,b))
    simp only [memory,ne_eq,not_true_eq_false,false_or]
    split_ifs <;> first | omega | congr 3; omega
  · intro v k
    apply memFloat_float
    intro b hb
    change b < 4 at hb
    change memory ⟨.global,0,393216+512*v.val+4*k.val+b⟩ = some (some (.float .f32 0,b))
    simp only [memory,ne_eq,not_true_eq_false,false_or]
    split_ifs <;> first | omega | congr 3; omega

end
end FlashKda.Packed.OneToken
