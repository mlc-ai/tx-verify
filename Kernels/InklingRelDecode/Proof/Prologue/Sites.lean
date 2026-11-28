-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Lemmas.Flow.Roles
public import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Flow

inductive Site where
  | sMax
  /-- The request words: `cu_seqlens_q[req]`, `cu_seqlens_q[req + 1]`, `seq_lens[req]`. -/
  | ld (k : Fin 3)
  | el (i : Fin 12)
  | init (i : Fin 12)
  | fnc0
  | bar2
  /-- The five barriers of preload block `b`. -/
  | pb (b : Fin 3) (j : Fin 5)
  | arr (b : Fin 3)
  /-- The two block-table loads of block `b`. -/
  | lb (b : Fin 3) (h : Fin 2)
  | psh (b : Fin 3)
  | pel (b : Fin 3) (j : Fin 4)
  | ptc (b : Fin 3) (j : Fin 4)
  | ldq (k : Fin 64)
  | stq (i : Fin 8) (j : Fin 4)
  | fnc1
  | st8
  | st9 (j : Fin 2)
  | bar18
  | exit
  deriving DecidableEq

def elPc : Fin 12 → Nat
  | 0 => 130 | 1 => 135 | 2 => 139 | 3 => 143 | 4 => 147 | 5 => 151 | 6 => 155 | 7 => 159
  | 8 => 163 | 9 => 167 | 10 => 171 | 11 => 175
def initPc (i : Fin 12) : Nat := 134 + 4*i.val
def pbPc (b : Fin 3) (j : Fin 5) : Nat :=
  [[192, 201, 212, 222, 227], [236, 243, 254, 264, 269], [278, 285, 296, 306, 311]].getD b []
    |>.getD j 0
def arrPc (b : Fin 3) : Nat := [193, 237, 279].getD b 0
def lbPc (b : Fin 3) (h : Fin 2) : Nat := [[197, 220], [241, 262], [283, 304]].getD b [] |>.getD h 0
def pshPc (b : Fin 3) : Nat := [202, 244, 286].getD b 0
def pelPc : Fin 3 → Fin 4 → Nat
  | 0, 0 => 203 | 0, 1 => 213 | 0, 2 => 223 | 0, 3 => 228
  | 1, 0 => 245 | 1, 1 => 255 | 1, 2 => 265 | 1, 3 => 270
  | 2, 0 => 287 | 2, 1 => 297 | 2, 2 => 307 | 2, 3 => 312
def ptcPc (b : Fin 3) (j : Fin 4) : Nat :=
  [[211, 217, 226, 231], [253, 259, 268, 273], [295, 301, 310, 315]].getD b [] |>.getD j 0

def Site.pc : Site → Nat
  | .sMax => 27
  | .ld k => [34, 37, 41].getD k 0
  | .el i => elPc i
  | .init i => initPc i
  | .fnc0 => 179
  | .bar2 => 180
  | .pb b j => pbPc b j
  | .arr b => arrPc b
  | .lb b h => lbPc b h
  | .psh b => pshPc b
  | .pel b j => pelPc b j
  | .ptc b j => ptcPc b j
  | .ldq k => 388 + 2 * k.val
  | .stq i _ => 526 + 6 * i.val
  | .fnc1 => 569
  | .st8 => 570
  | .st9 _ => 571
  | .bar18 => 573
  | .exit => 574

/-- The element of a vector store. -/
def Site.sub : Site → Nat
  | .stq _ j => j.val
  | .st9 j => j.val
  | _ => 0

/-- Each event in instruction order. A vector store has one site per element. -/
def allSites : List Site :=
  [.sMax] ++ (List.finRange 3).map Site.ld ++
  (List.finRange 12).flatMap (fun i => [.el i,.init i]) ++ [.fnc0,.bar2] ++
  (List.finRange 3).flatMap (fun b =>
    [.pb b 0,.arr b,.lb b 0,.pb b 1,.psh b,.pel b 0,.ptc b 0,.pb b 2,.pel b 1,
     .ptc b 1,.lb b 1,.pb b 3,.pel b 2,.ptc b 2,.pb b 4,.pel b 3,.ptc b 3]) ++
  (List.finRange 64).map Site.ldq ++
  (List.finRange 8).flatMap (fun i => (List.finRange 4).map (Site.stq i)) ++
  [.fnc1,.st8,.st9 0,.st9 1,.bar18,.exit]

def region : RoleDecl := ⟨[(27,575)],[574]⟩

theorem sites_pcs : (allSites.filter (fun s => s.sub == 0)).map Site.pc =
    RoleDecl.sites kernel region := by kernel_rfl

theorem sites_nodup : (allSites.map (fun s => (s.pc,s.sub))).Nodup := by decide +kernel

theorem Site.pc_range (s : Site) : 27 ≤ s.pc ∧ s.pc ≤ 574 := by
  cases s <;> repeat' first | apply And.intro <;> decide | (rename_i j; revert j)
  all_goals decide +kernel

end PTX.Kernels.InklingRelDecode.Proof.Prologue
