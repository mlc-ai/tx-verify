-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Mod8
public import Lemmas.Flow.Step.SiteShape
public import Lemmas.Flow.Step.ShapeNc
public import Lemmas.Flow.Step.ShapeAsync
public import Lemmas.Flow.Step.SiteCases
public import Lemmas.Flow.Step.ShapeAccAt

@[expose] public section

/-! # The TMA warp's events by state: the table

The event a state of the TMA warp fires is the event of its site (`Ev`): the election (full
mask), the two `.nc` length reads, the polls of `bar_q_utccp` and `bar_last_store_done` with
parity 0, per block the poll of `valid_coord_ready[slot]` with the ring's parity word and of
`raw_free[buf]` with the tile's flipped parity word, the coordinate reads (element `j` of
quadruple `k`: the `b32` word at the quadruples' base plus `coordOff k + 4 j`), the gathers on
`raw_ready[buf]`, the `expect_tx 36864` arrival on `raw_ready[buf]` and the arrival on
`valid_coord_free[slot]`, the barrier `12` of the whole CTA and the exit. An address-reading
event may instead fault (`ub`). The objects are the shared words of the registers (`smLoc`),
multiples of 8 whatever the slots (`Lib/Mod8.lean`). The obligations are `Shape*.lean`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- The shared words of the role's mbarriers (`%r669`, `%r672`, and the loop's `%r685`, `%r688`,
`%r696`, `%r773` of the slots). -/
abbrev qUtW (L : Launch) : BitVec 64 := addi (sbw L) 222784
abbrev lastW (L : Launch) : BitVec 64 := addi (sbw L) 222768
abbrev readyW (L : Launch) (d : D) : BitVec 64 := addi (ringB L d) 222840
abbrev freeW (L : Launch) (d : D) : BitVec 64 := addi (tileB L d) 222824
abbrev rawW (L : Launch) (d : D) : BitVec 64 := addi (tileB L d) 222808
abbrev cfreeW (L : Launch) (d : D) : BitVec 64 :=
  addi (mad32 d.slot (i32 (-248)) (crdB L d)) 222872
/-- The parity words of the two polls of a block (`%r686`, `%r689`). -/
abbrev prW (d : D) : BitVec 64 := andi (zext16 d.pr) 255
abbrev pfW (d : D) : BitVec 64 := andi (zext16w (xor16 d.pf)) 255

/-- The offset of coordinate quadruple `k` from the quadruples' base (`%r782`). -/
abbrev coordOff (k : Fin 16) : Int := 221728 + 16 * (k.val : Int)

/-- A poll of the word `x` with the parity of the word `q`, or undefined behaviour. -/
def Poll (L : Launch) (g : Nat) (x q : BitVec 64) (e : Event) : Prop :=
  (∃ ok, e.kind = .wait (smLoc L g x 0) ((truncBits 32 q).toNat % 2) ok true .cta) ∨
    ∃ f, e.kind = .ub f

/-- The event kind of each site. -/
def EvK (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .elect => (∃ inst ld, e.kind = .elect (2 ^ 32 - 1) inst ld) ∨ ∃ f, e.kind = .ub f
  | .loadTopk | .loadExtra => (∃ a bs, e.kind = .nc a bs) ∨ ∃ f, e.kind = .ub f
  | .qWait => Poll L g (qUtW L) (i32 0) e
  | .storeWait => Poll L g (lastW L) (i32 0) e
  | .coordWait => Poll L g (readyW L d) (prW d) e
  | .rawWait => Poll L g (freeW L d) (pfW d) e
  | .coord0 k => RdAt L g (crdB L d) (coordOff k) 4 0 e
  | .coord1 k => RdAt L g (crdB L d) (coordOff k) 4 1 e
  | .coord2 k => RdAt L g (crdB L d) (coordOff k) 4 2 e
  | .coord3 k => RdAt L g (crdB L d) (coordOff k) 4 3 e
  | .gather _ =>
      (∃ a s, e.kind = .tensorIssue a s ∧ s.mbar = smLoc L g (rawW L d) 0) ∨ ∃ f, e.kind = .ub f
  | .rawArrive => e.kind = .arrive (smLoc L g (rawW L d) 0) 36864 1 true .cta
  | .coordFree => e.kind = .arrive (smLoc L g (cfreeW L d) 0) 0 1 true .cta
  | .outBar => e.kind = .bar 12 none .sync
  | .exit => e.kind = .exit
  | .leave _ => True

/-- **The event-shape table of the TMA warp**: the site's pc and kind. -/
def Ev (L : Launch) (g : Nat) (d : D) (e : Event) : Prop := e.pc = d.site.pc ∧ EvK L g d e

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The ring's and the tile's bases are multiples of 8. -/
theorem m8_ringB (hp : Pre P L m) (d : D) : M8 (ringB L d) := m8_add32 (m8_sbw hp) (m8_shl3 _)
theorem m8_tileB (hp : Pre P L m) (d : D) : M8 (tileB L d) := m8_add32 (m8_sbw hp) (m8_shl3 _)

/-- An mbarrier word `x` that is a multiple of 8, at offset 0. -/
theorem al8 {x : BitVec 64} (h : M8 x) :
    (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 0)).toNat % 8 = 0 :=
  trunc_add_mod8 h (by decide)

set_option hygiene false in
/-- Open the shape obligation of a concrete site: the facts `hF`, the pc `hpc`, the instruction
by its lookup, and the table's row. -/
macro "tma_open" : tactic => `(tactic| (
  intro t ins e o hat _ hc hf
  obtain ⟨hpc, -, -, -, hF⟩ := hat
  try dsimp only [Flow.Code.AtD, code, facts, Site.pc, coordPc, Fin.isValue, Fin.val_zero,
    Fin.val_one, Fin.val_two] at hpc hc hF ⊢
  try simp only [Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.reduceLT, Nat.reduceEqDiff,
    Fin.isValue, Fin.val_ofNat, Nat.reduceMod] at hpc hc hF ⊢
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  try simp only [EvK, Poll]))

set_option hygiene false in
/-- `tma_open` keeping the sub-step `hsub` (the element of a coordinate load). -/
macro "tma_openS" : tactic => `(tactic| (
  intro t ins e o hat _ hc hf
  obtain ⟨hpc, hsub, -, -, hF⟩ := hat
  try dsimp only [Flow.Code.AtD, code, facts, Site.pc, Site.sub, coordPc, Fin.isValue,
    Fin.val_zero, Fin.val_one, Fin.val_two] at hpc hsub hc hF ⊢
  try simp only [Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.reduceLT, Nat.reduceEqDiff,
    Fin.isValue, Fin.val_ofNat, Nat.reduceMod] at hpc hc hF ⊢
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  try simp only [EvK]))

set_option hygiene false in
/-- A register's fact at an opened site. -/
macro "rg " r:num : term => `(regs_of_factsFrom hF (r := $r) (by decide))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
