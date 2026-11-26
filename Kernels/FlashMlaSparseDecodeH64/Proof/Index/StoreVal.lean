-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.NoUbSite
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Mod8

@[expose] public section

/-! # The value of a coordinate pair's store

At a coordinate pair's store (sites `stA`, `stB`) the strict state's registers hold the coordinate
words of the pair (`%r142`, `%r146` and their extra twins, `ixPairs`), so the store writes the
bytes of the word of its element: `ixStW`, the coordinate of the machine's current pair word
(`m0`, `m1`; `e0`, `e1`) for the validity of its position. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option hygiene false in
/-- Open the obligation of the state `d` at the site `hs` names. -/
macro "ixv_open" : tactic => `(tactic| (
  obtain ⟨s, el, ac, c⟩ := d
  dsimp only at hs; subst hs
  intro t ins e o hat hi hc hq hf
  obtain ⟨hpc, hsub, -, -, hF⟩ := hat
  dsimp only [Flow.Code.AtD, code, IxSite.pc] at hpc hsub hc hF hf hi ⊢
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))))

/-- **The word a coordinate store writes**, from the machine's words. -/
def ixStW (P : Params) (d : D) : BitVec 64 :=
  match d.site with
  | .stA =>
    if d.el = 0 then ixCoord d.c.m0 (pw P.page) (ixDiv528 (pw P.blockStride))
      (ixOk d.c.m0 (addi d.c.wpos (-1)) d.c.l0)
    else ixCoord d.c.m1 (pw P.page) (ixDiv528 (pw P.blockStride)) (ixOk d.c.m1 d.c.wpos d.c.l0)
  | _ =>
    if d.el = 0 then ixCoord d.c.e0 (pw P.extraPage) (ixDiv528 (pw P.extraBlockStride))
      (ixOk d.c.e0 (addi d.c.xa (-64)) d.c.l1)
    else ixCoord d.c.e1 (pw P.extraPage) (ixDiv528 (pw P.extraBlockStride))
      (ixOk d.c.e1 (addi d.c.xa (-63)) d.c.l1)

/-- **A coordinate pair's store writes the bytes of its element's word.** -/
theorem noUbq_pairVal (hp : Pre P L m) (d : D) {s : IxSite} (hs : d.site = s)
    (hn : s = .stA ∨ s = .stB) :
    ∀ (t : TState) (ins : Instr) (e : Event) (o : Option TState), (code P L g).AtD d t →
      (code P L g).inv d → kernel.code[(code P L g).pc d]? = some ins → QT ixQt t →
      Fires ((code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o →
      ∃ a, e.kind = .wr a (Value.bits 32 (ixStW P d)).toBytes := by
  rcases hn with rfl | rfl <;> ixv_open
  · have h0 : t.regs 600 = some (.bits 32 (ixCoord c.m0 (pw P.page)
      (ixDiv528 (pw P.blockStride)) (ixOk c.m0 (addi c.wpos (-1)) c.l0))) := rgq 600
    have h1 : t.regs 604 = some (.bits 32 (ixCoord c.m1 (pw P.page)
      (ixDiv528 (pw P.blockStride)) (ixOk c.m1 c.wpos c.l0))) := rgq 604
    change Fires _ (storeTmpl L g t .shared 32 612 221728 [.reg 600, .reg 604]) e o at hf
    have hs2 : t.sub < 2 := by rw [hsub]; simpa [IxSite.elems] using hi
    obtain ⟨a, ha⟩ := stPair_eq (rgq 612) h0 h1 hs2 (pair_m8 (g := g) hp c)
    rw [ha] at hf
    simp only [Fires] at hf
    refine ⟨a, ?_⟩
    rw [congrArg Event.kind hf.1, hsub]
    simp only [ixStW]
  · have h0 : t.regs 638 = some (.bits 32 (ixCoord c.e0 (pw P.extraPage)
      (ixDiv528 (pw P.extraBlockStride)) (ixOk c.e0 (addi c.xa (-64)) c.l1))) := rgq 638
    have h1 : t.regs 643 = some (.bits 32 (ixCoord c.e1 (pw P.extraPage)
      (ixDiv528 (pw P.extraBlockStride)) (ixOk c.e1 (addi c.xa (-63)) c.l1))) := rgq 643
    change Fires _ (storeTmpl L g t .shared 32 651 221728 [.reg 638, .reg 643]) e o at hf
    have hs2 : t.sub < 2 := by rw [hsub]; simpa [IxSite.elems] using hi
    obtain ⟨a, ha⟩ := stPair_eq (rgq 651) h0 h1 hs2 (pair_m8 (g := g) hp c)
    rw [ha] at hf
    simp only [Fires] at hf
    refine ⟨a, ?_⟩
    rw [congrArg Event.kind hf.1, hsub]
    simp only [ixStW]


/-- **The word a validity byte's store takes its low byte of**, from the machine's words: the
lane's validity bits `or`ed with the two received words (`%r508`, `%r511`). -/
def ixByteW (L : Launch) (g : Nat) (d : D) : BitVec 64 :=
  match d.site with
  | .bA => or32 (or32 (rvw d.c.rv1) (ixQuadW L g (okM0 d.c) (okM1 d.c))) (rvw d.c.rv2)
  | _ => or32 (or32 (rvw d.c.rv1) (ixQuadW L g (okE0 d.c) (okE1 d.c))) (rvw d.c.rv2)

/-- **A validity byte's store writes the low byte of its word.** -/
theorem noUbq_byteVal (d : D) {s : IxSite} (hs : d.site = s)
    (hn : s = .bA ∨ s = .bB) :
    ∀ (t : TState) (ins : Instr) (e : Event) (o : Option TState), (code P L g).AtD d t →
      (code P L g).inv d → kernel.code[(code P L g).pc d]? = some ins → QT ixQt t →
      Fires ((code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o →
      ∃ a, e.kind = .wr a (Value.bits 8 (truncBits 8 (ixByteW L g d))).toBytes := by
  rcases hn with rfl | rfl <;> ixv_open
  · have h1 : t.regs 508 = some (.bits 32 (or32 (or32 (rvw c.rv1)
      (ixQuadW L g (okM0 c) (okM1 c))) (rvw c.rv2))) := rgq 508
    change Fires _ (storeTmpl L g t .shared 8 613 221696 [.reg 508]) e o at hf
    have hs0 : t.sub = 0 := by rw [hsub]; simpa [IxSite.elems] using hi
    obtain ⟨a, ha⟩ := stByte_eq (rgq 613) h1 hs0
    rw [ha] at hf
    simp only [Fires] at hf
    exact ⟨a, by rw [congrArg Event.kind hf.1]; rfl⟩
  · have h1 : t.regs 511 = some (.bits 32 (or32 (or32 (rvw c.rv1)
      (ixQuadW L g (okE0 c) (okE1 c))) (rvw c.rv2))) := rgq 511
    change Fires _ (storeTmpl L g t .shared 8 652 221696 [.reg 511]) e o at hf
    have hs0 : t.sub = 0 := by rw [hsub]; simpa [IxSite.elems] using hi
    obtain ⟨a, ha⟩ := stByte_eq (rgq 652) h1 hs0
    rw [ha] at hf
    simp only [Fires] at hf
    exact ⟨a, by rw [congrArg Event.kind hf.1]; rfl⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
