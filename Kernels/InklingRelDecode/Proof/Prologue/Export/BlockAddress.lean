-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Occurs
public import Kernels.InklingRelDecode.Proof.Iface.GlobalReads
import Kernels.InklingRelDecode.Proof.Common.PrologueEvent
import Kernels.InklingRelDecode.Proof.Prologue.BlockInput
import Kernels.InklingRelDecode.Proof.Prologue.Data.Machine
import Kernels.InklingRelDecode.Proof.Prologue.PreloadCount
import Kernels.InklingRelDecode.Proof.Prologue.Steps.BlockPointer
import Kernels.InklingRelDecode.Proof.Lib.GlobalLoad
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Proof.Lib.Rows
import Lemmas.Kernel.Source.Launch

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Proof Control

private theorem lb_site (s : Site) :
    (s.pc = 197 ∨ s.pc = 220 ∨ s.pc = 241 ∨ s.pc = 262 ∨ s.pc = 283 ∨ s.pc = 304) →
    ∃ b h, s = .lb b h := by
  cases s <;> decide +revert

private theorem load_shape : ∀ (b : Fin 3) (h : Fin 2),
    Lib.globalLoad (Site.lb b h).pc (2071 + 2 * b.val + h.val) 32 = true ∧
    2071 + 2 * b.val + h.val ∈ ctlLive (Site.lb b h).pc := by decide +kernel

/-- The pc of the block-table load of block `b`, half `h`. -/
@[expose] public def lbPcAt (b h : Nat) : Nat :=
  ([[197, 220], [241, 262], [283, 304]].getD b []).getD h 0

/-- A block-table load reads the four bytes of the table entry of a slab of its request. -/
public theorem block_read {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : Occurs L X g k ⟨pc,.rd a bs⟩)
    (site : pc = 197 ∨ pc = 220 ∨ pc = 241 ∨ pc = 262 ∨ pc = 283 ∨ pc = 304) :
    ∃ s < 2 * Q.blocks ((L.ctaidOf (g / L.block)).get .z), a.loc = ⟨.global, 0, Q.btBase +
      4 * (((L.ctaidOf (g / L.block)).get .z) * Q.strideBt + s)⟩ ∧ a.size = 4 ∧
      ∀ (b : Fin 3) (h : Fin 2), pc = lbPcAt b.val h.val →
        s = 2 * ((L.ctaidOf (g / L.block)).get .x + b.val * Q.splits) + h.val := by
  have hg := he.lt hX
  obtain ⟨w,d,t,ins,u,ht,_,pce,hc,fire,_,hist⟩ := prologue_occ hp hX hf he (by simp)
    (by change 27 < pc; omega) (by change pc < 574; omega)
  have pc' : pc = d.site.pc := pce
  subst pc'
  obtain ⟨b,h,hs⟩ := lb_site d.site site
  obtain ⟨gl,key⟩ := load_shape b h
  obtain ⟨_,sub,_,_,regs⟩ := ht
  have hsub : t.sub = 0 := by change t.sub = d.site.sub at sub; rw [hs] at sub; exact sub
  have reg := holds_mem regs (mem_factsFrom (hs ▸ key))
  let req := (L.ctaidOf (g/L.block)).get .z
  let split := (L.ctaidOf (g/L.block)).get .x
  obtain ⟨hx,_,hr⟩ := Lib.coordinate_bounds hp hg
  change split < Q.splits at hx
  change req < Q.b at hr
  have hb32 := hp.bRange
  have val : valueOf Q L g w d (2071 + 2 * b.val + h.val) =
      u64 (blockPtr Q (req % 2 ^ 32) split b.val h.val) := by
    fin_cases b <;> fin_cases h <;>
      (rw [valueOf_query (by decide) (by decide)]; rfl)
  rw [val] at reg
  have hreq : req % 2 ^ 32 = req := Nat.mod_eq_of_lt (by omega)
  rw [hreq] at reg
  have lo : 41 < d.site.pc := by rw [hs]; fin_cases b <;> fin_cases h <;> decide
  have gate := hist.block b (by rw [hs]; rfl)
  have eq := preload_count hp hg (hist.known.first (by omega)) (hist.known.last (by omega))
    (hist.known.seq lo)
  have inc : b.val < Q.numIters req split := by
    have c : Iface.preloadCount Q L (g/L.block) ≤ Q.numIters req split := by
      exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
    have := b.isLt
    omega
  have hlt := Lib.blk_lt (by omega) inc
  have hs2 : 2 * (split + b.val * Q.splits) + h.val < 2 * Q.blocks req := by
    have := h.isLt; omega
  have hidx := hp.btIndexRange req hr _ hs2
  have eqp := block_ptr_eq (hp.seqRange req hr) (b.isLt) (h.isLt) hlt (by omega)
  rw [eqp] at reg
  have gl' : Lib.globalLoad d.site.pc (2071 + 2 * b.val + h.val) 32 = true := by
    rw [hs]; exact gl
  have rd : ∀ j < 4, Q.reads (Q.btBase + 4 * (req * Q.strideBt +
      (2 * (split + b.val * Q.splits) + h.val)) + j) := fun j hj =>
    .inr (.inr (.inr (.inr (.inr ⟨req, hr, _, hs2, j, hj, rfl⟩))))
  have bound := hp.readsRange _ (rd 0 (by omega))
  rw [Nat.add_zero] at bound
  have bmod := Nat.mod_eq_of_lt bound
  obtain ⟨loc, size⟩ := Lib.global_load_loc hc gl' hsub
    (x := (Q.btBase + 4 * (req * Q.strideBt + (2 * (split + b.val * Q.splits) + h.val))) % 2 ^ 64)
    (by simpa [u64] using reg) (Nat.mod_lt _ (by norm_num)) fire rfl
  rw [bmod] at loc
  refine ⟨_, hs2, loc, by simpa using size, fun b' h' hpc => ?_⟩
  have hb : b' = b ∧ h' = h := by
    rw [hs] at hpc
    revert hpc
    fin_cases b <;> fin_cases h <;> fin_cases b' <;> fin_cases h' <;> decide
  obtain ⟨rfl, rfl⟩ := hb
  rfl

/-- A block-table load reads input bytes. -/
public theorem block_address {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : Occurs L X g k ⟨pc,.rd a bs⟩)
    (site : pc = 197 ∨ pc = 220 ∨ pc = 241 ∨ pc = 262 ∨ pc = 283 ∨ pc = 304) :
    Iface.InputAcc Q a := by
  obtain ⟨s, hs, loc, size, -⟩ := block_read hp hX hf he site
  have hr := (Lib.coordinate_bounds hp (he.lt hX)).2.2
  refine ⟨by rw [loc], by rw [loc], fun j hj => ?_⟩
  rw [loc]
  exact .inr (.inr (.inr (.inr (.inr ⟨_, hr, s, hs, j, by omega, rfl⟩))))

/-- **A block-table load returns the page of an existing slab of its request.** -/
public theorem block_page {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some ⟨pc,.rd a bs⟩)
    (site : pc = 197 ∨ pc = 220 ∨ pc = 241 ∨ pc = 262 ∨ pc = 283 ∨ pc = 304) :
    ∃ s < 2 * Q.blocks ((L.ctaidOf (g / L.block)).get .z),
      rebuild 3 bs = .ok (b32 (Q.page ((L.ctaidOf (g / L.block)).get .z) s)) ∧
      ∀ (b : Fin 3) (h : Fin 2), pc = lbPcAt b.val h.val →
        s = 2 * ((L.ctaidOf (g / L.block)).get .x + b.val * Q.splits) + h.val := by
  obtain ⟨s, hs, loc, size, eq⟩ := block_read hp hX hf (.inl he) site
  have hz := (Lib.coordinate_bounds hp (Frame.lt_of_get hX he)).2.2
  refine ⟨s, hs, ?_, eq⟩
  have ro := Frame.LaunchReads.of_forall (hX.asm _ (show Assumptions.inputReadOnly ∈
    Assumptions.all by simp [Assumptions.all]))
  refine Frame.LaunchReads.value (v := b32 (Q.page ((L.ctaidOf (g / L.block)).get .z) s)) hX ro he
    (by rcases site with h | h | h | h | h | h <;> rw [h] <;> decide) (by rw [size]; rfl)
    (fun _ _ => trivial) (fun j hj => ?_) (by decide : 0 < 4) rfl
  rw [loc]
  change m ⟨.global, 0, _ + j⟩ = _
  exact hp.btInput _ hz s hs j hj

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
