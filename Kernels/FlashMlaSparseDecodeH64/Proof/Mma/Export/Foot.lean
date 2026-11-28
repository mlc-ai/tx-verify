-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Mma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Desc
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaIssue
import Lemmas.Tensor.LoadBox

@[expose] public section

/-! # The MMA warp's asynchronous shared reads and issue checks

`memRow_mmaFoot` (`MemRow.MmaFoot`): an operand byte of an MMA or a source byte of a copy of the
MMA warp is a byte of its CTA's dequantized tile or P tile. The event is fired from an MMA state
(`mma_at`) whose row (`Mma/Ev.lean`) states the shared descriptor words; their decoding
(`Mma/Desc.lean`) and the descriptors' footprints (`Lib/MmaFoot.lean`) place the byte. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MmaFoot

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The issuing CTA's group of one is the CTA alone. -/
private theorem group_self (hp : Pre P L m) {g : Nat} (hg : g < L.threads) :
    L.ctaGroup (g / L.block) .one = some [g / L.block] := by
  have hb : 0 < L.block := by rw [hp.block]; decide
  exact ctaGroup_self hp ((Nat.div_lt_iff_lt_mul hb).2 hg)

/-- A loop state's phase word is the phase `0` or `1`. -/
private theorem loop_pha {g : Nat} {d : Mma.D} {n : Mma.Cnt → Nat}
    (hR : Mma.RefCore L g d n) (hs : d.site.inLoop = true) : ∃ h < 2, d.pha = Arith32.W h := by
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp [Mma.Site.inLoop] at hs <;>
    simp only [Mma.RefCore, Mma.Site.inLoop, ↓reduceIte] at hR <;>
    obtain ⟨⟨-, -, -, -, -, hpha, -, -⟩, -⟩ := hR <;>
    exact ⟨_, Nat.mod_lt _ (by decide), hpha⟩

/-- The region of a phase's tile. -/
private theorem dequant_in {g h : Nat} (hh : h < 2) {l : Loc} (hsp : l.space = .shared)
    (hc : l.cta = g / L.block) (hlo : L.sharedBase + 65536 * h ≤ l.addr)
    (hhi : l.addr < L.sharedBase + 65536 * h + 65536) :
    MemRow.LocIn L (g / L.block) (.dequant ⟨h, hh⟩) l :=
  ⟨hsp, hc, by simpa [Region.lo] using hlo,
    by simpa [Region.lo, Region.size] using hhi⟩

/-- **A copy's source bytes are in tile 0**: a `tcgen05.cp` of the MMA warp reads the query tile
(`Mma/Ev.lean`, row `qCopy`), the dequantized tile 0 of its CTA. -/
theorem mmaFoot_cp (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {c : TcCopy.Spec} (hg : g < L.threads)
    (hget : X.get (g, k) = some ⟨pc, .tc (.cp c)⟩) (hat : MbarRow.MmaAt L g pc) {isB : Bool}
    {idx : Nat} {l : Loc} (hF : X.MmaFootprint (g, k) isB idx l) :
    MemRow.LocIn L (g / L.block) (.dequant 0) l := by
  obtain ⟨-, hlo, hhi⟩ := hat
  have hgs := group_self hp hg
  have hB128 := Mma.base_128 hp 0 rfl
  simp only [Nat.add_zero] at hB128
  rcases hF with ⟨dc, s, acc, mask, ⟨pc', hm⟩, -⟩ | ⟨c', j, cta, ⟨pc', hget'⟩, -, hcj, -, hl⟩
  · rw [hget] at hm
    cases hm
  rw [hget] at hget'
  cases hget'
  obtain ⟨d, hR, ⟨-, hE⟩, hlv, -⟩ := mma_at hp hX hFw hget (fun _ h => by cases h) ⟨hlo, hhi⟩
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site
  case qCopy i =>
    rcases hE with ⟨s', hk, hsh, -, -, hct, hsrc⟩ | ⟨f, hf⟩
    · cases hk
      rw [hgs] at hct
      have hcta : cta = g / L.block := by
        rw [← (Option.some.inj hct)] at hcj
        obtain ⟨hj, h2⟩ := List.getElem?_eq_some_iff.mp hcj
        obtain rfl : j = 0 := by simp at hj; omega
        exact h2.symm
      subst hcta
      rw [Mma.cpW_decode hp i.isLt] at hsrc
      rw [hsh, ← (Option.some.inj hsrc)] at hl
      obtain ⟨h1, h2, h3, h4⟩ := copy_foot hB128 i.isLt hl
      exact dequant_in (h := 0) (by decide) h1 h2 (by simpa using h3) (by simpa using h4)
    · cases hf
  case leave i => exact absurd rfl (hlv i)
  all_goals simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE

/-- **An operand byte in the P tile is a PV MMA's A operand**: a byte an MMA or copy of the MMA
warp reads lies in a dequantized tile, or in the P tile and then the event is an MMA with D below
column 256 (the PV MMA; the QK MMAs write D at column 400) and the byte is of operand A. -/
theorem mmaFoot_pv (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hat : MbarRow.MmaAt L g e.pc) {isB : Bool} {idx : Nat} {l : Loc}
    (hF : X.MmaFootprint (g, k) isB idx l) :
    (∃ b, MemRow.LocIn L (g / L.block) (.dequant b) l) ∨
      MemRow.LocIn L (g / L.block) .pExchange l ∧ l.addr < L.sharedBase + 204800 + 8192 ∧
        ∃ pc b s acc mask,
        e = ⟨pc, .tc (.mma b s acc mask)⟩ ∧ b < 256 ∧ isB = false := by
  obtain ⟨-, hlo, hhi⟩ := id hat
  have hgs := group_self hp hg
  have hB128 := Mma.base_128 hp 0 rfl
  simp only [Nat.add_zero] at hB128
  rcases hF with ⟨dc, s, acc, mask, ⟨pc, hget⟩, hl⟩ | ⟨c, j, cta, ⟨pc, hget⟩, hB, hcj, hI, hl⟩
  · rw [hget] at he
    cases he
    obtain ⟨d, hR, ⟨-, hE⟩, hlv, -⟩ := mma_at hp hX hFw hget (fun _ h => by cases h) ⟨hlo, hhi⟩
    have hc := hR (take_noUb hX hget)
    obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
    cases site
    case qk i =>
      obtain ⟨h, hh, rfl⟩ := loop_pha hc rfl
      rcases hE with ⟨s', hk, haT, hdi, ⟨ctas, hct, hcl, -⟩, -, hBd⟩ | ⟨f, hf⟩
      · cases hk
        have hD := qkD_eq hdi
        rw [hD, show qkD.group = .one from rfl, hgs] at hct
        cases hct
        simp only [List.head?_cons, Option.some.injEq] at hcl
        cases isB
        · simp [tmemA_none haT] at hl
        · rw [Mma.qkBW_decode hp hh i.isLt] at hBd
          obtain ⟨h1, h2, h3, h4⟩ := key_foot hD (Mma.base_128 hp (65536 * h) (by omega))
            i.isLt (Option.some.inj hBd).symm hl
          exact .inl ⟨_, dequant_in hh h1 (h2.trans hcl.symm) h3 h4⟩
      · cases hf
    case pv i =>
      obtain ⟨h, hh, rfl⟩ := loop_pha hc rfl
      rcases hE with ⟨s', hk, haT, hdi, ⟨ctas, hct, hcl, hch⟩, hAd, hBd⟩ | ⟨f, hf⟩
      · cases hk
        have hD := pvD_eq hdi
        rw [hD, show pvD.group = .one from rfl, hgs] at hct
        cases hct
        simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hcl hch
        cases isB
        · rw [Mma.pvAW_decode hp i.isLt] at hAd
          obtain ⟨h1, h2, h3, h4⟩ := prob_foot hD i.isLt (Option.some.inj hAd).symm haT hl
          refine .inr ⟨⟨h1, ?_, by simpa [Region.lo] using h3, ?_⟩, ?_, _, _, _, _, _, rfl,
            by simp only [Mma.pvCol]; omega, rfl⟩
          · rcases h2 with h2 | h2
            · exact h2.trans hcl.symm
            · exact h2.trans hch.symm
          · simp only [Region.lo, Region.size]
            omega
          · omega
        · rw [Mma.pvBW_decode hp hh i.isLt] at hBd
          obtain ⟨h1, h2, h3, h4⟩ := value_foot hD (Mma.base_128 hp (65536 * h) (by omega))
            i.isLt (Option.some.inj hBd).symm hl
          exact .inl ⟨_, dequant_in hh h1 (h2.trans hcl.symm) h3 h4⟩
      · cases hf
    case leave i => exact absurd rfl (hlv i)
    all_goals simp [Mma.EvK, Mma.PollEv, Mma.CommitEv] at hE
  · rw [hget] at he
    cases he
    exact .inl ⟨0, mmaFoot_cp hp hX hFw hg hget hat (.inr ⟨c, j, cta, ⟨pc, hget⟩, hB, hcj, hI, hl⟩)⟩

/-- **Row `MemRow.MmaLoad`**: query load `k` writes the 8192 bytes at `8192 k` (`Mma.QBox`,
`writeLoc_b128_64`). -/
theorem memRow_mmaLoad (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MemRow.MmaLoad P L X := by
  intro g k e hg he hat a s hk
  obtain ⟨-, hlo, hhi⟩ := hat
  obtain ⟨d, -, ⟨-, hE⟩, hlv, -⟩ :=
    mma_at hp hX hFw he (fun _ h => by rw [hk] at h; cases h) ⟨hlo, hhi⟩
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  cases site
  case qLoad i =>
    rcases hE with ⟨a', s', hk', -, -, hsb, ⟨h0, hr, hf, hsw⟩, ⟨bb, hb, hmap⟩, -⟩ | ⟨f, hf⟩
    · cases hk'
      refine ⟨?_, fun {x y b l} hl => ?_⟩
      · rw [hp.param1Object, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨-, rfl⟩ := hb
        rw [hp.mapQBind] at hmap
        exact (Option.some.inj hmap).symm
      obtain ⟨h1, h2, h3, h4⟩ := TensorCopy.writeLoc_b128_64 h0 hr hf hsw hl
      rw [hsb] at h1 h2 h3 h4
      have hi := i.isLt
      refine ⟨h1, h2, ?_, ?_⟩ <;> simp only [Region.lo, Region.size] at h3 h4 ⊢ <;> omega
    · cases hf
  case leave i => exact absurd rfl (hlv i)
  all_goals simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE

/-- **An MMA of the MMA warp passes the issue checks** (`TcMma.IssueShape`): the row's
descriptor words decode to the tiles' descriptors, whose checks are `Lib/MmaIssue.lean`. -/
theorem mma_issueShape (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.get (g, k) = some ⟨pc, .tc (.mma d s acc mask)⟩) (hr : 1850 ≤ pc ∧ pc < 2162) :
    TcMma.IssueShape L (g, k) d s mask := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  obtain ⟨d', hR, ⟨-, hE⟩, hl, -⟩ := mma_at hp hX hFw he (fun _ h => by cases h) hr
  have hc := hR (take_noUb hX he)
  obtain ⟨hA, hB⟩ := Mma.base_facts hp
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d'
  cases site
  case qk i =>
    obtain ⟨h, hh, rfl⟩ := loop_pha hc rfl
    rcases hE with ⟨s', hk, haT, hdi, hct, hAd, hBd⟩ | ⟨f, hf⟩
    · obtain ⟨rfl, rfl, -, rfl⟩ := TcKind.mma.inj (Kind.tc.inj hk)
      have hbd'' := (Option.some.inj ((Mma.qkBW_decode hp hh i.isLt).symm.trans hAd)).symm
      have hbd := (Option.some.inj ((Mma.qkBW_decode hp hh i.isLt).symm.trans hBd)).symm
      obtain ⟨ctas, hct, hcl, hch⟩ := hct
      exact qk_issueShape (B := L.sharedBase + 65536 * h) hg i.isLt (by omega) (by omega) rfl
        rfl (qkD_eq hdi) haT ⟨ctas, hct, hcl, hch⟩ hbd'' hbd
    · cases hf
  case pv i =>
    obtain ⟨h, hh, rfl⟩ := loop_pha hc rfl
    rcases hE with ⟨s', hk, haT, hdi, hct, hAd, hBd⟩ | ⟨f, hf⟩
    · obtain ⟨rfl, rfl, -, rfl⟩ := TcKind.mma.inj (Kind.tc.inj hk)
      have hb := (Option.some.inj ((Mma.pvBW_decode hp hh i.isLt).symm.trans hBd)).symm
      have ha := (Option.some.inj ((Mma.pvAW_decode hp i.isLt).symm.trans hAd)).symm
      obtain ⟨ctas, hct, hcl, hch⟩ := hct
      refine pv_issueShape (B := L.sharedBase + 65536 * h) (B' := L.sharedBase + 204800) hg
        i.isLt (by omega) (by omega) (by omega) (by omega) ?_ rfl (pvD_eq hdi) haT
        ⟨ctas, hct, hcl, hch⟩ ha hb
      simp only [Mma.pvCol]
      omega
    · cases hf
  case leave i => exact absurd rfl (hl i)
  all_goals simp [Mma.EvK, Mma.PollEv, Mma.CommitEv] at hE

/-- **A copy of the MMA warp passes `CopySafe`.** -/
theorem mma_cpSafe (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {c : TcCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tc (.cp c)⟩) (hr : 1850 ≤ pc ∧ pc < 2162) :
    TcMma.CopySafe c := by
  obtain ⟨d, hR, ⟨-, hE⟩, hlv, -⟩ := mma_at hp hX hFw he (fun _ h => by cases h) hr
  obtain ⟨hA, hB⟩ := Mma.base_facts hp
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site
  case qCopy i =>
    rcases hE with ⟨s', hk, hsh, -, -, -, hsrc⟩ | ⟨f, hf⟩
    · cases hk
      rw [Mma.cpW_decode hp i.isLt] at hsrc
      exact cp_safe i.isLt (by omega) (by omega) hsh (Option.some.inj hsrc).symm
    · cases hf
  case leave i => exact absurd rfl (hlv i)
  all_goals simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
