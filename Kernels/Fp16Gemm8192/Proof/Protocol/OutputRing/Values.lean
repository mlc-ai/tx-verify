-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.OutputRing.Sources
public import Lemmas.Async.ReadReuse

@[expose] public section

/-! # The bytes an output tensor store reads

The byte a consumer's TMA store of slice `s` reads at slot `(x, y, z)` is the byte its group's
thread of row `y` wrote there at its staging store of element `m = 4 (x / 8) + x / 2 % 4` of the
same slice (`staging_value`): byte `2 (x % 2) + z` of that store. The store is the thread's latest
write of the byte before its second output barrier of the slice, so its earlier writes of the byte
precede it in its program; the stores between write other elements; the barrier's event is no
write; and a later write of the byte is of a later slice of the same parity, which the TMA store's
read precedes (`tma_before_store`). The read is visible to the store (`store_vis_of_lt`), so the
read returns its byte (`read_byte_of_ordered_reuse`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

namespace OutputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The source byte of slot `(x, y, z)` is byte `2 (x % 2) + z` of the staging store of element
`(x / 8, x / 2 % 4)` of the row's thread (`source_in_store`, exactly). -/
theorem source_offset {sb T t' par x y b : Nat}
    (hphase : (sb + Consumer.stagingBase T par) / 128 % 4 = 0)
    (hx : x < 32) (hy : y < 128) (hb : b < 2) (ht' : t' = 128 * (T / 32 / 4) + y) :
    (sb + Consumer.stagingBase T par) +
        TensorSwizzle.offset .b64 (sb + Consumer.stagingBase T par) (64 * y + 2 * x + b) =
      sb + Consumer.stagingOff t' par (x / 8) (x / 2 % 4) + (2 * (x % 2) + b) := by
  have hv : x / 8 < 4 := by omega
  have h1 : 64 * y + 2 * x + b = 64 * y + 16 * (x / 8) + (4 * (x / 2 % 4) + 2 * (x % 2) + b) := by
    omega
  rw [h1, swizzle_zero_phase hphase hv (by omega)]
  have hxor : (t' / 2 % 4) ^^^ (x / 8) = vectorIndex y (x / 8) := by
    unfold vectorIndex
    rw [show t' / 2 % 4 = y / 2 % 4 by omega, Nat.xor_comm]
    rfl
  simp only [Consumer.stagingOff, Consumer.stage, Consumer.stagingBase, hxor]
  omega

set_option maxHeartbeats 8000000 in
/-- **The byte a TMA store reads** is the byte its row's thread wrote there in the slice. -/
theorem staging_value (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hagree : AllResponsesAgree L X)
    (hacc : StagingAccessors L X)
    (hub : ∀ g j pc f, X.get (g, j) ≠ some ⟨pc, .ub f⟩) {h k pc a : Nat}
    {sp : TensorStore.Spec} {c : Consumer.D} {s : Fin 8} {x y z : Nat}
    {o : TensorStore.Observation} {v : Byte}
    (hge : X.get (h, k) = some ⟨pc, .tensorStore a sp⟩)
    (hσd : Frame.stateAt (code L) X h k = some (some (.inr (.cons c)))) (hs : c.site = .tma s)
    (hx : x < 32) (hy : y < 128) (hz : z < 2) (ho : X.tensorStores (h, k) = some o)
    (hv : TensorStore.readByte o x y z = some v) :
    ∃ g' i' c' pc' a' bs, g' = h / L.block * L.block + (128 * (Consumer.tidOf L h / 32 / 4) + y) ∧
      i' < (X.tr g').length ∧ Frame.stateAt (code L) X g' i' = some (some (.inr (.cons c'))) ∧
      c'.site = .barB s ∧
      Consumer.outBars L g' ((X.tr g').take i') + 1 = Consumer.outBars L h ((X.tr h).take k) ∧
      X.get (g', i' - 16 + (4 * (x / 8) + x / 2 % 4)) = some ⟨pc', .wr a' bs⟩ ∧
      bs[2 * (x % 2) + z]? = some v := by
  have hht : h < L.threads := Frame.lt_of_get hX hge
  obtain ⟨c0, st, hc0, hsite, -, b0, cls, origin, hspec⟩ := ht.cons_tma hht hge hσd
  simp only [Sum.inr.injEq, Prologue.Role.cons.injEq] at hc0
  subst hc0
  obtain rfl : st = s := by rw [hs] at hsite; cases hsite; rfl
  have hspec' : sp = outSpec b0 cls origin (h / L.block)
      (L.sharedBase + Consumer.stagingBase (Consumer.tidOf L h) (st.val % 2)) := hspec
  -- the observation is of this store
  obtain ⟨⟨addr, pci, hiss⟩, -, -⟩ := hX.store (h, k) o ho
  have hosp : o.spec = sp := by
    have h1 := Option.some.inj (hge.symm.trans hiss)
    simp only [Event.mk.injEq, Kind.tensorStore.injEq] at h1
    exact h1.2.2.symm
  set cta := h / L.block with hcta
  have hk : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp hge).1
  obtain ⟨h2, ⟨pcb, hbar⟩, ⟨pcf, hfen⟩⟩ := ht.cons_tma_prev hht hk hσd hsite
  have hrw := ht.role_warp hht (idx_le hge) hσd
  simp only [roleWarp] at hrw
  have hblock := hpre.block
  have hal := hpre.sharedAlignment
  set grp := Consumer.tidOf L h / 32 / 4 with hgrpdef
  have hq2 : grp < 2 := by simp only [hgrpdef, Consumer.tidOf]; omega
  have hcg : cta < L.grid := by
    have : h < L.grid * L.block := hht
    rw [hcta, Nat.div_lt_iff_lt_mul (by omega)]
    exact this
  set base := L.sharedBase + Consumer.stagingBase (Consumer.tidOf L h) (st.val % 2) with hbase
  set loc : Loc := ⟨.shared, cta, base + TensorSwizzle.offset .b64 base (64 * y + 2 * x + z)⟩
    with hlocdef
  have hrl : TensorStore.readLoc sp x y z = some loc := by
    rw [hspec']; exact output_readLoc hx hy hz
  have hphase : base / 128 % 4 = 0 := by
    simp only [hbase, Consumer.stagingBase]; omega
  have hvv := source_in_store (sb := L.sharedBase) (T := Consumer.tidOf L h) (par := st.val % 2)
    (t' := 128 * grp + y) (x := x) (y := y) (b := z) hphase hx hy hz rfl
  have hb1 := stagingOff_bounds (t := 128 * grp + y) (b := st.val % 2) (i := x / 8)
    (el := x / 2 % 4) (by omega) (by omega)
  have hstaging : IsStaging L loc := by
    refine ⟨rfl, ?_, ?_⟩ <;>
    · simp only [hlocdef, hbase, Consumer.stagingBase, Consumer.stagingOff,
        Consumer.stage] at hvv hb1 ⊢
      omega
  -- the thread of the group whose index is the row
  have hlt384 : 128 * grp + y < L.block := by omega
  set g' := cta * L.block + (128 * grp + y) with hg'
  have hg'cta : g' / L.block = cta := by rw [hg', hblock]; omega
  have hg'mod : g' % L.block = 128 * grp + y := by rw [hg', hblock]; omega
  have hg'lt : g' < L.threads := by
    show g' < L.grid * L.block
    rw [hg', hblock]
    omega
  have hbarB : X.IsBarrier (h, k - 2) (grp + 10) (some 128) pcb := hbar
  have hw : (g' % L.block) / 32 ∈ group grp := by
    rw [hg'mod]
    simp only [group, Finset.mem_insert, Finset.mem_singleton]
    omega
  obtain ⟨i', pc', hbar', hcount⟩ := member_arrival hpre hX ht hq2 hbarB
    (show (h, k - 2).2 + 1 < (X.tr h).length by simp only; omega) (.of_all hagree _) (g := g')
    hg'cta hg'lt hw
  have hbar'' : X.get (g', i') = some ⟨pc', .bar (grp + 10) (some 128)⟩ := hbar'
  obtain ⟨dm, hσm⟩ := Frame.event_state ht.sound hX ht.tracked hbar'' nofun
  obtain ⟨cm, rfl⟩ := ht.bar_role hg'lt hbar'' hσm rfl
  obtain ⟨hrelm, hwrm, -, -, hbarm, -⟩ := ht.cons_out hg'lt hbar'' hσm
  obtain ⟨hrelh, -, -, -, -, -⟩ := ht.cons_out hht hge hσd
  have e1 : Consumer.outId L g' = grp + 10 := by
    simp only [Consumer.outId, Consumer.tidOf, hg'mod]; omega
  obtain ⟨s', hs'⟩ : ∃ s', cm.site = .barA s' ∨ cm.site = .barB s' := by
    rcases hbarm (grp + 10) (some 128) rfl with ⟨-, hid, -⟩ | ⟨hs, -, -⟩
    · exfalso
      simp only [Consumer.tidOf, hg'mod] at hid
      omega
    · exact hs
  have hO : Consumer.outBars L g' ((X.tr g').take i') =
      Consumer.outBars L h ((X.tr h).take (k - 2)) := by
    rw [Consumer.outBars_eq, Consumer.outBars_eq, e1]
    exact hcount
  have hT : Consumer.outBars L h ((X.tr h).take k) =
      Consumer.outBars L h ((X.tr h).take (k - 2)) + 1 := by
    have hsplit := take_two (es := X.tr h) (n := k - 2)
      (e1 := ⟨pcb, .bar (Consumer.outId L h) (some 128)⟩)
      (e2 := ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩) hbar
      (by rw [show k - 2 + 1 = k - 1 by omega]; exact hfen)
    rw [show k - 2 + 2 = k by omega] at hsplit
    rw [Consumer.outBars_eq, Consumer.outBars_eq, hsplit]
    simp [List.countP_append, Execution.isBarId]
  have hOh := hrelh.1
  simp only [Consumer.D.outPhase, hsite] at hOh
  have hOm := hrelm.1
  have hB : cm.site = .barB st := by
    have := s'.isLt
    have := st.isLt
    rcases hs' with hA | hB
    · exfalso
      simp only [Consumer.D.outPhase, hA] at hOm
      omega
    · simp only [Consumer.D.outPhase, hB] at hOm
      have hs'st : s' = st := Fin.ext (by omega)
      rw [← hs'st]
      exact hB
  have hk' : i' < (X.tr g').length := (List.getElem?_eq_some_iff.mp hbar'').1
  obtain ⟨hlen16, hst⟩ := ht.cons_slice_stores hg'lt (hub g') hk' hσm hB
  set mm := 4 * (x / 8) + x / 2 % 4 with hmm
  have hm16 : mm < 16 := by omega
  obtain ⟨pcw, aw, bsw, hwget, hwloc, hwsize, hwlen⟩ := hst _ hm16
  rw [show mm / 4 = x / 8 by omega, show mm % 4 = x / 2 % 4 by omega, hg'cta] at hwloc
  have htid' : Consumer.tidOf L g' = 128 * grp + y := hg'mod
  have hcovw : aw.Covers loc := by
    unfold Acc.Covers Loc.InRange
    rw [hwloc, hwsize]
    simp only [htid']
    refine ⟨?_, ?_, hvv.1, hvv.2⟩ <;> trivial
  have hint : X.Intent (.thread (g', i' - 16 + mm)) aw true :=
    Or.inr (.inl ⟨bsw, ⟨pcw, hwget⟩, rfl⟩)
  obtain ⟨cw, hσw⟩ : ∃ cw, Frame.stateAt (code L) X g' (i' - 16 + mm) =
    some (some (.inr (.cons cw))) := by
    rcases hacc _ aw true _ hint hcovw hstaging with
      ⟨e', pc'', bs'', cw, href, hget', hσw⟩ | ⟨i2, x2, y2, k2, c2, href, -⟩
    · cases href; exact ⟨cw, hσw⟩
    · cases href
  have hif : X.Intent (.async (h, k) (.read (.store x y z)))
    ⟨loc, 1, false, false, .cta, 0, false⟩ false :=
    ⟨rfl, _, a, ⟨pc, hge⟩, hrl, rfl⟩
  have hcb : (⟨loc, 1, false, false, .cta, 0, false⟩ : Acc).Covers loc :=
    ⟨rfl, rfl, le_refl _, Nat.lt_succ_self _⟩
  have hmono := countP_take_mono (Execution.isBarId (Consumer.outId L g')) (X.tr g')
    (a := i' - 16 + mm) (b := i') (by omega)
  rw [← Consumer.outBars_eq, ← Consumer.outBars_eq] at hmono
  have hvis := store_vis_of_lt hpre hX ht hagree hwget hσw hcovw hσd hif hcb hstaging.1 (by omega)
  have hct : g' / L.block = h / L.block := hg'cta
  have hgrp : Consumer.outId L g' = Consumer.outId L h := by
    rw [e1]
  -- the read
  have hread : X.MemReads (.async (h, k) (.read (.store x y z))) ⟨loc, 1, false, false, .cta, 0,
      false⟩
      [some v] :=
    ⟨o, addr, v, ho, ⟨pci, hiss⟩, by rw [hosp]; exact hrl, hv, rfl, rfl⟩
  have hwr : X.MemWrites (.thread (g', i' - 16 + mm)) aw bsw := .inl ⟨pcw, hwget⟩
  have hoffs := source_offset (sb := L.sharedBase) (T := Consumer.tidOf L h) (par := st.val % 2)
    (t' := 128 * grp + y) (x := x) (y := y) (b := z) hphase hx hy hz rfl
  have hlocaddr : loc.addr = L.sharedBase + Consumer.stagingOff (128 * grp + y) (st.val % 2)
      (x / 8) (x / 2 % 4) + (2 * (x % 2) + z) := hoffs
  have hres := read_byte_of_ordered_reuse hX hread (k := 0) Nat.zero_lt_one hwr
    (by simpa [Loc.at] using hcovw) (by simpa [Loc.at] using hvis) ?order
  case order =>
    intro other fp bytes hwo hcov
    simp only [Loc.at, Nat.add_zero] at hcov ⊢
    rcases hacc other fp true loc (Execution.MemWrites.intent hwo) hcov hstaging with
      ⟨⟨go, io⟩, pco, bso, co, rfl, hgo, hσo⟩ | ⟨i2, x2, y2, k2, c2, rfl, -⟩
    swap
    · exact absurd (Execution.MemWrites.intent hwo).1 (by simp [AsyncCopy.Part.writes])
    obtain ⟨ko, i0o, elo, hso, hobo, hctao, htido, hloo, hhio⟩ := store_info hX ht hgo hσo hcov
    simp only at hloo hhio
    obtain ⟨hpo1, hpo2⟩ := stagingOff_bounds (t := Consumer.tidOf L go) (b := ko.val % 2)
      i0o.isLt elo.isLt
    have hb2 := stagingOff_bounds (t := Consumer.tidOf L h) (b := st.val % 2) (i := 0) (el := 0)
      (by omega) (by omega)
    obtain ⟨hpar, hgq⟩ := buffer_eq (sb := L.sharedBase) (t := Consumer.tidOf L go)
      (b := ko.val % 2) (t' := 128 * grp + y) (b' := st.val % 2) (a := loc.addr)
      (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (by omega) (by omega)
      (by rw [hlocaddr]; omega) (by rw [hlocaddr]; omega)
    -- the same element of the same thread
    have hs8 : Consumer.stage (Consumer.tidOf L go) i0o % 8 = 0 := by
      simp only [Consumer.stage]; omega
    have hs8' : Consumer.stage (128 * grp + y) (x / 8) % 8 = 0 := by
      simp only [Consumer.stage]; omega
    have hoff : Consumer.stagingOff (Consumer.tidOf L go) (ko.val % 2) i0o elo =
        Consumer.stagingOff (128 * grp + y) (st.val % 2) (x / 8) (x / 2 % 4) := by
      rw [hlocaddr] at hloo hhio
      simp only [Consumer.stagingOff] at hloo hhio ⊢
      omega
    obtain ⟨htt, -, hii, hee⟩ := stagingOff_inj hgq i0o.isLt (show x / 8 < 4 by omega) elo.isLt
      (show x / 2 % 4 < 4 by omega) hoff
    have hgg : go = g' := by
      simp only [Consumer.tidOf] at htt
      have hc' : go / L.block = cta := by simp only [hlocdef] at hctao; omega
      have := Nat.div_add_mod go L.block
      rw [hc'] at this
      rw [hg']
      rw [hblock] at this htt ⊢
      omega
    subst hgg
    rcases Nat.lt_trichotomy io (i' - 16 + mm) with hlt | heq | hgt
    · exact .inr (.inl (.inl (.single
        (.inl (po_of_overlap (Or.inr (.inl ⟨bso, ⟨pco, hgo⟩, rfl⟩)) hint
          rfl hlt ⟨loc, hcov, hcovw⟩)))))
    · exact .inl (by rw [heq])
    · rcases Nat.lt_trichotomy io i' with h1 | h1 | h1
      · -- another element of the slice: another staging location
        exfalso
        obtain ⟨pcm, am, bsm, hgm, hlm, -, -⟩ := hst (io - (i' - 16)) (by omega)
        rw [show i' - 16 + (io - (i' - 16)) = io by omega, hgo] at hgm
        simp only [Option.some.injEq, Event.mk.injEq, Kind.wr.injEq] at hgm
        obtain ⟨-, rfl, -⟩ := hgm
        obtain ⟨-, hlc, hlo, hhi⟩ := hcov
        rw [hlm] at hlo hhi
        have hsz : fp.size = 4 := by
          obtain ⟨-, hst', -⟩ := ht.cons_out hg'lt hgo hσo
          obtain ⟨-, -, -, -, -, hsz⟩ := hst' fp bso rfl
          exact hsz
        rw [hsz, hlocaddr, hg'cta, htid'] at hhi
        rw [hlocaddr, hg'cta, htid'] at hlo
        have hs8m : Consumer.stage (128 * grp + y) ((io - (i' - 16)) / 4) % 8 = 0 := by
          simp only [Consumer.stage]; omega
        have hoffm : Consumer.stagingOff (128 * grp + y) (st.val % 2) ((io - (i' - 16)) / 4)
            ((io - (i' - 16)) % 4) =
            Consumer.stagingOff (128 * grp + y) (st.val % 2) (x / 8) (x / 2 % 4) := by
          simp only [Consumer.stagingOff] at hlo hhi ⊢
          omega
        obtain ⟨-, -, h3, h4⟩ := stagingOff_inj rfl (by omega) (show x / 8 < 4 by omega)
          (by omega) (show x / 2 % 4 < 4 by omega) hoffm
        omega
      · -- the barrier's event is no write
        exfalso
        subst h1
        rw [hbar''] at hgo
        cases hgo
      · -- a later slice of the same parity: after the TMA store's read
        have hmono' := countP_take_mono (Execution.isBarId (Consumer.outId L g')) (X.tr g')
          (a := i' + 1) (b := io) (by omega)
        rw [← Consumer.outBars_eq, ← Consumer.outBars_eq] at hmono'
        have hsucc : Consumer.outBars L g' ((X.tr g').take (i' + 1)) =
            Consumer.outBars L g' ((X.tr g').take i') + 1 := by
          rw [List.take_add_one, show (X.tr g')[i']? = _ from hbar'', Consumer.outBars_eq,
            Consumer.outBars_eq]
          simp [List.countP_append, Execution.isBarId, e1]
        have hko := ko.isLt
        have hst8 := st.isLt
        have h3 : Consumer.outBars L h ((X.tr h).take k) + 3 ≤
            Consumer.outBars L g' ((X.tr g').take io) := by omega
        obtain ⟨w, hpres, hbw, hhb⟩ :=
          tma_before_store hpre hX ht hagree hgo hσo rfl hge hσd rfl hct
          hgrp h3
        refine .inr (.inr ⟨⟨_, false, hif, hcb⟩, w, .inl ⟨.bulk .read, rfl, hbw, fun q hq => ?_⟩,
          .inl hhb⟩)
        have hstore : X.get (h, k) = some ⟨pc, .tensorStore a sp⟩ := hge
        simp only [GroupWaitStages, hstore, Option.map_some, List.mem_singleton] at hq
        subst hq
        exact hpres
  refine ⟨g', i', cm, pcw, aw, bsw, rfl, hk', hσm, hB, by omega, hwget, ?_⟩
  simp only [List.getElem?_cons_zero, Option.some.injEq, wbyte] at hres
  rw [hres]
  congr 1
  rw [hwloc]
  simp only [Loc.at, Nat.add_zero, htid']
  rw [hlocaddr]
  omega

end OutputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
