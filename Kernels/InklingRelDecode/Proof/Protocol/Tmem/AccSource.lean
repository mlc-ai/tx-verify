-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AccDone
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.Live
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.Reads
public import Lemmas.Tcgen05.TmemLatestSource
import Lemmas.Tcgen05.TcMmaZeroMask
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Kernels.InklingRelDecode.Proof.Mma.Export.Cover
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Lemmas.Tcgen05.TcProgramOrder

@[expose] public section

/-! # An accumulator read has a source

An accumulator read of a done MMA has a source with a value once one write is before it
(`TcMma.readSourceOfCandidate`; every writer is ordered with the read by `Tmem.reads_safe`). The
read of a step that accumulates into its own block's accumulator has the block's previous step as
its candidate: the same warp, the same accumulator, so pipelined (`Before.of_mma_po`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.TcMma Protocol.Scalar

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **An accumulator read with a candidate write has a source with a value.** -/
public theorem acc_source (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hWrites : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X)
    {r : EvId} {cell : Cell}
    (hCV : ∀ i d s acc mask, X.MmaIssue i d s acc mask → X.MmaCell i cell →
      WriteBefore L X i r → CompletedValues L Assumptions.all X i)
    (hdr : X.async.mmaDone r = true) (hr : X.MmaReadCell r cell)
    (cand : ∃ w, TmemWrite L X w cell ∧ WriteBefore L X w r) :
    ∃ source value, ReadSource L X .acc source r cell ∧
      Wrote L Assumptions.all X source cell value := by
  have hsafe : ReadsSafe L X := not_not.mp
    (reads_safe hp hX hf safe base rows init)
  have hmaster : ∀ w, TmemWrite L X w cell →
      WriteBefore L X w r ∨ ReadBefore L X .acc r w := fun w hw => by
    rcases (readsSafe_iff.mp hsafe).1 r w cell hr hw with h | h | h
    · exact .inr (.inl h.symm)
    · exact .inl h
    · exact .inr h
  obtain ⟨g, kp⟩ := r
  obtain ⟨d, s, mask, row, col, ⟨pc, he⟩, -⟩ := id hr
  have hlive : ∀ w, TmemWrite L X w cell → WriteBefore L X w (g, kp) →
      SourceLive L X w (g, kp) cell := fun w _ _ =>
    source_live_mma hX ht hmd ⟨pc, he⟩ (mma_cells hp hX hf base (.inr (.inl hr))).1
  obtain ⟨w, hw, hwb⟩ := cand
  obtain ⟨src, hsrc⟩ := readSourceOfCandidate hX hG hWrites hmaster hlive hw hwb
  obtain ⟨value, hv⟩ := wrote_of hX (fun d s acc mask hi hm => hCV _ d s acc mask hi hm hsrc.2.2.1)
    hsrc.2.1
    fun hm => acc_mma_done hp hX hf base hG hdr hr hsrc hm
  exact ⟨src, value, hsrc, hv⟩

/-- **An earlier MMA of the lane with the same accumulator is a write before the read.** -/
theorem step_candidate (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {g kp kw pc pcw d dw : Nat} {s sw : OperandSpec} {acc aw : Bool} {mask mw : List Nat}
    {cell : Cell} (hr : X.MmaReadCell (g, kp) cell)
    (he : X.get (g, kp) = some ⟨pc, .tc (.mma d s acc mask)⟩)
    (hw : X.get (g, kw) = some ⟨pcw, .tc (.mma dw sw aw mw)⟩) (hlt : kw < kp) (hd : dw = d)
    (hdesc : sw.descriptor = s.descriptor) :
    TmemWrite L X (g, kw) cell ∧ WriteBefore L X (g, kw) (g, kp) := by
  obtain ⟨hmw, lo1, hi1, -⟩ := mma_class hp hX hf base hw
  subst hmw
  obtain ⟨-, lo2, hi2, c2⟩ := mma_class hp hX hf base he
  have hlo : sw.lowCta = s.lowCta := by rw [lo1, lo2]
  have hhi : sw.highCta = s.highCta := by rw [hi1, hi2]
  obtain ⟨d', s', mask', row, col, ⟨pc', he'⟩, hres⟩ := hr
  have e := get_tc_inj he he'
  simp only [TcKind.mma.injEq] at e
  obtain ⟨rfl, rfl, -, -⟩ := e
  have hshape : s.descriptor.group = .one ∧ s.descriptor.m = 64 := by
    rcases c2 with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] <;> exact ⟨rfl, rfl⟩
  have hcell := writeCell_zeroMask hshape.1 hshape.2 hres
  refine ⟨.inl ⟨dw, sw, aw, [0, 0, 0, 0], row, col, ⟨_, hw⟩, ?_⟩, .inl (.inr ?_)⟩
  · rw [hd, ← writeCell_congr hdesc.symm hlo.symm hhi.symm]
    exact hcell
  · have hg : g < L.threads := Frame.lt_of_get hX he
    refine ⟨TcMma.sameWarp_self hg, .inl (baseCausality_of_tc_po hw rfl hlt (len_of_get he)),
      _, _, _, _, _, _, _, _, ⟨_, hw⟩, ⟨_, he⟩, ?_⟩
    exact ⟨hd, by rw [hdesc], by rw [hdesc], hlo, hhi⟩

/-- **The previous step of a QK step that accumulates**: an earlier QK step of the lane, in the
same block, which writes the cell the step reads. -/
public theorem qk_prev_step (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {g kp : Nat} {cell : Cell} (hr : X.MmaReadCell (g, kp) cell) {pc d s mask}
    (he : X.get (g, kp) = some ⟨pc, .tc (.mma d s true mask)⟩) {j : Fin 8}
    (hpcj : pc = Lib.qkIssue j) (j' : Fin 8) (hj' : j'.val + 1 = j.val) :
    ∃ kR, kR < kp ∧ (∃ d' s' a' m',
      X.get (g, kR) = some ⟨Lib.qkIssue j', .tc (.mma d' s' a' m')⟩) ∧
      pollRound 2462 ((X.tr g).take kR) = pollRound 2462 ((X.tr g).take kp) ∧
      TmemWrite L X (g, kR) cell ∧ WriteBefore L X (g, kR) (g, kp) := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  obtain ⟨-, lo, hi, bc, qk | pv⟩ := Mma.Export.columns hp hX hf base he
  · obtain ⟨-, -, hdst, -, hdesc⟩ := qk
    obtain ⟨b, hb, q1, -⟩ := Mma.Export.qk_block hp hX hf base he ⟨j, hpcj⟩
    obtain ⟨kR, lt, d', s', a', m', get, q⟩ := Mma.Export.qk_prior hp hX hf words hu he hpcj
      j' (by omega)
    obtain ⟨b', hb', q1', -⟩ := Mma.Export.qk_block hp hX hf base get ⟨_, rfl⟩
    obtain ⟨-, -, -, c⟩ := mma_class hp hX hf base get
    have hbb : b' = b := by omega
    have hd' : d' = d := by rw [hb', hb, hbb]
    have hdesc' : s'.descriptor = s.descriptor := by
      rcases c with ⟨-, e⟩ | ⟨h256, -⟩
      · rw [e, hdesc]
      · omega
    exact ⟨kR, lt, ⟨d', s', a', m', get⟩, q,
      step_candidate hp hX hf base hr he get lt hd' hdesc'⟩
  · obtain ⟨j'', hpc', -⟩ := pv
    exfalso
    have : Lib.qkIssue j = Lib.pvIssue j'' := hpcj.symm.trans hpc'
    revert this; fin_cases j <;> fin_cases j'' <;> decide

/-- **The previous step of a QK step that accumulates**: an earlier QK step of the lane, in the
same block, which writes the cell the step reads. -/
public theorem qk_prev (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {g kp : Nat} {cell : Cell} (hr : X.MmaReadCell (g, kp) cell) {pc d s mask}
    (he : X.get (g, kp) = some ⟨pc, .tc (.mma d s true mask)⟩) {j : Fin 8}
    (hpcj : pc = Lib.qkIssue j) :
    ∃ kR, kR < kp ∧ (∃ j' : Fin 8, ∃ d' s' a' m',
      X.get (g, kR) = some ⟨Lib.qkIssue j', .tc (.mma d' s' a' m')⟩) ∧
      pollRound 2462 ((X.tr g).take kR) = pollRound 2462 ((X.tr g).take kp) ∧
      TmemWrite L X (g, kR) cell ∧ WriteBefore L X (g, kR) (g, kp) := by
  obtain ⟨-, lo, hi, bc, qk | pv⟩ := Mma.Export.columns hp hX hf base he
  · obtain ⟨j0, hpc0, -, -, -⟩ := qk
    obtain ⟨b, hb, q1, -, -, hacc⟩ := Mma.Export.qk_block hp hX hf base he ⟨j, hpcj⟩
    have hj1 : 1 ≤ j.val := by
      have h := (hacc j hpcj).1.symm
      simp at h
      exact Nat.pos_of_ne_zero fun e => h (Fin.ext e)
    obtain ⟨kR, lt, ⟨d', s', a', m', get⟩, q, w⟩ :=
      qk_prev_step hp hX hf hu base hr he hpcj ⟨j.val - 1, by omega⟩ (by simp; omega)
    exact ⟨kR, lt, ⟨_, d', s', a', m', get⟩, q, w⟩
  · obtain ⟨j'', hpc', -⟩ := pv
    exfalso
    have : Lib.qkIssue j = Lib.pvIssue j'' := hpcj.symm.trans hpc'
    revert this; fin_cases j <;> fin_cases j'' <;> decide

/-- **The candidate write of an accumulating step**: every accumulating step but the first PV
step of a block (which accumulates into the previous block's) follows the block's previous
step. -/
public theorem acc_prev (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {g kp : Nat} {cell : Cell} (hr : X.MmaReadCell (g, kp) cell)
    (hnf : ∀ d s mask, X.get (g, kp) ≠ some ⟨Lib.pvIssue 0, .tc (.mma d s true mask)⟩) :
    ∃ w, TmemWrite L X w cell ∧ WriteBefore L X w (g, kp) := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  obtain ⟨d, s, mask, row, col, ⟨pc, he⟩, -⟩ := id hr
  obtain ⟨-, lo, hi, bc, qk | pv⟩ := Mma.Export.columns hp hX hf base he
  · obtain ⟨j, hpcj, -, -, -⟩ := qk
    obtain ⟨kR, -, -, -, hw, hwb⟩ := qk_prev hp hX hf hu base hr he hpcj
    exact ⟨_, hw, hwb⟩
  · obtain ⟨j, hpcj, hdst, -, hdesc⟩ := pv
    obtain ⟨b, hb, pb, one, -, -, -, hacc⟩ := Mma.Export.pv_block hp hX hf base he ⟨j, hpcj⟩
    have hj1 : 1 ≤ j.val := by
      rcases hacc j hpcj rfl with h | h
      · exact h
      · by_contra h0
        have hj0 : j = 0 := Fin.ext (by omega)
        subst hj0
        exact hnf d s mask (by rw [hpcj] at he; exact he)
    obtain ⟨-, -, hprior, -⟩ := Mma.Export.pv_prior hp hX hf words hu he hpcj
    obtain ⟨kR, lt, d', s', a', m', get, q⟩ := hprior ⟨j.val - 1, by omega⟩ (by simp; omega)
    obtain ⟨b', hd'', -⟩ := Mma.Export.pv_block hp hX hf base get ⟨_, rfl⟩
    obtain ⟨-, -, -, c⟩ := mma_class hp hX hf base get
    have hdesc' : s'.descriptor = s.descriptor := by
      rcases c with ⟨h256, -⟩ | ⟨-, e⟩
      · omega
      · rw [e, hdesc]
    exact ⟨_, step_candidate hp hX hf base hr he get lt (by omega) hdesc'⟩

/-- **The candidate write of the first PV step of a block**: the previous block's last PV step,
which writes the same accumulator. -/
public theorem acc_first (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {g kp : Nat} {cell : Cell} (hr : X.MmaReadCell (g, kp) cell) {d s mask}
    (he : X.get (g, kp) = some ⟨Lib.pvIssue 0, .tc (.mma d s true mask)⟩) :
    ∃ w, TmemWrite L X w cell ∧ WriteBefore L X w (g, kp) := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  obtain ⟨-, lo, hi, bc, qk | pv⟩ := Mma.Export.columns hp hX hf base he
  · obtain ⟨j, hpcj, -⟩ := qk
    exfalso
    have hq : Lib.qkIssue j = Lib.pvIssue 0 := hpcj.symm
    fin_cases j <;> exact absurd hq (by decide)
  · obtain ⟨j, hpcj, hdst, -, hdesc⟩ := pv
    obtain ⟨b, hd0, pb, one, -, -, -, hacc⟩ := Mma.Export.pv_block hp hX hf base he ⟨0, rfl⟩
    have hb2 : 2 ≤ b := by
      rcases hacc 0 rfl rfl with h | h
      · omega
      · exact h
    obtain ⟨-, -, -, hlast⟩ := Mma.Export.pv_prior hp hX hf words hu he (j := 0) rfl
    obtain ⟨kR, lt, d', s', a', m', get, q⟩ := hlast (by omega)
    obtain ⟨b', hd'', -⟩ := Mma.Export.pv_block hp hX hf base get ⟨7, rfl⟩
    obtain ⟨-, -, -, c⟩ := mma_class hp hX hf base get
    have hj0 : j = 0 := by
      have : Lib.pvIssue j = Lib.pvIssue 0 := hpcj.symm
      fin_cases j <;> first | rfl | exact absurd this (by decide)
    subst hj0
    have hdesc' : s'.descriptor = s.descriptor := by
      rcases c with ⟨h256, -⟩ | ⟨-, e⟩
      · omega
      · rw [e, hdesc]
    exact ⟨_, step_candidate hp hX hf base hr he get lt (by omega) hdesc'⟩

end PTX.Kernels.InklingRelDecode.Proof.Tmem
