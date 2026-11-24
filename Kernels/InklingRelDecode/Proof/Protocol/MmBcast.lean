-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.LpObs
public import Kernels.InklingRelDecode.Proof.Protocol.WpMma
public import Kernels.InklingRelDecode.Proof.Protocol.WmMmaCount
public import Kernels.InklingRelDecode.Proof.Interface.PrefixShfl

@[expose] public section

/-!
# Every broadcast of warp 7 receives the warp index (`Mma.MmaBcast`)

The MMA warp's machine follows its two broadcasts of the warp index for every received word: a
word other than 7 takes the branch that skips the half (`Mma.Site.qkSkip`, `pvSkip`). The layers
above use that warp 7 never takes it. A shuffle of a thread of warp 7 receives, by
DEP-WARP-SHUFFLE (`Consistent.shfl`), the operand of lane 0's shuffle of the same instance, or any
value when lane 0 exited before it.

* **The operand.** Every shuffle of a thread of warp 7 is its worker's broadcast or one of the MMA
  role's two, and all three broadcast the warp index, 7 (`w7_operand`).
* **Lane 0 does not exit first.** A thread of warp 7 exits only after its MMA role ended
  (`Lp.exists_setMaxRegInc`, from `RoleReads`). Before the role's entry a thread of warp 7 has made
  its worker's broadcast and no other shuffle (`cnt_entry_le`, `cnt_entry_ge`); along the role it
  makes `Wp.shfls d` (`Wp.shfl_cnt`), which is `2 n` at the role's end (`n = num_iters`, the same
  word for every thread of the CTA, `mma_iters`) and below `2 n` at a broadcast. So lane 0's exit
  has more shuffles before it than the lane's broadcast (`shfl_before_exit`).
* **The worker's own broadcast** is followed by its machine only on the warp index, and the thread
  is tracked.

`mmaBcast_of` is `Mma.MmaBcast` from the thread layer's facts, `RoleReads`, `BaseWordRead` and
`NumWordRead`; no fact of the lockstep is used.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Mb
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Worker (preRank)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The shuffle sites of a worker thread -/

theorem worker_shfl_pc (s : Worker.Site) (h : shflPc s.pc = true) : s = .shfl := by
  revert h
  cases s <;> decide +kernel

theorem mma_shfl_pc (s : Mma.Site) (h : shflPc s.pc = true) : s = .qkShfl ∨ s = .pvShfl := by
  revert h
  cases s <;> (try (rename_i j; revert j)) <;> decide +kernel

theorem idle_shfl_pc (s : Worker.Idle.Site) : shflPc s.pc = false := by
  cases s <;> decide +kernel

theorem loader_shfl_pc (s : Loader.Site) : shflPc s.pc = false := by
  cases s <;> decide +kernel

theorem exit_shfl_pc (s : WComp.ExitSite) : shflPc s.pc = false := by
  cases s <;> decide +kernel

/-- **The shuffle states of a worker thread**: the worker's broadcast and the MMA role's two. -/
theorem w_shfl_cases {s : WComp.WSt} (h : shflSt (.w s) = true) :
    (∃ P, s = .worker ⟨.shfl, P⟩) ∨
      ∃ d P, s = .mma d P ∧ (d.site = .qkShfl ∨ d.site = .pvShfl) := by
  have hp : shflPc (WComp.pc s) = true := h
  cases s with
  | worker w =>
    obtain ⟨site, P⟩ := w
    exact .inl ⟨P, by rw [worker_shfl_pc site hp]⟩
  | idle d =>
    rw [show WComp.pc (.idle d) = d.site.pc from rfl, idle_shfl_pc] at hp
    cases hp
  | loader d P =>
    rw [show WComp.pc (.loader d P) = d.site.pc from rfl, loader_shfl_pc] at hp
    cases hp
  | mma d P => exact .inr ⟨d, P, rfl, mma_shfl_pc _ hp⟩
  | exit x =>
    rw [show WComp.pc (.exit x) = x.site.pc from rfl, exit_shfl_pc] at hp
    cases hp

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
include hpre hX hf

omit hpre in
/-- The state of a shuffle event of a thread of warp 7. -/
theorem w7_shfl_state {x j pc : Nat} {m : ShflMode} {av : Value} {b c : Nat} {r : Value}
    {o : Bool} (hx : x < L.threads) (h7 : x % L.block / 32 = 7)
    (he : X.get (x, j) = some ⟨pc, .shfl m av b c r o⟩) :
    (∃ P, St Q L X x j = some (some (.w (.worker ⟨.shfl, P⟩)))) ∨
      ∃ d P, St Q L X x j = some (some (.w (.mma d P))) ∧
        (d.site = .qkShfl ∨ d.site = .pvShfl) := by
  obtain ⟨s, hσ⟩ := Frame.event_state hf.sound hX hf.tracked he (fun pc f h => by cases h)
  have hσ' : St Q L X x j = some (some s) := hσ
  have hsh : shflSt s = true := by
    rw [← isShfl_state hX hf hx he hσ']
    rfl
  have hjl : j ≤ (X.tr x).length := (List.getElem?_eq_some_iff.mp he).1.le
  cases s with
  | d sd =>
    exfalso
    have := (cls_inv j _ hjl hσ').mp trivial
    omega
  | w sw =>
    rcases w_shfl_cases hsh with ⟨P, rfl⟩ | ⟨d, P, rfl, hs⟩
    · exact .inl ⟨P, hσ'⟩
    · exact .inr ⟨d, P, hσ', hs⟩

include hT in
/-- **Every shuffle of a thread of warp 7 broadcasts 7.** -/
theorem w7_operand {x j pc : Nat} {m : ShflMode} {av : Value} {b c : Nat} {r : Value}
    {o : Bool} (hx : x < L.threads) (h7 : x % L.block / 32 = 7)
    (he : X.get (x, j) = some ⟨pc, .shfl m av b c r o⟩) : av = b32 7 := by
  rcases w7_shfl_state hX hf hx h7 he with ⟨P, hσ⟩ | ⟨d, P, hσ, hs⟩
  · obtain ⟨pc', recv, ok, hev⟩ := w_shfl_ev hX hf.sound hT hx he hσ
    simp only [Event.mk.injEq, Kind.shfl.injEq] at hev
    rw [hev.2.2.1]
    simp only [Worker.warpOf, h7]
  · have hsh := Wm.mma_ev_shape hpre hX hf he hσ
    unfold EvW.MmShape at hsh
    rcases hs with hs | hs <;> rw [hs] at hsh <;> obtain ⟨recv, ok, hev⟩ := hsh <;>
      simp only [Event.mk.injEq, Kind.shfl.injEq] at hev <;> rw [hev.2.2.1] <;>
      simp only [Worker.warpOf, h7]

/-! ### The shuffles before the MMA role's entry -/

omit hpre in
include hX hf in
/-- A shuffle of a thread of warp 7 before its MMA role's entry is its worker's broadcast, the
thread's event 3. -/
theorem shfl_before_entry (hR : RoleReads L X) (hpre : Pre Q L mem0) {y k k0 : Nat}
    {d0 : Mma.D} {P : Loader.Pro} {e : Event} (hy : y < L.threads)
    (hk0 : k0 < (X.tr y).length) (h0 : St Q L X y k0 = some (some (.w (.mma d0 P))))
    (hs0 : d0.site = .setMaxReg) (hk : k < k0) (he : (X.tr y)[k]? = some e)
    (hsh : Execution.isShfl e = true) : k = 3 := by
  have h7 : y % L.block / 32 = 7 := by
    simpa [RoleWarp, roleWarp] using roleWarp_inv hf.roleWarp k0 _ hk0.le h0
  obtain ⟨pc, kd⟩ := e
  cases kd <;> simp only [Execution.isShfl, Bool.false_eq_true] at hsh
  rename_i m av b c r o
  rcases w7_shfl_state hX hf hy h7 he with ⟨P', hσ⟩ | ⟨d, P', hσ, -⟩
  · exact w_pre_rank k (by omega) hσ rfl
  · exfalso
    obtain ⟨k1, d1, hk1, hσ1, hs1, -⟩ := Rd.mma_back hX hf k (by omega) hσ
    have := Rd.mma_entry_unique hpre hX hf hR (by omega) hk0 hσ1 hs1 h0 hs0
    omega

omit hpre in
include hX hf in
/-- **Before the MMA role's entry a thread of warp 7 has made at most one shuffle.** -/
theorem cnt_entry_le (hR : RoleReads L X) (hpre : Pre Q L mem0) {y k0 : Nat} {d0 : Mma.D}
    {P : Loader.Pro} (hy : y < L.threads) (hk0 : k0 < (X.tr y).length)
    (h0 : St Q L X y k0 = some (some (.w (.mma d0 P)))) (hs0 : d0.site = .setMaxReg) :
    cnt Execution.isShfl X y k0 ≤ 1 := by
  have key : ∀ k, k ≤ k0 → cnt Execution.isShfl X y k ≤ if 3 < k then 1 else 0 := by
    intro k
    induction k with
    | zero => intro _; simp [cnt]
    | succ k ih =>
      intro hk
      obtain ⟨e, he⟩ : ∃ e, (X.tr y)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [cnt_succ _ he]
      have ih' := ih (by omega)
      by_cases hc : Execution.isShfl e = true
      · have h3 := shfl_before_entry hX hf hR hpre hy hk0 h0 hs0 (by omega) he hc
        subst h3
        simp [hc] at ih' ⊢
        omega
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        split_ifs at ih' ⊢ <;> omega
  have := key k0 le_rfl
  split_ifs at this <;> omega

omit hpre in
include hT in
/-- **Before the MMA role's entry a thread of warp 7 has made its worker's broadcast.** -/
theorem cnt_entry_ge {y k0 : Nat} {d0 : Mma.D} {P : Loader.Pro} (hy : y < L.threads)
    (hk0 : k0 < (X.tr y).length) (h0 : St Q L X y k0 = some (some (.w (.mma d0 P)))) :
    1 ≤ cnt Execution.isShfl X y k0 := by
  have hd : ¬ IsDefault L y := by
    intro h
    have := (cls_inv k0 _ hk0.le h0).mpr h
    simp [TSt.isD] at this
  have h4 : 4 ≤ k0 := by
    by_contra hlt
    rcases w_pre_fwd (Q := Q) (X := X) hd k0 (by omega) hk0.le with ⟨w, hw, -⟩ | hn
    · rw [hw] at h0
      cases h0
    · rw [hn] at h0
      cases h0
  have h3 : St Q L X y 3 ≠ none := by
    intro hn
    have := Frame.stateAt_none_mono (C := code L Q) hn (show 3 ≤ k0 by omega)
    rw [show Frame.stateAt (code L Q) X y k0 = some (some (.w (.mma d0 P))) from h0] at this
    cases this
  obtain ⟨w, hw, hr⟩ := (w_pre_fwd (Q := Q) (X := X) hd 3 le_rfl (by omega)).resolve_right h3
  obtain ⟨site, P3⟩ := w
  have hsite : site = .shfl := by
    revert hr
    cases site <;> simp [preRank]
  subst hsite
  obtain ⟨e3, he3⟩ : ∃ e, (X.tr y)[3]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨pc, recv, ok, rfl⟩ := w_shfl_ev hX hf.sound hT hy he3 hw
  have h34 := cnt_succ (X := X) (g := y) Execution.isShfl he3
  have hm := cnt_mono (X := X) Execution.isShfl y (show 3 + 1 ≤ k0 by omega)
  simp only [Execution.isShfl, ↓reduceIte] at h34
  omega

/-! ### Lane 0 does not exit before the broadcast -/

include hT in
/-- **A lane of warp 7 has made more shuffles before its exit than another lane of the warp
before its MMA role's broadcast.** -/
theorem shfl_before_exit (hR : RoleReads L X) (hb : BaseWordRead L X) (hn : NumWordRead Q L X)
    {g a x kx pcx : Nat} {d : Mma.D} {P : Loader.Pro} (hg : g < L.threads)
    (hk : a < (X.tr g).length) (hσ : St Q L X g a = some (some (.w (.mma d P))))
    (hs : d.site = .qkShfl ∨ d.site = .pvShfl) (hw : SameWarp L g x)
    (hex : X.get (x, kx) = some ⟨pcx, .exit⟩) :
    cnt Execution.isShfl X g a < cnt Execution.isShfl X x kx := by
  have hx : x < L.threads := hw.1.2.1
  have h7 : g % L.block / 32 = 7 := by
    simpa [RoleWarp, roleWarp] using roleWarp_inv hf.roleWarp a _ hk.le hσ
  have hx7 : x % L.block / 32 = 7 := by rw [← hw.2]; exact h7
  -- the lane's count at its broadcast
  obtain ⟨k0, d0, hk0, h0, hs0, hcg⟩ := Wp.shfl_cnt hpre hX hf hR hg hk hσ
  have hA := cnt_entry_le hX hf hR hpre hg (by omega) h0 hs0
  have hI := mma_inv_at hX hf hk hσ
  have hsh : Wp.shfls d + 1 ≤ 2 * d.n := by
    rcases hs with hs | hs
    · have := hI.qk (by rw [hs]; trivial)
      simp only [Wp.shfls, hs]
      omega
    · have := hI.pv (by rw [hs]; trivial)
      simp only [Wp.shfls, hs]
      omega
  have hn1 : 1 ≤ d.n ∧ d.n ≤ 2147483646 := by
    rcases hs with hs | hs
    · have := hI.qk (by rw [hs]; trivial); omega
    · have := hI.pv (by rw [hs]; trivial); omega
  -- lane 0's exit is its last event, after the end of its MMA role
  have hkx : kx + 1 = (X.tr x).length := by
    obtain ⟨o, hr⟩ := hX.thr x hx
    exact Run.end_last hr hex (Or.inr rfl)
  have hlast : (X.tr x).getLast? = some ⟨pcx, .exit⟩ := by
    rw [List.getLast?_eq_getElem?, show (X.tr x).length - 1 = kx by omega]
    exact hex
  obtain ⟨j, dx, Px, hj, hσx, hsx⟩ := Lp.exists_setMaxRegInc hpre hX hf hR hx7 ⟨pcx, hlast⟩
  obtain ⟨k0x, d0x, hk0x, h0x, hs0x, hcx⟩ := Wp.shfl_cnt hpre hX hf hR hx hj hσx
  have hB := cnt_entry_ge hX hf hT hx (by omega) h0x
  -- the same `num_iters`
  have hcta : x / L.block = g / L.block := hw.1.2.2.symm
  have hnx : dx.n = d.n := by
    have e1 := mma_iters hpre hX hf hb hn (m := (x, j)) ⟨Px, hσx⟩ (by rw [hsx]; nofun)
      (by rw [hsx]; nofun)
    have e2 := mma_iters hpre hX hf hb hn (m := (g, a)) ⟨P, hσ⟩
      (by rcases hs with hs | hs <;> rw [hs] <;> nofun)
      (by rcases hs with hs | hs <;> rw [hs] <;> nofun)
    rw [e1, e2]
    unfold Result.Mma.reqOf Result.Mma.splitOf
    rw [Lp.cta_same hcta .z, Lp.cta_same hcta .x]
  have hIx := mma_inv_at hX hf hj hσx
  have hi0 : dx.i ≠ 0 := by
    intro h0'
    have := hIx.fin0 (by rw [hsx]; trivial) h0'
    omega
  have hshx : Wp.shfls dx = dx.n + dx.n := by
    simp only [Wp.shfls, hsx, hi0, ↓reduceIte]
  have hmono := cnt_mono (X := X) Execution.isShfl x (show j ≤ kx by omega)
  omega

/-! ### The broadcast word -/

include hT in
/-- **Every broadcast of a thread of warp 7 receives a word that reads as 7.** -/
theorem mmaBcast_of (hR : RoleReads L X) (hb : BaseWordRead L X) (hn : NumWordRead Q L X) :
    Mma.MmaBcast L X := by
  intro g hg h7 e hmem m av bv cv recv ok hk
  obtain ⟨a, ha⟩ := List.getElem?_of_mem hmem
  have hget : X.get (g, a) = some e := ha
  have hkl : a < (X.tr g).length := (List.getElem?_eq_some_iff.mp ha).1
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  rcases w7_shfl_state hX hf hg h7 hget with ⟨P, hσ⟩ | ⟨d, P, hσ, hs⟩
  · -- the worker's broadcast: its machine follows only the warp index
    have h1 := hf.tracked g (a + 1) hg
    rw [Frame.stateAt_succ ha, show Frame.stateAt (code L Q) X g a =
      some (some (.w (.worker ⟨.shfl, P⟩))) from hσ] at h1
    simp only [Option.bind_some] at h1
    have h2 : (threadCode L g Q).next (.w (.worker ⟨.shfl, P⟩)) ⟨pc, .shfl m av bv cv recv ok⟩ ≠
        some none := h1
    rw [next_w] at h2
    cases recv with
    | bits wd v =>
      by_cases hv : wd = 32 ∧ v = BitVec.ofNat 64 (Worker.warpOf L g)
      · obtain ⟨rfl, rfl⟩ := hv
        simp only [Raw.word32Of, Value.regBits, Worker.warpOf, h7, Option.map_some]
        rfl
      · exfalso
        apply h2
        simp [WComp.next, Worker.next, hv]
    | _ =>
      exfalso
      apply h2
      simp [WComp.next, Worker.next]
  · -- an MMA broadcast: the received word is lane 0's operand, 7
    have hsh := Wm.mma_ev_shape hpre hX hf hget hσ
    unfold EvW.MmShape at hsh
    obtain ⟨recv', ok', hev⟩ : ∃ recv' ok', (⟨pc, .shfl m av bv cv recv ok⟩ : Event) =
        ⟨d.site.pc, .shfl .idx (b32 (Worker.warpOf L g)) 0 31 recv' ok'⟩ := by
      rcases hs with hs | hs <;> rw [hs] at hsh <;> rw [hs] <;> exact hsh
    simp only [Event.mk.injEq, Kind.shfl.injEq] at hev
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hev
    have hK : X.ShflK (g, a) (cnt Execution.isShfl X g a) :=
      ⟨⟨_, _, _, _, _, _, _, hget⟩, rfl⟩
    obtain ⟨-, hsrc⟩ := hX.shfl g a _ pc .idx _ 0 31 recv ok hget hK
    have h0 : (shflSource .idx (laneOf L g) 0 31).1 = 0 := by
      simp [shflSource]
    rw [h0] at hsrc
    have hw := lane0_sameWarp hpre.block hg
    rcases hsrc with ⟨j, pc', b', c', r', o', -, hget'⟩ | ⟨kx, pcx, hex, hcx⟩
    · have hx : g - laneOf L g + 0 < L.threads := hw.1.2.1
      have hx7 : (g - laneOf L g + 0) % L.block / 32 = 7 := by rw [← hw.2]; exact h7
      have := w7_operand hpre hX hf hT hx hx7 hget'
      subst this
      simp [Raw.word32Of_b32]
    · exfalso
      have := shfl_before_exit hpre hX hf hT hR hb hn hg hkl hσ hs hw hex
      simp only [cnt] at this hcx
      omega

end
end PTX.Kernels.InklingRelDecode.Proof.Mb
