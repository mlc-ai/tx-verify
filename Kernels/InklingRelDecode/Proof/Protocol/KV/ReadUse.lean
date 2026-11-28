-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.EmptyCount
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
public import Kernels.InklingRelDecode.Proof.Lib.MmaPcs
import Kernels.InklingRelDecode.Proof.Mma.Export.Cover
import Kernels.InklingRelDecode.Proof.Mma.Export.CommitNext
import Kernels.InklingRelDecode.Proof.Mma.Export.EmptyCredit
import Lemmas.Flow.NthEv

@[expose] public section

/-! # The use of the ring slot an MMA reads is its block over three

Before the QK issue of block `b` (and before the PV issue of block `b - 1`), the lane returned the
slots of blocks `0 .. b - 2` exactly once each, so the read's slot `σ` has been returned `⌊n / 3⌋`
times for its block `n`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow PTX.Frame MbarRow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- Below a position `k` of an MMA event, a last PV step of ordinal `O` has the empty commit of
every ordinal up to `O` before `k`. -/
theorem commits_below (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (hu : NoUbOutside L X) {pc dst s acc mask}
    (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩) {kt O : Nat} (lt : kt < k)
    (top : ∃ d s a m', X.get (g,kt) = some ⟨Lib.pvIssue 7,.tc (.mma d s a m')⟩ ∧
      pollRound 2510 ((X.tr g).take kt) = O) :
    ∀ o, 1 ≤ o → o ≤ O → ∃ j < k, ∃ sp, X.get (g,j) = some ⟨2546,.tc (.commit sp)⟩ ∧
      pollRound 2510 ((X.tr g).take j) = o := by
  have nu := noUbBefore_of_get hX he
  have len : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have chain : ∀ n kt', kt' < k → (∃ d s a m', X.get (g,kt') = some ⟨Lib.pvIssue 7,
        .tc (.mma d s a m')⟩ ∧ pollRound 2510 ((X.tr g).take kt') = n) →
      ∀ o, 1 ≤ o → o ≤ n → ∃ j < k, ∃ sp, X.get (g,j) = some ⟨2546,.tc (.commit sp)⟩ ∧
        pollRound 2510 ((X.tr g).take j) = o := by
    intro n
    induction n with
    | zero => exact fun _ _ _ o h1 h2 => absurd h2 (by omega)
    | succ n ih =>
      intro kt' lt' ⟨d,s',a,m',get,ord⟩ o h1 h2
      by_cases ho : o = n + 1
      · subst ho
        obtain ⟨ev,hn⟩ : ∃ ev, X.get (g,kt'+1) = some ev :=
          ⟨_,List.getElem?_eq_getElem (by omega : kt'+1 < (X.tr g).length)⟩
        have clean : ∀ f, ev.kind ≠ .ub f := by
          rcases Nat.lt_or_ge (kt'+1) k with h | h
          · exact nu _ h _ hn
          · obtain rfl : kt'+1 = k := by omega
            obtain rfl := Option.some.inj (hn.symm.trans he)
            exact nofun
        obtain ⟨sp,rfl,same⟩ := Mma.Export.pv_commit_next hp hX hf get rfl hn clean
        refine ⟨kt'+1,?_,sp,hn,same.trans ord⟩
        rcases Nat.lt_or_ge (kt'+1) k with h | h
        · exact h
        · obtain rfl : kt'+1 = k := by omega
          cases Option.some.inj (hn.symm.trans he)
      · obtain ⟨-,-,-,last⟩ := Mma.Export.pv_prior hp hX hf words hu get (j := 7) rfl
        obtain ⟨kR,lt'',d',s'',a',m'',get',q⟩ := last (by omega)
        exact ih kR (by omega) ⟨_,_,_,_,get',by omega⟩ o h1 (by omega)
  obtain ⟨d,s',a,m',get,ord⟩ := top
  exact chain O kt lt ⟨d,s',a,m',get,ord⟩

/-- **The slot of a QK issue of block `b` was returned `b / 3` times.** -/
theorem qk_empty_count (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (hu : NoUbOutside L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {pc dst s acc mask} (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    (qk : ∃ j : Fin 8, pc = Lib.qkIssue j) {b : Nat} {σ : Fin 3}
    (hb : pollRound 2462 ((X.tr g).take k) = b + 1) (hσ : σ.val = b % 3) :
    ((X.tr g).take k).countP (commitsTo (Ring.empty.obj L (g / L.block) σ)) = b / 3 := by
  obtain ⟨b',-,hq,hp',warp,-⟩ := Mma.Export.qk_block hp hX hf base he qk
  have eq : b = b' := by omega
  subst eq
  obtain ⟨j,hj⟩ := qk
  rw [empty_count hp hX hf words warp rfl (T := b - 1) (fun j' lt _ _ => ?_) (fun o h1 h2 => ?_)]
  · have := σ.isLt
    unfold visits
    omega
  · have := countP_take_mono (okPollAt 2510) (X.tr g) (Nat.le_of_lt lt)
    change pollRound 2510 _ ≤ pollRound 2510 _ at this
    omega
  · obtain ⟨kR,lt,d,s',a,m',get,q⟩ := Mma.Export.qk_last hp hX hf words hu he hj (by omega)
    exact commits_below hp hX hf words hu he lt (O := b - 1) ⟨d,s',a,m',get,by omega⟩ o h1 h2

/-- **The slot of a PV issue of block `b - 1` was returned `(b - 1) / 3` times.** -/
theorem pv_empty_count (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (hu : NoUbOutside L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {pc dst s acc mask} (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    (pv : ∃ j : Fin 8, pc = Lib.pvIssue j) {b : Nat} {σ : Fin 3}
    (hb : pollRound 2510 ((X.tr g).take k) = b) (hσ : σ.val = (b - 1) % 3) :
    ((X.tr g).take k).countP (commitsTo (Ring.empty.obj L (g / L.block) σ)) = (b - 1) / 3 := by
  obtain ⟨b',-,hp',h1,-,-,warp,-⟩ := Mma.Export.pv_block hp hX hf base he pv
  have eq : b = b' := by omega
  subst eq
  obtain ⟨j,hj⟩ := pv
  have inl : pc ∈ [2530,2533,2535,2537,2539,2541,2543,2545] := by
    subst hj
    fin_cases j <;> decide
  rw [empty_count hp hX hf words warp rfl (T := b - 1) (fun j' lt sp get => ?_)
    (fun o h1 h2 => ?_)]
  · have := σ.isLt
    unfold visits
    omega
  · have := Mma.Export.commit_ord_lt hp hX hf words warp get lt he inl
    omega
  · obtain ⟨-,-,-,last⟩ := Mma.Export.pv_prior hp hX hf words hu he hj
    obtain ⟨kR,lt,d,s',a,m',get,q⟩ := last (by omega)
    exact commits_below hp hX hf words hu he lt (O := b - 1)
      ⟨d,s',a,m',get,q.trans (by rw [hb])⟩ o h1 h2

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
