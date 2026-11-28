-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.FollowSub
public import Kernels.InklingRelDecode.Proof.Prologue.PreloadCount
import Kernels.InklingRelDecode.Proof.Lib.Geometry
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof Arith32

noncomputable section
variable {Q : Params} {L : Launch} {g : Nat} {m : Mem0} {X : Execution}

/-- The sequence word used to initialize the Softmax loop is the one read from
the launch arrays. Its positive trip count equals the CTA's shared schedule count. -/
theorem handoff_limit {w d} (hp : Pre Q L m) (hg : g<L.threads)
    (known : Prologue.Known Q ((L.ctaidOf (g/L.block)).get .z) d) (site : d.site=.exit) :
    (dataEntry Q L g w d).limit = Lib.blocksOf Q L (g/L.block) := by
  have seq := known.seq (by rw [site]; decide)
  have v := Prologue.published_iters (w := w) hp hg seq
  have bound := Lib.blocksOf_lt hp hg
  have bits := Value.bits.inj v
  change (Prologue.Control.positive _).toNat = _
  rw [bits.2]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The epilogue skips its load exactly when the loop count is zero. -/
theorem skip_iff_limit (z : Int) :
    decide ((intBits 32 z).toNat = 0 ∨ 2^31 ≤ (intBits 32 z).toNat) =
      decide ((Prologue.Control.positive (intBits 32 z)).toNat = 0) := by
  have h : (intBits 32 z).toNat < 2^32 := by
    simp only [intBits, truncBits, BitVec.toNat_ofNat]; exact lt_of_le_of_lt (Nat.mod_le _ _)
      (Nat.mod_lt _ (by norm_num : 0 < 2^32))
  generalize intBits 32 z = b at h ⊢
  unfold Prologue.Control.positive
  simp only [scmpi, r32, truncBits, BitVec.toNat_ofNat, PTX.compare, toSigned, i32]
  have e0 : (BitVec.ofInt 64 0).toNat = 0 := by decide
  have m : b.toNat % 2^32 = b.toNat := Nat.mod_eq_of_lt h
  simp only [e0, m, Nat.zero_mod]
  split_ifs <;> simp_all <;> omega

/-- The numbers a Softmax entry carries are the launch's: the request's first token and length. -/
def EntryNumbers (Q : Params) (L : Launch) (g : Nat) (w : Value) (ent : Softmax.Control.Entry) :
    Prop :=
  (∃ d, ent = dataEntry Q L g w d) ∧
    ent.firstWord = b32 (Q.qStart ((L.ctaidOf (g/L.block)).get .z)) ∧
    ent.qlen = Q.qLen ((L.ctaidOf (g/L.block)).get .z)

/-- The request words the entry was built from are the launch's. -/
def EntryWords (Q : Params) (L : Launch) (g : Nat) (w : Value) (ent : Softmax.Control.Entry) :
    Prop :=
  ∃ d, ent = dataEntry Q L g w d ∧ d.seq = b32 (Q.seqK ((L.ctaidOf (g/L.block)).get .z)) ∧
    d.last = b32 (Q.qStart ((L.ctaidOf (g/L.block)).get .z + 1))

private def valid : (thread Q L g).D → Prop
  | (.inr ⟨.inl (.prologue w),.inr ⟨ent,_⟩⟩,_) => (ent.limit = Lib.blocksOf Q L (g/L.block) ∧
      decide (ent.blocks = 0 ∨ 2^31 ≤ ent.blocks) = decide (ent.limit = 0)) ∧
      EntryNumbers Q L g w ent ∧ EntryWords Q L g w ent
  | _ => True

/-- At the exit the entry's request words are the launch's. -/
private theorem handoff_numbers {w d} (hp : Pre Q L m) (hg : g<L.threads)
    (known : Prologue.Known Q ((L.ctaidOf (g/L.block)).get .z) d) (site : d.site=.exit) :
    EntryNumbers Q L g w (dataEntry Q L g w d) := by
  have f := known.first (by rw [site]; decide)
  have l := known.last (by rw [site]; decide)
  refine ⟨⟨d,rfl⟩,f,?_⟩
  have fine := Lib.qStart_mono hp (r := ((L.ctaidOf (g/L.block)).get .z)+1) (r' := Q.b)
    (by have := (Lib.coordinate_bounds hp hg).2.2; omega) le_rfl
  have mono := Lib.qStart_le hp (r := ((L.ctaidOf (g/L.block)).get .z))
    (by have := (Lib.coordinate_bounds hp hg).2.2; omega)
  have end_ := hp.cuEnd
  have nt := hp.nTokRange
  change (Prologue.Control.qlen d).toNat = _
  unfold Prologue.Control.qlen Prologue.Control.subValue
  rw [f,l]
  simp only [Params.qLen, Lib.word, Value.regBits, b32, sub32, truncBits, Option.getD_some,
    BitVec.toNat_ofNat, BitVec.toNat_sub,]
  omega

private theorem enter_valid (s : Startup.D) (n : Cls → Nat) :
    valid (Q := Q) (L := L) (g := g) (Code.enter (Startup.code Q L g)
      (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) := by
  obtain ⟨site,tm,x,w⟩ := s
  cases site <;> first | trivial | (rename_i r; cases r <;> trivial)

private theorem next_valid {s sn : (thread Q L g).D} {ev k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g<L.threads) (hk : k≤(X.tr g).length)
    (he : X.get (g,k)=some ev)
    (hs : Frame.stateAt (thread Q L) X g k = some (some s)) (old : valid s)
    (hn : (thread Q L g).next s ev = some (some sn)) : valid sn := by
  obtain ⟨s,n⟩ := s
  obtain ⟨sn,nn⟩ := sn
  obtain ⟨step,_⟩ := Code.counted_next_some hn
  rcases s with init | ⟨r,d⟩
  · obtain ⟨_,_,rfl⟩ := Code.glue_inl_some step
    exact enter_valid ..
  obtain ⟨dn,sub,rfl⟩ := Code.glue_inr_some step
  rcases r with r|r
  · cases r with
    | dispatch => trivial
    | prologue w =>
      rcases d with d|⟨ent,d⟩
      · obtain ⟨dt,localStep,rfl⟩ := Code.glue_inl_some sub
        unfold Code.enter
        split
        · rename_i en eq
          change dataExit Q L g w dt = some en at eq
          unfold dataExit at eq
          split at eq <;> cases eq
          rename_i exit
          have known := pro_known_step hp hX he hs (pro_known hp hX hk hs) localStep
          refine ⟨⟨handoff_limit hp hg known exit,?_⟩,handoff_numbers hp hg known exit,
            ⟨dt,rfl,known.seq (by rw [exit]; decide),known.last (by rw [exit]; decide)⟩⟩
          exact skip_iff_limit _
        · trivial
      · obtain ⟨_,_,rfl⟩ := Code.glue_inr_some sub
        exact old
  · cases sub

/-- Every reached data-role state after the prologue carries the launch trip count,
including the states entered after the last Softmax poll, and the epilogue's skip of the load
is the zero trip count. -/
theorem reached_both {k w ent s n} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g<L.threads) (hk : k≤(X.tr g).length)
    (hs : Frame.stateAt (thread Q L) X g k = some (some
      (.inr ⟨.inl (.prologue w),.inr ⟨ent,s⟩⟩,n))) : (ent.limit = Lib.blocksOf Q L (g/L.block) ∧
      decide (ent.blocks = 0 ∨ 2^31 ≤ ent.blocks) = decide (ent.limit = 0)) ∧
      EntryNumbers Q L g w ent ∧ EntryWords Q L g w ent := by
  suffices allValid : ∀ j ≤ (X.tr g).length, ∀ d, Frame.stateAt (thread Q L) X g j =
      some (some d) → valid d by exact allValid k hk _ hs
  intro j
  induction j with
  | zero =>
    intro _ d reached
    rw [Frame.stateAt_zero] at reached
    cases reached
    exact enter_valid ..
  | succ j ih =>
    intro len d reached
    have get := List.getElem?_eq_getElem (l := X.tr g) (i := j) (by omega)
    rw [Frame.stateAt_succ get] at reached
    rcases prev : Frame.stateAt (thread Q L) X g j with _|_|old <;> rw [prev] at reached <;>
      try solve | cases reached
    exact next_valid hp hX hg (by omega) get prev (ih (by omega) _ prev) reached

theorem reached_loop {k w ent s n} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g<L.threads) (hk : k≤(X.tr g).length)
    (hs : Frame.stateAt (thread Q L) X g k = some (some
      (.inr ⟨.inl (.prologue w),.inr ⟨ent,s⟩⟩,n))) : ent.limit = Lib.blocksOf Q L (g/L.block) ∧
      decide (ent.blocks = 0 ∨ 2^31 ≤ ent.blocks) = decide (ent.limit = 0) :=
  (reached_both hp hX hg hk hs).1

theorem reached_numbers {k w ent s n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g<L.threads) (hk : k≤(X.tr g).length)
    (hs : Frame.stateAt (thread Q L) X g k = some (some
      (.inr ⟨.inl (.prologue w),.inr ⟨ent,s⟩⟩,n))) : EntryNumbers Q L g w ent :=
  (reached_both hp hX hg hk hs).2.1

theorem reached_words {k w ent s n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g<L.threads) (hk : k≤(X.tr g).length)
    (hs : Frame.stateAt (thread Q L) X g k = some (some
      (.inr ⟨.inl (.prologue w),.inr ⟨ent,s⟩⟩,n))) : EntryWords Q L g w ent :=
  (reached_both hp hX hg hk hs).2.2

theorem reached_limit {k w ent s n} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g<L.threads) (hk : k≤(X.tr g).length)
    (hs : Frame.stateAt (thread Q L) X g k = some (some
      (.inr ⟨.inl (.prologue w),.inr ⟨ent,s⟩⟩,n))) : ent.limit = Lib.blocksOf Q L (g/L.block) :=
  (reached_loop hp hX hg hk hs).1

end
end PTX.Kernels.InklingRelDecode.Proof
