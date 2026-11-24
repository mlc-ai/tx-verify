-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.StateMap
public import Lemmas.Flow.TensorStoreOrigin

@[expose] public section
namespace FlashKda.Packed.StateMap
open PTX PTX.Flow PTX.Proof

theorem valid {base planes : Nat} {allocation : TensorDescriptor.AllocationClass}
    (aligned : base % 16 = 0) (nonempty : 0 < planes) (bound : planes ≤ 2^32) :
    TensorDescriptor.Valid (descriptor base planes allocation) := by
  refine ⟨by decide, aligned, ?_, ?_, ?_, ?_, by change 32 % 16 = 0; decide,
    Or.inr (by change 32 ≤ 32; decide), ?_, rfl⟩
  · intro a
    fin_cases a <;> simp [descriptor, nonempty]
    omega
  · intro a
    fin_cases a <;> norm_num [descriptor]
  · intro a
    fin_cases a <;> norm_num [descriptor]
  · intro a
    exact ⟨Nat.zero_lt_one, by change 1 ≤ 8; decide⟩
  · intro _
    rfl

structure Binding (L : Launch) (name : String) (map base planes : Nat)
    (allocation : TensorDescriptor.AllocationClass) : Prop where
  object : L.paramObjects name = some (⟨name, 8, 256, 128⟩, map)
  table : L.tensorMaps map = some ⟨2, descriptor base planes allocation⟩
  mapAlign : map % 128 = 0
  mapBound : map + 256 ≤ 2^64
  dataAlign : base % 16 = 0
  size : 0 < planes ∧ planes ≤ 2^32

private theorem map_read {L : Launch} {name : String} {map base planes : Nat} {allocation}
    (host : Binding L name map base planes allocation) {t : TState} {g r : Nat}
    (pointer : t.regs r = some (.ptr 64 true (.param name) 0)) (x y z : Nat) :
    tensorMap L g t (.reg r) [.reg x, .reg y, .reg z] .tile =
      .ok (map, ⟨2, descriptor base planes allocation⟩) := by
  have h64 : map % 64 = 0 := by have := host.mapAlign; omega
  have range : map ≤ 18446744073709551360 := by have := host.mapBound; omega
  simp [tensorMap, tensorMapAddress, readValue, readReg, pointer, host.object, host.mapAlign,
    range, ParamObjectDecl.bytes, host.table, h64, TensorMode.coordinates,
    valid host.dataAlign host.size.1 host.size.2, bind, Except.bind, pure, Except.pure]

private def words (i : Fin 16) (plane : Nat) : List (BitVec 64) :=
  [BitVec.ofNat 64 (8*i.val), 0, BitVec.ofNat 64 plane]

private theorem coords_read {L : Launch} {t : TState} {g x y z plane : Nat} (i : Fin 16)
    (hx : t.regs x = some (b32 (8*i.val))) (hy : t.regs y = some (b32 0))
    (hz : t.regs z = some (b32 plane)) (fits : plane < 2^31) :
    [Opnd.reg x, .reg y, .reg z].mapM (readBits L g t 32) = .ok (words i plane) := by
  simp only [List.mapM_cons, List.mapM_nil, readBits_b32 hx (by omega), readBits_b32 hy (by decide),
    readBits_b32 hz (by omega), bind, Except.bind, pure, Except.pure]
  rfl

private theorem origin {plane : Nat} (i : Fin 16) (fits : plane < 2^31) :
    (fun n : Fin 3 => (BitVec.ofNat 32 ((words i plane).getD n.val 0).toNat).toInt) =
      ![((8*i.val : Nat) : Int), 0, (plane : Int)] := by
  funext n
  have unpack (x : Nat) (h : x < 2^31) :
      (BitVec.ofNat 32 (BitVec.ofNat 64 x).toNat).toInt = (x:Int) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact toInt_ofNat_lt32 h
  fin_cases n
  · exact unpack _ (by omega)
  · rfl
  · exact unpack _ fits

private theorem box {base planes plane : Nat} {allocation} (i : Fin 16) :
    TensorDescriptor.BoxAligned (descriptor base planes allocation)
      ![((8*i.val : Nat) : Int), 0, (plane : Int)] := by
  change (((8*i.val : Nat) : Int)*4) % 16 = 0
  omega

private theorem origin_nonnegative (i : Fin 16) (plane : Nat) :
    ∀ n : Fin 3, 0 ≤ ![((8*i.val : Nat) : Int), 0, (plane : Int)] n := by
  intro n
  fin_cases n <;> simp

set_option maxRecDepth 8192 in
theorem store_event {L : Launch} {t : TState} {g r src x y z : Nat} {name : String}
    {map base planes plane : Nat} {allocation} (host : Binding L name map base planes allocation)
    (i : Fin 16) (fits : plane < 2^31) (aligned : L.sharedBase % 128 = 0)
    (space : L.sharedBase + 98304 ≤ 2^32)
    (pointer : t.regs r = some (.ptr 64 true (.param name) 0))
    (hx : t.regs x = some (b32 (8*i.val))) (hy : t.regs y = some (b32 0))
    (hz : t.regs z = some (b32 plane))
    (addr : t.regs src = some (b32 (L.sharedBase + 32768 + 4096*i.val))) :
    tensorStoreTmpl L g t (.cpTensorStore (.reg r) [.reg x, .reg y, .reg z] src 0 none .tile none) =
      .tensorStore map (strip base planes plane allocation ⟨.shared, g / L.block, L.sharedBase⟩ i)
        (PTX.next t) := by
  have hs := sharedEffAddr_b32 (L := L) (g := g) addr (by omega)
  have ha : (L.sharedBase + 32768 + 4096*i.val) % 128 = 0 := by omega
  have nonneg (n : Fin 3) : 0 ≤ (BitVec.ofNat 32 ((words i plane).getD n.val 0).toNat).toInt :=
    (congrFun (origin i fits) n).symm ▸ origin_nonnegative i plane n
  simp only [tensorStoreTmpl, tensorStoreSpec, map_read host pointer, hs,
    coords_read i hx hy hz fits,
    bind, Except.bind, pure, Except.pure, Option.all, ha, origin i fits, nonneg, cachePolicyRead,
    TensorMode.transfer, requireBoxAligned, box i, ↓reduceIte, true_or]
  rfl

private theorem cluster_shared {L : Launch} {t : TState} {g src a : Nat}
    (h : t.regs src = some (b32 a)) (fits : a < 2^32) :
    sharedEffAddr L g t true src 0 = .ok ⟨.shared, g / L.block, a⟩ := by
  have hc := sharedEffAddr_b32 (L := L) (g := g) h fits
  simpa only [sharedEffAddr, readReg, h, b32, bind, Except.bind, pure, Except.pure] using hc

set_option maxRecDepth 8192 in
theorem load_event {L : Launch} {t : TState} {g r dst x y z mb cache : Nat} {name : String}
    {map base planes plane : Nat} {allocation} (host : Binding L name map base planes allocation)
    (i : Fin 16) (fits : plane < 2^31) (aligned : L.sharedBase % 128 = 0)
    (space : L.sharedBase + 98392 ≤ 2^32) (grid : L.clusterGridValid) (cta : g/L.block < L.grid)
    (pointer : t.regs r = some (.ptr 64 true (.param name) 0))
    (hx : t.regs x = some (b32 (8*i.val))) (hy : t.regs y = some (b32 0))
    (hz : t.regs z = some (b32 plane))
    (addr : t.regs dst = some (b32 (L.sharedBase + 32768 + 4096*i.val)))
    (barrier : t.regs mb = some (b32 (L.sharedBase + 98384)))
    (policy : t.regs cache = some (b64 (2^60))) :
    tensorTmpl L g t (.cpTensor true false dst 0 (.reg r) [.reg x, .reg y, .reg z] mb 0
      none .tile (some (.reg cache))) =
      .tensorIssue map (input base planes plane allocation ⟨.shared, g/L.block, L.sharedBase⟩
        ⟨.shared, g/L.block, L.sharedBase+98384⟩ i) (PTX.next t) := by
  have hs := cluster_shared (L := L) (g := g) addr (by omega)
  have hb := cluster_shared (L := L) (g := g) barrier (by omega)
  have ha : (L.sharedBase + 32768 + 4096*i.val) % 128 = 0 := by omega
  have hm : (L.sharedBase + 98384) % 8 = 0 := by omega
  have route : TensorRoute L (g/L.block) true .one
      ⟨.shared, g/L.block, L.sharedBase+32768+4096*i.val⟩
      ⟨.shared, g/L.block, L.sharedBase+98384⟩ := by
    simp [TensorRoute, grid, sameCtaGroup_iff, CtaInCluster, cta]
  simp only [tensorTmpl, tensorLoadCopy, map_read host pointer, hs, mbarClusterLoc, hb,
    coords_read i hx hy hz fits, bind, Except.bind, pure, Except.pure, ha, hm, origin i fits,
    cachePolicyRead, readBits_b64 policy (by decide), TensorMode.transfer, requireBoxAligned,
    box i, Bool.false_eq_true, ↓reduceIte, route]
  rfl

end FlashKda.Packed.StateMap
