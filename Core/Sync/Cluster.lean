-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Value
public import Core.Sync.ClusterBarrierHistory

@[expose] public section

namespace PTX

/-! ## PROG-CLUSTER — cluster membership, coordinates and logical peer addresses

Statement: The grid of a cluster launch consists of whole clusters, each of the regular or of the
  preferred cluster shape. The model numbers the CTAs so that the CTAs of one cluster are
  consecutive, ordered by their rank in the cluster. The rank of a CTA selects the CTA with that
  position in the same cluster. A CTA's `%cluster_nctaid`, `%cluster_ctaid`, `%cluster_ctarank`,
  `%cluster_nctarank`, `%clusterid`, `%nclusterid` and `%ctaid` are those of its own cluster
  (EXT-CLUSTER-RANK). Mapping a shared location to a peer rank keeps its byte offset and changes its
  owning CTA to the peer.

Defs: Launch.locate, Launch.clusterOfCta, Launch.rankOfCta, Launch.clusterSizeAt,
  Launch.clusterStart, Launch.placeOf, Launch.clusterSizeOf, Launch.clusterNctaidOf,
  Launch.clusterCtaidOf, Launch.clusteridOf, Launch.nclusteridOf, Launch.ctaidOf,
  Launch.clusterGridValid, Launch.oneDimLaunch, Launch.locate_regular, Launch.oneDim_clusterPlaces,
  Launch.oneDim_clusterSizeAt, Launch.oneDim_clusterOfCta, Launch.oneDim_rankOfCta,
  Launch.oneDim_clusterStart, Launch.oneDim_clusterSizeOf, Launch.oneDim_clusterNctaidOf,
  Launch.oneDim_nclusteridOf, Launch.oneDim_clusterCtaidOf, Launch.oneDim_clusteridOf,
  Launch.oneDim_ctaidOf, Launch.oneDimLaunch_clusterGridValid, Launch.clusterGridValid_start,
  Launch.peerCta, Launch.mapShared, SameCluster

Source:
- §2.2.2: "Each CTA in a cluster has a unique CTA identifier within its cluster ( cluster_ctaid ).
    Each cluster of CTAs has 1D, 2D or 3D shape specified by the parameter cluster_nctaid . Each CTA
    in the cluster also has a unique CTA identifier ( cluster_ctarank ) across all dimensions. The
    total number of CTAs across all the dimensions in the cluster is specified by cluster_nctarank
    ."
- §2.2.3: "Each cluster has a unique cluster identifier ( clusterid ) within a grid of clusters."
- §10.12: "Each cluster in a grid has a unique identifier."
- §10.14: "It is guaranteed that: 0 <= %cluster_ctaid.x < %cluster_nctaid.x"
- §10.16: "It is guaranteed that: 0 <= %cluster_ctarank < %cluster_nctarank"
- §9.7.10.26 (mapa)
- EXT-CLUSTER-RANK
- EXT-PREFERRED-CLUSTER

Direction: reading

Applies: Grids and clusters of up to three dimensions, with clusters of the regular or the preferred
  shape

Premises: A valid cluster launch tiles the grid with its clusters (`Launch.clusterGridValid`,
  CORRECT-LAUNCH); a target rank belongs to the issuer's cluster.

Effect: Launch topology, special-register values and the logical location mapping used by
  peer-memory operations. The launch places each cluster (`Launch.clusterPlaces`, PROG-LAUNCH): its
  origin `%ctaid`, its shape and the `%clusterid` and `%nclusterid` its threads read. The CTA number
  (PROG-LAUNCH) is the model's own name of a CTA, used for the ownership of shared memory, barriers
  and Tensor Memory; no register shows it. Cluster `k` has the CTA numbers from
  `Launch.clusterStart k`, one for each rank (`Launch.locate`, `Launch.clusterOfCta`,
  `Launch.rankOfCta`). Every rule that names the cluster of a CTA, its rank or the size of its
  cluster (cluster barriers, peer addresses, CTA pairs, multicast masks, cluster launch control)
  uses these functions, so it applies to the CTA's own cluster, of either shape.
  `Launch.clusterGridValid` states what a placement must satisfy (EXT-PREFERRED-CLUSTER): the counts
  are the products of the shapes, each cluster lies in the grid on the lattice of the regular shape,
  the clusters together have the grid's CTAs, no two CTAs have one `%ctaid`, and no two clusters one
  `%clusterid`.

Review: `Launch.oneDimLaunch` is the launch condition of the kernels proved before the model had
  three-dimensional shapes: the grid, the CTA and the cluster are one-dimensional, the clusters are
  the regular clusters tiling the grid (`Launch.OneDim`), and the grid is a whole number of
  clusters. It implies `Launch.clusterGridValid` (`Launch.oneDimLaunch_clusterGridValid`). Under it
  the cluster of CTA `c` is `c / s` with rank `c % s` for cluster size `s`, `%ctaid` is `(c, 0, 0)`,
  `%clusterid` is `(c / s, 0, 0)` and `%cluster_ctaid` is `(c % s, 0, 0)`
  (`Launch.oneDim_clusterOfCta` and its neighbours), and every register has the value of the
  one-dimensional model (`sregValue_oneDim`, THREAD-SREG). A kernel whose precondition names it is
  proved for such launches only; a kernel for launches of any shape uses `Launch.clusterGridValid`.
  `mapShared` is the location transformation used by register-level mapa lowering and the peer-CTA
  lifetime checks (ERR-SHARED-LIFETIME); it is independent of any bit encoding of a shared/generic
  pointer.

### EXT-CLUSTER-RANK — cluster coordinates and rank

Statement: The model relates `%ctaid` to the cluster registers. In each dimension `d`,
  `%ctaid.d = origin.d + %cluster_ctaid.d` for the origin of the CTA's cluster. `%cluster_ctarank`
  is the linear index of `%cluster_ctaid` in the cluster's shape with `x` varying fastest:
  `%cluster_ctaid.x + %cluster_ctaid.y * %cluster_nctaid.x + %cluster_ctaid.z *
  %cluster_nctaid.x * %cluster_nctaid.y`. The rank is also the bit position of a `ctaMask` and the
  operand of `mapa`. When every cluster has the regular shape (`ClusterPlace.uniform`), `origin.d =
  %clusterid.d * %cluster_nctaid.d` and `%nclusterid.d = %nctaid.d / %cluster_nctaid.d`. In a
  one-dimensional launch with cluster size `s`, the CTA with `%ctaid.x` equal to `c` is in cluster
  `c / s` and has rank `c % s`; cluster `k` holds CTAs `k s` to `k s + s - 1`, and the grid is a
  multiple of `s`.

Source:
- §2.2.2 and §2.2.3 (a cluster is a group of CTAs; the grid is a grid of clusters)
- §10.12–§10.17 (`%clusterid`, `%cluster_ctaid`, `%cluster_nctarank`, `%cluster_ctarank`)
- §10.12–§10.17: "It is guaranteed that: 0 <= %cluster_ctarank < %cluster_nctarank"
- the production FP16 GEMM, which mixes peer ranks derived from `%ctaid` with `mapa` and
    `%cluster_ctarank`

Why it is not spec text: §10.12–§10.17 give the ranges of the identifiers and say that each CTA of a
  cluster has a unique one; the text does not relate `%ctaid` to the cluster, the cluster identifier
  or the rank, and it does not say how the rank linearizes `%cluster_ctaid`, so these formulas are
  not in the ISA. The order with `x` fastest is the one §9.7.17.1 gives for the warp rank of a
  thread.

Direction: reading

Effect: A program that derives a peer from `%ctaid` is judged with this mapping; if the hardware
  numbering differs, `mapa` targets and multicast masks denote other CTAs. Disclosed by every kernel
  whose statement names `SRegName.clusterid`, `SRegName.nclusterid`, `SRegName.clusterCtaid`,
  `SRegName.clusterNctaid`, `SRegName.clusterCtarank`, `SRegName.clusterNctarank`, `AddrInstr.mapa`,
  `Op.cluster`, `Op.clcTryCancel`, `SharedWindow.cluster`, `Op.mbarArrive (cluster := true)`,
  `Op.cpTensor (multicast ≠ none)` or `CtaGroup.two`: FlashAttn4Fwd, Fp16Gemm8192.
-/

/-- The cluster number and the rank of the CTA at flat offset `c` after the first `k` clusters,
looking at `n` more clusters; after the assigned clusters the CTA numbers continue in clusters of
the regular size. -/
def Launch.locate (L : Launch) : Nat → Nat → Nat → Nat × Nat
  | 0, k, c => (k + c / L.clusterSize.val, c % L.clusterSize.val)
  | n + 1, k, c =>
    let s := (L.clusterPlaces k).shape.prod
    if c < s then (k, c) else L.locate n (k + 1) (c - s)

/-- The cluster that contains CTA `cta`. -/
def Launch.clusterOfCta (L : Launch) (cta : Nat) : Nat := (L.locate L.nclusters 0 cta).1

/-- The rank of CTA `cta` in its cluster (`%cluster_ctarank`). -/
def Launch.rankOfCta (L : Launch) (cta : Nat) : Nat := (L.locate L.nclusters 0 cta).2

/-- The number of CTAs of cluster `k`. -/
def Launch.clusterSizeAt (L : Launch) (k : Nat) : Nat := (L.clusterPlaces k).shape.prod

/-- The CTA number of the CTA of rank 0 of cluster `k`. -/
def Launch.clusterStart (L : Launch) : Nat → Nat
  | 0 => 0
  | k + 1 => L.clusterStart k + L.clusterSizeAt k

/-- The place of the cluster of CTA `cta`. -/
def Launch.placeOf (L : Launch) (cta : Nat) : ClusterPlace := L.clusterPlaces (L.clusterOfCta cta)

/-- The number of CTAs of the cluster of CTA `cta` (`%cluster_nctarank`). -/
def Launch.clusterSizeOf (L : Launch) (cta : Nat) : Nat := L.clusterSizeAt (L.clusterOfCta cta)

/-- `%cluster_nctaid` of CTA `cta`: the shape of its cluster. -/
def Launch.clusterNctaidOf (L : Launch) (cta : Nat) : Dim3 := (L.placeOf cta).shape

/-- `%cluster_ctaid` of CTA `cta`: the coordinates of its rank in its cluster's shape, `x`
fastest (EXT-CLUSTER-RANK). -/
def Launch.clusterCtaidOf (L : Launch) (cta : Nat) : Dim3 :=
  (L.placeOf cta).shape.coord (L.rankOfCta cta)

/-- `%clusterid` of CTA `cta`: the identifier of its cluster. -/
def Launch.clusteridOf (L : Launch) (cta : Nat) : Dim3 := (L.placeOf cta).id

/-- `%nclusterid` as CTA `cta` reads it. -/
def Launch.nclusteridOf (L : Launch) (cta : Nat) : Dim3 := (L.placeOf cta).count

/-- `%ctaid` of CTA `cta`: its cluster's origin plus its coordinates in the cluster
(EXT-CLUSTER-RANK). -/
def Launch.ctaidOf (L : Launch) (cta : Nat) : Dim3 :=
  let o := (L.placeOf cta).origin
  let r := L.clusterCtaidOf cta
  ⟨o.x + r.x, o.y + r.y, o.z + r.z⟩

/-- The launch's cluster assignment is one the CUDA launch attributes admit
(EXT-PREFERRED-CLUSTER): the counts are the products of the shapes; each grid extent is a whole
number of regular and of preferred cluster extents, a preferred extent is a whole number of
regular extents in `x` and `y` and equal to it in `z`; each cluster has the regular or the
preferred shape, lies in the grid with its origin on the lattice of the regular shape, and has an
identifier below its count; the clusters together have the grid's CTAs, no two CTAs have one
`%ctaid` and no two clusters one `%clusterid`. -/
def Launch.clusterGridValid (L : Launch) : Prop :=
  L.ntid.prod = L.block ∧ L.nctaid.prod = L.grid ∧ L.clusterNctaid.prod = L.clusterSize.val ∧
  L.nctaid.x % L.clusterNctaid.x = 0 ∧ L.nctaid.y % L.clusterNctaid.y = 0 ∧
  L.nctaid.z % L.clusterNctaid.z = 0 ∧
  L.nctaid.x % L.preferredNctaid.x = 0 ∧ L.nctaid.y % L.preferredNctaid.y = 0 ∧
  L.preferredNctaid.x % L.clusterNctaid.x = 0 ∧ L.preferredNctaid.y % L.clusterNctaid.y = 0 ∧
  L.preferredNctaid.z = L.clusterNctaid.z ∧
  (∀ k < L.nclusters,
    let p := L.clusterPlaces k
    (p.shape = L.clusterNctaid ∨ p.shape = L.preferredNctaid) ∧
    p.origin.x % L.clusterNctaid.x = 0 ∧ p.origin.y % L.clusterNctaid.y = 0 ∧
    p.origin.z % L.clusterNctaid.z = 0 ∧
    p.origin.x + p.shape.x ≤ L.nctaid.x ∧ p.origin.y + p.shape.y ≤ L.nctaid.y ∧
    p.origin.z + p.shape.z ≤ L.nctaid.z ∧
    p.id.x < p.count.x ∧ p.id.y < p.count.y ∧ p.id.z < p.count.z) ∧
  L.clusterStart L.nclusters = L.grid ∧
  (∀ c < L.grid, ∀ d < L.grid, L.ctaidOf c = L.ctaidOf d → c = d) ∧
  (∀ k < L.nclusters, ∀ j < L.nclusters, (L.clusterPlaces k).id = (L.clusterPlaces j).id → k = j)

instance (L : Launch) : Decidable L.clusterGridValid := by
  unfold Launch.clusterGridValid
  infer_instance

/-- A one-dimensional launch with clusters of one shape whose grid is a whole number of clusters
(§2.2.2): the launch condition of the kernels proved with the one-dimensional model. -/
def Launch.oneDimLaunch (L : Launch) : Prop :=
  L.OneDim ∧ L.grid % L.clusterSize.val = 0

/-- In a launch whose clusters all have the regular size, the CTA at flat offset `c` after the
first `k` clusters is in cluster `k + c / clusterSize` with rank `c % clusterSize`. -/
theorem Launch.locate_regular {L : Launch}
    (hs : ∀ k, (L.clusterPlaces k).shape.prod = L.clusterSize.val) (n k c : Nat) :
    L.locate n k c = (k + c / L.clusterSize.val, c % L.clusterSize.val) := by
  have hpos := L.clusterSize.pos
  induction n generalizing k c with
  | zero => rfl
  | succ n ih =>
    simp only [Launch.locate, hs]
    split
    · rename_i hc
      simp [Nat.div_eq_of_lt hc, Nat.mod_eq_of_lt hc]
    · rename_i hc
      have hle : L.clusterSize.val ≤ c := Nat.le_of_not_lt hc
      rw [ih, Nat.div_eq_sub_div hpos hle, ← Nat.mod_eq_sub_mod hle]
      simp only [Prod.mk.injEq, and_true]
      omega

/-- The clusters of a one-dimensional launch: cluster `k` starts at CTA `k * s`, `(k * s, 0, 0)`,
has `s` CTAs in shape `(s, 1, 1)`, the identifier `(k, 0, 0)` and the count
`(grid / s, 1, 1)`, for cluster size `s`. -/
theorem Launch.oneDim_clusterPlaces {L : Launch} (h : L.OneDim) (k : Nat) :
    L.clusterPlaces k = ⟨⟨k * L.clusterSize.val, 0, 0⟩, ⟨L.clusterSize.val, 1, 1⟩, ⟨k, 0, 0⟩,
      ⟨L.grid / L.clusterSize.val, 1, 1⟩⟩ := by
  obtain ⟨-, hg, hc, -, -, hp⟩ := h
  simp [hp, ClusterPlace.uniform, hg, hc, Nat.mod_one]

/-- In a one-dimensional launch every cluster has `clusterSize` CTAs. -/
theorem Launch.oneDim_clusterSizeAt {L : Launch} (h : L.OneDim) (k : Nat) :
    L.clusterSizeAt k = L.clusterSize.val := by
  simp [Launch.clusterSizeAt, Launch.oneDim_clusterPlaces h, Dim3.prod]

/-- In a one-dimensional launch the cluster of CTA `cta` is `cta / clusterSize`. -/
theorem Launch.oneDim_clusterOfCta {L : Launch} (h : L.OneDim) (cta : Nat) :
    L.clusterOfCta cta = cta / L.clusterSize.val := by
  simp [Launch.clusterOfCta, Launch.locate_regular (fun k => Launch.oneDim_clusterSizeAt h k)]

/-- In a one-dimensional launch the rank of CTA `cta` is `cta % clusterSize`. -/
theorem Launch.oneDim_rankOfCta {L : Launch} (h : L.OneDim) (cta : Nat) :
    L.rankOfCta cta = cta % L.clusterSize.val := by
  simp [Launch.rankOfCta, Launch.locate_regular (fun k => Launch.oneDim_clusterSizeAt h k)]

/-- In a one-dimensional launch cluster `k` starts at CTA `k * clusterSize`. -/
theorem Launch.oneDim_clusterStart {L : Launch} (h : L.OneDim) (k : Nat) :
    L.clusterStart k = k * L.clusterSize.val := by
  induction k with
  | zero => simp [Launch.clusterStart]
  | succ k ih => simp [Launch.clusterStart, ih, Launch.oneDim_clusterSizeAt h, Nat.succ_mul]

/-- In a one-dimensional launch the cluster of every CTA has `clusterSize` CTAs. -/
theorem Launch.oneDim_clusterSizeOf {L : Launch} (h : L.OneDim) (cta : Nat) :
    L.clusterSizeOf cta = L.clusterSize.val := Launch.oneDim_clusterSizeAt h _

/-- In a one-dimensional launch `%cluster_nctaid` is `(clusterSize, 1, 1)`. -/
theorem Launch.oneDim_clusterNctaidOf {L : Launch} (h : L.OneDim) (cta : Nat) :
    L.clusterNctaidOf cta = ⟨L.clusterSize.val, 1, 1⟩ := by
  simp [Launch.clusterNctaidOf, Launch.placeOf, Launch.oneDim_clusterPlaces h]

/-- In a one-dimensional launch `%nclusterid` is `(grid / clusterSize, 1, 1)`. -/
theorem Launch.oneDim_nclusteridOf {L : Launch} (h : L.OneDim) (cta : Nat) :
    L.nclusteridOf cta = ⟨L.grid / L.clusterSize.val, 1, 1⟩ := by
  simp [Launch.nclusteridOf, Launch.placeOf, Launch.oneDim_clusterPlaces h]

/-- In a one-dimensional launch `%cluster_ctaid` is `(rank, 0, 0)`. -/
theorem Launch.oneDim_clusterCtaidOf {L : Launch} (h : L.OneDim) (cta : Nat) :
    L.clusterCtaidOf cta = ⟨L.rankOfCta cta, 0, 0⟩ := by
  have hs := L.clusterSize.pos
  simp only [Launch.clusterCtaidOf, Launch.placeOf, Launch.oneDim_clusterPlaces h,
    Launch.oneDim_rankOfCta h, Dim3.coord, Nat.mod_mod, Nat.mod_one, Nat.mul_one,
    Dim3.mk.injEq, true_and]
  exact Nat.div_eq_of_lt (Nat.mod_lt cta hs)

/-- In a one-dimensional launch `%clusterid` is `(cluster, 0, 0)`. -/
theorem Launch.oneDim_clusteridOf {L : Launch} (h : L.OneDim) (cta : Nat) :
    L.clusteridOf cta = ⟨L.clusterOfCta cta, 0, 0⟩ := by
  simp [Launch.clusteridOf, Launch.placeOf, Launch.oneDim_clusterPlaces h]

/-- In a one-dimensional launch `%ctaid` of CTA `cta` is `(cta, 0, 0)`. -/
theorem Launch.oneDim_ctaidOf {L : Launch} (h : L.OneDim) (cta : Nat) :
    L.ctaidOf cta = ⟨cta, 0, 0⟩ := by
  simp only [Launch.ctaidOf, Launch.placeOf, Launch.oneDim_clusterPlaces h,
    Launch.oneDim_clusterCtaidOf h, Launch.oneDim_clusterOfCta h, Launch.oneDim_rankOfCta h,
    Nat.add_zero, Dim3.mk.injEq, and_true]
  exact Nat.div_add_mod' cta _

/-- A one-dimensional launch of whole clusters is a valid cluster grid. -/
theorem Launch.oneDimLaunch_clusterGridValid {L : Launch} (h : L.oneDimLaunch) :
    L.clusterGridValid := by
  obtain ⟨h1, hd⟩ := h
  have hpos := L.clusterSize.pos
  have hP := Launch.oneDim_clusterPlaces h1
  have h1' := h1
  obtain ⟨hn, hg, hc, hN, hpr, -⟩ := h1'
  have hmul : L.grid / L.clusterSize.val * L.clusterSize.val = L.grid :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hd)
  refine ⟨by simp [hn, Dim3.prod], by simp [hg, Dim3.prod], by simp [hc, Dim3.prod],
    by simp [hg, hc, hd], by simp [hg, hc], by simp [hg, hc], by simp [hg, hpr, hc, hd],
    by simp [hg, hpr, hc], by simp [hpr], by simp [hpr], by simp [hpr], ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hN] at hk
    have hle : k * L.clusterSize.val + L.clusterSize.val ≤ L.grid := by
      have := Nat.mul_le_mul_right L.clusterSize.val (Nat.succ_le_of_lt hk)
      rw [hmul, Nat.succ_mul] at this
      exact this
    simp only [hP, hc, hg, hpr, true_or, Nat.mul_mod_left, Nat.mod_one, Nat.zero_add,
      Nat.le_refl, Nat.zero_lt_one, and_true, true_and]
    exact ⟨hle, hk⟩
  · rw [Launch.oneDim_clusterStart h1, hN, hmul]
  · intro c _ d _ he
    simpa [Launch.oneDim_ctaidOf h1] using he
  · intro k _ j _ he
    simpa [hP] using he

/-- In a valid cluster grid the number of CTAs is the sum of the cluster sizes. -/
theorem Launch.clusterGridValid_start {L : Launch} (h : L.clusterGridValid) :
    L.clusterStart L.nclusters = L.grid := h.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The CTA with rank `rank` in the cluster of CTA `cta`, if there is one. The rank is relative
to that cluster and is not a grid-wide CTA number. -/
def Launch.peerCta (L : Launch) (cta rank : Nat) : Option Nat :=
  let peer := L.clusterStart (L.clusterOfCta cta) + rank
  if cta < L.grid ∧ rank < L.clusterSizeOf cta ∧ peer < L.grid then
    some peer
  else none

/-- Logical meaning of mapa on a shared location within the issuer's cluster. -/
def Launch.mapShared (L : Launch) (issuer rank : Nat) (a : Loc) : Option Loc :=
  if a.space = .shared ∧ a.cta < L.grid ∧
      L.clusterOfCta a.cta = L.clusterOfCta issuer then
    (L.peerCta issuer rank).map fun peer => { a with cta := peer }
  else none

/-- Threads `g` and `h` belong to CTAs of one cluster. -/
def SameCluster (L : Launch) (g h : Nat) : Prop :=
  g < L.threads ∧ h < L.threads ∧
  L.clusterOfCta (g / L.block) = L.clusterOfCta (h / L.block)

end PTX
