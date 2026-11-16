import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Basic
import Mathlib.Basic.Real.Basic
-- `⌊x⌋` (the `to_int` of a Real-valued ranking) needs both the
-- notation and the `FloorRing ℝ` instance.
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Zip
import Mathlib.Tactic.FinCases
-- `MatMul` sums in an `AddCommMonoid`, and `BitVec n` is one only through
-- Mathlib's ring instances: without them a `BV.MatMul` does not elaborate.
import Mathlib.Data.BitVec
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

/-!
  Mat — matrix type, operations, and lemmas.
  Core `Box` combinators that consume/produce `Mat` live in `Relational.Box`.
-/

/-- A matrix of `m` rows and `n` columns: Mathlib's `Matrix`, indexed by
    `Fin`. Its `+`, `-`, `0` and `*` (the matrix product) are Mathlib's. -/
abbrev Mat (t: Type) (m n: Nat)  := Matrix (Fin m) (Fin n) t

/-- The matrix whose entry `(i, j)` is `f i j`: `Mat.mk fun i j => …`.

    `Matrix` is a definition that `simp` and instance search do not see
    through, so a bare `fun i j => …` is a function to them, not a `Mat`,
    even where a `Mat` is expected: no `Matrix` lemma matches it, and
    `s - fun _ _ => 1` does not elaborate. `Mat.mk` gives the same function
    the type `Mat`, so a matrix built from its entries is built with it.
    Mathlib's `Matrix.of` does that too, but it is an `Equiv`: once `simp`
    has rewritten an `if`'s condition, the `Decidable` instance still names
    `Matrix.of …`, and `simp` stops there.

    `[implicit_reducible]`: unfolded where Lean checks implicit and instance
    arguments for definitional equality, and by `decide` and `rfl`, but not
    when `simp` indexes a term or instance search runs, so `simp` meets
    `Mat.mk` itself and takes it apart with `Mat.mk_apply`. `omega` does not
    see through it; `simp` first.

    That is for a lambda that is a term. A definition whose body is
    `fun i j => …`, like `matVecAffine` below, is left as it is: its
    equation lemma takes `i j` as arguments, so `simp` unfolds it only at an
    entry and never meets the lambda. Wrapped in `Mat.mk`, the lemma would
    rewrite the matrix itself wherever it occurs, and the certificates'
    `simp` then stalls on an `if` between two such matrices. -/
@[implicit_reducible] def Mat.mk {t : Type} {m n : Nat} (f : Fin m → Fin n → t) : Mat t m n := f

/-- A `Mat.mk` read at an entry is that entry. A pre-lemma (`↓`): `simp`
    rewrites with it before entering `f`. Entering first, it simplifies `f`
    under its binders at every entry it reads, which for a 32-element
    `match` takes more than a proof's heartbeat budget. -/
@[simp↓] theorem Mat.mk_apply {t : Type} {m n : Nat} (f : Fin m → Fin n → t)
    (i : Fin m) (j : Fin n) : Mat.mk f i j = f i j := id rfl

/-  The matrix operations under the names generated code uses, each
    Mathlib's.

    Reducible, like `Mat` itself: a generated proof that compares matrix
    entries does so under `decide`, and once `simp` has unfolded `a + b`
    in the proposition the `Decidable` instance still names `MatAdd`.
    From Lean v4.34 `simp` will not rewrite a term whose instance agrees
    with it only through a semireducible unfolding. -/

@[reducible] def MatAdd [Add t] (a b : Mat t m n) : Mat t m n := a + b

@[reducible] def MatMul [Mul t] [AddCommMonoid t] (a : Mat t m k) (b : Mat t k n) : Mat t m n :=
  a * b

@[reducible] def MatZero [Zero t]: Mat t m n := 0

@[reducible] def MatTranspose (A : Mat t m n) : Mat t n m := Matrix.transpose A


/-- Affine map (math convention): `affineLinear A x b = A * x + b`, i.e. the
    matrix `A` acts on the column vector(s) `x` from the left. This matches the
    theory's `LIA.Linear`/`LRA.Linear` semantics `Y = A·X + B`. -/
def affineLinear [Mul t] [AddCommMonoid t]
    (A : Mat t m k) (x : Mat t k n) (b : Mat t m n) : Mat t m n :=
  A * x + b

/-- Element-wise ReLU: `relu x i j = max 0 (x i j)` -/
def ReLu [Max t] [OfNat t 0] (x : Mat t m n) : Mat t m n :=
  fun i j => Max.max 0 (x i j)

/-! The three reductions below enumerate their elements with `List.ofFn`
    rather than `List.finRange`, and the difference is not cosmetic: the
    certificates' `simp_mat` carries `List.ofFn_succ` and `List.ofFn_zero`
    and no lemma that computes `List.finRange`, so a `finRange` fold stays
    stuck in the goal at every concrete shape and every closer fails on it
    (fixed in `be70a43`). Row-major order, seeds and tie-breaking are
    exactly as they were. -/

/-- Reduce a matrix to its minimum, packed as `Mat t 1 1`.
    Folds row-major from element `(0,0)`; an empty matrix has no minimum and
    yields `default`. Min/Max are unary reductions in the theory, matching
    `Argmax`'s shape. -/
def matMin {t : Type} [Min t] [Inhabited t] {m n : Nat} (x : Mat t m n) : Mat t 1 1 :=
  fun _ _ =>
    match (List.ofFn (fun i : Fin m => List.ofFn (fun j : Fin n => x i j))).flatten with
    | [] => default
    | v0 :: vs => vs.foldl Min.min v0

/-- Reduce a matrix to its maximum, packed as `Mat t 1 1`. See `matMin`. -/
def matMax {t : Type} [Max t] [Inhabited t] {m n : Nat} (x : Mat t m n) : Mat t 1 1 :=
  fun _ _ =>
    match (List.ofFn (fun i : Fin m => List.ofFn (fun j : Fin n => x i j))).flatten with
    | [] => default
    | v0 :: vs => vs.foldl Max.max v0

/-- 1-dimensional argmax: returns the column index of the maximum element
    of a `Mat t 1 n`, packed as `Mat Nat 1 1`.
    In case there are multiple greatest elements, the *first* maximal index
    is returned. An empty row has no argmax and yields 0. -/
def argmax_1d {t : Type} [LT t] [DecidableRel ((· < ·) : t → t → Prop)]
    {n : Nat} (x : Mat t 1 n) : Mat Nat 1 1 :=
  fun _ _ =>
    match List.ofFn (fun j : Fin n => (j.val, x 0 j)) with
    | [] => 0
    | p0 :: ps =>
      (ps.foldl
        (fun (best : Nat × t) p => if best.2 < p.2 then p else best) p0).1

/-- 2-dimensional argmax: the *row-major flat* index `i * n + j` of the
    maximum element of a `Mat t m n`, packed as `Mat Nat 1 1` — a single
    index, not an `[i, j]` pair.
    Ties go to the lowest flat index, so this agrees with `argmax_1d`
    whenever `m = 1`. An empty matrix has no argmax and yields 0. -/
def argmax {t : Type} [LT t] [DecidableRel ((· < ·) : t → t → Prop)]
    {m n : Nat} (x : Mat t m n) : Mat Nat 1 1 :=
  fun _ _ =>
    match (List.ofFn (fun i : Fin m =>
             List.ofFn (fun j : Fin n => (i.val * n + j.val, x i j)))).flatten with
    | [] => 0
    | p0 :: ps =>
      (ps.foldl
        (fun (best : Nat × t) p => if best.2 < p.2 then p else best) p0).1


/-! Reading an entry of a matrix operation.

    A `decide` inside an `if`'s condition is where these go wrong: if its
    proposition is rewritten and its `Decidable` instance is not, the
    instance states the old terms, Lean no longer takes the `if` to be
    well-typed under the transparency `simp` checks at, and `Mat_ite_apply`
    does not match it. Two things keep the instance in step:

    - They are pre-lemmas (`↓`): `simp` moves `i j` inward, through every
      operation down to the entries, and splits each `if` between matrices
      before it simplifies anything inside it.
    - They are proved by `id rfl`, not `rfl`. A lemma proved by `rfl` is one
      `dsimp` uses, and `dsimp`, and `simp` rewriting by one, change a
      term in place, instances untouched. Proved otherwise, `simp` rewrites
      through congruence, which builds the instance anew. Mathlib's own
      `Matrix.add_apply` and the like are `rfl` lemmas; a `dsimp` over
      generated matrices has to leave them out. -/
@[simp↓] theorem affineLinear_apply [Mul t] [AddCommMonoid t]
    (A : Mat t m k) (x : Mat t k n) (b : Mat t m n) (i : Fin m) (j : Fin n) :
    affineLinear A x b i j = Finset.sum Finset.univ (fun l => A i l * x l j) + b i j := by
  simp [affineLinear, Matrix.mul_apply]


@[simp↓] theorem relu_apply [Max t] [OfNat t 0]
    (x : Mat t m n) (i : Fin m) (j : Fin n) :
    ReLu x i j = Max.max 0 (x i j) := id rfl



@[simp] theorem MatAdd_apply {m n : Nat} (a b : Mat Int m n) (i : Fin m) (j : Fin n) :
    MatAdd a b i j = a i j + b i j := id rfl

@[simp] theorem MatMul_apply {m k n : Nat} (a : Mat Int m k) (b : Mat Int k n) (i : Fin m) (j : Fin n) :
    MatMul a b i j = Finset.sum Finset.univ (fun l => a i l * b l j) := id rfl

@[simp↓] theorem MatZero_apply {t : Type} [Zero t] {m n : Nat} (i : Fin m) (j : Fin n) :
    (MatZero : Mat t m n) i j = 0 := id rfl

@[simp] theorem MatAdd_eq_add {m n : Nat} (a b : Mat Int m n) :
    MatAdd a b = a + b := rfl

@[simp] theorem MatMul_eq_mul {m n : Nat} [Mul t] [AddCommMonoid t]
  (a : Mat t m k) (b : Mat t k n) :
    MatMul a b = a * b := rfl

/-- Reduce `(a * b) i j` directly (needed because `MatMul_eq_mul` rewrites
    `MatMul` away before `MatMul_apply` can fire). -/
@[simp↓] theorem mul_Mat_apply [Mul t] [AddCommMonoid t]
    (a : Mat t m k) (b : Mat t k n) (i : Fin m) (j : Fin n) :
    (a * b) i j = Finset.sum Finset.univ (fun l => a i l * b l j) := id rfl

@[simp↓] theorem add_Mat_apply [Add t]
    (a b : Mat t m n) (i : Fin m) (j : Fin n) :
    (a + b) i j = a i j + b i j := id rfl

@[simp↓] theorem sub_Mat_apply [Sub t]
    (a b : Mat t m n) (i : Fin m) (j : Fin n) :
    (a - b) i j = a i j - b i j := id rfl

@[simp↓] theorem neg_Mat_apply [Neg t]
    (a : Mat t m n) (i : Fin m) (j : Fin n) :
    (-a) i j = -(a i j) := id rfl

@[simp↓] theorem MatTranspose_apply
    (a : Mat t m n) (i : Fin n) (j : Fin m) :
    MatTranspose a i j = a j i := id rfl

-- This complicates the proofs..
/- coercion between single-element matrix and the element -/
-- instance {t: Type} : Coe t (Mat t 1 1) where
--   coe x := fun _ _ => x

-- instance : Coe (Mat Bool 1 1) Bool where
--   coe m := m 0 0

-- instance : Coe (Mat Real 1 1) Real where
--   coe m := m 0 0

-- instance : Coe (Mat Int 1 1) Int where
--   coe m := m 0 0

/- break ValTuple...
instance {t: Type} : Coe (Mat t 1 1) t where
  coe m := m 0 0
-/

instance : Coe Bool (Mat Bool 1 1) where
  coe x := Mat.mk fun _ _ => x

instance : Coe (Mat Bool 1 1) Bool where
  coe m := m 0 0



/- this might be necessary to automate the proofs -/
@[simp] theorem coe_bool_mat (b : Bool) :
  Coe.coe b = (Mat.mk fun _ _ => b : Mat Bool 1 1) := by rfl

@[simp] theorem coe_mat_bool (m : Mat Bool 1 1) :
  Coe.coe m = m 0 0 := by rfl

theorem Mat_1_1_eq (f : Mat t 1 1) : f = Mat.mk fun _ _ => f 0 0 := by
  ext i j;
  have hi: i = ⟨ 0, by simp ⟩ := by exact Fin.fin_one_eq_zero i
  have hj: j = ⟨ 0, by simp ⟩ := by exact Fin.fin_one_eq_zero j
  rw [hi, hj]
  rfl

@[simp] theorem Mat_1_1_eq_iff {t : Type} (a b : Mat t 1 1) :
    (a = b) ↔ (a 0 0 = b 0 0) := by
  constructor
  · intro h; rw [h]
  · intro h
    ext i j
    have hi : i = ⟨0, by simp⟩ := Fin.fin_one_eq_zero i
    have hj : j = ⟨0, by simp⟩ := Fin.fin_one_eq_zero j
    rw [hi, hj]; exact h

/- theorem ite_Mat_1_1 (p : Prop) [Decidable p] (a b : Mat t 1 1) : -/
/-       (if p then a else b) = fun _ _ => if p then a 0 0 else b 0 0 := by -/
/-     ext i j; fin_cases i; fin_cases j; split <;> rfl -/

  instance [LT t] : LT (Mat t 1 1) where
    lt a b := a 0 0 < b 0 0

  instance [LE t] : LE (Mat t 1 1) where
    le a b := a 0 0 ≤ b 0 0

@[simp] theorem Mat_1_1_lt_iff {t : Type} [LT t] (a b : Mat t 1 1) :
    a < b ↔ a 0 0 < b 0 0 := Iff.rfl

@[simp] theorem Mat_1_1_le_iff {t : Type} [LE t] (a b : Mat t 1 1) :
    a ≤ b ↔ a 0 0 ≤ b 0 0 := Iff.rfl

  instance [LT t] [DecidableRel (· < · : t → t → Prop)] :
      DecidableRel (· < · : Mat t 1 1 → Mat t 1 1 → Prop) :=
    fun a b => inferInstanceAs (Decidable (a 0 0 < b 0 0))

  instance [LE t] [DecidableRel (· ≤ · : t → t → Prop)] :
      DecidableRel (· ≤ · : Mat t 1 1 → Mat t 1 1 → Prop) :=
    fun a b => inferInstanceAs (Decidable (a 0 0 ≤ b 0 0))

/-! ### Scalar collapse lemmas for zeroth_hammer -/

/-- An `if` between matrices, read at an entry. `ite_fun_apply` does this
    for functions, and to `simp` a `Mat` is not one.

    A pre-lemma (`↓`), so `simp` splits the `if` before it simplifies the
    condition. The other way round, the condition is rewritten while a
    `decide` inside it keeps the `Decidable` instance it was built with,
    which states the old terms, and the lemma no longer matches: a counter
    whose condition reads `(ctrl + 1) 0 0` kept its `if` between matrices. -/
@[simp↓] theorem Mat_ite_apply {t : Type} {m n : Nat} (p : Prop) [inst : Decidable p]
    (a b : Mat t m n) (i : Fin m) (j : Fin n) :
    (if p then a else b) i j = if p then a i j else b i j := by
  cases inst <;> rfl

/-- Collapse `(fun _ _ => v) i j` to `v`. Fires after `ite_fun_apply` peels
    ite through Mat 1 1 constructors. -/
theorem fun_const_1_1_apply {t : Type} (v : t) (i : Fin 1) (j : Fin 1) :
    (fun (_ : Fin 1) (_ : Fin 1) => v) i j = v := rfl

/-- Reduce `a ≠ b` for `Mat t 1 1` to pointwise inequality. -/
theorem Mat_1_1_ne_iff {t : Type} (a b : Mat t 1 1) :
    (a ≠ b) ↔ (a 0 0 ≠ b 0 0) := by
  simp [Mat_1_1_eq_iff]


/-! ### Reflected affine map over list literals

A constant `Linear` op is emitted as a `matVecAffine` over plain `List` literals
(cheap to elaborate; reduces to a linear expression under `simp` without a dense
matrix `match` or a symbolic `Finset.sum`). `matVecAffine_eq` proves — once,
generically — that it agrees with `affineLinear` of the matrix the lists denote,
so the codegen's contraction is machine-checked rather than trusted. -/

@[simp] def dotL [Mul t] [Add t] [Zero t] : List (t × t) → t
  | [] => 0
  | p :: ps => p.1 * p.2 + dotL ps

/-- Contract a dense `List (List t)` matrix and `List t` (column) bias against a
    `Mat t n batch`: `Y i j = Σ_l A[i][l] · x[l][j] + b[i]` (bias broadcast over
    the `batch` columns), matching the theory's `Y = A·X + B`. -/
def matVecAffine [Mul t] [Add t] [Zero t] (m : Nat) (A : List (List t)) (b : List t)
    {n batch : Nat} (x : Mat t n batch) : Mat t m batch :=
  fun i j => dotL ((A.getD i.val []).zip (List.ofFn (fun l : Fin n => x l j))) + b.getD i.val 0

/-- Dense matrix denoted by a `List (List t)` (out-of-range entries are `0`). -/
def matrixOf [Zero t] (m n : Nat) (A : List (List t)) : Mat t m n :=
  fun i j => (A.getD i.val []).getD j.val 0

/-- Column bias `List t` broadcast to a `Mat t m batch` (every column is `b`). -/
def colOf [Zero t] (m batch : Nat) (b : List t) : Mat t m batch :=
  fun i _ => b.getD i.val 0

/-- Core bridge: the list fold equals the `Finset.sum` contraction. -/
theorem dotL_zip_ofFn [Mul t] [AddCommMonoid t] {n : Nat}
    (row : List t) (g : Fin n → t) (hlen : row.length = n) :
    dotL (row.zip (List.ofFn g)) = ∑ l : Fin n, row.getD l.val 0 * g l := by
  induction n generalizing row with
  | zero => simp [dotL]
  | succ k ih =>
    match row with
    | [] => simp at hlen
    | a :: as =>
      rw [List.ofFn_succ, List.zip_cons_cons, dotL, Fin.sum_univ_succ,
          ih as (fun i => g i.succ) (by simpa using hlen)]
      simp

/-- Generic correspondence: the reflected form equals `affineLinear` of the
    matrix/bias the literals denote, given each row has the expected length.
    Holds for any batch width. -/
theorem matVecAffine_eq [Mul t] [AddCommMonoid t] (m n batch : Nat)
    (A : List (List t)) (b : List t) (x : Mat t n batch)
    (hwf : ∀ i : Fin m, (A.getD i.val []).length = n) :
    matVecAffine m A b x = affineLinear (matrixOf m n A) x (colOf m batch b) := by
  funext i j
  simp only [matVecAffine, affineLinear_apply, matrixOf, colOf]
  rw [dotL_zip_ofFn (A.getD i.val []) (fun l => x l j) (hwf i)]
