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
-- A matrix product sums in an `AddCommMonoid`, and `BitVec n` is one only
-- through Mathlib's ring instances: without them a `BV.MatMul` does not
-- elaborate.
import Mathlib.Data.BitVec
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

/-!
  Matrices, the operations on them that Mathlib lacks, and lemmas.

  A matrix of `m` rows and `n` columns is Mathlib's
  `Matrix (Fin m) (Fin n) t`; its `+`, `-`, `0`, `*` (the matrix product)
  and `Matrix.transpose` are Mathlib's. The `Box` combinators over matrices
  live in `Relational.Circ`.
-/

/-- The matrix whose entry `(i, j)` is `f i j`: `Matrix.mk fun i j => …`.
    ReactLib's, not Mathlib's.

    `Matrix` is a definition that `simp` and instance search do not see
    through, so a bare `fun i j => …` is a function to them, not a
    `Matrix`, even where a `Matrix` is expected: no `Matrix` lemma matches
    it, and `s - fun _ _ => 1` does not elaborate. `Matrix.mk` gives the
    same function the type `Matrix`, so a matrix built from its entries is
    built with it. Mathlib's `Matrix.of` does that too, but it is an
    `Equiv`: once `simp` has rewritten an `if`'s condition, the `Decidable`
    instance still names `Matrix.of …`, and `simp` stops there.

    `[implicit_reducible]`: unfolded where Lean checks implicit and instance
    arguments for definitional equality, and by `decide` and `rfl`, but not
    when `simp` indexes a term or instance search runs, so `simp` meets
    `Matrix.mk` itself and takes it apart with `Matrix.mk_apply`. `omega`
    does not see through it; `simp` first.

    That is for a lambda that is a term. A definition whose body is
    `fun i j => …`, like `matVecAffine` below, is left as it is: its
    equation lemma takes `i j` as arguments, so `simp` unfolds it only at an
    entry and never meets the lambda. Wrapped in `Matrix.mk`, the lemma would
    rewrite the matrix itself wherever it occurs, and the certificates'
    `simp` then stalls on an `if` between two such matrices. -/
@[implicit_reducible] def Matrix.mk {t : Type} {m n : Nat} (f : Fin m → Fin n → t) :
    Matrix (Fin m) (Fin n) t := f

/-- A `Matrix.mk` read at an entry is that entry. A pre-lemma (`↓`): `simp`
    rewrites with it before entering `f`. Entering first, it simplifies `f`
    under its binders at every entry it reads, which for a 32-element
    `match` takes more than a proof's heartbeat budget. -/
@[simp↓] theorem Matrix.mk_apply {t : Type} {m n : Nat} (f : Fin m → Fin n → t)
    (i : Fin m) (j : Fin n) : Matrix.mk f i j = f i j := id rfl

/-- Affine map (math convention): `affineLinear A x b = A * x + b`, i.e. the
    matrix `A` acts on the column vector(s) `x` from the left. This matches the
    theory's `LIA.Linear`/`LRA.Linear` semantics `Y = A·X + B`. -/
def affineLinear [Mul t] [AddCommMonoid t]
    (A : Matrix (Fin m) (Fin k) t) (x : Matrix (Fin k) (Fin n) t) (b : Matrix (Fin m) (Fin n) t) :
    Matrix (Fin m) (Fin n) t :=
  A * x + b

/-- Element-wise ReLU: `relu x i j = max 0 (x i j)` -/
def ReLu [Max t] [OfNat t 0] (x : Matrix (Fin m) (Fin n) t) : Matrix (Fin m) (Fin n) t :=
  fun i j => Max.max 0 (x i j)

/-! The three reductions below enumerate their elements with `List.ofFn`
    rather than `List.finRange`, and the difference is not cosmetic: the
    certificates' `simp_mat` carries `List.ofFn_succ` and `List.ofFn_zero`
    and no lemma that computes `List.finRange`, so a `finRange` fold stays
    stuck in the goal at every concrete shape and every closer fails on it
    (fixed in `be70a43`). Row-major order, seeds and tie-breaking are
    exactly as they were. -/

/-- Reduce a matrix to its minimum, packed as a 1×1 matrix.
    Folds row-major from element `(0,0)`; an empty matrix has no minimum and
    yields `default`. Min/Max are unary reductions in the theory, matching
    `Argmax`'s shape. -/
def matMin {t : Type} [Min t] [Inhabited t] {m n : Nat} (x : Matrix (Fin m) (Fin n) t) :
    Matrix (Fin 1) (Fin 1) t :=
  fun _ _ =>
    match (List.ofFn (fun i : Fin m => List.ofFn (fun j : Fin n => x i j))).flatten with
    | [] => default
    | v0 :: vs => vs.foldl Min.min v0

/-- Reduce a matrix to its maximum, packed as a 1×1 matrix. See `matMin`. -/
def matMax {t : Type} [Max t] [Inhabited t] {m n : Nat} (x : Matrix (Fin m) (Fin n) t) :
    Matrix (Fin 1) (Fin 1) t :=
  fun _ _ =>
    match (List.ofFn (fun i : Fin m => List.ofFn (fun j : Fin n => x i j))).flatten with
    | [] => default
    | v0 :: vs => vs.foldl Max.max v0

/-- 1-dimensional argmax: returns the column index of the maximum element
    of a one-row matrix, packed as a 1×1 matrix.
    In case there are multiple greatest elements, the *first* maximal index
    is returned. An empty row has no argmax and yields 0. -/
def argmax_1d {t : Type} [LT t] [DecidableRel ((· < ·) : t → t → Prop)]
    {n : Nat} (x : Matrix (Fin 1) (Fin n) t) : Matrix (Fin 1) (Fin 1) Nat :=
  fun _ _ =>
    match List.ofFn (fun j : Fin n => (j.val, x 0 j)) with
    | [] => 0
    | p0 :: ps =>
      (ps.foldl
        (fun (best : Nat × t) p => if best.2 < p.2 then p else best) p0).1

/-- 2-dimensional argmax: the *row-major flat* index `i * n + j` of the
    maximum element of an `m × n` matrix, packed as a 1×1 matrix — a single
    index, not an `[i, j]` pair.
    Ties go to the lowest flat index, so this agrees with `argmax_1d`
    whenever `m = 1`. An empty matrix has no argmax and yields 0. -/
def argmax {t : Type} [LT t] [DecidableRel ((· < ·) : t → t → Prop)]
    {m n : Nat} (x : Matrix (Fin m) (Fin n) t) : Matrix (Fin 1) (Fin 1) Nat :=
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
    well-typed under the transparency `simp` checks at, and `Matrix_ite_apply`
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
    (A : Matrix (Fin m) (Fin k) t) (x : Matrix (Fin k) (Fin n) t) (b : Matrix (Fin m) (Fin n) t)
    (i : Fin m) (j : Fin n) :
    affineLinear A x b i j = Finset.sum Finset.univ (fun l => A i l * x l j) + b i j := by
  simp [affineLinear, Matrix.mul_apply]


@[simp↓] theorem relu_apply [Max t] [OfNat t 0]
    (x : Matrix (Fin m) (Fin n) t) (i : Fin m) (j : Fin n) :
    ReLu x i j = Max.max 0 (x i j) := id rfl


/-- The matrix product read at an entry. -/
@[simp↓] theorem mul_Matrix_apply [Mul t] [AddCommMonoid t]
    (a : Matrix (Fin m) (Fin k) t) (b : Matrix (Fin k) (Fin n) t) (i : Fin m) (j : Fin n) :
    (a * b) i j = Finset.sum Finset.univ (fun l => a i l * b l j) := id rfl

@[simp↓] theorem add_Matrix_apply [Add t]
    (a b : Matrix (Fin m) (Fin n) t) (i : Fin m) (j : Fin n) :
    (a + b) i j = a i j + b i j := id rfl

@[simp↓] theorem sub_Matrix_apply [Sub t]
    (a b : Matrix (Fin m) (Fin n) t) (i : Fin m) (j : Fin n) :
    (a - b) i j = a i j - b i j := id rfl

@[simp↓] theorem neg_Matrix_apply [Neg t]
    (a : Matrix (Fin m) (Fin n) t) (i : Fin m) (j : Fin n) :
    (-a) i j = -(a i j) := id rfl

@[simp↓] theorem zero_Matrix_apply [Zero t] (i : Fin m) (j : Fin n) :
    (0 : Matrix (Fin m) (Fin n) t) i j = 0 := id rfl

@[simp↓] theorem transpose_Matrix_apply
    (a : Matrix (Fin m) (Fin n) t) (i : Fin n) (j : Fin m) :
    Matrix.transpose a i j = a j i := id rfl

-- This complicates the proofs..
/- coercion between single-element matrix and the element -/
-- instance {t: Type} : Coe t (Matrix (Fin 1) (Fin 1) t) where
--   coe x := fun _ _ => x

-- instance : Coe (Matrix (Fin 1) (Fin 1) Bool) Bool where
--   coe m := m 0 0

-- instance : Coe (Matrix (Fin 1) (Fin 1) Real) Real where
--   coe m := m 0 0

-- instance : Coe (Matrix (Fin 1) (Fin 1) Int) Int where
--   coe m := m 0 0

/- break ValTuple...
instance {t: Type} : Coe (Matrix (Fin 1) (Fin 1) t) t where
  coe m := m 0 0
-/

instance : Coe Bool (Matrix (Fin 1) (Fin 1) Bool) where
  coe x := Matrix.mk fun _ _ => x

instance : Coe (Matrix (Fin 1) (Fin 1) Bool) Bool where
  coe m := m 0 0



/- this might be necessary to automate the proofs -/
@[simp] theorem coe_bool_mat (b : Bool) :
  Coe.coe b = (Matrix.mk fun _ _ => b : Matrix (Fin 1) (Fin 1) Bool) := by rfl

@[simp] theorem coe_mat_bool (m : Matrix (Fin 1) (Fin 1) Bool) :
  Coe.coe m = m 0 0 := by rfl

theorem Matrix_1_1_eq (f : Matrix (Fin 1) (Fin 1) t) : f = Matrix.mk fun _ _ => f 0 0 := by
  ext i j;
  have hi: i = ⟨ 0, by simp ⟩ := by exact Fin.fin_one_eq_zero i
  have hj: j = ⟨ 0, by simp ⟩ := by exact Fin.fin_one_eq_zero j
  rw [hi, hj]
  rfl

@[simp] theorem Matrix_1_1_eq_iff {t : Type} (a b : Matrix (Fin 1) (Fin 1) t) :
    (a = b) ↔ (a 0 0 = b 0 0) := by
  constructor
  · intro h; rw [h]
  · intro h
    ext i j
    have hi : i = ⟨0, by simp⟩ := Fin.fin_one_eq_zero i
    have hj : j = ⟨0, by simp⟩ := Fin.fin_one_eq_zero j
    rw [hi, hj]; exact h

/- theorem ite_Matrix_1_1 (p : Prop) [Decidable p] (a b : Matrix (Fin 1) (Fin 1) t) : -/
/-       (if p then a else b) = fun _ _ => if p then a 0 0 else b 0 0 := by -/
/-     ext i j; fin_cases i; fin_cases j; split <;> rfl -/

  instance [LT t] : LT (Matrix (Fin 1) (Fin 1) t) where
    lt a b := a 0 0 < b 0 0

  instance [LE t] : LE (Matrix (Fin 1) (Fin 1) t) where
    le a b := a 0 0 ≤ b 0 0

@[simp] theorem Matrix_1_1_lt_iff {t : Type} [LT t] (a b : Matrix (Fin 1) (Fin 1) t) :
    a < b ↔ a 0 0 < b 0 0 := Iff.rfl

@[simp] theorem Matrix_1_1_le_iff {t : Type} [LE t] (a b : Matrix (Fin 1) (Fin 1) t) :
    a ≤ b ↔ a 0 0 ≤ b 0 0 := Iff.rfl

  instance [LT t] [DecidableRel (· < · : t → t → Prop)] :
      DecidableRel (· < · : Matrix (Fin 1) (Fin 1) t → Matrix (Fin 1) (Fin 1) t → Prop) :=
    fun a b => inferInstanceAs (Decidable (a 0 0 < b 0 0))

  instance [LE t] [DecidableRel (· ≤ · : t → t → Prop)] :
      DecidableRel (· ≤ · : Matrix (Fin 1) (Fin 1) t → Matrix (Fin 1) (Fin 1) t → Prop) :=
    fun a b => inferInstanceAs (Decidable (a 0 0 ≤ b 0 0))

/-! ### Scalar collapse lemmas for zeroth_hammer -/

/-- An `if` between matrices, read at an entry. `ite_fun_apply` does this
    for functions, and to `simp` a `Matrix` is not one.

    A pre-lemma (`↓`), so `simp` splits the `if` before it simplifies the
    condition. The other way round, the condition is rewritten while a
    `decide` inside it keeps the `Decidable` instance it was built with,
    which states the old terms, and the lemma no longer matches: a counter
    whose condition reads `(ctrl + 1) 0 0` kept its `if` between matrices. -/
@[simp↓] theorem Matrix_ite_apply {t : Type} {m n : Nat} (p : Prop) [inst : Decidable p]
    (a b : Matrix (Fin m) (Fin n) t) (i : Fin m) (j : Fin n) :
    (if p then a else b) i j = if p then a i j else b i j := by
  cases inst <;> rfl

/-- Collapse `(fun _ _ => v) i j` to `v`. Generated code builds a constant
    matrix as `Matrix.mk fun _ _ => v`, which `Matrix.mk_apply` reads. -/
theorem fun_const_1_1_apply {t : Type} (v : t) (i : Fin 1) (j : Fin 1) :
    (fun (_ : Fin 1) (_ : Fin 1) => v) i j = v := rfl

/-- Reduce `a ≠ b` for 1×1 matrices to pointwise inequality. -/
theorem Matrix_1_1_ne_iff {t : Type} (a b : Matrix (Fin 1) (Fin 1) t) :
    (a ≠ b) ↔ (a 0 0 ≠ b 0 0) := by
  simp [Matrix_1_1_eq_iff]


/-! ### Reflected affine map over list literals

A constant `Linear` op is emitted as a `matVecAffine` over plain `List` literals
(cheap to elaborate; reduces to a linear expression under `simp` without a dense
matrix `match` or a symbolic `Finset.sum`). `matVecAffine_eq` proves — once,
generically — that it agrees with `affineLinear` of the matrix the lists denote,
so the codegen's contraction is machine-checked rather than trusted. -/

@[simp] def dotL [Mul t] [Add t] [Zero t] : List (t × t) → t
  | [] => 0
  | p :: ps => p.1 * p.2 + dotL ps

/-- Contract a dense `List (List t)` matrix and `List t` (column) bias against an
    `n × batch` matrix: `Y i j = Σ_l A[i][l] · x[l][j] + b[i]` (bias broadcast over
    the `batch` columns), matching the theory's `Y = A·X + B`. -/
def matVecAffine [Mul t] [Add t] [Zero t] (m : Nat) (A : List (List t)) (b : List t)
    {n batch : Nat} (x : Matrix (Fin n) (Fin batch) t) : Matrix (Fin m) (Fin batch) t :=
  fun i j => dotL ((A.getD i.val []).zip (List.ofFn (fun l : Fin n => x l j))) + b.getD i.val 0

/-- Dense matrix denoted by a `List (List t)` (out-of-range entries are `0`). -/
def matrixOf [Zero t] (m n : Nat) (A : List (List t)) : Matrix (Fin m) (Fin n) t :=
  fun i j => (A.getD i.val []).getD j.val 0

/-- Column bias `List t` broadcast to an `m × batch` matrix (every column is `b`). -/
def colOf [Zero t] (m batch : Nat) (b : List t) : Matrix (Fin m) (Fin batch) t :=
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
    (A : List (List t)) (b : List t) (x : Matrix (Fin n) (Fin batch) t)
    (hwf : ∀ i : Fin m, (A.getD i.val []).length = n) :
    matVecAffine m A b x = affineLinear (matrixOf m n A) x (colOf m batch b) := by
  funext i j
  simp only [matVecAffine, affineLinear_apply, matrixOf, colOf]
  rw [dotL_zip_ofFn (A.getD i.val []) (fun l => x l j) (hwf i)]
