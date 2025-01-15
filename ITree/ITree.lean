import Qpf
import Mathlib.Data.QPF.Multivariate.Constructions.Sigma

namespace ITree

/-!
# Interaction Trees

We define interaction trees, a coinductive data-structure used for giving
semantics of side-effecting, possibly non-terminating, programs

[1] https://arxiv.org/abs/1906.00046
[2] https://github.com/DeepSpec/InteractionTrees

Thank you to Alex Keizer (github.com/alexkeizer) for the help in figuring this out!
-/


/-
  ## Step 1: Defining Shape
-/

-- Intuitively: `ρ` is `ITree E A`, and `ν` is `(Ans : Type) × (E Ans) × (Ans → ITree E A)`.
inductive Shape (E : Type u -> Type u) (A : Type (u+1)) (ρ : Type (u+1)) (ν : Type (u+1)) : Type (u+1)
| ret (r : A) : Shape E A ρ ν
| tau (t : ρ) : Shape E A ρ ν
| vis (e : ν) : Shape E A ρ ν

abbrev Shape.Uncurried (E : Type u -> Type u) : TypeFun 3 := TypeFun.ofCurried (Shape E)

instance : MvFunctor (Shape.Uncurried E) where
  map f
    | .ret a => .ret (f 2 a)
    | .tau t => .tau (f 1 t)
    | .vis e => .vis (f 0 e)

/-
  ## Step 2: Functors for constructors
-/

qpf G_ret (E : Type u -> Type u) A ρ := A
qpf G_tau (E : Type u -> Type u) A ρ := ρ
-- qpf G_vis (E : Type -> Type) A ρ := (Ans : Type) × E Ans × (Ans → ρ) -- this unfortunately doesn't work, hence the workaround below

section SigmaWorkaround
  /-- `qpf G (Ans : Type) (E : Type → Type) A ρ ν := E Ans × (Ans → ρ)`, but universe-polymorphic -/
  abbrev G.Uncurried (Ans : Type u) (E : Type u → Type u) : TypeFun.{u+1, u+1} 2 :=
    MvQPF.Comp (n := 2) (m := 2) -- compose two 2-ary (A, ρ) functors `E Ans` and `Ans -> ρ`
      (TypeFun.ofCurried Prod.{u+1, u+1})  -- ✓ MvQPF
      ![
        MvQPF.Const 2 (ULift.{u+1} (E Ans)), -- ✓ inst₁
        MvQPF.Comp (n := 1) (m := 2) -- ✓ inst₂
          (TypeFun.ofCurried (MvQPF.Arrow (ULift.{u+1} Ans)))
          ![MvQPF.Prj (n := 2) 0]
      ]

  instance inst₁ {Ans : Type u} {E : Type u -> Type u} : MvQPF.{u+1, u+1} (MvQPF.Const 2 (ULift.{u+1} (E Ans))) := inferInstance

  instance : MvQPF.{u+1,u+1} (MvQPF.Prj (n := 2) 0) := inferInstance
  instance : MvQPF.{u+1,u+1} (![MvQPF.Prj (n := 2) 0] 0) := MvQPF.Prj.mvqpf 0
  instance : ∀i, MvQPF.{u+1,u+1} (![MvQPF.Prj (n := 2) 0] i) := fun | 0 => inferInstance
  instance inst₂ {Ans : Type u} : MvQPF.{u+1, u+1} (MvQPF.Comp (n := 1) (m := 2)
      (TypeFun.ofCurried (MvQPF.Arrow (ULift.{u+1} Ans)))
      ![MvQPF.Prj (n := 2) 0]
    ) := inferInstance

  set_option pp.universes true
  abbrev G_vis.Uncurried (E : Type u → Type u) : TypeFun.{u+1,u+1} 2 :=
    MvQPF.Sigma.{_} (A := Type (u)) fun (Ans : Type u) => (G.Uncurried Ans E)

  abbrev G_vis (E : Type u → Type u) (A : Type (u+1)) (ρ : Type (u+1)) : Type (u+1) := G_vis.Uncurried E ![A, ρ]

  #synth MvQPF (TypeFun.ofCurried (n := 2) @Prod) -- :)

  instance inst₃ {Ans : Type u} {E : Type u -> Type u} : ∀i, MvQPF.{u+1, u+1} (
      ![
        MvQPF.Const 2 (ULift.{u+1} (E Ans)), -- ✓ inst₁
        MvQPF.Comp (n := 1) (m := 2) -- ✓ inst₂
          (TypeFun.ofCurried (MvQPF.Arrow (ULift.{u+1} Ans)))
          ![MvQPF.Prj (n := 2) 0]
      ] i
  ) := fun
    | 0 => inst₁
    | 1 => inst₂

  instance {Ans} {E : Type u -> Type u} : MvQPF.{u+1, u+1} (G.Uncurried Ans E) := inferInstance

  #synth MvQPF.{_, _} (G.Uncurried ?Ans ?E) -- :)
  #synth MvQPF.{_, _} (G_vis.Uncurried ?E) -- :)
end SigmaWorkaround

abbrev ConstructorFs (E : Type u -> Type u) : Fin2 3 -> TypeVec 2 -> Type (u+1) :=
  ![G_ret.Uncurried E, G_tau.Uncurried E, G_vis.Uncurried E]

/- For some reason tc synthesis can't figure these out by itself
  `#synth MvQPF (G_vis.Uncurried ?E)` -- works
  `#synth MvQPF (ConstructorFs ?E 0)` -- fails :(
-/
instance [inst : MvQPF (G_vis.Uncurried E)] : MvQPF (ConstructorFs E 0) := inst
instance [inst : MvQPF (G_tau.Uncurried E)] : MvQPF (ConstructorFs E 1) := inst
instance [inst : MvQPF (G_ret.Uncurried E)] : MvQPF (ConstructorFs E 2) := inst
instance {E : Type u -> Type u} : (i : Fin2 3) -> MvQPF (ConstructorFs E i) :=
  fun
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance

/- ## Step 3: Base
  This step takes `Shape E : (A : Type) -> (ρ : Type 1) -> (ν : Type 1) -> Type 1`,
  and makes the `ν` disappear by expressing it in terms of `ρ`, thus obtaining
  `Base E : (A : Type) -> (ρ : Type 1) -> Type 1`.
-/

abbrev Base.Uncurried  (E : Type u -> Type u) : TypeFun.{u+1} 2 :=
  MvQPF.Comp
    (TypeFun.ofCurried (n := 3) (Shape E))
    ![G_ret.Uncurried E, G_tau.Uncurried E, G_vis.Uncurried E]

abbrev Base (E : Type u -> Type u) (A : Type (u+1)) (ρ : Type (u+1)) : Type (u+1) :=
  Base.Uncurried E ![ULift.{u+1} A, ρ]

instance {E : Type u -> Type u} : MvFunctor.{u+1, u+1} (Base.Uncurried E) where
  map f x := MvQPF.Comp.map f x

/-
  ## Step 4: Showing that `Base` is a QPF
  We do this by showing that `Shape` is isomorphic to a polynomial functor defined
  via `HeadT` and `ChildT`. Then we obtain the `MvQPF` instance for `Shape` using `ofPolynomial`.

  Once we know that `Shape` is a MvQPF, we automatically know that `Base` is a MvQPF, because
  `Base` is expressed using only MvQPFs and combinators (`Comp`, `Prj`, `Sigma`, `Arrow`, `Const`)
  which preserve MvQPF.
-/

inductive HeadT : Type u
| ret
| tau
| vis

abbrev ChildT : HeadT -> TypeVec.{u+1} 3
| .ret => ![PFin2 1, PFin2 0, PFin2 0] -- One `A`, zero `ρ`, zero `ν`
| .tau => ![PFin2 0, PFin2 1, PFin2 0] -- Zero `A`, one `ρ`, zero `ν` (remember, `ρ` intuitively means `ITree E A`)
| .vis => ![PFin2 0, PFin2 0, PFin2 1] -- Zero `A`, zero ρ, one ν (where ν is our `(Ans : Type) × ...`)

abbrev P : MvPFunctor.{u+1} 3 := ⟨HeadT, ChildT⟩
abbrev F (E : Type u -> Type u) : TypeVec.{u+1} 3 -> Type (u+1) := Shape.Uncurried E

def box (E : Type u -> Type u) : F E α → P.Obj α
| .ret (a : α 2) => Sigma.mk HeadT.ret fun -- `a : A`
  | 2 => fun (_ : PFin2 1) => a
  | 1 => PFin2.elim0
  | 0 => PFin2.elim0
| .tau (t : α 1) => Sigma.mk HeadT.tau fun -- `t : ρ`
  | 2 => PFin2.elim0
  | 1 => fun (_ : PFin2 1) => t
  | 0 => PFin2.elim0
| .vis (e : α 0) => Sigma.mk HeadT.vis fun -- `e : ν`
  | 2 => PFin2.elim0
  | 1 => PFin2.elim0
  | 0 => fun (_ : PFin2 1) => e

def unbox (E : Type u -> Type u) : P.Obj α → F E α
| ⟨.ret, child⟩ => Shape.ret (child 2 .fz)
| ⟨.tau, child⟩ => Shape.tau (child 1 .fz)
| ⟨.vis, child⟩ => Shape.vis (child 0 .fz)

theorem box_unbox_id (x : P.Obj α) : box E (unbox E x) = x := by
  rcases x with ⟨head, child⟩
  cases head <;> (
    rw [unbox, box]
    congr
    (funext i; fin_cases i) <;> (simp only [Nat.reduceAdd, Function.Embedding.coeFn_mk]; funext j; fin_cases j)
    rfl
  )

theorem unbox_box_id (x : F E α) : unbox E (box E x) = x := by cases x <;> rfl

instance Shape.instMvQPF : MvQPF (F E) := MvQPF.ofPolynomial P (box E) (unbox E) box_unbox_id unbox_box_id (by
  intro α β f x
  cases x <;> (simp only [Nat.reduceAdd]; rfl)
)

instance Base.instMvQPF : MvQPF (Base.Uncurried E) := inferInstance

/-
  ## Step 5: Finally `Cofix`, constructors, corecursor
  This step takes `Base E : (A : Type) -> (ρ : Type 1) -> Type 1`, and makes the `ρ` disappear
  by taking the cofixpoint, thus obtaining `ITree E : (A : Type) -> Type 1`.
  We need to show that Base is a MvQPF in order to take the fixpoint, which we've shown in step 4.

  And now we can:
  - Define our constructors `ret`, `tau`, and `vis`
  - Define our (co-)eliminator, `cases`, etc.
-/

set_option pp.universes true
-- abbrev Uncurried (E : Type u -> Type u) : TypeVec.{u + 1} 1 -> Type (u + 1) := MvQPF.Cofix (Base.Uncurried E)
abbrev Uncurried (E : Type _ -> Type _) : TypeVec 1 -> Type _ := MvQPF.Cofix (Base.Uncurried E)

abbrev _root_.PITree.{u, v} (E : Type (max u v) -> Type (max u v)) (A : Sort v) : Type (max u v + 1) :=
  Uncurried E ![ULift.{max u v + 1} <| PLift.{v} A]

/-- Just like ITree, but universe-polymorphic, allowing you to write `PITree _ P` where `P : Prop`. -/
abbrev _root_.PITree'.{u, v} (E : Type (max u v) -> Type (max u v)) (A : Sort v) : Type (max (u+1) v) :=
  Uncurried E ![ULift.{max (u+1) v} <| PLift.{v} A]

abbrev _root_.ITree (E : Type _ -> Type _) (A : Type _) : Type _ := PITree E A



abbrev ret.{u, v} {E : Type (max u v) -> Type (max u v)} {A : Sort v} (a : A) : ITree E A
  := MvQPF.Cofix.mk (Shape.ret (.up (.up a)))
abbrev tau.{u, v} {E : Type (max u v) -> Type (max u v)} {A : Sort v} (t : ITree E A) : ITree E A
  := MvQPF.Cofix.mk (Shape.tau t)
abbrev vis.{u, v} {E : Type (max u v) -> Type (max u v)} {A : Sort v} {Ans : Type (max u v)}
  (e : E Ans)
  (k : Ans -> ITree E A)
  : ITree E A :=
    MvQPF.Cofix.mk (Shape.vis ⟨Ans, .up e, fun ans => k ans.down⟩)

def corec' {E : Type (max u v) -> Type (max u v)} {A : Sort v} {β : Type (max u v + 1)}
  -- (f : (β → Base E (ULift.{max u v + 1} <| PLift.{v} A) β : Type (max u v + 1)))
  (f : β → Base.Uncurried E ![ULift.{max u v + 1} <| PLift.{v} A, β])
  (b : β)
  : ITree.{u, v} E A
    := MvQPF.Cofix.corec (n := 1) (F := Base.Uncurried E) f b


-- def corec {E : Type (max u v) -> Type (max u v)} {A : Sort v} {β : Type (max u v + 1)}
--   (f : (β → Base E (ULift.{max u v + 1} <| PLift.{v} A) β : Type (max u v + 1)))
--   -- (f : β → Base.Uncurried E ![ULift.{max u v + 1} <| PLift.{v} A, β])
--   (b : β)
--   : ITree.{u, v} E A
--     := corec.internal f b

-- def dest {E : Type (max u v) -> Type (max u v)} {A : Sort _} : ITree E A -> Base E A (ITree E A)
--   := MvQPF.Cofix.dest.{u, v}

@[cases_eliminator, elab_as_elim]
def cases {E : Type (max u v) -> Type (max u v)} {A : Sort v} {motive : ITree.{u, v} E A -> Sort w}
  (ret : (r : A) → motive (ITree.ret.{u, v} r))
  (tau : (x : ITree.{u, v} E A) → motive (tau.{u, v} x))
  (vis : {Ans : Type _} -> (e : E Ans) → (k : Ans → ITree E A) → motive (vis.{u, v} e k))
  (x : ITree.{u, v} E A) : motive x
  := sorry
  -- match h : MvQPF.Cofix.dest x with
  -- | .ret (.up r) =>
  --   have h : x = ITree.ret r := by
  --     apply_fun MvQPF.Cofix.mk at h
  --     simpa [MvQPF.Cofix.mk_dest] using h
  --   h ▸ ret r
  -- | .tau y =>
  --   have h : x = ITree.tau y := by
  --     apply_fun MvQPF.Cofix.mk at h
  --     simpa [MvQPF.Cofix.mk_dest] using h
  --   h ▸ tau y
  -- | .vis ⟨Ans, .up e, k⟩ =>
  --   have h : x = ITree.vis e (fun ans => k (.up ans)) := by
  --     apply_fun MvQPF.Cofix.mk at h
  --     simpa [MvQPF.Cofix.mk_dest] using h
  --   h ▸ vis e (fun ans => k (.up ans))

#exit

-- Computation rules
theorem cases_ret : cases (motive := motive) c_ret c_tau c_vis (.ret r) = c_ret r := rfl
theorem cases_tau : cases (motive := motive) c_ret c_tau c_vis (.tau t) = c_tau t := sorry
theorem cases_vis : cases (motive := motive) c_ret c_tau c_vis (.vis e k) = c_vis e k := sorry


/-
  # Some common stuff
-/

def spin : ITree E A := corec (fun .unit => .tau .unit) PUnit.unit


/-- Just a convenience function. Re-plays a tree within another tree. -/
def Base.replay (ta : ITree E A₁) (fTree : ITree E A₁ -> C) (fRet : A₁ -> A₂ := by exact id) : ITree.Base E A₂ C := sorry
--   match ta.dest with
--   | .ret (.up a : _) => .ret (.up (fRet a))
--   | .tau (t : ITree E A₁) => .tau (fTree t)
--   | .vis ⟨_, e, k⟩ => .vis e (fun x => fTree (k x))

def Base.Map (f : C -> D) : TypeVec.Arrow (TypeVec.ofList [C, B, E]) (TypeVec.ofList [D, B, E])
  := TypeVec.appendFun TypeVec.id f
