set_option pp.fieldNotation false

/- ---------------------------------------------------------------------------------
# CSE 230 MIDTERM 2

In this exam, we will add an `IF b THEN c` command to `Com` and

- Define its `BigStep` semantics
- Prove the command is equivalent to a plain `IF` but where the `ELSE` is `Skip`
- Define the `FH` rule for the command
- Prove the `FH` rule is sound wrt the `BigStep` semantics
- Define the `pre` for the command
- Prove the `pre` is sound with respect to the `FH` rule.

**NOTE:**

1. You only need to change parts of the file marked with **FIX_THIS** or `sorry`.
2. `axiom` can be used like a `theorem` (but where we don't provide a proof).
------------------------------------------------------------------------------------ -/

namespace Preliminaries

-- Variables, Values and States -------------------------------

abbrev Val := Nat
abbrev Vname := String

abbrev State := Vname -> Val
-- update state
def upd (s: State) (x: Vname) (v: Val) : State :=
  λ y => if y = x then v else s y

notation:10 s " [ " x " := " v " ] " => upd s x v

-- Arithmetic Expressions -------------------------------------

inductive Aexp where
  | num : Val -> Aexp
  | var : Vname -> Aexp
  | add : Aexp -> Aexp -> Aexp
  | sub : Aexp -> Aexp -> Aexp
  deriving Repr

open Aexp

class ToAexp (a : Type) where
  toAexp : a -> Aexp

@[simp]
instance : ToAexp Nat where
  toAexp := num

@[simp]
instance : ToAexp String where
  toAexp := var

@[simp]
instance : ToAexp Aexp where
  toAexp a := a

@[simp]
instance : OfNat Aexp (n: Nat) where
  ofNat := num n

@[simp]
instance : Add Aexp where
  add := fun a1 a2 => add a1 a2

@[simp]
instance : HAdd String Aexp Aexp where
   hAdd := fun s a => add (var s) a

@[simp]
instance : HAdd String Nat Aexp where
   hAdd := fun s a => add (var s) (num a)

@[simp]
instance : HAdd String String Aexp where
   hAdd := fun s a => add (var s) (var a)

@[simp]
instance : HSub String Nat Aexp where
   hSub := fun s a => sub (var s) (num a)

@[simp]
instance : HSub Nat String Aexp where
   hSub := fun a s => sub (num a) (var s)


def mkVar (s: String) (i : Nat) : Aexp := var (s!"{s}_{i}")

notation:80 lhs:91 "#" rhs:90 => mkVar lhs rhs

@[simp]
def x := "x"

@[simp]
def y := "y"

@[simp]
def z := "z"

def aexp0 : Aexp := x#1 + y#1 + z#1 + 5

def aval (a: Aexp) (s: State) : Val :=
  match a with
  | num n => n
  | var x => s x
  | add a1 a2 => aval a1 s + aval a2 s
  | sub a1 a2 => aval a1 s - aval a2 s

-- initial state
def st0 : State := λ _ => 0
def aexp_5 := num 5
def aexp_x := var "x"
def aexp_x_plus_y := add (var "x") (var "y")
def aexp_2_plus_z_plus_3 := add (num 2) (add (var "z") (num 3))

-- Substitution -----------------------------------------------

def subst (x : Vname) (xa : Aexp) (a : Aexp) : Aexp :=
  match a with
  | num n => num n
  | var y => if x = y then xa else var y
  | add a1 a2 => add (subst x xa a1) (subst x xa a2)
  | sub a1 a2 => sub (subst x xa a1) (subst x xa a2)

example : subst "x" (num 3) (add (var "x") (var "y")) = add (num 3) (var "y") := rfl

theorem subst_aval : ∀ {x xa a}, aval (subst x xa a) s = aval a (s [x := aval xa s])
  := by
  intros x xa a
  induction a
  case num n => simp [subst, aval]
  case var y => simp [subst, aval]
                split
                case isTrue => simp [upd, *]
                case isFalse => simp [upd, *]; split <;> simp_all [aval]
  case add a1 a2 ih1 ih2 => simp_all [subst, aval]
  case sub a1 a2 ih1 ih2 => simp_all [subst, aval]


-- Boolean Expressions ---------------------------------------------

inductive Bexp where
  | Bc    : Bool -> Bexp
  | Bnot  : Bexp -> Bexp
  | Band  : Bexp -> Bexp -> Bexp
  | BLess : Aexp -> Aexp -> Bexp
  deriving Repr

open Bexp

class ToBexp (a : Type) where
  toBexp : a -> Bexp

@[simp]
instance : ToBexp Bool where
  toBexp := Bc

@[simp]
instance : ToBexp Bexp where
  toBexp (b) := b


def bval (b: Bexp) (st: State) : Bool :=
  match b with
  | Bc v        => v
  | Bnot b1     => ! bval b1 st
  | Band b1 b2  => bval b1 st && bval b2 st
  | BLess a1 a2 => aval a1 st < aval a2 st

def bsubst (x : Vname) (xa : Aexp) (b : Bexp) : Bexp :=
  match b with
  | Bc v        => Bc v
  | Bnot b'     => Bnot  (bsubst x xa b')
  | Band  b1 b2 => Band  (bsubst x xa b1) (bsubst x xa b2)
  | BLess a1 a2 => BLess (subst x xa a1) (subst x xa a2)

theorem subst_bval : ∀ {x xa b}, bval (bsubst x xa b) s = bval b (s [x := aval xa s]) := by
  intros x xa b
  induction b
  case Bc v       => simp_all [bsubst, bval]
  case Bnot b' ih => simp_all [bsubst, bval, ih]
  case Band b1 b2 ih1 ih2 => simp_all [bsubst, bval, ih1, ih2]
  case BLess a1 a2 => simp_all [bsubst, bval, subst_aval]

end Preliminaries

open Preliminaries

/------------------------------------------------------------------------
## Commands

Let us extend the syntax of commands `Com` with a new `IfThen b c` statement,
which is like an `If` statement **with only** a "then" branch (no "else" branch).
----------------------------------------------------------------------- -/

inductive Com where
  | Skip   : Com
  | Assign : Vname -> Aexp -> Com
  | Seq    : Com   -> Com  -> Com
  | If     : Bexp  -> Com  -> Com -> Com
  | While  : Bexp  -> Com  -> Com
  | IfThen : Bexp  -> Com  -> Com           -- This is the new `IfThen` command
  deriving Repr

open Com

def bLess (a1 a2 : Aexp) : Bexp := Bexp.BLess a1 a2

infix:10 "<<"  => fun x y => Bexp.BLess (ToAexp.toAexp x) (ToAexp.toAexp y)
infix:10 "<~"  => Com.Assign
infixr:8 ";;"  => Com.Seq
notation:10 "IF" b "THEN" c => Com.IfThen b c
notation:10 "IF" b "THEN" c1 "ELSE" c2 => Com.If b c1 c2
notation:12 "WHILE" b "DO" c "END" => Com.While b c

--
def com0 := IF 0 << x THEN x <~ x + 1
def com1 := IF 0 << x THEN x <~ x + 1 ELSE y <~ y + 1

/- -----------------------------------------------------------------------
## Part 1: Bigstep Semantics

Below we have the `BigStep` rules for `Com` -- but where the two rules
for `IfThen` are wrong (they are just like `Skip`).
**Fix** the rules for `IfThenTrue` and `IfThenFalse`, so that you can
prove that `IfThen b c` is equivalent to `If b c Skip`.

------------------------------------------------------------------------- -/
open Com

inductive BigStep : Com -> State -> State -> Prop where
  | Skip   : ∀ {st},
                BigStep Skip st st
  | Assign : ∀ {st a n},
                BigStep (Assign a n) st (st [a := aval n st])
  | Seq    : ∀ {c1 c2 st1 st2 st3},
                BigStep c1 st1 st2 -> BigStep c2 st2 st3 ->
                BigStep (Seq c1 c2) st1 st3
  | IfTrue : ∀ {b c1 c2 st st'},
                bval b st = true -> BigStep c1 st st' ->
                BigStep (If b c1 c2) st st'
  | IfFalse : ∀ {b c1 c2 st st'},
                bval b st = false -> BigStep c2 st st' ->
                BigStep (If b c1 c2) st st'
  | WhileFalse : ∀ {b c st},
                bval b st = false ->
                BigStep (While b c) st st
  | WhileTrue : ∀ {b c st st' st''},
                bval b st = true -> BigStep c st st' -> BigStep (While b c) st' st'' ->
                BigStep (While b c) st st''

-- ### Problem 1(a): FIX_THIS this rule so that you can prove 1(c)
  | IfThenTrue: ∀ {b c st st'},
                bval b st = true ->
                BigStep c st st' ->
                BigStep (IfThen b c) st st'

-- ### Problem 1(b): FIX_THIS this rule so that you can prove 1(c)
  | IfThenFalse: ∀ {b c st},
                bval b st = false ->
                BigStep (IfThen b c) st st


notation:12 "⟨" c "," s "⟩"  "==>" t  => BigStep c s t

@[simp]
def equiv_com (c1 c2 : Com) := ∀ {st st' : State},
  ( ⟨ c1, st ⟩ ==> st') ↔ ( ⟨ c2, st ⟩ ==> st' )

infix:50 "≃" => equiv_com

-- ### Problem 1(c): Prove that `IF b THEN c` is equivalent to `IF b THEN c ELSE Skip`

-- @[autogradedProof 20]
theorem ifthen_equiv: ∀ {b c}, (IF b THEN c) ≃ (IF b THEN c ELSE Skip) := by
  intros b c st st'
  constructor <;> intros cst
  . case mp =>
    cases cst
    . case IfThenTrue h1 h2 =>
      apply BigStep.IfTrue
      repeat assumption
    . case IfThenFalse h =>
      apply BigStep.IfFalse
      apply h
      . apply BigStep.Skip
  . case mpr =>
    cases cst
    . case IfTrue h1 h2 =>
      apply BigStep.IfThenTrue
      repeat assumption
    . case IfFalse h1 h2 =>
      cases h2
      apply BigStep.IfThenFalse
      apply h1

/- -----------------------------------------------------------------------
## Part 2: Floyd-Hoare Logic

Next, extend the proof rules for FH logic to handle the `IfThen` commands,
and prove the rule is sound.
------------------------------------------------------------------------- -/

abbrev Assertion := State -> Prop

@[simp]
def Implies (p q : Assertion) := ∀ s, p s -> q s

notation:10 p " ⊆ " q => Implies p q

notation:10 p "[[ " x ":=" a "]]" => fun s => p (s [ x := (aval a s) ])
inductive FH : Assertion -> Com -> Assertion -> Prop where

  | Skip              : ∀ {p},
                          FH p Skip p

  | Assign            : ∀ {p x a},
                          FH (p [[ x := a ]]) (x <~ a) p

  | Seq               : ∀ {p c1 c2 q r},
                          FH p c1 q -> FH q c2 r ->
                          FH p (c1 ;; c2) r

  | If                : ∀ {p b c1 c2 q},
                        FH (fun s => p s /\   bval b s) c1 q -> FH (fun s => p s /\ ¬ bval b s) c2 q ->
                        FH p (If b c1 c2) q

  | While             : ∀ {p b c},
                        FH (fun s => p s /\ bval b s) c p ->
                        FH p (While b c) (fun s => p s /\ ¬ bval b s)

  | CnsL              : ∀ {p' p c q},
                        FH p c q ->
                        (p' ⊆ p) ->
                        FH p' c q

  | CnsR              : ∀ {p c q q'},
                        FH p c q ->
                        (q ⊆ q') ->
                        FH p c q'

-- ### Problem 2(a) **FIX_THIS** the FH rule for `IfThen` commands so that you can prove 2(b), and then `freebie1` and `freebie2`
  | IfThen            : ∀ {p b c q},
                        FH (fun s => p s ∧ bval b s) c q ->
                        FH (fun s => p s ∧ ¬ bval b s) Skip q ->
                        FH p (IfThen b c) q

notation:10 "⊢" " {{" p "}} " c " {{" q "}}" => FH p c q

/- -------------------------------------------------------------------------------------------------
-- Recall the definition of `Legit` FH triples.
--------------------------------------------------------------------------------------------------- -/

@[simp]
def Legit (p: Assertion) (c: Com) (q: Assertion) :=
  ∀ s t, p s -> (⟨ c, s ⟩ ==> t) -> q t

notation:10 "⊧" " {{" p "}} " c " {{" q "}}" => Legit p c q

-- @[legalAxiom]
axiom conseq_l_sound : ∀ { p' p q : Assertion} { c : Com},
  (p' ⊆ p) -> (⊧ {{ p }} c {{ q }}) ->
  (⊧ {{ p' }} c {{ q }})

-- @[legalAxiom]
axiom conseq_r_sound : ∀ { p q q' : Assertion} {c : Com},
  (⊧ {{ p }} c {{ q }}) -> ( q ⊆ q' ) ->
  (⊧ {{ p }} c {{ q' }})

-- @[legalAxiom]
axiom skip_sound : ∀ {p},
  ⊧ {{ p }} Skip {{ p }}

-- @[legalAxiom]
axiom assign_sound: ∀ { x a q },
  ⊧ {{ q [[ x := a ]] }} x <~ a {{ q }}

-- @[legalAxiom]
axiom seq_sound : ∀ {p q r c1 c2},
  (⊧ {{p}} c1 {{q}}) -> ( ⊧ {{q}} c2 {{r}}) ->
  ( ⊧ {{p}} c1 ;; c2 {{ r }})

-- @[legalAxiom]
axiom if_sound : ∀ {b c1 c2 p q},
  ( ⊧ {{ λs => p s /\ bval b s }} c1 {{ q }}) -> ( ⊧ {{ λs => p s /\ ¬ bval b s }} c2 {{ q }}) ->
  ( ⊧ {{ p }} If b c1 c2 {{ q }})

-- @[legalAxiom]
axiom while_sound : ∀ {b c inv},
  ( ⊧ {{ λ s => inv s /\ bval b s }} c {{ inv }} ) ->
  ( ⊧ {{ inv }} While b c {{ λ s => inv s /\ ¬ bval b s }} )

-- @[legalAxiom]
theorem ifthen_sound : ∀ {b c p q},
  ( ⊧ {{ λ s => p s /\ bval b s }} c {{ q }} ) ->
  ( ⊧ {{ λ s => p s /\ ¬ bval b s }} Skip {{ q }} ) ->
  ( ⊧ {{ p }} IfThen b c {{ q }} ) := by
  intros b c p q h1 h2
  simp_all
  intros s t ps if_then
  cases if_then
  case IfThenTrue =>
    apply h1
    repeat assumption
  case IfThenFalse b_false =>
    apply h2
    apply ps
    apply b_false
    apply BigStep.Skip

/- ### Problem 2 (b) Complete the proof of `fh_sound`

   You need **only** remove the `sorry` in the `case IfThen`.

   Of course, you can define and prove any new helper theorems if you like.

-/

-- @[autogradedProof 35]
theorem fh_sound : ∀ {p c q}, (⊢ {{ p }} c {{ q }}) -> ( ⊧ {{ p }} c {{ q }}) := by
  intros p c q pcq
  induction pcq
  . case Skip   => apply skip_sound
  . case Assign => apply assign_sound
  . case Seq    => apply seq_sound; repeat assumption
  . case If     => apply if_sound; repeat assumption
  . case While  => apply while_sound; repeat assumption
  . case CnsL   => apply conseq_l_sound; repeat assumption
  . case CnsR   => apply conseq_r_sound; repeat assumption
  . case IfThen => apply ifthen_sound; repeat assumption

/- ------------------------------------------------------------------------------------------------
## Part 3: Verification Conditions

Next, extend the `vc` and `pre` functions to handle `IfThen`,
and prove your extensions correct.

-------------------------------------------------------------------------------------------------- -/

inductive ACom where
  | Skip   : ACom
  | Assign : Vname -> Aexp -> ACom
  | Seq    : ACom  -> ACom -> ACom
  | If     : Bexp  -> ACom -> ACom -> ACom
  | While  : Assertion -> Bexp  -> ACom -> ACom
  | IfThen : Bexp  -> ACom -> ACom
open ACom

@[simp]
def erase (c : ACom) : Com :=
  match c with
  | ACom.Skip         => Com.Skip
  | ACom.Assign x a   => Com.Assign x a
  | ACom.Seq c1 c2    => Com.Seq     (erase c1) (erase c2)
  | ACom.If b c1 c2   => Com.If b    (erase c1) (erase c2)
  | ACom.While _ b c  => Com.While b (erase c)
  | ACom.IfThen b c   => Com.IfThen b (erase c)

notation:10 "⊢" " {|" p "|} " c " {|" q "|}" => (⊢ {{ p }} (erase c) {{ q }})

@[simp]
def pre (c: ACom) (q : Assertion) : Assertion :=
  match c with
  | ACom.Skip         => q
  | ACom.Assign x a   => ( q [[ x := a ]] )
  | ACom.Seq c1 c2    => pre c1 (pre c2 q)
  | ACom.If b c1 c2   => (λ s => if bval b s then pre c1 q s else pre c2 q s)
  | ACom.While i _ _  => i

-- ### Problem 3(a): FIX_THIS the implementation of `pre` for `IfThen`, so you can prove 3(b)
  | ACom.IfThen b c   => (λ s => if bval b s then pre c q s else q s)

@[simp]
def vc (c : ACom) (q : Assertion) : Prop :=
  match c with
  | ACom.Skip        => True
  | ACom.Assign _ _  => True
  | ACom.Seq c1 c2   => vc c1 (pre c2 q) /\ (vc c2 q)
  | ACom.If _ c1 c2  => vc c1 q /\ vc c2 q
  | ACom.While i b c => (∀ s, i s -> bval b s -> pre c i s) /\
                        (∀ s, i s -> ¬ bval b s -> q s) /\
                        vc c i
  | ACom.IfThen _ c  => vc c q

theorem simp_if_true : ∀ { b : Bexp } { p1 p2 : Assertion},
  (λ s => (if bval b s = true then p1 s else p2 s) ∧ bval b s = true) ⊆ p1
  := by simp [Implies]; intros; simp_all []

theorem simp_if_false : ∀ { b : Bexp } { p1 p2 : Assertion},
  (λ s => (if bval b s = true then p1 s else p2 s) ∧ ¬ bval b s = true) ⊆ p2
  := by simp [Implies]; intros; simp_all []

-- ### Problem 3(b): Prove that your extension of `pre` for `IfThen` is sound.
-- **HINT**  You may find `simp_if_true`, `simp_if_false`
-- (oddly named `foo_true` `foo_false` in the hw3.lean) helpful...

-- @[autogradedProof 25]
theorem ifthen_pre : ∀ {b c q},
  ((vc c q ) -> (⊢ {| pre c q |} c {| q |})) ->
  (vc (IfThen b c) q) ->
  ( ⊢ {| pre (IfThen b c) q |} IfThen b c {| q |} )
  := by
  intros b c q vc1 vc2
  simp_all
  constructor
  . apply FH.IfThen
    apply FH.CnsL
    apply vc1
    apply simp_if_true
    apply q
    apply FH.CnsL
    apply FH.Skip
    apply simp_if_false
  . intros s h
    apply h

-- @[legalAxiom]
axiom vc_pre : ∀ {c q},
  vc c q -> (⊢ {{ pre c q }} (erase c) {{ q }})

-- @[legalAxiom]
axiom vc_sound : ∀ {c q},
  vc c q -> (⊧ {{ pre c q }} erase c {{ q }})

--  Extend `vc` to check triples `{p} c {q}`, by generating a `vc' p c q`
@[simp]
def vc' (p : Assertion) (c : ACom) (q : Assertion) := (p ⊆ pre c q) /\ vc c q

-- @[legalAxiom]
axiom vc'_sound : ∀ {p c q},
  (vc' p c q) -> (⊧{{ p }} erase c {{ q }})

namespace Problem3

notation:10 x "<~" e  => ACom.Assign x (ToAexp.toAexp e)
infixr:20 ";;"  => ACom.Seq
notation:10 "IF" b "THEN" c1 "ELSE" c2 => ACom.If b c1 c2
notation:10 "IF" b "THEN" c            => ACom.IfThen b c
notation:12 "WHILE" "{-@" inv "@-}" b "DO" c "END" => ACom.While inv (ToBexp.toBexp b) c
notation:20 "[|" c "|]" => erase c
notation:10 "⊢" " {|" p "|}" c "{|" q "|}" => FH p (erase c) q
notation:10 "⊧" " {|" p "|}" c "{|" q "|}" => (⊧ {{p}} (erase c) {{q}})

-- If you defined `vc` and `pre` correctly, the following proof should just work automatically.

theorem freebie :
  ⊧ {| λ s => s x = 100 |}
      (IF 0 << x THEN x <~ x - 1) ;;
      (IF 0 << x THEN x <~ x - 1) ;;
      (IF 0 << x THEN x <~ x - 1)
     {| λs => s x = 97 |}
  := by
  apply vc'_sound;
  simp_all [aval,upd,bval]

end Problem3
