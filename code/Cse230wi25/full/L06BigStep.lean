import Cse230wi25.L04Arith

set_option pp.fieldNotation false
set_option pp.proofs true

open Aexp
open Bexp

/- @@@

## Lean Tip: Overloading Operators

Some convenient ways to "write" `Aexp` in lean by overloading the `+` operator.

@@@ -/

class ToAexp (a : Type) where
  toAexp : a -> Aexp

instance : ToAexp Nat where
  toAexp := num

instance : ToAexp String where
  toAexp := var

instance : OfNat Aexp (n: Nat) where
  ofNat := num n

instance : Add Aexp where
  add := fun a1 a2 => add a1 a2

instance : HAdd String Aexp Aexp where
  hAdd := fun s a => add (var s) a

instance : HAdd String Nat Aexp where
  hAdd := fun s a => add (var s) (num a)

def mkVar (s: String) (i : Nat) : Aexp := var (s!"{s}_{i}")

notation:80 lhs:91 "#" rhs:90 => mkVar lhs rhs

def x := "x"
def y := "y"
def z := "z"

def aexp0 : Aexp := x#1 + y#1 + z#1 + 5

#eval aexp0

/- @@@
## An Imperative Language: `Com`
@@@ -/


inductive Com where
  | Skip   : Com
  | Assign : Vname -> Aexp -> Com
  | Seq    : Com   -> Com  -> Com
  | If     : Bexp  -> Com  -> Com -> Com
  | While  : Bexp  -> Com  -> Com
  deriving Repr

open Com

/- @@@
More notation tricks to make it easier to write `Com` programs.
@@@ -/


infix:10 "<<"  => fun x y => bless (ToAexp.toAexp x) (ToAexp.toAexp y)
infix:10 "<~"  => Com.Assign
infixr:8 ";;"  => Com.Seq
notation:10 "IF" b "THEN" c1 "ELSE" c2 => Com.If b c1 c2
notation:12 "WHILE" b "DO" c "END" => Com.While b c


def a_10 := "a" <~ 10
def b_20 := "b" <~ 20
def x_ab := "x" <~ "a" + var "b"

def com0 := x <~ y + 1
def com1 := y <~ 2
def com2 := com0 ;; com1
def com3 := x <~ y + 1 ;; y <~ x + 2
def com4 := Skip ;; Skip ;; Skip ;; Skip
def com5 := IF 10 << x THEN x <~ 1 ELSE y <~ 2
def com6 := WHILE x << 5 DO x <~ x + 1 END

def st_x_10_y_20 := st0 [x := 10 ] [ y := 20]

#eval com3
#eval com4

def meaning (c: Com) (s0: State): State :=
  match c with
    | Skip => s0
    | Assign x a => upd s0 x (aval a s0)
    | Com.Seq c1 c2 => meaning c2 (meaning c1 s0)
    | If b c1 c2 => if bval b s0 then meaning c1 s0 else meaning c2 s0
    | While b c => if bval b s0
                    then
                      let s1 := (meaning c s0)
                      meaning (While b c) s1
                    else s0

/- @@@
## Big Step Semantics for `Com`



<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>

@@@ -/


inductive BigStep : Com -> State -> State -> Prop where
  | Skip   : ∀ {st},
                BigStep Skip st st
  | Assign : ∀ {st x a},
                BigStep (Assign x a) st (st [x := aval a st])
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

notation:12 "⟨" c "," s "⟩" "==>" t  => BigStep c s t

/- @@@

### Big Step Evaluation: Examples

We say that `c : Com` started in `s: State` big-steps to `t : State`
whenever we have the proposition `⟨ c, s ⟩ ==> t`. This proposition
captures the intuition that when you "run" the command `c` from a
state `s`, the execution terminates in the state `t`.

Let's try some examples of "running" `Com` programs using the big step semantics.

@@@ -/

example : ⟨ (x <~ 5 ;; y <~ var x) , st0 ⟩ ==> st0 [x := 5] [y := 5] := by
  apply BigStep.Seq
  apply BigStep.Assign
  apply BigStep.Assign

example : ⟨ (x <~ 5 ;; y <~ var x) , st0 ⟩ ==> st0 [x := 5] [y := 5] := by
  repeat constructor

example : ⟨ (x <~ 5 ;; y <~ x + 1) , st0 ⟩ ==> st0 [x := 5] [y := 6] := by
  repeat constructor

/- @@@

### EXERCISE: Using Big Step Evaluation

Lets see how we can use big-step semantics to precisely state and verify some
intuitive facts about programs.

Suppose we have a command `c` that *does not assign to* a variable `x`.
Now, suppose that when we run `c` from a state `s` we finish at state `t`.

What do you think is the relationship between the value of `x` at `s` and `t`?

Can you try to formalize the above "english" as a precise theorem? (Ex 7.1 from NK)

@@@ -/

/- @@@ START: CUT @@@ -/
def assigned(c: Com) (x: Vname): Bool :=
  match c with
  | Com.Assign y _ => x == y
  | Com.Seq c1 c2  => assigned c1 x || assigned c2 x
  | Com.If _ c1 c2 => assigned c1 x || assigned c2 x
  | Com.While _ c  => assigned c x
  | Com.Skip       => false

theorem ex_unchanged: ∀ {x c s t},
  (⟨ c, s ⟩ ==> t) -> (assigned c x == false) -> s x = t x := by
  intros x c s t cst asg
  induction cst <;> simp_all [assigned, upd]
/- @@@ END: CUT @@@ -/


/- @@@

## Equivalence of Commands

We say that two commands `c1` and `c2` are **equivalent**
if `c1` started in `s` big-steps to `t` **iff** `c2`
started in `s` also big-steps to `t`.

We can formalize this idea as a definition.

**NOTE:** The `≃` symbol can be typed as `\` + `equiv`.

@@@ -/

def equiv_com (c1 c2 : Com) := ∀ {st st' : State}, ( ⟨ c1, st ⟩ ==> st') ↔ ( ⟨ c2, st ⟩ ==> st' )

infix:50 "≃"  => equiv_com

theorem skip_skip': (Skip;; Skip) ≃ Skip := by
  simp [equiv_com]
  intros s t
  constructor
  . case mp => -- modus ponens
    intros skip_skip
    cases skip_skip
    rename_i skip1 skip2
    cases skip1
    assumption
  . case mpr =>
    intros skip
    cases skip
    solve_by_elim

  -- determines if a command behaves like SKIP
def like_skip (c: Com): Prop :=
  match c with
  | Com.Skip => true
  | Com.Assign _ _ => false
  | Com.Seq c1 c2 => like_skip c1 ∧ like_skip c2
  | Com.If b c1 c2 => ∀ s, (bval b s ∧ like_skip c1) ∨ (¬bval b s ∧ like_skip c2)
  | Com.While b c => (∀ s, ¬bval b s) ∨ like_skip c

theorem like_skip_corect (c: Com): like_skip c ↔ c ≃ Skip := by
  simp [like_skip, equiv_com]
  constructor
  case mp =>
    intros h s t
    induction c
    case Skip => rfl
    case Assign => contradiction
    case Seq c1 c2 h1 h2 =>
      constructor
      sorry
    case If => sorry
    case While => sorry
  case mpr =>
    intros h
    sorry

def deskip (c: Com): Com :=
  match c with
  | Com.Seq c1 c2 => match deskip c1 with
                      | Com.Skip => deskip c2
                      | c1' => Com.Seq c1' (deskip c2)
  | Com.If b c1 c2 => Com.If b (deskip c1) (deskip c2)
  | Com.While b c => Com.While b (deskip c)
  | _ => c


def deskip' (c: Com): Com :=
  match c with
  | Com.Seq Com.Skip c2 => deskip c2
  | Com.Seq c1 Com.Skip => deskip c1
  | Com.Seq c1 c2 => Com.Seq (deskip c1) (deskip c2)
  | Com.If b c1 c2 => Com.If b (deskip c1) (deskip c2)
  | Com.While b c => Com.While b (deskip c)
  | _ => c

#eval deskip (Skip ;; Skip ;; x <~ 2)

#eval deskip' (Skip ;; Skip ;; x <~ 2;; Skip ;; Skip)

#eval deskip' (Skip ;; Skip ;; Skip ;; Skip)

theorem deskip_correct (c: Com): deskip c ≃ c := by
  simp [equiv_com]
  intros s t
  induction c
  case Skip => rfl
  case Assign => rfl
  case Seq c1 c2 ih1 ih2 =>
    simp [deskip]
    cases deskip c1
    case Skip =>
      simp_all []
    case _ =>
      simp [ih1, ih2]
  case If b c1 c2 ih1 ih2 =>
    simp [deskip]
    repeat constructor
    sorry
  case While b c ih =>
    simp [deskip]
    repeat constructor
    sorry

/- @@@
Lets prove that a sequence of three commands `c1,c2,c3` does the same thing,
no matter where you put the `;;` i.e. `(c1;;c2);;c3` is equivalant to `c1;;(c2;;c3)`


@@@ -/

theorem seq_assoc : ∀ {c1 c2 c3}, (c1 ;; (c2 ;; c3)) ≃ ((c1 ;; c2) ;; c3) := by
/- @@@ START:SORRY @@@ -/
  simp [equiv_com]
  intros c1 c2 c3 s t
  constructor    -- This breaks the `≃` into tw
  . case mp =>
    intros tx12_3
    cases tx12_3
    rename_i tx23
    cases tx23
    repeat (constructor; repeat assumption)
  . case mpr =>
    intros tx12_3
    cases tx12_3
    rename_i tx1_2 _
    cases tx1_2
    repeat (constructor; repeat assumption)
/- @@@ END:SORRY @@@ -/

/- @@@

**NOTE:** how the first `constructor` splits the proof into two subgoals.

```lean
-- case mp
c1 c2 c3 : Com
st st' : State
⊢ (⟨c1;;c2;;c3,st⟩ ==> st') → (⟨(c1;;c2);;c3,st⟩ ==> st')

-- case mpr
c1 c2 c3 : Com
st st' : State
⊢ (⟨(c1;;c2);;c3,st⟩ ==> st') → (⟨c1;;c2;;c3,st⟩ ==> st')
```

Because in general, to prove that `P ↔ Q` we need to prove two things,

* `case mp` which corresponds to `P → Q` (*assuming `P`, prove `Q`*) and
* `case mpr` which corresponds to `Q -> P` (*assuming `Q`, prove `P`*).

Lets do a few more such equivalences.
@@@ -/

theorem skip_skip : ∀ {c: Com}, (Skip ;; c) ≃ c := by
/- @@@ START:SORRY @@@ -/
  intros c st st'
  constructor
  . case mp =>
    intros tx_skip_c
    cases tx_skip_c
    rename_i _ tx_skip tx_c
    cases tx_skip
    assumption
  . case mpr =>
    intros tx_c
    constructor
    constructor
    assumption
/- @@@ END:SORRY @@@ -/

/- @@@

### Lean Tip: Case Splitting on Assumptions

Lets try to prove that `IF b then c else c` is equivalent to `c`.

@@@ -/

theorem if_c_c_stuck : ∀ { b c }, (IF b THEN c ELSE c) ≃ c := by
   intros b c s s'
   constructor
   case mp =>
    intros tx_if; cases tx_if <;> assumption
   case mpr =>
    intros tx_c
    cases hb: bval b s
    . case false =>
      apply BigStep.IfFalse <;> assumption
    . case true =>
      apply BigStep.IfTrue <;> assumption

/- @@@

Yikes! In the `mpr` case we are *stuck* because we don't know if the `bval b s`
is `true` or `false` and so we don't know whether to take the `THEN` or `ELSE`
branch! Of course, in this case, it *does not matter* which branch we take: either
way we are going to run `c` so lets just tell `lean` to **case split**
on the value of `bval b s` by

1. **adding a new hypothesis** `hb : bval b s` and
2. **case splitting** on the value of `cases hb : bval b s`

@@@ -/

theorem if_c_c : ∀ { b c }, (IF b THEN c ELSE c) ≃ c := by
   intros b c s s'
   constructor
   case mp =>
    intros tx_if; cases tx_if <;> assumption
   case mpr =>
    intros tx_c
    cases hb : bval b s
    -- aha, split cases on the `hb : bval b s`
    . case false =>
      -- we have: hb: bval b s = false
      apply BigStep.IfFalse <;> assumption
    . case true =>
      -- we have: hb: bval b s = true
      apply BigStep.IfTrue  <;> assumption

/- @@@
**Exercise:** Complete the proof of the below.
@@@ -/

theorem unfold_while : ∀ {b c},
  (WHILE b DO c END) ≃ ((IF b THEN c ELSE Skip) ;; (WHILE b DO c END)) :=
  by
/- @@@ START:SORRY @@@ -/
  intros b c s s'
  constructor
  . case mp =>
    intros tx_w; cases tx_w
    . case WhileFalse =>
      constructor
      . case a => apply BigStep.IfFalse <;> solve_by_elim
      . case a => solve_by_elim
    . case WhileTrue =>
      constructor <;> solve_by_elim
  . case mpr =>
    intros tx_if_w
    cases tx_if_w
    rename_i _ tx_if _
    cases tx_if
    . case Seq.IfTrue => solve_by_elim
    . case Seq.IfFalse => rename_i tx_skip; cases tx_skip; solve_by_elim
/- @@@ END:SORRY @@@ -/

/- @@@

### `equiv_com` is an equivalence relation

It is easy to prove that `≃` is an **equivalence relation**, that is,
it is **reflexive**, **symmetric** and **transitive**.

@@@ -/

theorem equiv_refl : ∀ {c}, c ≃ c := by
  simp_all [equiv_com]

theorem equiv_symm : ∀ {c c'}, c ≃ c' -> c' ≃ c := by
  simp_all [equiv_com]

theorem equiv_trans : ∀ {c1 c2 c3}, c1 ≃ c2 -> c2 ≃ c3 -> c1 ≃ c3 := by
  simp_all [equiv_com]

/- @@@
**Exercise:** Complete the proof of the below; you may need a helper lemma.
(Exercise 7.6 from [Nipkow and Klein](http://www.concrete-semantics.org/)).
@@@ -/

theorem while_cong_helper : ∀ {b c c' s t},
  (⟨ WHILE b DO c END , s ⟩ ==> t) ->
  c ≃ c' ->
  (⟨ WHILE b DO c' END, s ⟩ ==> t) := by
/- @@@ START:SORRY @@@ -/
   intros b c c' s t tx_wc c_eq_c'
   generalize h : (WHILE b DO c END) = x at tx_wc -- this is ANF / Nico's tip
   induction tx_wc <;> simp_all []
   . case WhileFalse =>
      constructor <;> try assumption
   . case WhileTrue =>
      constructor <;> try assumption
      simp_all [equiv_com]
/- @@@ END:SORRY @@@ -/

theorem while_cong : ∀ {b c c'},
  c ≃ c' ->
  (WHILE b DO c END) ≃ (WHILE b DO c' END) := by
  intros b c c' c_eq_c'
  simp_all [equiv_com]
  intros st st'
  apply Iff.intro
  . case mp =>
      intros wc
      apply while_cong_helper
      assumption
      assumption
  . case mpr =>
      intros wc
      apply while_cong_helper
      assumption
      apply equiv_symm
      assumption



/- @@@

## Verifying an Optimization

Consider the following code

```
x <~ a ;; y <~ a
```

It seems a bit *redundant* to compute the `a` again, when we have just assigned it to `x`, right?

Instead, we should be able to just replace the above with

```
x <~ a ;; y <~ x
```

That is, just "copy" the value we computed and saved in `x`.

Right?

Lets see if we can formalize this as an *equivalence* ...

@@@ -/

theorem assign_steps : ∀ {x a s},
  ( ⟨ x <~ a, s ⟩ ==> t ) <-> t = (s [ x := aval a s]) := by
  intros x a s
  constructor
  case mp => intros xs; cases xs ; trivial
  case mpr => intros; simp_all [] ; apply BigStep.Assign

-- how to say 'does not contain x'?


def does_not_contain (a : Aexp) (x :Vname) :=
  match a with
  | num _ => true
  | var y => not (x = y)
  | add a1 a2 => does_not_contain a1 x && does_not_contain a2 x

theorem dnc_upd : ∀ {x a s n},
  does_not_contain a x -> aval a (s [ x := n ]) = aval a s := by
  intros x a s n dnc_a_x
  induction a
  constructor
  . case var v =>
      simp_all [aval, upd, does_not_contain]
      intro h
      simp_all [Eq.symm]
  . case add a1 a2 ih1 ih2 => simp_all [aval, upd, does_not_contain]

theorem double_assign :
  does_not_contain a x -> (( x <~ a ;; y <~ a) ≃ (x <~ a ;; y <~ var x)) := by
  simp [equiv_com]; intros dnc_a_x s t; constructor
  all_goals
    intros xaya; cases xaya;
    constructor
    assumption
    simp_all [aval, upd, assign_steps, dnc_upd]


















def reads (a: Aexp) (x: Vname) : Bool :=
  match a with
  | var y     => x = y
  | num _     => false
  | add a1 a2 => reads a1 x || reads a2 x

theorem unmodified_assign: ∀ {x a n s},
  reads a x = false -> (aval a (s [x := n]) = aval a s) := by
  intros x a n s not_reads_x
  induction a <;> simp_all [aval, reads]
  . case var => simp_all [upd]; intros; simp_all []

@[simp]
theorem assign_step : ∀ {x a s t}, (⟨ x <~ a, s ⟩ ==> t) <-> (t = (s [x := (aval a s)])) := by
  intros x a s t
  apply Iff.intro
  .case mp => intros xs; cases xs ; trivial
  .case mpr => intros; simp_all [] ; apply BigStep.Assign

theorem redundant_assign : ∀ {x y a}, reads a x = false -> (x <~ a ;; y <~ a) ≃ (x <~ a ;; y <~ var x) := by
  simp_all [equiv_com]
  intros x y a not_reads s t
  generalize ff : aval a s = n
  have aa : aval a (s [x := n ]) = aval a s  := by
    apply unmodified_assign; assumption
  constructor
  . case mp =>
    intros xaya; cases xaya; rename_i s' xa ya
    cases xa; cases ya
    constructor
    constructor
    simp [aval]
    simp_all [upd]
  . case mpr =>
    intros xayx; cases xayx; rename_i s' xa yx
    cases xa; cases yx
    constructor
    constructor
    simp [aval]
    simp_all [upd]



/- @@@

### BigStep Semantics are Deterministic

Finally, we want to design languages that are **deterministic** which means,
that if you *start* running a command `c` from some state `s` then there is *at most*
one state `t` that it can *finish* in. (It would be rather strange if we started in the
same state and *sometimes* the program finished with `x = 10` and at other times `x = 20`).

**EXERCISE:** Can you think of some examples where programs are **non-deterministic** ?

How can we *specify* that our big step semantics for `Com` are indeed deterministic?


<br>
<br>
<br>
<br>
<br>
<br>
<br>

And now, how can we *prove* it?

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>

**HINT:**

1. Recall `induction ... generalizing`
2. Recall that you can "add" facts to your hypotheses using `have`

@@@ -/

theorem bigstep_deterministic : ∀ {c s t1 t2},
  (⟨ c, s ⟩ ==> t1) -> (⟨ c, s ⟩ ==> t2) -> t1 = t2 := by
  intros c s t1 t2 tx_s_to_t1 tx_s_to_t2
  induction tx_s_to_t1 generalizing t2
  . case Skip =>
    cases tx_s_to_t2
    rfl
  . case Assign =>
    cases tx_s_to_t2
    rfl
  . case Seq =>
    rename_i c1 c2 s0 s1 s2 _ _ ih1 ih2
    cases tx_s_to_t2
    rename_i s1' tx_c1_s0_s1' tx_c2_s1'_t2
    apply ih2
    have fact1 := ih1 tx_c1_s0_s1'
    simp_all []
  . case IfTrue =>
    cases tx_s_to_t2 <;> simp_all []
    rename_i ih _ _
    apply ih
    assumption
  . case IfFalse =>
    cases tx_s_to_t2 <;> simp_all []
    rename_i ih _ _
    apply ih
    assumption
  . case WhileFalse =>
    cases tx_s_to_t2 <;> simp_all []
  . case WhileTrue =>
    cases tx_s_to_t2 <;> simp_all []
    rename_i _ _ ih_c ih_w _ _ tx_c2 tx_w2
    apply ih_w
    have fact1 := ih_c tx_c2
    simp_all []
