import Cse230wi25.BigStep
import Cse230wi25.L07Axiomatic

set_option pp.fieldNotation false
set_option pp.proofs true

/- @@@

# Automating Floyd-Hoare with Verification Conditions

FH rules are nice but still *quite* tedious to use, because it seems like we
need to spell out

1. where to apply which rule
2. how exactly the rules of consequence work

etc.

In fact, the rules are *mostly* **syntax directed** meaning that there is
**exactly one** rule that can be applied for each kind of term.

- The rules of _consequence_
- The loop _invariant_

Next, lets see how we can automate away more or less everything except
the above.

@@@ -/

/- @@@

## Annotated Commands

Lets assume that the programmer has **annotated** their code with the
loop invariant, so we can define a `ACom` type which looks just like
the previous `Com` except for the loop constructor which is now of the
form `While inv b c` case, so the `inv` is baked into the code.

@@@ -/


inductive ACom where
  | Skip   : ACom
  | Assign : Vname -> Aexp -> ACom
  | Seq    : ACom  -> ACom -> ACom
  | If     : Bexp  -> ACom -> ACom -> ACom
  | While  : Assertion -> Bexp  -> ACom -> ACom
open ACom

/- @@@
In fact, if we `erase` the `inv` from each while, we can convert an `ACom` program
back into the old `Com` programs.
@@@ -/

@[simp]
def erase (c : ACom) : Com :=
  match c with
  | ACom.Skip        => Com.Skip
  | ACom.Assign x a  => Com.Assign x a
  | ACom.Seq c1 c2   => Com.Seq     (erase c1) (erase c2)
  | ACom.If b c1 c2  => Com.If b    (erase c1) (erase c2)
  | ACom.While _ b c => Com.While b (erase c)

/- @@@
As before we can define some "notation" to make it easier to write `ACom` programs.
@@@ -/

notation:10 x "<~" e  => ACom.Assign x (ToAexp.toAexp e)
infixr:20 ";;"  => ACom.Seq
notation:10 "IF" b "THEN" c1 "ELSE" c2 => ACom.If b c1 c2
notation:12 "WHILE" "{-@" inv "@-}" b "DO" c "END" => ACom.While inv (ToBexp.toBexp b) c
notation:20 "[|" c "|]" => erase c
notation:10 "⊢" " {|" p "|}" c "{|" q "|}" => FH p (erase c) q

/- @@@

Specifically, note the `⊢ {| p |} c {| q |}` triple
which means that the triple holds for the **erased**
command `c`.

## Weakest Preconditions

The central idea is reformulate the FH rules into the notion
of the **weakest precondition** `wp c q` which defines the
**largest** set of *starting states* from which executing
the command `c` will yield a *final state* in which the
assertion `q` is guaranteed to hold.


wp (x <~ 10) (λ s => s x = 10)
==
(λ s => s x = 10) [[ x := a ]]
==
tt

wp (x <~ 99 ;; x <~ 10) (λ s => s x = 10)
=
wp (x <~ 99) (wp (x <~ 10) (λ s => s x = 10))
=
wp (x <~ 99) tt
=
tt


@@@ -/

example : ((λ s => s x = 10) [[ x := 10 ]]) = tt := by
  funext
  simp [aval, upd, tt]

example : ((λ s => s x = 10) [[ x := 10 ]]) = tt := by
  funext
  simp [aval, upd, tt]


/-

"weakest pre"

     IF (vc c q) THEN ⊢ {{ wp c q }} c {{ q }}

"side conditions"

     (vc c q) : Prop


-/


@[simp]
def wp (c: ACom) (q : Assertion) : Assertion :=
  match c with
  | ACom.Skip        => q
  | ACom.Assign x a  => q [[ x := a ]]
  | ACom.Seq c1 c2   => wp c1 (wp c2 q)
  | ACom.If b c1 c2  => (λ s => if bval b s then wp c1 q s else wp c2 q s)
  | ACom.While i _ _ => i

@[simp]
def vc (c : ACom) (q : Assertion) : Prop :=
  match c with
  | ACom.Skip        => True
  | ACom.Assign _ _  => True
  | ACom.Seq c1 c2   => vc c1 (wp c2 q) /\ (vc c2 q)
  | ACom.If _ c1 c2  => vc c1 q /\ vc c2 q
  | ACom.While inv b c =>
      (∀ s, inv s -> bval b s -> wp c inv s) /\ -- {inv /\ b} c { inv }
      (∀ s, inv s -> ¬ bval b s -> q s) /\      -- (inv /\ ¬b) ⊆ q
      vc c inv

def ass_99: Assertion := λ s => s x = 10

example : ((wp ((x <~ 99) ;; (x <~ 10)) ass_99) = tt) := by
  funext
  simp [wp, aval, upd, ass_99]


theorem vc_sound : vc c q -> (⊢ {| wp c q |} c {| q |})
  := by
  intros vcq
  induction c generalizing q
  . case Skip   => constructor
  . case Assign => constructor
  . case Seq    =>
    rename_i c1 c2 ih1 ih2
    simp []
    constructor
    apply ih1; simp_all
    apply ih2; simp_all
  . case If     => sorry
  . case While  => sorry

/- ----------------------------------------------------------------------------------------------- -/

@[simp]
def vc' (p: Assertion) (c: ACom) (q: Assertion) : Prop := (p ⊆ wp c q) ∧ (vc c q)

theorem vc'_sound : vc' p c q -> (⊢ {{ p }} (erase c) {{ q }}) := by
  intros vcq
  cases vcq
  rename_i vc1 vc2
  apply FH.CnsL
  apply vc_sound; assumption
  apply vc1


/- ----------------------------------------------------------------------------------------------- -/

theorem ex_swap :
  ⊢ {| λs => s x = a /\ s y = b |}
      (z <~ x) ;;
      (x <~ y) ;;
      (y <~ z)
    {| λs => s x = b /\ s y = a |}
  := by
  apply vc'_sound; simp_all [aval, upd]

/- ----------------------------------------------------------------------------------------------- -/

theorem ex1 : ⊢ {| tt |}
                  x <~ 5
                {| λs => s x = 5 |}
  := by
  apply vc'_sound; simp_all [aval, upd]

/- ----------------------------------------------------------------------------------------------- -/

theorem ex2 : ⊢ {| λs => s x = 10 |}
                  (x <~ x + 1) ;;
                  (x <~ x + 1)
                {| λs => s x = 12 |}
  := by
  apply vc'_sound; simp_all [aval, upd]

/- ----------------------------------------------------------------------------------------------- -/

theorem ex3 : ⊢ {| λs => s x = 10 ∧ s y = 1|}
                  (x <~ x + y) ;;
                  (x <~ x + y)
                {| λs => s x = 12 |}
  := by
  apply vc'_sound; simp_all [aval, upd]

/- ----------------------------------------------------------------------------------------------- -/

theorem ex4 : ⊢ {| tt |}
                WHILE {-@ tt @-} true DO
                  Skip
                END
                {| ff |}
  := by
  apply vc'_sound
  simp_all [vc', bval]

/- ----------------------------------------------------------------------------------------------- -/

theorem ex_loop :
  ⊢ {| tt |}
      (y <~ 0) ;;
      (x <~ 100) ;;
      (WHILE {-@ λ s => (100 ≤ s x) ∧ (0 ≤ s y) @-} y << z DO
         ((x <~ x + y) ;;
          (y <~ y + 1))
      END)
    {| λ s => 100 ≤ s x |}
  := by
  apply vc'_sound
  simp_all [aval, bval, upd]
  intros s hx _
  calc 100 <= s x       := by assumption
       _   <= s x + s y := by simp_arith []


/-
(x:=n, y:=0)
(x:=n-1, y:=1)
(x:=n-2, y:=2)
...
(x:=1, y := n-1)
(x:=0, y := n)
-/

theorem bob: ∀ {a b}, 0 < a -> a - 1 + (b + 1) = a + b := by
  intros a b a_pos
  -- cases a
  sorry

theorem ex_drain: ∀ {n: Nat},
 ⊢ {| λ s => s x = n |}
    (y <~ 0) ;;
    (WHILE {-@ λ s => s x + s y = n @-} 0 << x DO
      (x <~ x - 1) ;;
      (y <~ y + 1)
     END)
  {| λ s => s y = n |}
  := by
  intro n
  apply vc'_sound
  simp_all [aval, bval, upd]
  constructor
  . intros s xy_n  x_pos; simp [<-xy_n]; apply bob; assumption
  . intros s xy_n x_0; simp_all

/-
x:=n, y:=0
x:=n-1, y:=0 + n
x:=n-2, y:=0 + n + (n-1)
x:=n-3, y:=0 + n + (n-1) + (n-2)
...
x:=0, y:=0 + n + (n-1) + ... + 1
-/

theorem imp_sum' :
  ⊢ {| λ s => s "x" = n |}
      (y <~ 0) ;;
      (WHILE {-@ wsum_inv n @-} (0 << x) DO
        (y <~ y + x) ;;
        (x <~ x - 1)
       END)
    {| λ s => s "y" = sum n |}
  := by
  apply vc'_sound
  simp_all [aval, bval, wsum_inv, upd]
  constructor <;> repeat constructor
  . case a.left =>
    intros
    rename_i s _ _
    generalize hx : s x = vx
    cases vx <;> simp_all [sum, Nat.add_assoc]
  . case a.right =>
    intros
    rename_i s _ _
    generalize hx : s x = vx
    cases vx <;> simp_all [sum, Nat.add_assoc]
