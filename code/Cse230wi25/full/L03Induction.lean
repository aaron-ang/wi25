set_option pp.fieldNotation false

/- @@@
# Datatypes and Recursion

This material is based on

- Chapter 2 of [Concrete Semantics](http://www.concrete-semantics.org/)
- Induction Exercises by [James Wilcox](https://jamesrwilcox.com/InductionExercises.html)

@@@-/

namespace MyNat

inductive Nat where
  | zero : Nat
  | succ : Nat -> Nat
  deriving Repr

open Nat

def add (n m : Nat) : Nat :=
  match n with
  | zero => m
  | succ n' => succ (add n' m)

-- tail-recursive version
def add_tr(n m : Nat) : Nat :=
  match m with
  | zero => n
  | succ m' => add_tr (succ n) m'

#eval add (succ (succ zero)) (succ zero)

#eval add_tr (succ (succ zero)) (succ zero)

example : add (succ (succ zero)) (succ zero) = add_tr (succ (succ zero)) (succ zero) := rfl

/- @@@
## Trick 1: Helper Lemmas

### Example `add_comm`

Let's try to prove that `add` is commutative; that is, that the order of arguments does not matter.

If we plunge into trying a direct proof-by-induction, we get stuck at two places.

1. What is the value of `add m zero` ?
2. What is the value of `add m (succ n)` ?

It will be convenient to have **helper lemmas** that tell us that

1. `∀ m, add m zero = m`
2. `∀ n m, add n (succ m) = succ (add n m)`

@@@ -/

/- @@@ START:CUT @@@ -/
theorem add_zero: ∀ (n : Nat), add n zero = n := by
  intros n
  induction n
  . case zero => simp [add]
  . case succ => simp [add, *]

theorem add_succ: ∀ (n m : Nat), add n (succ m) = succ (add n m) := by
  intros n
  induction n
  . case zero => simp [add]
  . case succ => simp [add, *]
/- @@@ END:CUT @@@ -/

theorem add_comm : ∀ (n m: Nat), add n m = add m n := by
  intros n
  induction n
/- @@@ START:SORRY @@@-/
  . case zero => simp [add, add_zero]
  . case succ n' ih => simp [add, ih, add_succ]
/- @@@ END:SORRY @@@-/

end MyNat

open List

/- @@@
### Example `rev_rev`

Lets look at another example where we will need helper lemmas.

@@@ -/


/-@@@
**Appending lists**
@@@-/

def app {α : Type} (xs ys: List α) : List α :=
  match xs with
  | [] => ys
  | x::xs' => x :: app xs' ys

example : app [0,1,2] [3,4,5] = [0,1,2,3,4,5] := rfl

/-@@@
**Reversing lists**
@@@-/

def rev {α : Type} (xs: List α) : List α :=
  match xs with
  | [] => []
  | x :: xs' => app (rev xs') [x]

example : rev [0,1,2,3] = [3,2,1,0] := rfl

/- @@@
Now, lets _prove_ that the above was not a fluke:
if you reverse a list *twice* then you get back
the original list.
@@@ -/

/- @@@ START:CUT @@@ -/
@[simp]
theorem app_nil : ∀ {α : Type} (xs: List α), app xs nil = xs := by
  intro α xs
  induction xs
  case nil => rfl
  case cons => simp [app, *]

theorem app_assoc : ∀ {α : Type} (xs ys zs: List α), app (app xs ys) zs = app xs (app ys zs) := by
  intros  α xs ys zs
  induction xs
  case nil => rfl
  case cons => simp [app, *]

theorem rev_app : ∀ {α : Type} (xs ys: List α), rev (app xs ys) = app (rev ys) (rev xs) := by
  intro α xs ys
  induction xs
  case nil => simp [app, rev, app_nil]
  case cons x xs' ih => simp [app, rev, ih, app_assoc]
/- @@@ END:CUT @@@ -/

theorem rev_rev : ∀ {α : Type} (xs: List α), rev (rev xs) = xs := by
  intro α xs
  induction xs
  case nil  => rfl
  case cons x xs' ih => simp [rev, rev_app, app, *]

/- @@@
Yikes. We're stuck again. What helper lemmas could we need?









## Trick 2: Generalizing the Variables

Consider the below variant of `add`.

How is it different than the original?
@@@ -/

open MyNat.Nat

def itadd (n m: MyNat.Nat) : MyNat.Nat :=
  match n with
  | zero => m
  | succ n' => itadd n' (succ m)

example : itadd (succ (succ zero)) (succ zero) = succ (succ (succ zero)):= by rfl

/- @@@
Lets try to prove that `itadd` is equivalent to `add`.
@@@ -/

theorem itadd_eq : ∀ (n m: MyNat.Nat), itadd n m = MyNat.add n m := by
  intros n m
  induction n
/- @@@ START:CUT @@@ -/
  generalizing m
/- @@@ END:CUT @@@ -/
  case zero => simp [MyNat.add, itadd]
  case succ n' ih => simp [MyNat.add, MyNat.add_succ, itadd, ih]

/- @@@
Ugh! Why does the proof fail???

We are left with the goal

```lean
m n' : MyNat.Nat
ih : itadd n' m = MyNat.add n' m
⊢ itadd n' (succ m) = succ (MyNat.add n' m)
```

**IH is too weak**

In the goal above, the `ih` *only* talks about `itadd n m` but *says nothing*
about `itadd n (succ m)`. In fact, the IH should be true **for all** values of `m`
as we **do not really care** about `m` in this theorem. That is, we want to tell
`lean` that the `ih` should be

```lean
m n' : MyNat.Nat
ih : ∀ m, itadd n' m = MyNat.add n' m
⊢ itadd n' (succ m) = succ (MyNat.add n' m)
```

**Generalizing**
We can do so, by using the `induction n generalizing m` which tells `lean` that

- we are doing induction on `n` and
- we *don't care* about the value of `m`

Now, go and see what the `ih` looks like in the `case succ ...`

This time we can **actually use** the `ih` and so the proof works.
@@@ -/


/- @@@
## Trick 3: Generalizing the Induction Hypothesis

Often, the thing you want to prove is not "inductive" by itself. Meaning, that
you want to prove a goal `∀n. P(n)` but in fact you need to prove something stronger
like `∀n. P(n) /\ Q(n)` or even `∀n m, Q(n, m)` which then implies your goal.


### Example: Tail-Recursive `sum`
@@@ -/

def sum (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 => n + sum n' -- not tail-recurisve because we are operating on the result of the recursive call

/- @@@

**Tail-Recursively Summing**

In an _iterative_ language you might write a **loop**
to sum the numbers `n + n-1 + ... + 0` e.g.

```rust
fn sum_tr(mut n: Nat) -> Nat {
  let mut acc = 0;
  while let succ m = n {
    acc += n;
    n = m
  }
  acc
}
```

We can write the above with **tail-recursion**

- The recursive call is the "last thing" the function does
- That is, the recursive result is returned without any further computation

**NOTE:** Go and look at `itadd`; is it tail recursive?

@@@-/

def sum_tr (n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | n' + 1 => sum_tr n' (n + acc)

def sum' (n: Nat) := sum_tr n 0

/- @@@

Lets try to prove that `sum` and `sum'` always compute the *same result*.

@@@ -/

theorem sum'_eq: ∀ n acc, sum_tr n acc = sum n + acc := by
  intros n acc
  induction n generalizing acc
  case zero => simp [sum_tr, _root_.sum]
  case succ => simp_arith [sum_tr, _root_.sum, *]

theorem sum_eq_sum' : ∀ n, sum n = sum' n := by
  simp [sum', sum'_eq]

/- @@@
Oops, we are stuck.

We need to know something about `sum_tr n' (n' + 1)` but what?

Can you think of a suitable helper lemma, which would let us directly
prove `sum_eq_sum'`?

```lean
theorem helper: ∀ n acc, sum_tr n acc = sum n + acc := by ...

theorem sum_eq_sum' : ∀ n, sum' n = sum n := by
  intros
  simp_arith [sum', helper]
```

@@@ -/

/- @@@ START:CUT @@@ -/

theorem sum_eq_sum'' : ∀ n, sum' n = sum n := by
  simp_arith [sum', sum'_eq]
/- @@@ END:CUT @@@ -/


open List

/- @@@
### Example: Tail-Recursive `sum_list`
@@@ -/

/- @@@
**Summing a List***
@@@-/

def sum_list (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x ::xs' => x + sum_list xs'

/- @@@
**Tail-Recursively Summing a List***

In an _iterative_ language you might write a **loop**
to sum the elements of a list, e.g.

```rust
fn sum_list(xs: List<Nat>) {
  let mut acc = 0;
  while let cons x ys = xs {
    acc += x;
    xs = ys
  }
  return acc
}
```

We can write the above with *tail-recursion* (where the recursive call is the "last thing")
that the function does. (Hint: Go and look at `itadd`; is it tail recursive?)

@@@-/

def sum_list_tr (xs : List Nat) (acc : Nat): Nat :=
  match xs with
  | [] => acc
  | x :: ys => sum_list_tr ys (acc + x)

def sum_list' (xs: List Nat) := sum_list_tr xs 0

/- @@@
Can you figure out a suitable helper lemma that would let us complete
the proof of `sum_list_eq_sum_list'` below?
@@@ -/

theorem sum_list'_eq : ∀ (xs acc), sum_list_tr xs acc = sum_list xs + acc := by
  intros xs
  induction xs
  case nil => simp[sum_list_tr, sum_list]
  case cons => simp_arith [sum_list_tr, sum_list, *]

theorem sum_list_eq_sum_list' : ∀ xs, sum_list' xs = sum_list xs := by
  simp_arith [sum_list', sum_list'_eq]


/- @@@
### Example: Tail-Recursive Reverse
@@@ -/

def rev_tr {α : Type} (xs acc: List α) : List α :=
  match xs with
  | [] => acc
  | x ::xs' => rev_tr xs' (x :: acc)

def rev' (xs: List α) := rev_tr xs []

example : rev' [0,1,2,3] = [3,2,1,0] := by rfl

/- @@@
Can you figure out a suitable helper lemma `rev_tr_app` that would let us complete
the proof of `rev_eq_rev'` below?
@@@ -/

/- @@@ START:CUT @@@ -/
theorem rev_tr_app : ∀ {α : Type} (xs ys: List α), rev_tr xs ys = app (rev xs) ys := by
  intros α xs ys
  induction xs generalizing ys
  case nil => rfl
  case cons x xs' ih => simp [rev_tr, ih, rev, app_assoc, app]
/- @@@ END:CUT @@@ -/

theorem rev_eq_rev' : ∀ {α : Type} (xs: List α), rev' xs = rev xs := by
/- @@@ START:SORRY @@@ -/
  simp [rev', rev_tr_app] -- added @[simp] to app_nil
/- @@@ END:SORRY @@@ -/


/- @@@
### Example: Tail-Recursive Evaluator

**Arithmetic Expressions**
@@@ -/

inductive Aexp : Type where
  | const : Nat -> Aexp
  | plus  : Aexp -> Aexp -> Aexp
  deriving Repr

open Aexp

def two_plus_three := plus (const 2) (const 3)

/- @@@
**Evaluating Expressions**
@@@-/

def eval (e: Aexp) : Nat :=
  match e with
  | const n => n
  | plus e1 e2 => eval e1 + eval e2

#eval eval two_plus_three

def eval_acc (e: Aexp) (acc: Nat) : Nat :=
  match e with
  | const n => n + acc
  | plus e1 e2 => eval_acc e2 (eval_acc e1 acc)

def eval' (e: Aexp) := eval_acc e 0

example : eval' two_plus_three = eval two_plus_three := by rfl

/- @@@
### QUIZ: Is `eval_acc` tail recursive? Ans: Yes, because the recursive call is the last thing the function does.

Lets try to prove that `eval'` and `eval` are "equivalent".

Can you figure out a suitable helper lemma that would let us complete
the proof of `eval_eq_eval'`?
@@@ -/

/- @@@ START:CUT @@@ -/
theorem eval_acc_eq : ∀ e, eval_acc e acc = eval e + acc := by
  intros e
  induction e generalizing acc
  case const => simp_arith [eval, eval_acc]
  case plus => simp_arith [eval, eval_acc, *]
/- @@@ END:CUT @@@ -/

theorem eval'_eq_eval : ∀ e, eval e = eval' e := by
  simp [eval', eval_acc_eq]




/- @@@
## Trick 4: Functional Induction

Based on [Joachim Breitner's notes on Functional Induction](https://lean-lang.org/blog/2024-5-17-functional-induction/)

@@@ -/

def len (xs: List α) : Nat :=
  match xs with
  | [] => 0
  | _::xs' => 1 + len xs'

def alt (xs ys : List α) : List α :=
  match xs, ys with
  | [], ys => ys
  | xs, [] => xs
  | x::xs, y::ys => x :: y :: alt xs ys

#eval alt [1,2,3,4] [10,20,30]

/- @@@
First, lets try a "brute force" proof.
@@@ -/

theorem alt_len : ∀ {α : Type} (xs ys : List α), len (alt xs ys) = len xs + len ys := by
/- @@@ START:SORRY @@@ -/
  intros α xs ys
  induction xs generalizing ys
  . case nil =>
    simp [alt, len]
  . case cons x xs' ih =>
    cases ys
    . case nil => simp [alt, len]
    . case cons y ys' => simp_arith [alt, len, *]
/- @@@ END:SORRY @@@ -/

/- @@@
Instead, it can be easier to do the *same* induction as mirrors the recursion in `alt`
@@@ -/

theorem alt_len' : ∀ {α : Type} (xs ys : List α), len (alt xs ys) = len xs + len ys := by
  intros α xs ys
  induction xs, ys using alt.induct
  . case case1 => simp [alt, len]
  . case case2 => simp [alt, len]
  . case case3 => simp_all_arith [alt, len]
