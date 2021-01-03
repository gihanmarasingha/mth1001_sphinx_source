.. _sec_recursion:

***********************
Recursion and Induction
***********************

Inductive types
===============

In Lean, mathematical object are defined as inductive types. The most familiar example is the type
``ℕ`` of natural numbers.

For ``x`` to be a natural number means that ``x`` is zero or that ``x`` is the 'successor' of a 
natural number.

The natural number type is declared in Lean by the following code.

.. code-block:: lean

  namespace hidden
  -- BEGIN  
  inductive nat : Type
  | zero : nat
  | succ : nat → nat
  -- END
  end hidden

This states that ``nat`` has two constructors: 1) ``nat.zero`` a function that takes no arguments
and returns a natural number and 2) ``nat.succ`` a function that takes a natural number and returns
anoter natrual number.

Though I refer to ``nat.zero`` and ``nat.succ`` as functions, there is no 'body' to these functions.
That is, if you ask 'what natural number is given by ``nat.succ (nat.zero)``, the answer is simply
``nat.succ (nat.zero)`` itself. Of course, we are meant to think of this number as :math:`1`.
Likewise, we should think of ``nat.succ (nat.succ nat.zero)`` as :math:`2`. However, these are
purely conveniences for human consumption.

We want to do more than merely define types. We want to define functions on those types.

.. code-block:: lean

  namespace hidden

  set_option pp.structure_projections false

  inductive nat : Type
  | zero : nat
  | succ : nat → nat

  local notation ℕ := nat

  namespace nat

  -- BEGIN
  def add_two (n : ℕ) : ℕ :=
  nat.rec_on n (succ (succ zero)) (assume (m h : ℕ), succ h)

  #reduce add_two (succ zero)

  -- END

  end nat

  end hidden