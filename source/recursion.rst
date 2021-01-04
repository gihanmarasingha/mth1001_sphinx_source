.. _sec_recursion:

***********************
Recursion and Induction
***********************

Functions of one natural number variable
========================================

In Lean, mathematical object are expressed as inductive types. The most familiar example is the type
``nat`` of natural numbers. This type is provided in core Lean and has the alternative notation
``ℕ`` (written ``\N``). We'll recreate this type, calling it ``mynat``

For ``x`` to be a natural number means that ``x`` is zero or that ``x`` is the 'successor' of a 
natural number. Every natural number can be constructed by repeated application of these two
principles.

The following Lean declaration defines the natural number type.

.. code-block:: lean

  namespace hidden
  -- BEGIN  
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  -- END
  end hidden

This states that ``mynat`` has two constructors: 1) ``mynat.zero``, a function that takes no arguments
and returns a natural number, and 2) ``mynat.succ``, a function that takes a natural number and returns
another natural number. These names can be abbreviated to ``zero`` and ``succ`` in the ``mynat``
'namespace'.

Though I refer to ``zero`` and ``succ`` as functions, there is no 'body' to these functions.
That is, if you ask 'what natural number is given by ``succ (zero)``, the answer is simply
``succ (zero)`` itself. Of course, we are meant to think of this number as :math:`1`.
Likewise, we should think of ``succ (succ zero)`` as :math:`2`. However, these are
purely conveniences for human consumption.

A Lean 'notation declaration' permits the use of the  alternative notation ``ℕ`` for ``mynat``.

.. code-block:: lean

  namespace hidden
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  -- BEGIN
  local notation ℕ := mynat
  -- END
  end hidden

We want to do more than declare types. We want to define functions on those types. To define
a function ``f : ℕ → ℕ`` (or, more generally, ``f : ℕ → α`` for a type ``α``), it suffices to 
define 1) ``f(zero)`` and 2) ``f(succ n)``, given ``n : ℕ``. The recursive construction of ``ℕ``
permits us to define ``f(succ n)`` in terms of ``f(n)``.

Using the above ideas, we define a function ``double : ℕ → ℕ`` that doubles its input.
Clearly, we should take ``double(zero) = zero``. What about ``double (succ n)``? For the moment,
imagine we have already defined notions such as addition and multiplication. We want
``double (succ n)`` to be :math:`2(n+1) = 2n + 2`. That is, we require
``double (succ n) = succ (succ (double n))``.

The easiest way to write the recursive definition of ``double`` in Lean is to use the following 
syntax.

.. code-block:: lean

  namespace hidden
  set_option pp.structure_projections false
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  local notation ℕ := mynat
  namespace mynat

  -- BEGIN
  def double : ℕ → ℕ
  | zero      := zero
  | (succ n)  := succ(succ(double n))
  -- END

  end mynat
  end hidden

Each constructor gives rise to an equation.

.. code-block:: lean

  namespace hidden
  set_option pp.structure_projections false
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  local notation ℕ := mynat
  namespace mynat
  def double (n : ℕ) : ℕ := mynat.rec_on n zero (λ _ h, h.succ.succ)

  -- BEGIN
  example : double zero = zero := rfl
  example (n : ℕ) : double (succ n) = succ (succ (double n)) := rfl
  -- END

  end mynat
  end hidden

Values of the function can be computed using ``#reduce``. For instance,
``#reduce double (succ zero)`` returns ``succ (succ zero)``.

Likewise, ``#reduce double (double (succ zero))`` returns ``succ (succ (succ (succ zero)))``.
In this spirit of Lean, these computations can be thought of as theorems, proved by reflexivity.

.. code-block:: lean

  namespace hidden
  set_option pp.structure_projections false
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  local notation ℕ := mynat
  namespace mynat
  def double (n : ℕ) : ℕ := mynat.rec_on n zero (λ _ h, h.succ.succ)

  -- BEGIN
  example : double(succ zero) = (succ(succ zero)) := rfl
  -- END

  end mynat
  end hidden

It's awkward to read and write long sequences of ``succ`` s. Lean's built-in ``nat`` type comes
with the facility to use decimal numerals to represent natural numbers. Inter alia, the following
arcane commands (you don't need to understand what they do!) set up coercions between ``mynat``
type and the built-in ``nat`` type.

.. code-block:: lean

  namespace hidden
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  local notation ℕ := mynat
  -- BEGIN
  instance coe₁ : has_coe mynat nat :=
    ⟨λ n, mynat.rec_on n 0 (λ _ h, h + 1)⟩
  instance coe₂ : has_coe nat mynat :=
    ⟨λ n, nat.rec_on n mynat.zero (λ _ h, h.succ)⟩
  instance : has_repr ℕ :=
    ⟨λ n, nat.repr $ nat.rec_on n 0 (λ _ h, h + 1)⟩
  instance : has_zero mynat := ⟨mynat.zero⟩
  instance : has_one ℕ  := ⟨mynat.succ 0⟩
  instance : has_add ℕ :=
    ⟨λ x, mynat.rec_on x id (λ _ h, λ y, mynat.succ (h y))⟩
  -- END
  end hidden

After issuing these incantations, we can use numerals for our ``mynat`` type.
The ``#eval`` command below is not part of Lean's trusted kernel, but
allows more efficient computation than ``#reduce``.

.. code-block:: lean

  namespace hidden
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  local notation ℕ := mynat
  instance coe₁ : has_coe mynat nat := ⟨λ n, mynat.rec_on n 0 (λ _ h, h + 1)⟩
  instance coe₂ : has_coe nat mynat := ⟨λ n, nat.rec_on n mynat.zero (λ _ h, h.succ)⟩
  instance : has_repr ℕ := ⟨λ n, nat.repr $ nat.rec_on n 0 (λ _ h, h + 1)⟩
  instance : has_zero mynat := ⟨mynat.zero⟩
  instance : has_one ℕ  := ⟨mynat.succ 0⟩
  instance : has_add mynat := ⟨λ x, mynat.rec_on x id (λ _ h, λ y, mynat.succ (h y))⟩
  namespace mynat
  set_option pp.structure_projections false
  def double (n : ℕ) : ℕ := mynat.rec_on n 0 (λ _ h, h.succ.succ)

  -- BEGIN
  example : double 1 = 2 := rfl
  example : double 7 = 14 := rfl
  #reduce double 2 -- displays `succ (succ (succ (succ zero)))`
  #eval double 25 -- displays `50`
  -- END

  end mynat
  end hidden

How might you define a function ``pow2 : ℕ → ℕ`` so that :math:`\operatorname{pow2}(n)=2^n`?

For the moment, pretend we have defined exponentiaion and multiplication. We require
``pow2(0) = 1`` and ``pow2(n+1) = 2^(n+1) = 2^n * 2 = double(pow2(n))``, for every ``n : ℕ``.
This translates into the following definition.

.. code-block:: lean

  namespace hidden
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  local notation ℕ := mynat
  instance coe₁ : has_coe mynat nat := ⟨λ n, mynat.rec_on n 0 (λ _ h, h + 1)⟩
  instance coe₂ : has_coe nat mynat := ⟨λ n, nat.rec_on n mynat.zero (λ _ h, h.succ)⟩
  instance : has_repr ℕ := ⟨λ n, nat.repr $ nat.rec_on n 0 (λ _ h, h + 1)⟩
  instance : has_zero mynat := ⟨mynat.zero⟩
  instance : has_one ℕ  := ⟨mynat.succ 0⟩
  instance : has_add mynat := ⟨λ x, mynat.rec_on x id (λ _ h, λ y, mynat.succ (h y))⟩
  namespace mynat
  set_option pp.structure_projections false

  def double (n : ℕ) : ℕ := mynat.rec_on n 0 (λ _ h, h.succ.succ)

  -- BEGIN
  def pow2 : ℕ → ℕ
  | 0         := succ 0
  | (succ n)  := double (pow2 n)
  -- END

  end mynat
  end hidden

As with ``double``, each line of the definition of ``pow2`` gives rise to an equation.

.. code-block:: lean

  namespace hidden
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  local notation ℕ := mynat
  instance coe₁ : has_coe mynat nat := ⟨λ n, mynat.rec_on n 0 (λ _ h, h + 1)⟩
  instance coe₂ : has_coe nat mynat := ⟨λ n, nat.rec_on n mynat.zero (λ _ h, h.succ)⟩
  instance : has_repr ℕ := ⟨λ n, nat.repr $ nat.rec_on n 0 (λ _ h, h + 1)⟩
  instance : has_zero mynat := ⟨mynat.zero⟩
  instance : has_one ℕ  := ⟨mynat.succ 0⟩
  instance : has_add mynat := ⟨λ x, mynat.rec_on x id (λ _ h, λ y, mynat.succ (h y))⟩
  namespace mynat
  set_option pp.structure_projections false
  def double (n : ℕ) : ℕ := mynat.rec_on n 0 (λ _ h, h.succ.succ)
  def pow2 (n : ℕ) : ℕ := mynat.rec_on n 1 (λ _ h, double h)

  -- BEGIN
  example : pow2 0 = succ 0 := rfl
  example (n : ℕ) : pow2 (succ n) = double (pow2 n) := rfl
  -- END

  end mynat 
  end hidden

We can compute values of ``pow2`` using ``#reduce`` or ``#eval``. For instance, ``#eval pow2 8``
displays ``256``. Alternatively, we can express this as a theorem.

.. code-block:: lean

  namespace hidden
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  local notation ℕ := mynat
  instance coe₁ : has_coe mynat nat := ⟨λ n, mynat.rec_on n 0 (λ _ h, h + 1)⟩
  instance coe₂ : has_coe nat mynat := ⟨λ n, nat.rec_on n mynat.zero (λ _ h, h.succ)⟩
  instance : has_repr ℕ := ⟨λ n, nat.repr $ nat.rec_on n 0 (λ _ h, h + 1)⟩
  instance : has_zero mynat := ⟨mynat.zero⟩
  instance : has_one ℕ  := ⟨mynat.succ 0⟩
  instance : has_add mynat := ⟨λ x, mynat.rec_on x id (λ _ h, λ y, mynat.succ (h y))⟩
  namespace mynat
  set_option pp.structure_projections false
  def double (n : ℕ) : ℕ := mynat.rec_on n 0 (λ _ h, h.succ.succ)
  def pow2 (n : ℕ) : ℕ := mynat.rec_on n 1 (λ _ h, double h)

  -- BEGIN
  example : pow2 8 = 256 := rfl
  -- END

  end mynat 
  end hidden


Some more general theorems can be proved by reflexivity. Lean simply applies the second constructor
of ``pow2`` two times to prove the following, which is equivalent to the mathematical statement
:math:`2^{n+2} = (2^n\times2)\times2`.

.. code-block:: lean

  namespace hidden
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  local notation ℕ := mynat
  instance coe₁ : has_coe mynat nat := ⟨λ n, mynat.rec_on n 0 (λ _ h, h + 1)⟩
  instance coe₂ : has_coe nat mynat := ⟨λ n, nat.rec_on n mynat.zero (λ _ h, h.succ)⟩
  instance : has_repr ℕ := ⟨λ n, nat.repr $ nat.rec_on n 0 (λ _ h, h + 1)⟩
  instance : has_zero mynat := ⟨mynat.zero⟩
  instance : has_one ℕ  := ⟨mynat.succ 0⟩
  instance : has_add mynat := ⟨λ x, mynat.rec_on x id (λ _ h, λ y, mynat.succ (h y))⟩
  namespace mynat
  set_option pp.structure_projections false
  def double (n : ℕ) : ℕ := mynat.rec_on n 0 (λ _ h, h.succ.succ)
  def pow2 (n : ℕ) : ℕ := mynat.rec_on n 1 (λ _ h, double h)

  -- BEGIN
  example (n : ℕ) :
    pow2(succ (succ n)) = double(double(pow2 n)) := rfl
  -- END

  end mynat 
  end hidden


Taking this idea one step further, we can iterate exponentiation.

.. code-block:: lean

  namespace hidden
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  local notation ℕ := mynat
  instance coe₁ : has_coe mynat nat := ⟨λ n, mynat.rec_on n 0 (λ _ h, h + 1)⟩
  instance coe₂ : has_coe nat mynat := ⟨λ n, nat.rec_on n mynat.zero (λ _ h, h.succ)⟩
  instance : has_repr ℕ := ⟨λ n, nat.repr $ nat.rec_on n 0 (λ _ h, h + 1)⟩
  instance : has_zero mynat := ⟨mynat.zero⟩
  instance : has_one ℕ  := ⟨mynat.succ 0⟩
  instance : has_add mynat := ⟨λ x, mynat.rec_on x id (λ _ h, λ y, mynat.succ (h y))⟩
  namespace mynat
  set_option pp.structure_projections false
  def double (n : ℕ) : ℕ := mynat.rec_on n 0 (λ _ h, h.succ.succ)
  def pow2 (n : ℕ) : ℕ := mynat.rec_on n 1 (λ _ h, double h)

  --BEGIN
  def rep_pow2 : ℕ → ℕ
  | 0         := 0
  | (succ n)  := pow2 (rep_pow2 n)
  -- END

  end mynat 
  end hidden

By reflexivity, we extract simple results.

.. code-block:: lean

  namespace hidden
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  local notation ℕ := mynat
  instance coe₁ : has_coe mynat nat := ⟨λ n, mynat.rec_on n 0 (λ _ h, h + 1)⟩
  instance coe₂ : has_coe nat mynat := ⟨λ n, nat.rec_on n mynat.zero (λ _ h, h.succ)⟩
  instance : has_repr ℕ := ⟨λ n, nat.repr $ nat.rec_on n 0 (λ _ h, h + 1)⟩
  instance : has_zero mynat := ⟨mynat.zero⟩
  instance : has_one ℕ  := ⟨mynat.succ 0⟩
  instance : has_add mynat := ⟨λ x, mynat.rec_on x id (λ _ h, λ y, mynat.succ (h y))⟩
  namespace mynat
  set_option pp.structure_projections false
  def double (n : ℕ) : ℕ := mynat.rec_on n 0 (λ _ h, h.succ.succ)
  def pow2 (n : ℕ) : ℕ := mynat.rec_on n 1 (λ _ h, double h)
  def rep_pow2 (n : ℕ) : ℕ := mynat.rec_on n 0 (λ _ h, pow2 h)

  --BEGIN
  example : rep_pow2 0 = 0 := rfl
  example (n : ℕ) : rep_pow2 (succ n) = pow2 (rep_pow2 n) := rfl

  example : rep_pow2 3 = pow2(pow2(pow2 0)) := rfl
  example : rep_pow2 4 = pow2(pow2(pow2(pow2 0))) := rfl
  example : rep_pow2 5 = pow2(pow2(pow2(pow2(pow2 0)))) := rfl
  -- END
  end mynat 
  end hidden

On my computer, ``#reduce rep_pow2 4`` displays 16 ``succ`` s followwed by ``zero``
(i.e. the number 16), but ``#reduce rep_pow2 5`` returns an
error message complaining about deep recursion and lack of stack space. The more efficient
``#eval rep_pow2 5`` displays ``65536``. However, even ``#eval`` cannot compute ``rep_pow 6``,
a number with 19729 digits.

Functions of two natural number variables
=========================================

Mathematically, a recursive definition of addition on ``ℕ`` can be expressed via two equations,
:math:`0 + y = 0` and :math:`\operatorname{succ}(x) + y = \operatorname{succ}(x+y)`.

.. code-block:: lean

  namespace hidden
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  local notation ℕ := mynat
  instance : has_zero mynat := ⟨mynat.zero⟩
  namespace mynat

  -- BEGIN
  def add : ℕ → ℕ → ℕ
  | 0         y   := y
  | (succ x)  y   := succ (add x y)
  -- END

  end mynat
  end hidden

As with ``double`` and ``pow2``, we extract the defining equations of ``add`` as theorems.

.. code-block:: lean

  namespace hidden
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  local notation ℕ := mynat
  instance : has_zero mynat := ⟨mynat.zero⟩
  namespace mynat
  def add (x : ℕ) : ℕ → ℕ := mynat.rec_on x id (λ _ h, λ y, succ (h y))
  instance : has_add mynat := ⟨add⟩

  -- BEGIN
  example (y : ℕ) : add 0 y = y := rfl
  example (x y : ℕ) : add (succ x) y = succ (add x y) := rfl
  -- END

  end mynat
  end hidden

We can prove numerical results by reflexivity.

.. code-block:: lean


  namespace hidden
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  local notation ℕ := mynat
  instance coe₁ : has_coe mynat nat := ⟨λ n, mynat.rec_on n 0 (λ _ h, h + 1)⟩
  instance coe₂ : has_coe nat mynat := ⟨λ n, nat.rec_on n mynat.zero (λ _ h, h.succ)⟩
  instance : has_repr ℕ := ⟨λ n, nat.repr $ nat.rec_on n 0 (λ _ h, h + 1)⟩
  instance : has_zero mynat := ⟨mynat.zero⟩
  instance : has_one ℕ  := ⟨mynat.succ 0⟩
  namespace mynat
  def add (x : ℕ) : ℕ → ℕ := mynat.rec_on x id (λ _ h, λ y, succ (h y))
  instance : has_add mynat := ⟨add⟩

  -- BEGIN
  example : add 10 15 = 25 := rfl
  -- END

  end mynat
  end hidden


We can ask Lean to use the familar ``+`` notation for addition via special commands, as before.
Consequently, we rewrite the defining equations using this notation.

.. code-block:: lean

  namespace hidden
  inductive mynat : Type
  | zero : mynat
  | succ : mynat → mynat
  local notation ℕ := mynat
  namespace mynat
  def add (x : ℕ) : ℕ → ℕ := mynat.rec_on x id (λ _ h, λ y, succ (h y))
  instance : has_add mynat := ⟨add⟩
  instance : has_zero mynat := ⟨zero⟩

  -- BEGIN
  lemma zero_add (y : ℕ) : 0 + y = y := rfl
  lemma succ_add (x y : ℕ) : (succ x) + y = succ (x + y) := rfl
  -- END

  end mynat

  end hidden
