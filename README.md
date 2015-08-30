# Assign-Recurse-Flow (ARF)

This is a tiny language calculus intended to research how to efficiently type-check recursive functions when performing a full-program analysis.

Such a procedure is important for full-program type checkers such as the [plint] type-checker I am writing for Python source code.

This research is now complete. Read on for details if you are interested in the theory. On the other hand if you just want to try out the ARF type checker, skip down to the "Try ARF!" section below.

[plint]: https://github.com/davidfstr/plint

## Abstract

I have an algorithm that can fully type a recursive assignment-based program in **O(m·n)** worst case time, where:

* **m** is the total number of functions in the program and
* **n** is number of functions in the largest mutually recursive function group in the program.

## ARF Language

Below is an (inefficient and slightly contrived) Python program that tests whether a specified integer >= 0 is even or odd:

```
def main(args):
    k = int(args[0])
    result = is_even(k)
    return result

def is_even(n):
    if n == 0:
        k = True
        return k
    else:
        result = is_odd(n - 1)
        return result

def is_odd(n):
    if n == 0:
        k = False
        return k
    else:
        result = is_even(n - 1)
        return result

if __name__ == '__main__':
    import sys
    print(main(sys.argv[1:]))
```

If you save this as `is_even.py` then you can test whether an integer like `42` is even by running the command `python3 is_even.py 42`.

This same program in the ARF language would be written as:

```
def main(_):
    k = <int>               # AssignLiteral
    result = is_even(k)     # AssignCall
    return result           # Return

def is_even(n):
    if:                     # If
        k = <bool>          # AssignLiteral
        return k            # Return
    else:
        result = is_odd(n)  # AssignCall
        return result       # Return

def is_odd(n):
    if:                     # If
        k = <bool>          # AssignLiteral
        return k            # Return
    else:
        result = is_even(n) # AssignCall
        return result       # Return
```

Notice that various parts of the original Python program are erased in the ARF version, such as the condition of the if-statement and the specific values of literals like `True` and `False`. In particular anything that a flow-based type checker wouldn't care about is erased. This keeps the language focused on representing what such a type checker would see and need to evaluate.

It so happens that every possible ARF statement occurs in the above program, namely:

* **AssignLiteral**(target_var, literal_type)
* **AssignCall**(target_var, func_name, arg_var)
* **If**(then_block, else_block)
* **Return**(result_var)

There are a few additional constructs a type checker for a general purpose language must consider that ARF does not natively represent, namely loops and multi-parameter functions, but it is straightforward to extend the ARF language and type checker to support such constructs.

## Type Checking

Given an ARF program, it is the objective of the ARF type checker to determine, for each function and argument type passed, what type the function will return.

In the example ARF program above, the determined types are:

```
main(NoneType) -> bool
is_even(int) -> bool
is_odd(int) -> bool
```

Notice that there is no deduced return type for calls like `is_even(bool)` because no such calls were made during any possible execution of the program.

The naive strategy for deducing such return types is simply to execute the ARF program along all possible code paths. However if there are any functions that perform a recursive calls (to a function earlier on the call stack) then the type checker will go into an infinite loop, descending infinitely into the function call graph.

### Recursive Call Loops

A smarter solution is to detect, when executing a call, whether the call is a recursive call and then suspend execution along that code path if it is. Once the target of the recursive call has an initial approximation of its return type, the suspended execution path can be resumed with the approximate return type that was deduced. This may happen repeatedly as the approximate return type of the recursive call's target is refined over time.[^max-refinements-in-loop] This procedure is analogous to the way the fixed point of a loop would be computed.

[^max-refinements-in-loop]: At maximum there will be **t** refinements, where **t** is the number of types defined in the program. Currently **t** is bounded to exactly 3, since there are 3 builtin types (`NoneType`, `int`, and `bool`) and no user-defined types.

### Infinitely Recursive Call Loops

Another difficulty that arises is that a function may provably always go into an infinite loop[^provable-infinite-loop], which prevents deducing any specific approximate return type for the function. For example neither function in the following ARF program will ever terminate:

```
def infinite_loop_1(_):
    _ = infinite_loop_2(_)
    return _

def infinite_loop_2(_):
    _ = infinite_loop_1(_)
    return _
```

In the case of such provably non-terminating function, the type checker can use a special return type that indicates the function can never return. This special type is written as ⊥ and pronounced "bottom". When the type checker receives a ⊥ as a result of a call, it suspends execution of the calling statement block.

If all execution paths in a function are suspended due to a ⊥ then the function itself returns a ⊥.

[^provable-infinite-loop]: A function **f** provably goes into an infinite loop if, after executing all possible paths in the function, all of those paths were suspended due to recursive invocations of **f**. In that situation **f** is waiting on the suspended executions and the suspended executions are waiting on **f**, creating an unresolvable deadlock.

### Avoiding Exponential Time with Non-Recursive Calls

The above strategy is sufficient for type checking any ARF program in such a way that the type checker itself will never go into an infinite loop when checking a program. However the type checker may do a lot of unnecessary work.

Consider the following ARF program:

```
def f1(_):
    if:
        _ = f2(_)
    else:
        _ = f2(_)

def f2(_):
    if:
        _ = f3(_)
    else:
        _ = f3(_)

...

def f31(_):
    if:
        _ = f32(_)
    else:
        _ = f32(_)

def f32(_):
    pass  # no statements in block, returning NoneType
```

If you have **n** functions in a program following this pattern then type checking will take **O(2ⁿ)** time, which is clearly unacceptable.

The performance issue arises because functions **f<sub>2</sub>**..**f<sub>32</sub>** are needlessly type-checked multiple times. After such a function has returned with a final deduced return type, it is unnecessary to recheck it.

Therefore while type checking you can introduce a cache of all functions whose final return type has been deduced. If an attempt is made to call a function whose return type resides in the cache, the cached return type can be used immediately.

Such a caching strategy reduces the time to type-check a program in this pattern to **O(n)**. Much better.

### Avoiding Exponential Time with Recursive Calls

However the preceding caching strategy faces some challenges when working with recursive function calls, since recursive calls can suspend execution and thereby delay the computation of a function's *final* return type.

Consider the following ARF program:

```
def f1(_):
    if:
        _ = f1(_)
        return _
    else:
        if:
            _ = f2()
            return _
        else:
            if:
                _ = f3()
                return _
            else
                ... (up to f32)

def f2(_):
    ... (same statements as in f1)

...

def f32(_):
    if:
        ... (same statements as in f1)
    else:
        pass  # no statements in block, returning NoneType
```

In this program, every function calls every other function in the program. The last function additionally may return `NoneType`, which will eventually propagate to every other function's return type.

When type-checking function **f<sub>2</sub>**..**f<sub>32</sub>**, it is not possible to immediately deduce a final return type for the function because it depends on the return type of **f<sub>1</sub>**, which doesn't even have a first approximation by the time that **f<sub>2</sub>**..**f<sub>32</sub>** complete their execution the first time around.

It is the case, however, that any function **f** requires at most two executions of its body to fully determine its exact return type.[^max-two-executions-of-body] In the worst case, as demonstrated above, every function in the recursive function group must execute twice within its caller. In such a case the recursive function group executes in time **O(n²)**, where **n** is the number of functions in the recursive function group.

#### What about Recursive Calls in Series?

Consider the following ARF program:

```
def f1(_):
    if:
        if:
            _ = f1(_)
            ...
            _ = f32(_)
            return _
        else:
            if:
                _ = f2()
                ...
                _ = f32()
                _ = f1()
                return _
            else:
                if:
                    _ = f3()
                    ...
                    _ = f32()
                    _ = f1()
                    ...
                    _ = f2()
                    return _
                else
                    ... (up to f32)
    else:
        pass  # no statements in block, returning NoneType

def f2(_):
    ... (same statements as in f1)

...

def f32(_):
    ... (same statements as in f1)
```

This program still executes in **O(n²)** time<sup>†</sup>, where **n** is the number of functions in the recursive function group, since my previous statements about evaluating recursion function groups still apply.

† However an **O(n²)** total execution time is misleading here since it incorrectly assumes that the average function size is constant and not related to **n**. Here however each function contains **O(n²)** statements, based on the pattern of construction. Therefore the total execution time of a program written in this pattern is actually **O((n²)²) = O(n⁴)**.

### Summarizing the Worst Case Time

Considering all of the prior discussion, a program is made of a set of functions, with certain function subsets being mutually recursive. These mutually recursive functions groups are non-overlapping (because otherwise they would be in the same group). Therefore there can be at most **O(m/n)** recursive function groups, where **m** is the total number of functions in the program and **n** is the size (i.e. number of functions in) the largest recursive group.

Each recursive function group takes at worst **O(n²)** time to execute, where **n** is the size of the group, as mentioned in prior discussions.

When a program with **m** functions contains no recursive functions invocations, it takes **O(m)** to execute, since every function body only needs to be executed once.

When a program containing a mix of both recursive and non-recursive functions is executed, it takes (at worst) time:

* (Max # recursive function groups)·(Worst case time for the largest group) + (Worst case time for program if all functions were non-recursive) =
* O(m/n)·O(n²) + O(m) =
* O((m/n)(n²) + m) =
* O(m·n + m) =
* **O(m·n)**

QED.

## Try ARF!

Enough theory. Try the ARF type checker yourself on some sample programs!

### Build

* Install Make.
* Install OPAM and OCaml 4.02.1.
    * On OS X, run `brew install opam` to get OPAM.
    * With OPAM, run <tt>opam switch 4.02.1</tt> and <tt>eval &#x60;opam config env&#x60;</tt>
* Run `make deps` to install remaining OCaml dependencies.
* Run `make test` to build ARF and run the automated tests.

### Run

There are a series of sample files in the `samples/` directory of the ARF project. You can run samples using a command like:

```
./Arf.native samples/is_even.arf
```

That will type-check the specified ARF program and output the deduced return types of all functions:

```
main(NoneType) -> bool
is_even(int) -> bool
is_odd(int) -> bool
```

If there are functions that provably never terminate, they will be given a ⊥ ("bottom") return type. For example:

```
infinite_loop_1(NoneType) -> ⊥
infinite_loop_2(NoneType) -> ⊥
```

### Test

There are a number of automated unit tests for ARF. These tests contain several interesting programs.

Run the automated tests with:

```
make test
```

## License

Copyright (c) 2015 by David Foster

If you wish to cite my work in your own publications, please use the following format:

* **Title:** Assign-Recurse-Flow (ARF)
* **Author:** David Foster
* **Link:** https://github.com/davidfstr/arf

[^max-two-executions-of-body]: The "max two executions needed" property requires a lot of exposition to prove formally, so I will simply assert its truth for the moment.