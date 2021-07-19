# verification-project

## building

```bash
npm run build
```

## web interface

run:

```bash
npm start
```

and go to <http://127.0.0.1:5000/>

you can click on any of the files listed under "benchmarks" or write a function yourself in the editor.

## ---

choose a benchmark from the drop down list below "benchmarks"

to verify it click on "verify"

to try to generate invariants using horn click on "verify w/ horn"

![1](imgs/Screenshot%20from%202021-07-19%2015-07-52.png)

## editor

on the left there's a code editor where you can change the current function or write a new one

## paths

when verification fails you can view the paths that made it fail by choosing a path from the dropdown list.

![2](imgs/Screenshot%20from%202021-07-19%2015-11-25.png)

you'll get the proposition that failed, the path's reachability condition, its transformation relation and a counterexample

![3](imgs/Screenshot%20from%202021-07-19%2015-13-39.png)

## horn

when `verify w/ horn` succeeds the invariants will be listed and their locations can be viewed in the editor by clicking on the corresponding `locate` button

![4](imgs/Screenshot%20from%202021-07-19%2015-18-58.png)

## testing

```bash
python3 test.py
```

## TODO

- [X] support `switch`
- [X] properly handle `for`
- [X] support explicit casts
- [ ] support implicit casts
- [ ] handle fixed size ints as bitvectors
- [ ] implement an `is_nan()` operator
- [ ] make the parser work with float literals
- [X] implement phantom variables
- [X] implement `assume()`
- [X] implement a simple gui
- [X] add source locations to the cfg
- [X] implement a gui for horn (invariants synthesis)
- [X] (horn) allow providing partial invariants
- [X] (horn, gui) highlight cut points

## features

- `requires(prop)`
- `ensures(prop)`
- `assert(prop)`
- `freeze(id, expr)` :: declares a phantom variable `id` and stores `expr` in it
- `remember(prop)` :: adds `prop` to all `assert`s following it
- `phantom(statement)` :: surrounds a statement that's used only by the verifier (e.g. assigning to a phantom variable)
- `assume(prop)` :: lets the verifier assume that `prop` holds in that point
- `then(expr, prop)` :: implication
- `then(expr, prop1, prop2)` :: if-then-else
- `forall(id, range(expr1, expr2), prop)` :: universal quantifier (for a range of integers)
- `exists(id, range(expr1, expr2), prop)` :: existential quantifier (for a range of integers)
