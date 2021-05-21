# verification-project

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
- [ ] implement a gui for horn (invariants synthesis)
- [ ] (horn) allow providing partial invariants

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
