# TwoSAT

A 2SAT solver, written in Rust. If you are curious enough to search through the git history of this repository
you will find that I initially implemented this 2SAT solver using the logical rule of resolution. However, it ran in $O(n^4)$ time or something like that, incredibly inefficient (it was still polytime though!).
Regardless, after learning about a linear time solution to 2SAT using strongly connected components of its implication graph (see [Wikipedia](https://en.wikipedia.org/wiki/2-satisfiability#Strongly_connected_components)), I decided to convert my solution to this more efficient one that other people had figured out, something more respectable to publish online.

# Usage

An input formula is specified using `~` for logical negation, `&` for logical AND, and `|` for logical OR. Variables may be any alphanumeric string, not starting with a number. Then, the input must be specified as a 2CNF, where clauses (ORs) with 2 variables are enclosed in parentheses, and all clauses are conjoined by `&`. `&` must not appear within parentheses, only `|` can. `|` cannot appear outside parentheses. Parentheses may not be nested. Some valid formula strings:
```py
"(a|b)&~c&(~a|~d)&(a|a)&c"
"(x1|x2)&(x3|~x4)
```
Some invalid formula strings:
```py
"a|b"
"(a&b)|(c&d)"
"(a|b|c)" # this one isn't a 2CNF
"a&(b|c)&((c|a)&d|e)"
```

Then, if your correctly specified formula is `<phi>`, check if it's satisfiable with
```sh
$ cargo run <phi>
```

For example,
```sh
$ cargo run "(a|b)&(~a|d)&(b|c)&(~b|d)&(~b|e)&(~d|~c)&(~e|~d)"
Formula is SAT: false

$ cargo run "(a|b)"
Formula is SAT: true
```
