# tree-grammars

Simple regular tree grammar library for Haskell.


Regular tree grammars correspond closely to algebraic data types as in Haskell:

    data Tree = Node Tree Tree | Leaf

    T -> Leaf() | Node(T,T)

We can rewrite a non-terminal such as `T` to a (often infinite) family of terms:


    T
    Node(Leaf,Leaf)
    Node(Node(Leaf,Leaf),Leaf)
    ...


The interesting thing is that regular tree grammars also closely correspond to regular grammars. NFA/DFA algorithms such as. We can support algorithms such as:

- union
- intersection
- minimization

My personal need for this is to recursive type definitions with strictness and absence info from recursive functions.
To do this, I must unify and anti-unify these recursive terms, which exactly corresponds to these regular tree grammar operations.


They also closely correspond to term-graphs and E-Graphs, with some differences:

- Basic E-Graphs cannot reason about cycles with identical topology
- We do not support rewrite rules over tree grammars
- We use a closed world assumption. Adding additional rules later, as is common in E-Graphs, could invalidate previous minimizations
