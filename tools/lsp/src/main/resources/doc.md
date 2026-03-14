%keywords continue_behavior continue_behaviour exceptional_behavior return_behavior normal_behavior model_behavior

## Behavior

----- 
%keywords post ensures ensures_free ensures_redundantly

## post conditions

* `ensures`
* `pre`

allowed suffixes `_free` and `_redundantly`.

-----
%keywords pre requires requires_free requires_redundantly

## pre condition

`requires` and `pre` clause form the pre-condition of a method, a loop or a code block.

```java 
//@ requires <jml-expression> ; 
```

Both can occur with a `_redundantly` prefix. In KeY `requires_free` is also valid.

-----
%keywords non_null_by_default nullable_by_default nullable

## Null modifiers

`non_null_by_default`, `nullable_by_default`, `@NonNullByDefault`, `@NullableByDefault`

The `non_null_by_default` and `nullable_by_default` modifiers or, equivalently, the `@NonNullByDefault` and
`@NullableByDefault` Java annotations, specify the default nullity declaration within the class. Nullness is described
in \S\ref{TODO`. The default applies to all typenames in declarations and in expressions (e.g. cast expressions), and
recursively to any nested or inner
classes that do not have default nullity declarations of their own.

These default nullity modifiers are not inherited by derived classes.

A class cannot be modified by both modifiers at once. If a class has no nullity modifier, it uses the nullity modifier
of the enclosing class; the default for a top-level class is
`non_null_by_default`. This top-level default may be altered by tools.

-----
%keywords pure @Pure

## Purity of functions

Specifying that a class is `pure` means that each method and nested class within the class is specified as pure.
The `pure` modifier on a class is not inherited by derived classes, though `pure` modifiers on methods are.

There is no modifier to disable an enclosing `pure` specification.


-----

\subsection{`@Options``
The `@Options` modifier takes as argument either a String literal or an array of String
literals (with the syntax `@Options({\emph{s1 ...``)`) with each literal being just like a command-line argument,
that is beginning with one or two hyphens and possibly containing
an `=` character with a value.
These command-line options are applied to the processing (e.g., ESC or RAC) of each method within the class. The options may be augmented or disabled by corresponding `
@Options` modifiers on nested methods or classes. In effect, the options that apply to a given class are the
concatenation of the options given for each enclosing class, from the outermost in.

An Options modifier is not inherited by derived classes.

Not all command-line options can be applied to an individual method or class.





-----
`invariant clause``
\label{invariant-clause`
Grammar:\\
\begin{grammar`
\gntd{invariant-clause` \gis \gterm{invariant`  \gnt{opt-name` \gnt{predicate` \gterm{;`
\end{grammar`

\jmlxtodo{TODO`

\jmlxtodo{visibility modifiers? `

-----
`constraint clause``
\label{consstraint-clause`
Grammar:\\
\begin{grammar`
\gntd{constraint-clause` \gis \gterm{constraint`  \gnt{opt-name` \gnt{predicate` \gterm{;`
\end{grammar`

Type information: The \gnt{predicate` has boolean type and is evaluated in the post-state.

An `constraint` clause for a type is equivalent to an additional postcondition for each
non-constructor method of the type, as if an additional `ensures` clause (with the predicate stated by the `constraint`
clause) were added to every behavior of each method in the type.
like an `ensures` clause, an `initially` clause is evaluated in the post-state.

`Constraint` clauses are used only by methods of the class in which the clause appears. The clause is not ``
inherited" by derived classes.

\jmlxtodo{visibility modifiers? `

-----
`initially clause``
\label{initially-clause`
Grammar:\\
\begin{grammar`
\gntd{initially-clause` \gis \gterm{initially`  \gnt{opt-name` \gnt{predicate` \gterm{;`
\end{grammar`

Type information: The \gnt{predicate` has boolean type and is evaluated in the post-state.

\jmlxtodo{visibility modifiers? `

An `initially` clause for a type is equivalent to an additional postcondition for each
constructor of the type, as if an additional `ensures` clause (with the predicate stated by the `initially` clause) is
added to every behavior of each constructor in the type.
like an `ensures` clause, an `initially` clause were evaluated in the post-state.

`Constraint` clauses are used only by methods of the class in which the clause appears. The clause is not ``
inherited" by derived classes.

A typical use of a `constraint` clause is to require some condition about the fields of a class to hold between
the pre- and post-states of every method of the class. For example, \\
\centerline{`constraint count >= \bs old{count`;``\\
states that the field `count` never decreases when methods of the class are called.

-----
%keywords ghost

## `ghost` fields

A ghost field declaration has the same syntax as a Java declaration except that it contains the
`ghost` modifier and is in a JML annotation. It declares a field that is visible only in
specifications. Runtime-assertion-checking compilers would compile a ghost field like a normal
Java field.

The type of a ghost field may be any JML or Java type.

-----
%keyword model

## `model` fields

A ghost field declaration has the same syntax as a Java declaration except that it contains the
`model` modifier and is in a JML annotation. However, a model field is not a ``real" field in the sense that it is not compiled into an executable representation of its containing class, even for RAC compilation. Rather a model field designates some abstract property of its containing class. The value of that property may be completely uninterpreted, determined only by the constraints imposed by various other specifications. Alternately, the value of a model field may be given directly by a `represents`
clause.

A model field is also implicitly a
\emph{datagroup` in that it designates a set of memory locations (store-refs), given by various `in` and `maps`
clauses.

-----
`represents clause``
Grammar:\\
\begin{grammar`
\gntd{represents-clause` \gis \glb \gterm{static` \grb
\gnt{represents-keyword` \gnt{ident` \\
\gindentb \glp \gterm{=` \gnt{jml-expression` \gterm{;`\\
\gindentb \gbar \gterm{\bs such_that` \gnt{predicate` \gterm{;` \\
\gindentb \grp \\
\gntd{represents-keyword` \gis \gterm{represents` \gbar \gterm{represents_redundantly`
\end{grammar`

Type information:
\begin{itemize`[noitemsep]
\item The identifier named in the represents clause must be a model field declared in or inherited by the class containing
the represents clause.
\item the \gnt{jml-expression` in the first form must have a type assignable to the type of
the given field (that is, \emph{ident` `==` \emph{expr` must be type-correct).
\item the \gnt{predicate` in the second form must be a \gnt{jml-expression` with boolean type
\item A represents-clause can be declared as static. In a static represents clause, only static elements can be referenced both in the left-hand side and the right-hand side. In addition, a static represents clause must be declared in the type where the model field on the left-hand side is declared.
\item A non-static represents clause must not have a static model field in its left-hand side.
\end{itemize`

The first form of a represents clause is called a functional abstraction. This form defines the value of the given
identifier in a visible state as the value of the expression that follows the =. The represents clause for field
\emph{f` with expression \emph{e` in class \emph{C` is equivalent to assuming\\
\centerline{`forall non_null C c; c.f == e_c``
where $e_c$ is `e` with `c` replacing `this`.

The second form (with `\such_that`) is called a relational abstraction. This form constrains the value of the identifier
in a visible state to satisfy the given predicate.

A represents clause does not take a visibility modifier. In essence, its visibility is that of
the field whose representation is is defining. However, there is no restriction on the
visibility of names on the right-hand-side. For example, the representation of a public model field may be an expression
containing private concrete fields.

Note that represents clauses can be recursive. That is, a represents clause may name a field on its right hand side that
is the same as the field being represented (named on the left hand side). It is the specifier's responsibility to make
sure such definitions are well-defined. But such recursive represents clauses can be useful when dealing with recursive
datatypes \cite{Mueller-Poetzsch-Heffter-Leavens03`.

-----
%keywords model

## `model methods` and `model classes`

----- 
%keywords axiom

## axiom-clause

```
axiom-clause:  'axiom' [name ':'] predicate ';'
```

Type information: The `predicate` has boolean type. An axiom must be a state-independent formula.

Axioms always have public visibility.

Axioms are assumptions introduced into the proof. An axiom must be a state-independent formula. Typically it might express a property of a mathematical type that is too difficult for an
automated tool to prove. As assumptions, axioms are a soundness risk for verification, unless they are separately proved.

-----
%keyword readable-if-clause writeable-if-clause

## readable if clause and writable if clause

```
\gntd{readable-if-clause` \gis \gterm{readable` \gnt{ident` \gterm{if` \gnt{jml-expression` ';' \\
\gntd{writable-if-clause` \gis 'writable ident \gterm{if` \gnt{jml-expression` ';'
```

Type information:
\begin{itemize`[noitemsep]
\item the \gnt{ident` must name a field (possibly inherited) visible in the class containing the clause
\item the \gnt{jml-expression` must have boolean type
\item Any name used on the right-hand-side must be visible in any context in which the given \gnt{ident` is visible.
\end{itemize`

The `readable-if` clause states a condition that must be true at any program point at which the given field is read.

The `writable-if` clause states a condition that must be true at any program point at which the given field is
written.


-----
%keywords monitor_for

## `monitors_for` clause

```bnf
monitors-for-clause: 
    monitors_for ident '=' jml-expression ... term ';'
```

Type information:
\begin{itemize`[noitemsep]
\item the \gnt{ident` must name a field (possibly inherited) visible in the class containing the clause
\item the \gnt{jml-expression`s must evaluate to a (possibly null) reference
\end{itemize`

A monitors-for-clause such as `monitors_for f = e1, e2;` specifies a relationship between the field, `f`, and a set of
objects, denoted by a specification expression list `e1, e2`. The meaning of this declaration is that all of the (
non-null) objects in the list, in this example, the objects denoted by `e1` and `e2`, must be locked at the program
point at
which the given field (f in the example) is read or written.

Note that the righthand-side of the monitors-for-clause is not just a list of memory locations, but is in fact a list of
expressions, where each expression evaluates to a reference to an object.

The monitors-for-clause is adapted from ESC/Java.

