# Migration guide from 2.x

This document lists changes in 3.0 and how to migrate to them from 2.x versions.

## Changes on `Type` AST nodes hierarchy

### `ArrayType` (Issue 112)

We introduced a new `ArrayType` subclass of `Type` to correctly model array types. `ReferenceType` is now abstract and
is a base class for `ArrayType` and `ClassOrInterfaceType`. `ArrayType` only encapsulate **one level of array
dimension** and the corresponding annotations for that array dimension.

Accordingly, you have to update your visitors to handle the new visit method for `ArrayType` and remove the visit method
for `ReferenceType`.

### Annotations on `ClassOrInterfaceType` (Issue 107)

Annotations are now correctly dispatched to `ClassOrInterfaceType` instances and their scope. Beware to change your code
that relied on the previously wrong behavior. See the issue to get more information on what was wrong in the previous
behavior.

### `UnionType` and `CatchClause`s (Issue 111)

We introduced a new `UnionType` subclass of `Type` to correctly model union types used in catch clauses. As a result, we
removed the `MultiTypeParameter` which name was confusing. A `CatchClause` may now have a `Parameter` that have a
`UnionType` type.

Accordingly, you have to update your visitors to handle the new visit method for `UnionType` and remove the visit method
for `MultiTypeParameter`.

### `IntersectionType` and casts with multiple bounds (Issue 149)

We introduced a new `IntersectionType` subclass of `Type` to correctly model intersection types used in casts with
multiple bounds. Those were not parsed at all. Also, annotations on bounds are now parsed correctly as specified by the
Java Language Specification 8. As a result, a `CastExpr` may now have an `IntersectionType` type.

Accordingly, you have to update your visitors to handle the new visit method for `IntersectionType`.

### Various changes on annotated types

1. Begin positions of annotated `Types` were not computed correctly. This is fixed.
2. Annotated `Types` in `instanceof` expressions were not parsed. This is fixed.
