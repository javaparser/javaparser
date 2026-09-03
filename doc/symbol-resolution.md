# Parsing and symbol resolution APIs

There are two steps: parse source into an AST, then (optionally) resolve names and types on that AST. This page is a short guide, then a per-class reference.

Related: [About the Symbol Solver](https://github.com/javaparser/javaparser/wiki/About-the-Symbol-Solver) (lookup strategy and history), [JavaParser vs StaticJavaParser](https://javaparser.org/the-quick-and-the-full-api-of-javaparser/).

## Parsing

Use `JavaParser` with a `ParserConfiguration`. The configuration is what carries the `SymbolResolver`; the parser injects it into every successfully parsed compilation unit.

```java
ParserConfiguration config = new ParserConfiguration()
        .setSymbolResolver(new JavaSymbolSolver(typeSolver));
JavaParser parser = new JavaParser(config);

ParseResult<CompilationUnit> result = parser.parse(source);
if (!result.isSuccessful()) {
    result.getProblems().forEach(System.err::println);
    return;
}
CompilationUnit cu = result.getResult().get();
```

The same instance also has the fragment parsers, each returning `ParseResult<T>`:

```java
ParseResult<BlockStmt> block = parser.parseBlock("{ return 1; }");
ParseResult<Statement> stmt = parser.parseStatement("int x = 1;");
ParseResult<ImportDeclaration> imp = parser.parseImport("import java.util.List;");
```

Language level and the symbol resolver both live on `ParserConfiguration`. Build one `JavaParser` per configuration and reuse it.

### `StaticJavaParser`

`StaticJavaParser` is a convenience shortcut — its Javadoc calls it "a simpler, static API than `JavaParser`". It is fine for scripts, tests, and single-threaded one-offs. It is not what to use for real resolution work:

- Parse errors are thrown instead of returned as `ParseResult`.
- Configuration is a `ThreadLocal`. `setConfiguration` on one thread does not apply on another, so the `SymbolResolver` is silently missing and `resolve()` fails with the "not configured" exception below.

## Configure and resolve

```java
TypeSolver typeSolver = new TypeSolverBuilder()
        .withCurrentJRE()
        .withSourceCode("src/main/java")
        .build();

ParserConfiguration config = new ParserConfiguration()
        .setSymbolResolver(new JavaSymbolSolver(typeSolver));
JavaParser parser = new JavaParser(config);

ParseResult<CompilationUnit> result = parser.parse(source);
CompilationUnit cu = result.getResult().get();
MethodCallExpr call = cu.findFirst(MethodCallExpr.class).get();
ResolvedMethodDeclaration resolved = call.resolve();
ResolvedType type = call.calculateResolvedType();
```

These go through `SymbolResolver` and throw `UnsolvedSymbolException` when the name cannot be found.

| Call | Typical result |
| --- | --- |
| `Resolvable.resolve()` | Declaration for that node |
| `Expression.calculateResolvedType()` | `ResolvedType` of the expression |
| `Type.resolve()` | `ResolvedType` for that type node |

Nodes that implement `Resolvable` include method/constructor/field/parameter/type declarations, `MethodCallExpr`, `ObjectCreationExpr`, `MethodReferenceExpr`, `FieldAccessExpr`, `NameExpr`, `ThisExpr`, `AnnotationExpr`, and `ExplicitConstructorInvocationStmt`.

## What goes wrong

Without a resolver, or if the node is not in a compilation unit, `getSymbolResolver()` throws before resolution even starts:

```
IllegalStateException: Symbol resolution not configured: to configure consider setting a SymbolResolver in the ParserConfiguration
IllegalStateException: The node is not inserted in a CompilationUnit
```

Once a resolver is present, a name that cannot be found throws `UnsolvedSymbolException`.

Two styles exist next to each other:

- **Throwing:** `TypeSolver.solveType(String)`, `node.resolve()`, `calculateResolvedType()`. Failure is `UnsolvedSymbolException` (or the `IllegalStateException`s above).
- **`SymbolReference`:** `TypeSolver.tryToSolveType(String)`, `Context.solveSymbol` / `solveType` / `solveMethod`. Check `isSolved()` before `getCorrespondingDeclaration()`.

`tryToSolveType` vs `solveType` on `TypeSolver` is the same split: one returns an unsolved reference, the other throws.

Resolved types are cached on the node through `DataKey`s (`TYPE_WITH_LAMBDAS_RESOLVED` / `TYPE_WITHOUT_LAMBDAS_RESOLVED`). `calculateResolvedType()` therefore goes stale if the AST is mutated afterwards. `JavaParserFacade` also caches instances per `typeSolver.getRoot()` — see below.

`JavaParserFacade.get` is `synchronized` because of [#2668](https://github.com/javaparser/javaparser/issues/2668). That is not a claim that the facade (or JavaParser) is safe to share across threads — the Javadoc says so explicitly and points at [#2671](https://github.com/javaparser/javaparser/issues/2671). Treat one facade / one `TypeSolver` tree as single-threaded.

`StaticJavaParser`'s `ThreadLocal` configuration isolates config per thread; it does not make resolution thread-safe.

## Layering

From the node API down:

```
node.resolve() / calculateResolvedType()
        → JavaSymbolSolver          (SymbolResolver on the CompilationUnit)
            → JavaParserFacade      (needs a TypeSolver; caches per getRoot())
                → SymbolSolver      (Solver: walk a Context)
                    → Context       (scope around the node, walks outward)
```

`JavaSymbolSolver` delegates to `JavaParserFacade.get(typeSolver)` for essentially every resolution. `calculateType` is `JavaParserFacade.get(typeSolver).getType(expression)`, so `node.calculateResolvedType()` is the facade, one hop further out.

The difference is configuration:

- **Node API** (`resolve()`, `calculateResolvedType()`): needs a `SymbolResolver` injected into the compilation unit, then reads naturally from the AST. Set it with `ParserConfiguration#setSymbolResolver`, or after the fact with `JavaSymbolSolver.inject(compilationUnit)`.
- **`JavaParserFacade`**: needs nothing but a `TypeSolver` in hand. Use it when you already have an AST that was parsed without a resolver. Typical calls: `JavaParserFacade.get(typeSolver).solve(methodCallExpr)`, `.getType(node)`, `.solveMethodAsUsage(call)`.

`JavaParserFacade` holds a static `WeakHashMap<TypeSolver, JavaParserFacade>`. The cache key is `typeSolver.getRoot()`, not the instance you passed. `clearInstances()` drops that map.

## `SymbolResolver` / `JavaSymbolSolver`

`com.github.javaparser.resolution.SymbolResolver` is the interface the AST talks to:

- `resolveDeclaration(Node, Class<T>)` — declaration for a node
- `toResolvedType(Type, Class<T>)` — resolved form of a type node
- `calculateType(Expression)` — type of an expression
- `toTypeDeclaration(Node)` — reference type declaration for a type-declaring node

`JavaSymbolSolver` is the implementation that wraps the symbol-solver library. Create one instance per `TypeSolver` and reuse it across compilation units.

## `TypeSolver`

A `TypeSolver` only answers “what is the type named X?”. It does not walk expressions.

- `tryToSolveType(String)` → `SymbolReference<ResolvedReferenceTypeDeclaration>`
- `solveType(String)` → declaration, or `UnsolvedSymbolException`

Common implementations (also available through `TypeSolverBuilder`): `ReflectionTypeSolver` (JRE / current classpath), `JavaParserTypeSolver` (source roots), `JarTypeSolver` / `AarTypeSolver`, `ClassLoaderTypeSolver`, `MemoryTypeSolver`, combined with `CombinedTypeSolver`.

### `CombinedTypeSolver` and `getRoot()`

Type solvers form a parent chain. `getRoot()` walks `getParent()` until it is null.

`CombinedTypeSolver.add` (and the constructor) calls `setParent(this)` on each child. A type solver can only have one parent — adding the same instance to a second combined solver throws `IllegalStateException: This TypeSolver already has a parent`.

That parent link matters in two places:

- Child solvers that build declarations with `getRoot()` (for example `JarTypeSolver`) see sibling solvers only if the parent is set. A bare `JarTypeSolver` cannot see JRE types from a `ReflectionTypeSolver` sitting next to it unless both live under the same `CombinedTypeSolver`.
- `JavaParserFacade.get(typeSolver)` caches on `typeSolver.getRoot()`. Passing a child of a combined solver returns the facade for the combined solver, not a facade bound to that child alone.

Add children through `CombinedTypeSolver` (constructor or `add`). Do not call `setParent` yourself.

## `SymbolSolver` (`Solver`)

`SymbolSolver` implements `Solver`. It is the engine behind the facade: `solveSymbol`, `solveSymbolAsValue`, `solveType`, `solveMethod`, `solveTypeUsage`, `solveSymbolInType`. Application code rarely constructs this directly.

`Solver.solveMethod(...)` returns a `MethodUsage` (declaration plus resolved type variables).

## `Context`

`Context` is the scope object used internally while walking outward from a node. `JavaParserFactory.getContext(node, typeSolver)` builds one.

| Call | Result |
| --- | --- |
| `Context.solveMethod(...)` | `SymbolReference<ResolvedMethodDeclaration>` |
| `Context.solveMethodAsUsage(...)` | `Optional<MethodUsage>` (declaration plus resolved type variables) |

`Solver.solveMethod` already returns a `MethodUsage`; `Context.solveMethod` returns the declaration reference. Use `solveMethodAsUsage` on a `Context` when you want the `MethodUsage`.

`Context.solveType(String)` is deprecated in favour of `solveType(String, List)`. The list form considers type arguments; pass `null` for the old behaviour. `solveTypeInParentContext(String)` is deprecated the same way.

Other `Context` calls: `solveSymbol`, `solveSymbolAsValue`, `solveGenericType`, `solveConstructor`.
