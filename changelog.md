Version 3.0.0-alpha.3
------------------
* 112 237 466 465 461 460 458 457 fundamentally changes how we deal with arrays. It is explained in the last post of https://github.com/javaparser/javaparser/issues/237
* 472 456 makes the "data" field on every node more structured.
* 477 468 refactor TypeArguments. You will find that TypeArguments is no longer a type, it is just a list in some nodes.
* 482 adds the "nodeTypes" packages to the osgi export.
* 479 476 makes all setters on nodes return this so they become chainable.
* 473 437 clean up CloneVisitor.

Version 3.0.0-alpha.2
------------------
* 157 a new parser frontend, check https://github.com/javaparser/javaparser/pull/447 for explanations
* 435 more builder methods like 400 and 405
* 111 440 443 444 445 446 bugs & cleanups

Version 3.0.0-alpha.1
------------------
* 400 405 introduce many "builder" style methods for constructing code. Thanks DeepSnowNeeL!
* 409 remove ASTHelper (methods are now on specific Node subclasses)
* 414 JavaParser can now be instantiated and reused. InstanceJavaParser removed
* 418 417 411 408 bugs
* 367 420 407 402 various cleanups

Version 2.5.1
-------------
* 394 OSGi manifest added
* 391 fix ModifierVisitor NullPointerException bug
* 385 a few new parse methods
* 386 fix dumping an empty import (a single ; after the package declaration)

Version 2.5.0
-------------
API breaking changes:

* 191: moved TreeVisitor to visitor package
* 368, 162, 303, 302, 360: use correct type in some places.
* 371: code is now compiled with Java 8
* 342, 331: ModifierVisitorAdapter detects and removes broken nodes
* 328, 270: upgrade JavaCC (use TokenMgrException now)
Other changes:

* 297: enable access to tokens.
* 341, 361: node positions are now OO
* 211, 373: escaping of \n \r for string literals
* 336, 276, 141: JavaDoc support now works
* 337, 281: reorganize the stream reading code
* 343, 309, 332, 57: take advantage of common interfaces
* 329, 326, 327: deal with platform issues
* 163, 236, 252, 296, 269, 339, 321, 322, 252, 253, 293, 295: various fixes
* 310, 311, 313, 301, 294: some code clean-ups 

Version 2.4.0
-------------
* several fixes in DumpVisitor for bugs due to lazy initialization
* make TypeDeclaration implements DocumentableNode directly
* TypedNode interface introduced
* introduce MultiBoundType
* refactored IntersectionType and UnionType
* refactored CatchClause
* parsing annotations in throws declarations
* parse orphan semicolons in import statements
* added PackageDeclaration.getPackageName
* solved issue with newlines in string literals
* fixed handling of UnknownType in EqualsVisitor
* improvements to CommentsParser
* removing old grammar

Version 2.3.0
-------------
* ClassOrInterfaceType implements NamedNode
* DumpVisitor can now be extended
* Improved documentation
* AST: lists are now lazy initialized

Version 2.1.0-SNAPSHOT
-------------
* Features
  * [#75 performance improvement for `PositionUtils.sortByBeginPosition`](https://github.com/javaparser/javaparser/issues/75)
  * [#64 In getDeclarationAsString parameter names should be optional](https://github.com/javaparser/javaparser/issues/64)
* Bugfixes
  * [#79 Fix NPE in `ConstructorDeclaration.getDeclarationAsString`](https://github.com/javaparser/javaparser/pull/79)
  * [#86 Add missing functions to ModifierVisitorAdapter](https://github.com/javaparser/javaparser/pull/86)
  * [#82 set LambdaExpr as parent of its child nodes](https://github.com/javaparser/javaparser/issues/82)
  * [#87 implement `setJavadoc` and `getJavadoc` at various classes](https://github.com/javaparser/javaparser/issues/87)
  * [#96 Fixed encoding issue in `Javaparser.parse`](https://github.com/javaparser/javaparser/pull/96)
  * [#85 Casting a lambda expression causes a parsing failure](https://github.com/javaparser/javaparser/issues/85)
  * [#88 `MethodReferenceExpr` and `TypeExpr` don't set themselves as parents](https://github.com/javaparser/javaparser/issues/88)
* Internal
  * [#89 CommentsParser.State contains unused fields](https://github.com/javaparser/javaparser/issues/89)
  * Switched from drone.io to [Travis](https://travis-ci.org/javaparser/javaparser)
  * [#105 Enforce compiling the library for a certain Java version](https://github.com/javaparser/javaparser/pull/105)

[Code changes](https://github.com/javaparser/javaparser/compare/javaparser-parent-2.0.0...master)

Version 2.0.0
-------------
* support Java 8
