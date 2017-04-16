Version 3.2.1
------------------
Beta: `TreeStructureVisitor`.

* Maven dependencies were updated to their latest versions 
* 890 the concept of "method signature" now exists in JavaParser
* 896 891 889 887 882 789 smaller improvements and fixes

Version 3.2.0
------------------
The lexical preservation code is stable!

Beta: `TreeStructureVisitor`.

* 885 884 879 878 smaller improvements and fixes

Version 3.1.4
------------------
This is the first version to parse Java 9.

Beta: `TreeStructureVisitor`, and `LexicalPreservingPrinter`.

* 872 873 874 787 Remaining Java 9 work.

Version 3.1.3
------------------
Beta: `TreeStructureVisitor`, and `LexicalPreservingPrinter`.

A start has been made on source level support. The default level is Java 8.
It can be set to Java 9 like this for a parser *instance*:
```java
private final JavaParser parser = new JavaParser(new ParserConfiguration().setValidator(new Java9Validator()));
```
and like this for the static parse methods:
```java
JavaParser.getStaticConfiguration().setValidator(new Java9Validator());
```

* 862 552 "_" is an illegal identifier on source level 9.
* 869 867 109 855 857 smaller improvements and fixes

Version 3.1.2
------------------
Beta: `TreeStructureVisitor`, `ConcreteSyntaxModel`, and `LexicalPreservingPrinter`.

* 594 849 831 a validation framework was introduced to inform about problems in the AST without needing to change the grammar,
and without requiring parsing code.
It is open for extension by users.
* 852 853 826 832 846 839 smaller improvements and fixes

Version 3.1.1
------------------
Beta: `TreeStructureVisitor`, `ConcreteSyntaxModel`, and `LexicalPreservingPrinter`.

* 654 124 lexical preservation (printing source code with the same formatting it had when parsing) has been added.
    Thank you @ftomassetti for a lot of work! 
* 554 800 first (big) step towards Java 9 support: JavaParser can read project Jigsaw module definitions.
* 795 786 751 extend the TreeVisitor with more traversal options. Thanks @ryan-beckett!
* 791 `GenericListVisitorAdapter` has been added which collects its results in a list. Thanks @Gottox!
* 815 798 797 813 clean up Problem text
* 819 818 817 816 441 809 808 807 fix various absurd annotation related issues. 
* 777 805 802 796 790 792 793 781 784 785 783 782 779 357 799 763 smaller improvements and fixes

Version 3.1.0
------------------
Beta: `TreeStructureVisitor` and `ConcreteSyntaxModel`.

* 705 755 Add the concrete syntax model, which will give you information about the exact syntax a certain nodes matches.

* 777 smaller improvements and fixes

Version 3.1.0-beta.2
------------------
This version is a beta because `TreeStructureVisitor` is not in its definite state yet.

* 762 761 772 merge `javaparser-metamodel` and `javaparser-generator-utils` into `javaparser-core`.
* 766 the `ModifierVisitor` is now created by a code generator. Its behaviour has been made logical, and may give different results than before.
* 755 `ConstructorDeclaration` and `MethodDeclaration` now share a parent: `CallableDeclaration`
* 687 759 773 769 768 767 765 759 smaller improvements and fixes

Version 3.1.0-beta.1
------------------
This version is a beta because there are a lot of new features that may still change.

This version needs a minor version increase because of a backwards compatability issue: 
* 719 `getJavadoc`, `getJavadocComment` and `getComment` could return null. Our promise was to return `Optional`, so that is what they do now.

New:
* 658 718 736 737 we have created a metamodel.
It gives information about the structure of the various AST nodes, as if you are introspecting them.
You can find it in `javaparser-metamodel`, the main class is `JavaParserMetaModel`
* 353 365 visitors are no longer hand made, they are now generated from the metamodel. This should make them 100% reliable.
Affected visitors are: `GenericVisitorAdapter`, `EqualsVisitor`, `VoidVisitorAdapter`, `VoidVisitor`, `GenericVisitor`, `HashCodeVisitor`, `CloneVisitor`.

If you want to generate your own visitors, you can use the `VisitorGenerator` class from `javaparser-core-generators`

If you want to reuse the code generation utilities, look at module `javaparser-generator-utils` - there is a very useful `SourceRoot` class in there that takes away a lot of file management troubles.
* 538 735 `TreeStructureVisitor` has been added, which should be considered beta.
* 220 733 717 749 745 750 743 748 666 732 746 734 733 smaller improvements and fixes

Version 3.0.1
------------------
* 699 433 325 Javadoc can now be parsed
* 703 696 added NodeWithOptionalScope
* 702 FieldAccessExpr now implements NodeWithSimpleName, *which means that "field" has been renamed to "name"*
* 707 706 improve range of array types and levels
* 709 smaller improvements and fixes

Version 3.0.0
------------------
* 695 697 689 680 693 691 682 690 677 679 688 684 683 smaller improvements and fixes

Version 3.0.0-RC.4
------------------
* 668 669 TypeDeclarationStmt became LocalClassDeclarationStmt
* 347 665 every node now has some documentation
* 660 670 673 four types of import declaration have been merged back into the old ImportDeclaration
* 659 The pretty printer can now take customized visitors 
* 650 671 672 674 524 smaller improvements and fixes

Version 3.0.0-RC.3
------------------
* 639 622 632 657 656 652 653 647 648 645 194 643 630 624 628 627 626 625 623 cleanups, small fixes, and general housekeeping

Version 3.0.0-RC.2
------------------
* 593 EmptyImportDeclaration and NonEmptyImportDeclaration have been removed
* 612 VariableDeclaratorId has been removed. It has been substituted by "SimpleName name"
* 614 617 the list of tokens has been linearized and simplified
* 615 support for arrays has once more been changed. See [the issue](https://github.com/javaparser/javaparser/issues/592) 
* 580 453 380 618 580 611 610 424 608 smaller improvements and fixes

Version 3.0.0-RC.1
------------------
* 499 601 renames many fields to be more consistent
* 596 605 602 604 smaller improvements and fixes

Version 3.0.0-alpha.11
------------------
* 547 595 Node.range is now using Optional instead of Range.UNKNOWN
* 584 588 548 585 bug fixes and improvements

Version 3.0.0-alpha.10
------------------
* 578 579 577 575 290 570 568 567 562 564 551 bug fixes and improvements

Version 3.0.0-alpha.9
------------------
* 403 358 549 Make all names nodes: either SimpleName or Name. This makes every name in the AST visitable. NameExpr is now a wrapper to use SimpleName in an expression.
* 516 536 use Optional<> for return values.
* 556 557 558 550 small improvements and fixes.
* 560 559 make nodes observable.

Version 3.0.0-alpha.8
------------------
* 344 529 turn DumpVisitor into an official PrettyPrinter
* 532 508 427 530 531 513 528 cleanups

Version 3.0.0-alpha.7
------------------
* 515 roll back attempt at using Optional
* 522 504 make NodeList not a Node (restores parent/children behaviour to before alpha.4)
* 527 526 rename getChildrenNodes to getChildNodes
* 525 495 520 bug fix

Version 3.0.0-alpha.6
------------------
* 503 modified ImportDeclaration hierarchy to have getters for static and "asterisk" again
* 506 bug fix

Version 3.0.0-alpha.5
------------------
* 451 null is no longer allowed in the AST. [See last post in issue](https://github.com/javaparser/javaparser/issues/451)
* 501 421 420 316 use a special type of list for nodes: NodeList. [See last post in issue](https://github.com/javaparser/javaparser/issues/421)

Version 3.0.0-alpha.4
------------------
* 463 471 nodes can now be removed easily
* 491 import handling changed. Instead of "ImportDeclaration", we now have the four types of import as described in the JLS. [See issue](https://github.com/javaparser/javaparser/pull/491)
* 452 355 474 494 various improvements
* 493 492 485 Simplify the JavaParser interface

Version 3.0.0-alpha.3
------------------
* 112 237 466 465 461 460 458 457 fundamentally changes how we deal with arrays. [It is explained in the last post here](https://github.com/javaparser/javaparser/issues/237)
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

Version 2.1.0
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

Version 1.0.8 (2010-01-17)
-------------
* Fixed issues:
	* Issue 17: A refactor suggestion for AnnotationExpr and its subclasses
	* Issue 21: Java 5 JavaParser compiled JARs
	* Issue 22: Please use java.lang.reflect.Modifier constants in japa.parser.ast.body.ModifierSet
	* Issue 27: Implement the "equal" method
	* Issue 30: equals and hashCode methods

Version 1.0.7 (2009-04-12)
-------------
* Issue 19 fixed: 
* Tests changed to run with junit 4 

Version 1.0.6 (2009-01-11)
-------------
* Issue 11 fixed: changed method get/setPakage to get/setPackage in the class CompilationUnit
* Created new visitor adapter to help AST modification: ModifierVisitorAdapter
* Changed visitor adapters to abstract  

Version 1.0.5 (2008-10-26)
-------------
* Created simplified constructors in the nodes of the AST (without positional arguments) 
* Created ASTHelper class with some helpful methods (more methods are still needed)

Version 1.0.4 (2008-10-07)
-------------
* Moved to javacc 4.1.
* The java_1_5.jj can be build alone without compilation errors

Version 1.0.3 (2008-09-06)
-------------
* Removed SuperMemberAccessExpr class, it was no longer used
* Removed the methods get/setTypeArgs() from ArrayCreationExpr, this node shouldn't have these methods.
* Fixed the bug with start/end position of the nodes IntegerLiteralMinValueExpr and LongLiteralMinValueExpr  
* The methods get/setAnnotations() from all BodyDeclaration subclasses were pushed down to BodyDeclaration class 

Version 1.0.2 (2008-07-20)
-------------
* Issue fixed: Issue 1: Add support for editing AST nodes or create new ones

Version 1.0.1 (2008-07-01)
-------------
* Issue fixed: Issue 5: end line and end column equal to begin line and begin column

Version 1.0.0 (2008-06-25)
-------------
* Changed version numbering, starting version 1.0.0
* Javadoc done for packages:
    * japa.parser
    * japa.parser.ast
* Corrected bug when parsing in multithread: 
    * JavaParser.setCacheParser(false) must be called before to use the parser concurrent 

2008-06-19
-------------
* No code changes, added binary distribution to download page 

2008-06-11
-------------
* Bug corrected: NPE in VoidVisitorAdapter 
	* http://code.google.com/p/javaparser/issues/detail?id=2

2008-06-09
-------------
* Added Adapters for de visitors

2008-05-28
-------------
* This project now is published at Google Code:
	* http://code.google.com/p/javaparser/

2008-05-25
-------------
* Added support for comments and javadoc to the tree. 
	* Javadocs are stored directly to members (BodyDeclaration and all deriveds (classes, methods, fields, etc.)), accessible by the method getJavadoc().
	* All comments are stored in the CompilationUnit, accessible by the method getComments().

2008-04-01
-------------
* Changed all nodes public attributes to be private and created getters to access them
* Changed the methods of the Node getLine e getColumn to getBeginLine and getBeginColumn
* Added the methods getEndLine and getEndColumn to the Node class (works only in the BlockNode)

2007-12-22
-------------
* Corrected ConditionalExpression bug

2007-10-21
-------------
* Added LGPL License

2007-10-21
-------------
* Bugs corrected:  
  * Created PackageDeclaration member of CompilationUnit to add suport for annotations in the package declaration
  * Parameterized anonymous constructor invocation
  * Explicit constructor invotation Type Arguments
  * ctrl+z ("\u001A") ar end of compilation unit

2007-10-09
-------------
* EnumConstantDeclaration annotation support corrected
* Parssing Java Unicode escape characters suport added

2007-10-03
-------------
* Bug corrected: "MotifComboPopup.this.super()" statement was generating parser error
	                    
2007-10-01
-------------
* Bug corrected: Casting signed primitive values
```
	double d = (double) -1;
	                    ^
```
2007-08-06
-------------
* Bug with the single line comments in the final of the unit corrected

2007-07-31
-------------
* Fixed the bug with the following expression:  `Class c = (int.class);`

2007-06-26
-------------
* Bug fixes from Leon Poyyayil work
	* suport for hex floating point
	* unicode digits in indentifier 
	* MemberValueArrayInitializer

2007-03-09
-------------
* Long and Integer literal MIN_VALUE bug	

2007-02-24
-------------
* '\0' bug fixed	

2007-02-01
-------------
* Many bug fixes
* Added line/column to nodes
