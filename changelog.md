
Next Release (Version 3.27.2-snapshot)
--------------------------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/214?closed=1)

### Added
### Changed
### Deprecated
### Removed
### Fixed
### Security

Version 3.27.1
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/213?closed=1)

### Changed

* fix: switch expression improvement (PR [#4823](https://github.com/javaparser/javaparser/pull/4823) by [@seokjun7410](https://github.com/seokjun7410))

### Fixed

* Fix: Adjusts the range limits of lambda expression parameters to ignore brackets. (PR [#4860](https://github.com/javaparser/javaparser/pull/4860) by [@jlerbsc](https://github.com/jlerbsc))
* Fix issue 4846 (PR [#4855](https://github.com/javaparser/javaparser/pull/4855) by [@PiTheGuy](https://github.com/PiTheGuy))
* Revert checkstyle plugin upgrade (PR [#4836](https://github.com/javaparser/javaparser/pull/4836) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 4832 Resolving type of fully qualified varargs invocation throws IndexOutOfBoundsException (PR [#4835](https://github.com/javaparser/javaparser/pull/4835) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: Issue 4829 Infinite loop in DifferenceElementCalculator when calling setPermittedTypes (PR [#4834](https://github.com/javaparser/javaparser/pull/4834) by [@jlerbsc](https://github.com/jlerbsc))
* XmlPrinter: fix duplicate attribute name in generated xml (PR [#4806](https://github.com/javaparser/javaparser/pull/4806) by [@sgqy](https://github.com/sgqy))
*  Use lambda parameter counts and block bodies for improved resolution  (PR [#4796](https://github.com/javaparser/javaparser/pull/4796) by [@johannescoetzee](https://github.com/johannescoetzee))
* Fix issue #4791 (PR [#4792](https://github.com/javaparser/javaparser/pull/4792) by [@bannmann](https://github.com/bannmann))

### Developer Changes

* fix(deps): update dependency org.checkerframework:checker-qual to v3.51.1 (PR [#4862](https://github.com/javaparser/javaparser/pull/4862) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-javadoc-plugin to v3.12.0 (PR [#4843](https://github.com/javaparser/javaparser/pull/4843) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update dependency com.google.guava:guava to v33.5.0-jre (PR [#4839](https://github.com/javaparser/javaparser/pull/4839) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update codecov/codecov-action action to v5.5.1 (PR [#4827](https://github.com/javaparser/javaparser/pull/4827) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update dependency org.checkerframework:checker-qual to v3.50.0 (PR [#4825](https://github.com/javaparser/javaparser/pull/4825) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update actions/setup-java action to v5 (PR [#4822](https://github.com/javaparser/javaparser/pull/4822) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update actions/checkout action to v5 (PR [#4811](https://github.com/javaparser/javaparser/pull/4811) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency com.puppycrawl.tools:checkstyle to v11 (PR [#4808](https://github.com/javaparser/javaparser/pull/4808) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-surefire-plugin to v3.5.4 (PR [#4701](https://github.com/javaparser/javaparser/pull/4701) by [@renovate[bot]](https://github.com/apps/renovate))

### Uncategorised

* Improves documentation on LexicalPreservingPrinter (PR [#4820](https://github.com/javaparser/javaparser/pull/4820) by [@jlerbsc](https://github.com/jlerbsc))
* Improves documentation on the raw langage level (PR [#4819](https://github.com/javaparser/javaparser/pull/4819) by [@jlerbsc](https://github.com/jlerbsc))
* Fix javadoc of Name class (PR [#4789](https://github.com/javaparser/javaparser/pull/4789) by [@bannmann](https://github.com/bannmann))
* Fix NormalAnnotationExpr Javadoc (PR [#4784](https://github.com/javaparser/javaparser/pull/4784) by [@bannmann](https://github.com/bannmann))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@seokjun7410](https://github.com/seokjun7410)
* [@bannmann](https://github.com/bannmann)
* [@sgqy](https://github.com/sgqy)
* [@johannescoetzee](https://github.com/johannescoetzee)
* [@PiTheGuy](https://github.com/PiTheGuy)
* [@jlerbsc](https://github.com/jlerbsc)


Version 3.27.0
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/212?closed=1)

### Developer Changes

* fix(deps): update dependency org.junit:junit-bom to v5.13.1 (PR [#4775](https://github.com/javaparser/javaparser/pull/4775) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency maven to v3.9.10 (PR [#4774](https://github.com/javaparser/javaparser/pull/4774) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update dependency org.checkerframework:checker-qual to v3.49.4 (PR [#4770](https://github.com/javaparser/javaparser/pull/4770) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update dependency org.junit:junit-bom to v5.13.0 (PR [#4766](https://github.com/javaparser/javaparser/pull/4766) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update codecov/codecov-action action to v5.4.3 (PR [#4755](https://github.com/javaparser/javaparser/pull/4755) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update dependency org.checkerframework:checker-qual to v3.49.3 (PR [#4745](https://github.com/javaparser/javaparser/pull/4745) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update codecov/codecov-action action to v5.4.2 (PR [#4731](https://github.com/javaparser/javaparser/pull/4731) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update dependency org.junit:junit-bom to v5.12.2 (PR [#4728](https://github.com/javaparser/javaparser/pull/4728) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update dependency com.google.guava:guava to v33.4.7-jre (PR [#4719](https://github.com/javaparser/javaparser/pull/4719) by [@renovate[bot]](https://github.com/apps/renovate))

### Uncategorised

* Fix resolution for method refs used as varargs (PR [#4759](https://github.com/javaparser/javaparser/pull/4759) by [@johannescoetzee](https://github.com/johannescoetzee))
* Fix IndexOutOfBoundsException resulting from empty varargs call as method usage (PR [#4754](https://github.com/javaparser/javaparser/pull/4754) by [@johannescoetzee](https://github.com/johannescoetzee))
* Fix resolution of lambdas used as varargs (PR [#4752](https://github.com/javaparser/javaparser/pull/4752) by [@johannescoetzee](https://github.com/johannescoetzee))
* Fix: issue 4747 Lexical preserving fails after replacing MarkerAnnotationExpr name (PR [#4748](https://github.com/javaparser/javaparser/pull/4748) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 4503 Unable to find the method declaration corresponding to a method reference (PR [#4739](https://github.com/javaparser/javaparser/pull/4739) by [@jlerbsc](https://github.com/jlerbsc))
* Fix issue 4724 Duplicate fields returned by JavaParserEnumDeclaration.getAllFields() (PR [#4735](https://github.com/javaparser/javaparser/pull/4735) by [@jlerbsc](https://github.com/jlerbsc))
* Make some helper methods protected in DefaultPrettyPrinterVisitor (PR [#4729](https://github.com/javaparser/javaparser/pull/4729) by [@johanneskloos](https://github.com/johanneskloos))
* Fix constructor resolution issue 4703 (PR [#4727](https://github.com/javaparser/javaparser/pull/4727) by [@johannescoetzee](https://github.com/johannescoetzee))
* Fix MethodAmbiguityException for methods with varargs (PR [#4725](https://github.com/javaparser/javaparser/pull/4725) by [@johannescoetzee](https://github.com/johannescoetzee))
* Fix range for cast expression with lambda child (PR [#4721](https://github.com/javaparser/javaparser/pull/4721) by [@johannescoetzee](https://github.com/johannescoetzee))
* Add Javadoc to the various parts of the DefaultPrettyPrinterVisitor (PR [#4718](https://github.com/javaparser/javaparser/pull/4718) by [@johanneskloos](https://github.com/johanneskloos))
* Make JarTypeSolver and ReflectionTypeSolver a bit more versatile. (PR [#4716](https://github.com/javaparser/javaparser/pull/4716) by [@johanneskloos](https://github.com/johanneskloos))
* Fix formatting issues (PR [#4715](https://github.com/javaparser/javaparser/pull/4715) by [@jlerbsc](https://github.com/jlerbsc))
* Fix Switch toString to LexicalPreservingPrinter when configured (PR [#4712](https://github.com/javaparser/javaparser/pull/4712) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 4697 Updating the com.google.guava:guava dependency to v334.5-jre fails. (PR [#4711](https://github.com/javaparser/javaparser/pull/4711) by [@jlerbsc](https://github.com/jlerbsc))
* Implement MethodResolutionCapability in JavassistRecordDeclaration (PR [#4709](https://github.com/javaparser/javaparser/pull/4709) by [@johanneskloos](https://github.com/johanneskloos))
* Fix: issue 4707 Upgrading from junit 5.11.4 -> 5.12.1 causes junit exception (PR [#4708](https://github.com/javaparser/javaparser/pull/4708) by [@jlerbsc](https://github.com/jlerbsc))
* Fix for #3710 by cutting off resolution loops involving object creation steps. (PR [#4704](https://github.com/javaparser/javaparser/pull/4704) by [@johanneskloos](https://github.com/johanneskloos))
* [SECURITY] Fix Zip Slip Vulnerability (PR [#3684](https://github.com/javaparser/javaparser/pull/3684) by [@JLLeitschuh](https://github.com/JLLeitschuh))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@johanneskloos](https://github.com/johanneskloos)
* [@johannescoetzee](https://github.com/johannescoetzee)
* [@jlerbsc](https://github.com/jlerbsc)
* [@JLLeitschuh](https://github.com/JLLeitschuh)

Version 3.26.4
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/211?closed=1)

### Developer Changes

* fix(deps): update byte-buddy.version to v1.17.5 (PR [#4702](https://github.com/javaparser/javaparser/pull/4702) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency com.puppycrawl.tools:checkstyle to v10.22.0 (PR [#4700](https://github.com/javaparser/javaparser/pull/4700) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-install-plugin to v3.1.4 (PR [#4689](https://github.com/javaparser/javaparser/pull/4689) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update codecov/codecov-action action to v5.4.0 (PR [#4688](https://github.com/javaparser/javaparser/pull/4688) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-deploy-plugin to v3.1.4 (PR [#4687](https://github.com/javaparser/javaparser/pull/4687) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency com.diffplug.spotless:spotless-maven-plugin to v2.44.3 (PR [#4682](https://github.com/javaparser/javaparser/pull/4682) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-clean-plugin to v3.4.1 (PR [#4681](https://github.com/javaparser/javaparser/pull/4681) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.assertj:assertj-core to v3.27.2 (PR [#4644](https://github.com/javaparser/javaparser/pull/4644) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update dependency com.google.guava:guava to v33.4.0-jre (PR [#4637](https://github.com/javaparser/javaparser/pull/4637) by [@renovate[bot]](https://github.com/apps/renovate))

### Uncategorised

* Fix: issue 4554 Import added through CompilationUnit.addImport should not have a range (PR [#4693](https://github.com/javaparser/javaparser/pull/4693) by [@jlerbsc](https://github.com/jlerbsc))
* Improving documentation on SwithEntry (PR [#4685](https://github.com/javaparser/javaparser/pull/4685) by [@jlerbsc](https://github.com/jlerbsc))
* Fix issue 4670 LexicalPreservingPrinter removed incorect token when removing modifier of a Parameter with annotations (PR [#4674](https://github.com/javaparser/javaparser/pull/4674) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 4668 Issue with FieldAccessExpr resolving for custom class (PR [#4671](https://github.com/javaparser/javaparser/pull/4671) by [@jlerbsc](https://github.com/jlerbsc))
* #4664 remove misleading javadoc (PR [#4666](https://github.com/javaparser/javaparser/pull/4666) by [@verhasi](https://github.com/verhasi))
* #4653 use report-aggregate of jacoco instead of report to use the dep… (PR [#4658](https://github.com/javaparser/javaparser/pull/4658) by [@verhasi](https://github.com/verhasi))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@jlerbsc](https://github.com/jlerbsc)
* [@verhasi](https://github.com/verhasi)

Version 3.26.3
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/210?closed=1)

### Changed

* Fixes #4599 making B.class for testing non-empty (PR [#4600](https://github.com/javaparser/javaparser/pull/4600) by [@JiriOndrusek](https://github.com/JiriOndrusek))

### Fixed

* Fix: issue 3990 Local Enum and Interface (Java 16) (PR [#4626](https://github.com/javaparser/javaparser/pull/4626) by [@jlerbsc](https://github.com/jlerbsc))
* Fix bug in `VisitorSet.toString()` (PR [#4615](https://github.com/javaparser/javaparser/pull/4615) by [@Laughh](https://github.com/Laughh))
* Fix issue #4607: don't forget to clone guard when cloning stmt.SwitchEntry (PR [#4608](https://github.com/javaparser/javaparser/pull/4608) by [@DaniilSuchkov](https://github.com/DaniilSuchkov))
* Fixed return within void method (PR [#4587](https://github.com/javaparser/javaparser/pull/4587) by [@Universe-E](https://github.com/Universe-E))
* Fix: issue 4579 Switch expr and var incompatibility (PR [#4581](https://github.com/javaparser/javaparser/pull/4581) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 4568 Resolution of ObjectCreationExprs broken (PR [#4577](https://github.com/javaparser/javaparser/pull/4577) by [@jlerbsc](https://github.com/jlerbsc))
* Fix issue 4560 Does not solve String.format on multiline strings (PR [#4561](https://github.com/javaparser/javaparser/pull/4561) by [@jlerbsc](https://github.com/jlerbsc))


### Developer Changes

* fix(deps): update byte-buddy.version to v1.15.11 (PR [#4635](https://github.com/javaparser/javaparser/pull/4635) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update codecov/codecov-action action to v5.1.0 (PR [#4629](https://github.com/javaparser/javaparser/pull/4629) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-javadoc-plugin to v3.11.1 (PR [#4605](https://github.com/javaparser/javaparser/pull/4605) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-surefire-plugin to v3.5.2 (PR [#4604](https://github.com/javaparser/javaparser/pull/4604) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update actions/checkout action to v4.2.2 (PR [#4594](https://github.com/javaparser/javaparser/pull/4594) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update junit5 monorepo to v5.11.3 (PR [#4589](https://github.com/javaparser/javaparser/pull/4589) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update dependency net.bytebuddy:byte-buddy-agent to v1.15.5 (PR [#4586](https://github.com/javaparser/javaparser/pull/4586) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update dependency com.google.guava:guava to v33.3.1-jre (PR [#4558](https://github.com/javaparser/javaparser/pull/4558) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.hamcrest:hamcrest to v3 (PR [#4510](https://github.com/javaparser/javaparser/pull/4510) by [@renovate[bot]](https://github.com/apps/renovate))

### Uncategorised


### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@DaniilSuchkov](https://github.com/DaniilSuchkov)
* [@JiriOndrusek](https://github.com/JiriOndrusek)
* [@jlerbsc](https://github.com/jlerbsc)
* [@Universe-E](https://github.com/Universe-E)
* [@Laughh](https://github.com/Laughh)


Version 3.26.2
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/209?closed=1)


### Changed

* Move formatting workflows into separate file (PR [#4480](https://github.com/javaparser/javaparser/pull/4480) by [@johannescoetzee](https://github.com/johannescoetzee))
* Exclude unavailable macos <-> java version combinations from github tests (PR [#4479](https://github.com/javaparser/javaparser/pull/4479) by [@johannescoetzee](https://github.com/johannescoetzee))

### Fixed

* Fixes #4526. Fix Node.PostOrderIterator for roots without children (PR [#4538](https://github.com/javaparser/javaparser/pull/4538) by [@ktul](https://github.com/ktul))
* Add missing copyright notice to RecordPatternExpr.java (PR [#4527](https://github.com/javaparser/javaparser/pull/4527) by [@johannescoetzee](https://github.com/johannescoetzee))
* Add missing type erasure in ClassOrInterfaceType.toDescriptor (PR [#4522](https://github.com/javaparser/javaparser/pull/4522) by [@johanneskloos](https://github.com/johanneskloos))
* Allow primitive types for patterns (PR [#4506](https://github.com/javaparser/javaparser/pull/4506) by [@johannescoetzee](https://github.com/johannescoetzee))
* Fix project formatting (PR [#4499](https://github.com/javaparser/javaparser/pull/4499) by [@johannescoetzee](https://github.com/johannescoetzee))
* Fix: issue 4492 resolve LambdaExpr has NullPointException (PR [#4497](https://github.com/javaparser/javaparser/pull/4497) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 2738 UnsolvedSymbolException while trying to ResolvedMethodDeclaration from MethodCallExpr (PR [#4482](https://github.com/javaparser/javaparser/pull/4482) by [@jlerbsc](https://github.com/jlerbsc))

### Developer Changes

* fix(deps): update byte-buddy.version to v1.15.1 (PR [#4547](https://github.com/javaparser/javaparser/pull/4547) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update byte-buddy.version to v1.15.0 (PR [#4543](https://github.com/javaparser/javaparser/pull/4543) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update dependency com.google.guava:guava to v33.3.0-jre (PR [#4532](https://github.com/javaparser/javaparser/pull/4532) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update dependency net.bytebuddy:byte-buddy-agent to v1.14.19 (PR [#4531](https://github.com/javaparser/javaparser/pull/4531) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update junit5 monorepo to v5.11.0 (PR [#4528](https://github.com/javaparser/javaparser/pull/4528) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update byte-buddy.version to v1.14.18 (PR [#4493](https://github.com/javaparser/javaparser/pull/4493) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update actions/checkout action to v4.1.7 (PR [#4486](https://github.com/javaparser/javaparser/pull/4486) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update actions/checkout action to v4.0.0 (PR [#4485](https://github.com/javaparser/javaparser/pull/4485) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update junit5 monorepo to v5.10.3 (PR [#4483](https://github.com/javaparser/javaparser/pull/4483) by [@renovate[bot]](https://github.com/apps/renovate))

### Uncategorised

* Add better instructions for re-formatting the project (PR [#4540](https://github.com/javaparser/javaparser/pull/4540) by [@johannescoetzee](https://github.com/johannescoetzee))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@johanneskloos](https://github.com/johanneskloos)
* [@ktul](https://github.com/ktul)
* [@johannescoetzee](https://github.com/johannescoetzee)
* [@kamilkrzywanski](https://github.com/kamilkrzywanski)
* [@jlerbsc](https://github.com/jlerbsc)


Version 3.26.1
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/208?closed=1)

### Added

* Fix record declarations nested in annotation declarations (PR [#4460](https://github.com/javaparser/javaparser/pull/4460) by [@johannescoetzee](https://github.com/johannescoetzee))

### Changed

* Format code with spotless (PR [#4465](https://github.com/javaparser/javaparser/pull/4465) by [@johannescoetzee](https://github.com/johannescoetzee))
* Simplifying the search for types in compilation unit (PR [#4459](https://github.com/javaparser/javaparser/pull/4459) by [@jlerbsc](https://github.com/jlerbsc))
* Add spotless plugin configuration (PR [#4409](https://github.com/javaparser/javaparser/pull/4409) by [@johannescoetzee](https://github.com/johannescoetzee))

### Fixed

* Disable spotless ratcheting and fix formatting (PR [#4478](https://github.com/javaparser/javaparser/pull/4478) by [@johannescoetzee](https://github.com/johannescoetzee))
* Fix: issue 4450 Endless recursion (-> StackOverflow) with cyclic static references (PR [#4477](https://github.com/javaparser/javaparser/pull/4477) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 4399 MethodCallExpr inside lambda in assignment expression cannot be resolved (PR [#4462](https://github.com/javaparser/javaparser/pull/4462) by [@jlerbsc](https://github.com/jlerbsc))
* Fix crash on SwitchExpr entries if tokens are not stored (PR [#4461](https://github.com/javaparser/javaparser/pull/4461) by [@johannescoetzee](https://github.com/johannescoetzee))
* Fix lookahead for pattern expression in switch entries [Issue 4455] (PR [#4458](https://github.com/javaparser/javaparser/pull/4458) by [@johannescoetzee](https://github.com/johannescoetzee))

### Developer Changes

* Automatically format code after codegen and validate with a github action (PR [#4468](https://github.com/javaparser/javaparser/pull/4468) by [@johannescoetzee](https://github.com/johannescoetzee))
* Add git-blame-ignore-revs file to ignore the reformatting commit in git blame (PR [#4466](https://github.com/javaparser/javaparser/pull/4466) by [@johannescoetzee](https://github.com/johannescoetzee))

### Uncategorised

* Add link to the guide to adding nodes in CONTRIBUTING.md (PR [#4453](https://github.com/javaparser/javaparser/pull/4453) by [@johannescoetzee](https://github.com/johannescoetzee))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@johannescoetzee](https://github.com/johannescoetzee)
* [@jlerbsc](https://github.com/jlerbsc)



Version 3.26.0
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/207?closed=1)

### Added

* [JEP 440] Add support for record patterns (PR [#4432](https://github.com/javaparser/javaparser/pull/4432) by [@johannescoetzee](https://github.com/johannescoetzee))
* PatternExpr -> TypePatternExpr refactor in preparation for record pattern implementation (PR [#4387](https://github.com/javaparser/javaparser/pull/4387) by [@johannescoetzee](https://github.com/johannescoetzee))
* [JEP441] Add support for switch pattern matching (PR [#4375](https://github.com/javaparser/javaparser/pull/4375) by [@johannescoetzee](https://github.com/johannescoetzee))
* Add support for `case null, default` in switch and fix concrete syntax model for new switch syntax (PR [#4364](https://github.com/javaparser/javaparser/pull/4364) by [@johannescoetzee](https://github.com/johannescoetzee))

### Changed

* Fixes SYSTEM_EOL warnings (PR [#4412](https://github.com/javaparser/javaparser/pull/4412) by [@matthieu-vergne](https://github.com/matthieu-vergne))
* Refact: Adds a find node by range method in Node class (PR [#4377](https://github.com/javaparser/javaparser/pull/4377) by [@jlerbsc](https://github.com/jlerbsc))

### Fixed

* Fix: issue 3277 StackOverflow issue while parse MethodCallExpr/FieldAccessExpr, their ancestor/child node is ObjectCreation expression which contain .new (PR [#4447](https://github.com/javaparser/javaparser/pull/4447) by [@jlerbsc](https://github.com/jlerbsc))
* Fix expressions in the body of switch expression entries (Issue 4440) (PR [#4446](https://github.com/javaparser/javaparser/pull/4446) by [@johannescoetzee](https://github.com/johannescoetzee))
* Fix: issue 4442 LexicalPreservingPrinter does not support unexpected token (PR [#4444](https://github.com/javaparser/javaparser/pull/4444) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 3100 JavaSymbolSolver unable to resolve an inner class defined in a base class (PR [#4441](https://github.com/javaparser/javaparser/pull/4441) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: 4330 Method 'forEach' cannot be resolved in certain context (PR [#4436](https://github.com/javaparser/javaparser/pull/4436) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: 'permits' and 'sealed' Contextual keyworlds usage (PR [#4434](https://github.com/javaparser/javaparser/pull/4434) by [@jlerbsc](https://github.com/jlerbsc))
* Fixes an error in jbehave tests when they are run in a Windows os (PR [#4433](https://github.com/javaparser/javaparser/pull/4433) by [@jlerbsc](https://github.com/jlerbsc))
* Make resolution of implements and extends types start with the parent… (PR [#4430](https://github.com/javaparser/javaparser/pull/4430) by [@eldapiiro](https://github.com/eldapiiro))
* Fix: solveMethodAsUsage() for implicit method <enum>::values() (PR [#4424](https://github.com/javaparser/javaparser/pull/4424) by [@Kimmmey](https://github.com/Kimmmey))
* Fix: <enum>::values() is a static method, was not static (PR [#4417](https://github.com/javaparser/javaparser/pull/4417) by [@Kimmmey](https://github.com/Kimmmey))
* Fix missed generated code from PatternExpr refactor (PR [#4414](https://github.com/javaparser/javaparser/pull/4414) by [@johannescoetzee](https://github.com/johannescoetzee))
* Fixes #4410 (PR [#4411](https://github.com/javaparser/javaparser/pull/4411) by [@matthieu-vergne](https://github.com/matthieu-vergne))
* Fix issue 2368 Unable to calculate the type of a varargs parameter (PR [#4402](https://github.com/javaparser/javaparser/pull/4402) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: Fixes the version currently supported by Javaparser. (PR [#4393](https://github.com/javaparser/javaparser/pull/4393) by [@jlerbsc](https://github.com/jlerbsc))
* ?? make mvnw command runnable by copy-pasting (PR [#4382](https://github.com/javaparser/javaparser/pull/4382) by [@cravingPixels](https://github.com/cravingPixels))

### Developer Changes

* chore(deps): bump actions/checkout from 4.1.4 to 4.1.5 (PR [#4415](https://github.com/javaparser/javaparser/pull/4415) by [@dependabot[bot]](https://github.com/apps/dependabot))
* Minor refactoring on Concrete syntax model (PR [#4405](https://github.com/javaparser/javaparser/pull/4405) by [@jlerbsc](https://github.com/jlerbsc))
* chore(deps): bump actions/checkout from 4.1.2 to 4.1.3 (PR [#4381](https://github.com/javaparser/javaparser/pull/4381) by [@dependabot[bot]](https://github.com/apps/dependabot))

### Uncategorised

* Improve unit test on generic (PR [#4407](https://github.com/javaparser/javaparser/pull/4407) by [@jlerbsc](https://github.com/jlerbsc))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@eldapiiro](https://github.com/eldapiiro)
* [@cravingPixels](https://github.com/cravingPixels)
* [@johannescoetzee](https://github.com/johannescoetzee)
* [@matthieu-vergne](https://github.com/matthieu-vergne)
* [@jlerbsc](https://github.com/jlerbsc)
* [@Kimmmey](https://github.com/Kimmmey)


Version 3.25.10
---------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/206?closed=1)

### Fixed

* Fix issue 4345 Strange error when trying to find erasure of generic t… (PR [#4362](https://github.com/javaparser/javaparser/pull/4362) by [@jlerbsc](https://github.com/jlerbsc))
* fix: issue 4358 prevent infinite cycles with static imports (PR [#4359](https://github.com/javaparser/javaparser/pull/4359) by [@kdunee](https://github.com/kdunee))
* Refactor `ResolvedReferenceType#equals` (PR [#4351](https://github.com/javaparser/javaparser/pull/4351) by [@freya022](https://github.com/freya022))
* fix: issue 4331 Cannot be 'abstract' and also 'private'. for a private method in an interface (PR [#4332](https://github.com/javaparser/javaparser/pull/4332) by [@jlerbsc](https://github.com/jlerbsc))

### Developer Changes

* chore(deps): bump actions/checkout from 4.1.1 to 4.1.2 (PR [#4341](https://github.com/javaparser/javaparser/pull/4341) by [@dependabot[bot]](https://github.com/apps/dependabot))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@kdunee](https://github.com/kdunee)
* [@freya022](https://github.com/freya022)
* [@jlerbsc](https://github.com/jlerbsc)



Version 3.25.9
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/205?closed=1)

### Added

* Fix: issue #3878 resolve MethodReference in ObjectCreationExpr (PR [#4296](https://github.com/javaparser/javaparser/pull/4296) by [@fishautumn](https://github.com/fishautumn))

### Changed

* Switch order of literals to prevent NullPointerException (PR [#4322](https://github.com/javaparser/javaparser/pull/4322) by [@citizenjosh](https://github.com/citizenjosh))
* Minor refactoring to use the existing getArgumentPosition method (PR [#4306](https://github.com/javaparser/javaparser/pull/4306) by [@jlerbsc](https://github.com/jlerbsc))
* Optimize find ancestor (PR [#4294](https://github.com/javaparser/javaparser/pull/4294) by [@magicwerk](https://github.com/magicwerk))
* refac: Removes useless ExpressionHelper utility class and replaces some explicit casts by using the javaparser API (PR [#4291](https://github.com/javaparser/javaparser/pull/4291) by [@jlerbsc](https://github.com/jlerbsc))

### Fixed

* fix: Dead stores should be removed (sonar rule) (PR [#4329](https://github.com/javaparser/javaparser/pull/4329) by [@jlerbsc](https://github.com/jlerbsc))
* fix: Replace this if-then-else statement by a single return statement (sonar rule) (PR [#4328](https://github.com/javaparser/javaparser/pull/4328) by [@jlerbsc](https://github.com/jlerbsc))
* fix: issue 2043 getAccessSpecifier should return public for interface methods (PR [#4317](https://github.com/javaparser/javaparser/pull/4317) by [@jlerbsc](https://github.com/jlerbsc))
* Further improve correction of whitespace during difference application (PR [#4316](https://github.com/javaparser/javaparser/pull/4316) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue #3946 Symbol solver is unable to resolve inherited inner classes (PR [#4314](https://github.com/javaparser/javaparser/pull/4314) by [@jlerbsc](https://github.com/jlerbsc))
* fix: issue 4311 IllegalStateException when removing all comments with LexicalPreservingPrinter (PR [#4313](https://github.com/javaparser/javaparser/pull/4313) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 3939 SymbolResolver.calculateType(Expression) may fails on first try, then succeed on later tries (PR [#4290](https://github.com/javaparser/javaparser/pull/4290) by [@jlerbsc](https://github.com/jlerbsc))
* Adds unit test for issue 4284 "ClassCastException when resolving MethodCallExpr inside an enhanced switch statement" (PR [#4285](https://github.com/javaparser/javaparser/pull/4285) by [@jlerbsc](https://github.com/jlerbsc))
* Change `SwitchStmt` to `SwitchNode` in `SwitchEntryContext` to avoid `ClassCastException` (PR [#4283](https://github.com/javaparser/javaparser/pull/4283) by [@PalashSharma20](https://github.com/PalashSharma20))

### Developer Changes

* chore(deps): bump org.codehaus.mojo:exec-maven-plugin from 3.1.1 to 3.2.0 (PR [#4323](https://github.com/javaparser/javaparser/pull/4323) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update junit5 monorepo to v5.10.2 (PR [#4307](https://github.com/javaparser/javaparser/pull/4307) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update codecov/codecov-action action to v4 (PR [#4304](https://github.com/javaparser/javaparser/pull/4304) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update actions/cache action to v4 (PR [#4293](https://github.com/javaparser/javaparser/pull/4293) by [@renovate[bot]](https://github.com/apps/renovate))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@citizenjosh](https://github.com/citizenjosh)
* [@magicwerk](https://github.com/magicwerk)
* [@PalashSharma20](https://github.com/PalashSharma20)
* [@jlerbsc](https://github.com/jlerbsc)
* [@fishautumn](https://github.com/fishautumn)


Version 3.25.8
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/204?closed=1)

### Added

* feat: creates cache statistics and moves Cache interface to javaparser-core (PR [#4278](https://github.com/javaparser/javaparser/pull/4278) by [@jlerbsc](https://github.com/jlerbsc))
* feat: Add parseArrayInitializerExpr to JavaParser API (PR [#4276](https://github.com/javaparser/javaparser/pull/4276) by [@iMashtak](https://github.com/iMashtak))
* feat: A visitor looking for a node by its position in an AST (PR [#4258](https://github.com/javaparser/javaparser/pull/4258) by [@jlerbsc](https://github.com/jlerbsc))

### Changed

* fix: Partial removal of the use of instanceof in favour of the use of the API (PR [#4280](https://github.com/javaparser/javaparser/pull/4280) by [@jlerbsc](https://github.com/jlerbsc))
* [GHA] Run on java 18 (PR [#4252](https://github.com/javaparser/javaparser/pull/4252) by [@hazendaz](https://github.com/hazendaz))

### Fixed

* fix: issue 4240 Calling resolve on catch block parameter throws exception (PR [#4279](https://github.com/javaparser/javaparser/pull/4279) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 4270 Exception when resolving ObjectCreationExpr with nested varargs (PR [#4273](https://github.com/javaparser/javaparser/pull/4273) by [@jlerbsc](https://github.com/jlerbsc))
* add Java_18 to yieldSupport (PR [#4262](https://github.com/javaparser/javaparser/pull/4262) by [@Kimmmey](https://github.com/Kimmmey))
* fix: issue #4245 UnsupportedOperationException with LexicalPreservingPrinter when removing a sealed modified (PR [#4253](https://github.com/javaparser/javaparser/pull/4253) by [@jlerbsc](https://github.com/jlerbsc))
* [ci] Fix change log released version as 3.25.7 (PR [#4251](https://github.com/javaparser/javaparser/pull/4251) by [@hazendaz](https://github.com/hazendaz))
* Fix: issue 3278 Lazy types cause stack overflow when trying to find the least upper bound type (PR [#4246](https://github.com/javaparser/javaparser/pull/4246) by [@jlerbsc](https://github.com/jlerbsc))

### Developer Changes

* chore(deps): bump com.google.guava:guava from 32.1.3-jre to 33.0.0-jre (PR [#4264](https://github.com/javaparser/javaparser/pull/4264) by [@dependabot[bot]](https://github.com/apps/dependabot))

### Uncategorised

* Revert "Refactoring: Move cache features to javaparser-core" (PR [#4274](https://github.com/javaparser/javaparser/pull/4274) by [@jlerbsc](https://github.com/jlerbsc))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@hazendaz](https://github.com/hazendaz)
* [@iMashtak](https://github.com/iMashtak)
* [@jlerbsc](https://github.com/jlerbsc)
* [@Kimmmey](https://github.com/Kimmmey)

Version 3.25.7
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/203?closed=1)

### Added

* [GHA] Remove old comment that is no longer valid around jdks and add jdk 17 (PR [#4226](https://github.com/javaparser/javaparser/pull/4226) by [@hazendaz](https://github.com/hazendaz))
* Fix: issue 3833 No enum constant com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_18 (PR [#4221](https://github.com/javaparser/javaparser/pull/4221) by [@jlerbsc](https://github.com/jlerbsc))

### Changed

* Refactoring: Move cache features to javaparser-core (PR [#4238](https://github.com/javaparser/javaparser/pull/4238) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: removes reference to coveralls plugin which is not useful because codecov is used to track code coverage (PR [#4235](https://github.com/javaparser/javaparser/pull/4235) by [@jlerbsc](https://github.com/jlerbsc))
* Uses jakarta.json api, upgrades jakarta.json-api to the latest version & uses new default  Eclipse Parsson (PR [#4234](https://github.com/javaparser/javaparser/pull/4234) by [@jlerbsc](https://github.com/jlerbsc))
* Move mockito to 4.11.0 and handle byte buddy consistently as well as properly define its agent in argLine for surefire (PR [#4228](https://github.com/javaparser/javaparser/pull/4228) by [@hazendaz](https://github.com/hazendaz))
* Cleanup poms, use jakarta provided (javax namespace), hamcrest follow up, and switch coveralls plugin - Fixes #4111 (PR [#4225](https://github.com/javaparser/javaparser/pull/4225) by [@hazendaz](https://github.com/hazendaz))
* [pom] Switch from hamcrest-library (deprecated) to hamcrest (PR [#4200](https://github.com/javaparser/javaparser/pull/4200) by [@hazendaz](https://github.com/hazendaz))
* Putting code in the .orElse that has a side effect that can affect performance (PR [#4199](https://github.com/javaparser/javaparser/pull/4199) by [@jlerbsc](https://github.com/jlerbsc))

### Fixed

* Fix: issue 3650 unreproducible MAVEN_BUILD_TIMESTAMP (PR [#4243](https://github.com/javaparser/javaparser/pull/4243) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 3972 StackOverflowError when resolving type of scope of a MethodCall (PR [#4236](https://github.com/javaparser/javaparser/pull/4236) by [@jlerbsc](https://github.com/jlerbsc))
* [fix] Jdk 18 enum stub was extended off java 16 post processor not java17 (PR [#4227](https://github.com/javaparser/javaparser/pull/4227) by [@hazendaz](https://github.com/hazendaz))
* Fix: issue #4047 Symbol Solver mixes name with type (PR [#4206](https://github.com/javaparser/javaparser/pull/4206) by [@jlerbsc](https://github.com/jlerbsc))
* Fix grammar (PR [#4203](https://github.com/javaparser/javaparser/pull/4203) by [@mernst](https://github.com/mernst))
* Minor changes : corrupted format, useless cast, javadoc (PR [#4198](https://github.com/javaparser/javaparser/pull/4198) by [@jlerbsc](https://github.com/jlerbsc))

### Developer Changes

* chore(deps): update actions/setup-java action to v4 (PR [#4241](https://github.com/javaparser/javaparser/pull/4241) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): bump org.codehaus.mojo:build-helper-maven-plugin from 3.4.0 to 3.5.0 (PR [#4223](https://github.com/javaparser/javaparser/pull/4223) by [@dependabot[bot]](https://github.com/apps/dependabot))
* Adds sponsor link to help the project live and grow (PR [#4204](https://github.com/javaparser/javaparser/pull/4204) by [@jlerbsc](https://github.com/jlerbsc))
* chore(deps): bump org.codehaus.mojo:templating-maven-plugin from 1.0.0 to 3.0.0 (PR [#4195](https://github.com/javaparser/javaparser/pull/4195) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update junit5 monorepo to v5.10.1 (PR [#4193](https://github.com/javaparser/javaparser/pull/4193) by [@renovate[bot]](https://github.com/apps/renovate))

### Uncategorised

* Added unit tests for visitors (PR [#4239](https://github.com/javaparser/javaparser/pull/4239) by [@4everTheOne](https://github.com/4everTheOne))
* Unit tests for class GenericListVisitorAdapter (PR [#4237](https://github.com/javaparser/javaparser/pull/4237) by [@4everTheOne](https://github.com/4everTheOne))
* Update readme.md (PR [#4222](https://github.com/javaparser/javaparser/pull/4222) by [@jlerbsc](https://github.com/jlerbsc))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@hazendaz](https://github.com/hazendaz)
* [@jlerbsc](https://github.com/jlerbsc)
* [@mernst](https://github.com/mernst)
* [@4everTheOne](https://github.com/4everTheOne)


Version 3.25.6
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/202?closed=1)

### Changed

* reformat javaconcept take 2 (PR [#4167](https://github.com/javaparser/javaparser/pull/4167) by [@JimmyGan437](https://github.com/JimmyGan437))
* Using JAXP on XMLPrinter implementation (PR [#4166](https://github.com/javaparser/javaparser/pull/4166) by [@lcbarcellos](https://github.com/lcbarcellos))
* replace deprecated methond calls to their replacements (PR [#4157](https://github.com/javaparser/javaparser/pull/4157) by [@JimmyGan437](https://github.com/JimmyGan437))
* feat(#4075): Improve the validation error messages (PR [#4116](https://github.com/javaparser/javaparser/pull/4116) by [@volodya-lombrozo](https://github.com/volodya-lombrozo))

### Fixed

* Fix: issue #2751 new HashSet()" != "new HashSet<>() (PR [#4183](https://github.com/javaparser/javaparser/pull/4183) by [@lcbarcellos](https://github.com/lcbarcellos))
* Fixes #2625 Add messages to thrown exceptions (PR [#4177](https://github.com/javaparser/javaparser/pull/4177) by [@oannhpham](https://github.com/oannhpham))
* Fix: issue 4163 Calling MethodDeclaration.getDeclarationAsString leads to MethodDelaration.getComment returning no comment (PR [#4165](https://github.com/javaparser/javaparser/pull/4165) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 3673 isAssignableBy method StackOverflowError (PR [#4156](https://github.com/javaparser/javaparser/pull/4156) by [@jlerbsc](https://github.com/jlerbsc))
* fix: issue 3184 Unable to get the resolved type of class ResolvedReferenceType from T (PR [#4147](https://github.com/javaparser/javaparser/pull/4147) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue #3269 Test resources containing included interfaces do not compile (PR [#4139](https://github.com/javaparser/javaparser/pull/4139) by [@jlerbsc](https://github.com/jlerbsc))
* CalculateResolvedType Type error (PR [#4138](https://github.com/javaparser/javaparser/pull/4138) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue #4036 LeastUpperBoundLogic.lub returns null when matches ConditionalExpr (PR [#4137](https://github.com/javaparser/javaparser/pull/4137) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue #2484 SymbolResolver on MethodCallExpr fails if method parameter is of kind Class<? extends y> (PR [#4136](https://github.com/javaparser/javaparser/pull/4136) by [@jlerbsc](https://github.com/jlerbsc))

### Developer Changes

* chore(deps): bump com.google.guava:guava from 32.1.2-jre to 32.1.3-jre (PR [#4154](https://github.com/javaparser/javaparser/pull/4154) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update actions/checkout action to v4 (PR [#4141](https://github.com/javaparser/javaparser/pull/4141) by [@renovate[bot]](https://github.com/apps/renovate))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@lcbarcellos](https://github.com/lcbarcellos)
* [@volodya-lombrozo](https://github.com/volodya-lombrozo)
* [@JimmyGan437](https://github.com/JimmyGan437)
* [@jlerbsc](https://github.com/jlerbsc)
* [@oannhpham](https://github.com/oannhpham)



Version 3.25.5
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/201?closed=1)

### Added

* fix: issue 4115 ResolvedUnionType should give access to a list of resolved types (PR [#4119](https://github.com/javaparser/javaparser/pull/4119) by [@jlerbsc](https://github.com/jlerbsc))
* Support getting more annotation default values using reflection (PR [#4103](https://github.com/javaparser/javaparser/pull/4103) by [@freya022](https://github.com/freya022))

### Changed

* Minor refactoring: Simplifies how to group deleted tokens by extracting a method into an independent class (PR [#4134](https://github.com/javaparser/javaparser/pull/4134) by [@jlerbsc](https://github.com/jlerbsc))
* Replace deprecated command with environment file (PR [#4122](https://github.com/javaparser/javaparser/pull/4122) by [@70825](https://github.com/70825))
* Fixes missing named constructor in Modifier.java  (PR [#4092](https://github.com/javaparser/javaparser/pull/4092) by [@Auties00](https://github.com/Auties00))

### Fixed

* Fix: issue 4133 Top-level class containerType() throws an exception instead of Optional.empty() (PR [#4135](https://github.com/javaparser/javaparser/pull/4135) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: apply multiline strings (PR [#4130](https://github.com/javaparser/javaparser/pull/4130) by [@70825](https://github.com/70825))
* Fix: issue 3976 Issue resolving implicit generic types (PR [#4128](https://github.com/javaparser/javaparser/pull/4128) by [@jlerbsc](https://github.com/jlerbsc))
* Add unit test for PR 4091 Fixed missing permits in pretty printer (PR [#4126](https://github.com/javaparser/javaparser/pull/4126) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 4124 UnsupportedOperationException: 'T' is thrown in MethodCallExpr resolve (PR [#4125](https://github.com/javaparser/javaparser/pull/4125) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 4051 Switched upperBounds and lowerBounds on ResolvedTypeP… (PR [#4123](https://github.com/javaparser/javaparser/pull/4123) by [@jlerbsc](https://github.com/jlerbsc))
* Fix failing test on JDK 17 (PR [#4121](https://github.com/javaparser/javaparser/pull/4121) by [@mahesh-hegde](https://github.com/mahesh-hegde))
* Fix: issue 3673 isAssignableBy method StackOverflowError (PR [#4118](https://github.com/javaparser/javaparser/pull/4118) by [@jlerbsc](https://github.com/jlerbsc))
* Orphan comment added when using lexical preservation is not printed (PR [#4114](https://github.com/javaparser/javaparser/pull/4114) by [@jlerbsc](https://github.com/jlerbsc))
* Fixed missing permits in pretty printer (PR [#4091](https://github.com/javaparser/javaparser/pull/4091) by [@Auties00](https://github.com/Auties00))

### Developer Changes

* chore(deps): update actions/checkout action to v3.6.0 (PR [#4127](https://github.com/javaparser/javaparser/pull/4127) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): bump com.google.guava:guava from 32.1.1-jre to 32.1.2-jre (PR [#4109](https://github.com/javaparser/javaparser/pull/4109) by [@dependabot[bot]](https://github.com/apps/dependabot))

### Uncategorised

* Fix: issue 4104 LPP doesn't handle new switch entries well (PR [#4106](https://github.com/javaparser/javaparser/pull/4106) by [@jlerbsc](https://github.com/jlerbsc))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@freya022](https://github.com/freya022)
* [@Auties00](https://github.com/Auties00)
* [@mahesh-hegde](https://github.com/mahesh-hegde)
* [@jlerbsc](https://github.com/jlerbsc)
* [@70825](https://github.com/70825)


Version 3.25.4
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/200?closed=1)

### Changed

* Nested 'if' statements should be simplified (PR [#4085](https://github.com/javaparser/javaparser/pull/4085) by [@jlerbsc](https://github.com/jlerbsc))
* BDD tests: migarte to JBehave 5 (PR [#4028](https://github.com/javaparser/javaparser/pull/4028) by [@valfirst](https://github.com/valfirst))

### Fixed

* Fix: issue 4077 After building JavaParser (with tests) on MacOS multi… (PR [#4086](https://github.com/javaparser/javaparser/pull/4086) by [@jlerbsc](https://github.com/jlerbsc))
* fix line separators of selected test files (PR [#4083](https://github.com/javaparser/javaparser/pull/4083) by [@abego](https://github.com/abego))
* Fix: issue 3978 typesolver can't parse in parallel (PR [#4073](https://github.com/javaparser/javaparser/pull/4073) by [@jlerbsc](https://github.com/jlerbsc))
* Fix #4056 isDeclaredInInterface() returns true for fields declared inside enumerations contained in an interface (PR [#4057](https://github.com/javaparser/javaparser/pull/4057) by [@Elewyth](https://github.com/Elewyth))
* Fix: issue 4037 ArrayIndexOutOfBoundsException throws when method param is variadic (PR [#4046](https://github.com/javaparser/javaparser/pull/4046) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 4016 Failed to parse variable with name 'sealed' or 'permits' (PR [#4039](https://github.com/javaparser/javaparser/pull/4039) by [@jlerbsc](https://github.com/jlerbsc))

### Developer Changes

* chore(deps): bump guava from 32.1.0-jre to 32.1.1-jre (PR [#4089](https://github.com/javaparser/javaparser/pull/4089) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump guava from 32.0.0-jre to 32.1.0-jre (PR [#4087](https://github.com/javaparser/javaparser/pull/4087) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump checkstyle from 10.12.0 to 10.12.1 (PR [#4084](https://github.com/javaparser/javaparser/pull/4084) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump versions-maven-plugin from 2.15.0 to 2.16.0 (PR [#4055](https://github.com/javaparser/javaparser/pull/4055) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump maven-release-plugin from 3.0.0 to 3.0.1 (PR [#4053](https://github.com/javaparser/javaparser/pull/4053) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump guava from 31.1-jre to 32.0.0-jre (PR [#4042](https://github.com/javaparser/javaparser/pull/4042) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump maven-dependency-plugin from 3.5.0 to 3.6.0 (PR [#4035](https://github.com/javaparser/javaparser/pull/4035) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump maven-checkstyle-plugin from 3.2.2 to 3.3.0 (PR [#4033](https://github.com/javaparser/javaparser/pull/4033) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump maven-scm-plugin from 2.0.0 to 2.0.1 (PR [#4031](https://github.com/javaparser/javaparser/pull/4031) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump codecov/codecov-action from 3.1.3 to 3.1.4 (PR [#4030](https://github.com/javaparser/javaparser/pull/4030) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump build-helper-maven-plugin from 3.3.0 to 3.4.0 (PR [#4026](https://github.com/javaparser/javaparser/pull/4026) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update dependency maven to v3.9.2 (PR [#4024](https://github.com/javaparser/javaparser/pull/4024) by [@renovate[bot]](https://github.com/apps/renovate))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@valfirst](https://github.com/valfirst)
* [@abego](https://github.com/abego)
* [@Elewyth](https://github.com/Elewyth)
* [@jlerbsc](https://github.com/jlerbsc)


Version 3.25.3
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/199?closed=1)


### Added

* add Java 17 sealed/non-sealed classes (PR [#3997](https://github.com/javaparser/javaparser/pull/3997) by [@kris-scheibe](https://github.com/kris-scheibe))

### Changed

* Minor simplification of the Difference class (PR [#4008](https://github.com/javaparser/javaparser/pull/4008) by [@jlerbsc](https://github.com/jlerbsc))
* Perf: Remove unnecessary methods and quickly return to the Range.cont… (PR [#3996](https://github.com/javaparser/javaparser/pull/3996) by [@jlerbsc](https://github.com/jlerbsc))

### Fixed

* Fix: issue 1843 Problems with hasAnnotation() and hasDirectlyAnnotati… (PR [#4015](https://github.com/javaparser/javaparser/pull/4015) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: Issue 3995 resolving a method call with a variadic argument of p… (PR [#3998](https://github.com/javaparser/javaparser/pull/3998) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 3983 why FieldDeclaration in an interface calling isStatic… (PR [#3986](https://github.com/javaparser/javaparser/pull/3986) by [@jlerbsc](https://github.com/jlerbsc))

### Developer Changes

* chore(deps): bump checkstyle from 10.9.3 to 10.10.0 (PR [#4014](https://github.com/javaparser/javaparser/pull/4014) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update junit5 monorepo to v5.9.3 (PR [#4012](https://github.com/javaparser/javaparser/pull/4012) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): bump jacoco-maven-plugin from 0.8.9 to 0.8.10 (PR [#4011](https://github.com/javaparser/javaparser/pull/4011) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps-dev): bump okhttp from 4.10.0 to 4.11.0 (PR [#4009](https://github.com/javaparser/javaparser/pull/4009) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump codecov/codecov-action from 3.1.2 to 3.1.3 (PR [#4006](https://github.com/javaparser/javaparser/pull/4006) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump maven-checkstyle-plugin from 3.2.1 to 3.2.2 (PR [#4005](https://github.com/javaparser/javaparser/pull/4005) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump actions/checkout from 3.5.1 to 3.5.2 (PR [#3994](https://github.com/javaparser/javaparser/pull/3994) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump actions/checkout from 3.5.0 to 3.5.1 (PR [#3992](https://github.com/javaparser/javaparser/pull/3992) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump codecov/codecov-action from 3.1.1 to 3.1.2 (PR [#3988](https://github.com/javaparser/javaparser/pull/3988) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump maven-deploy-plugin from 3.1.0 to 3.1.1 (PR [#3985](https://github.com/javaparser/javaparser/pull/3985) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump jacoco-maven-plugin from 0.8.8 to 0.8.9 (PR [#3981](https://github.com/javaparser/javaparser/pull/3981) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump checkstyle from 10.9.1 to 10.9.3 (PR [#3980](https://github.com/javaparser/javaparser/pull/3980) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump maven-resources-plugin from 3.3.0 to 3.3.1 (PR [#3979](https://github.com/javaparser/javaparser/pull/3979) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump maven-install-plugin from 3.1.0 to 3.1.1 (PR [#3975](https://github.com/javaparser/javaparser/pull/3975) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump maven-release-plugin from 2.5.3 to 3.0.0 (PR [#3965](https://github.com/javaparser/javaparser/pull/3965) by [@dependabot[bot]](https://github.com/apps/dependabot))

### Uncategorised

* add test for showing interface field shall be static & final (PR [#3984](https://github.com/javaparser/javaparser/pull/3984) by [@XenoAmess](https://github.com/XenoAmess))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@kris-scheibe](https://github.com/kris-scheibe)
* [@jlerbsc](https://github.com/jlerbsc)
* [@XenoAmess](https://github.com/XenoAmess)


Version 3.25.2
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/198?closed=1)

### Changed

* chore(deps): bump maven-scm-plugin from 1.13.0 to 2.0.0 (PR [#3961](https://github.com/javaparser/javaparser/pull/3961) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump checkstyle from 10.8.1 to 10.9.1 (PR [#3958](https://github.com/javaparser/javaparser/pull/3958) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump actions/checkout from 3.3.0 to 3.4.0 (PR [#3954](https://github.com/javaparser/javaparser/pull/3954) by [@dependabot[bot]](https://github.com/apps/dependabot))

### Fixed

* Fix: issue 3947 MANIFEST.MF points to non-existent URL (PR [#3966](https://github.com/javaparser/javaparser/pull/3966) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 3951 ConfilictingGenericTypesException is thrown when an Object type is expected as a parameter and an interface is provided as the actual parameter (PR [#3963](https://github.com/javaparser/javaparser/pull/3963) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 3949 LexicalPreservingPrinter Ignores Changes to LambdaExp… (PR [#3959](https://github.com/javaparser/javaparser/pull/3959) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: Unit test since Return-Type-Substituable is fully implemented on reference type (PR [#3943](https://github.com/javaparser/javaparser/pull/3943) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue on FunctionalInterfaceLogic but waiting for Return-Type-Su… (PR [#3941](https://github.com/javaparser/javaparser/pull/3941) by [@jlerbsc](https://github.com/jlerbsc))
* Suggested fix: hardcoded specific LambdaExpr case in LexicalDifferenc… (PR [#3938](https://github.com/javaparser/javaparser/pull/3938) by [@blacelle](https://github.com/blacelle))
* Fix TextBlockLiteralExpr in LexicalDifferenceCalculator (PR [#3937](https://github.com/javaparser/javaparser/pull/3937) by [@blacelle](https://github.com/blacelle))
* Fix: issue 3919 An array of primitive type cannot be assigned to an array of object (PR [#3933](https://github.com/javaparser/javaparser/pull/3933) by [@jlerbsc](https://github.com/jlerbsc))

### Developer Changes

* chore(deps): update actions/checkout action to v3.5.0 (PR [#3953](https://github.com/javaparser/javaparser/pull/3953) by [@renovate[bot]](https://github.com/apps/renovate))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@blacelle](https://github.com/blacelle)
* [@jlerbsc](https://github.com/jlerbsc)


Version 3.25.1
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/197?closed=1)

### API or Behaviour Change

* Fix: Issue 3045 Unexpected exception when solving type inside an Anonymous class (PR [#3896](https://github.com/javaparser/javaparser/pull/3896) by [@jlerbsc](https://github.com/jlerbsc))

### Added

* Improved search for functional interfaces (PR [#3894](https://github.com/javaparser/javaparser/pull/3894) by [@jlerbsc](https://github.com/jlerbsc))

### Changed

* chore(deps): bump maven-compiler-plugin from 3.10.1 to 3.11.0 (PR [#3928](https://github.com/javaparser/javaparser/pull/3928) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump checkstyle from 10.7.0 to 10.8.0 (PR [#3927](https://github.com/javaparser/javaparser/pull/3927) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump versions-maven-plugin from 2.14.2 to 2.15.0 (PR [#3914](https://github.com/javaparser/javaparser/pull/3914) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump maven-javadoc-plugin from 3.4.1 to 3.5.0 (PR [#3906](https://github.com/javaparser/javaparser/pull/3906) by [@dependabot[bot]](https://github.com/apps/dependabot))
* Refactor: cleanup/refactor code after fixing #3859 (PR [#3886](https://github.com/javaparser/javaparser/pull/3886) by [@abego](https://github.com/abego))

### Fixed

* Fix: issue 3924 Removing ImportDeclaration with Annotated package thr… (PR [#3926](https://github.com/javaparser/javaparser/pull/3926) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 3918 JavaParserTypeDeclarationAdapter resolving wrong Type via Ancestor (PR [#3921](https://github.com/javaparser/javaparser/pull/3921) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 3919 ResolvedType::isAssignableBy(ResolvedType) is wrong f… (PR [#3920](https://github.com/javaparser/javaparser/pull/3920) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 3911 java.lang.UnsupportedOperationException: T[] while resolving generic method with type parameter with arrays like List<T[]> (PR [#3917](https://github.com/javaparser/javaparser/pull/3917) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: \s escape gives lexical error but should be valid since Java 15 (PR [#3903](https://github.com/javaparser/javaparser/pull/3903) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: Issue 3045 Unexpected exception when solving type inside an Anonymous class (PR [#3896](https://github.com/javaparser/javaparser/pull/3896) by [@jlerbsc](https://github.com/jlerbsc))
* Fix issue 1883 Finding lambda return type (PR [#3890](https://github.com/javaparser/javaparser/pull/3890) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 1815 ArrayIndexOutOfBoundsException when resolving lambda parameter. This fix is offered by Blackgen (PR [#3888](https://github.com/javaparser/javaparser/pull/3888) by [@jlerbsc](https://github.com/jlerbsc))

### Developer Changes

* chore(deps): bump checkstyle from 10.6.0 to 10.7.0 (PR [#3885](https://github.com/javaparser/javaparser/pull/3885) by [@dependabot[bot]](https://github.com/apps/dependabot))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@abego](https://github.com/abego)
* [@jlerbsc](https://github.com/jlerbsc)


Version 3.25.0
--------------

[issues resolved](https://github.com/javaparser/javaparser/milestone/196?closed=1)

### Added

* First part of the implementation of least upper bound logic (PR [#3880](https://github.com/javaparser/javaparser/pull/3880) by [@jlerbsc](https://github.com/jlerbsc))
* feat: Improved support for calculating the type of an object creation… (PR [#3877](https://github.com/javaparser/javaparser/pull/3877) by [@jlerbsc](https://github.com/jlerbsc))
* feat: Implement addRecord & getRecordByName for CompilationUnit (PR [#3836](https://github.com/javaparser/javaparser/pull/3836) by [@marcluque](https://github.com/marcluque))
* Support Jigsaw requires static (PR [#3826](https://github.com/javaparser/javaparser/pull/3826) by [@jlerbsc](https://github.com/jlerbsc))
* Add toDescriptor to ResolvedMethodDeclaration (PR [#3819](https://github.com/javaparser/javaparser/pull/3819) by [@vanHekthor](https://github.com/vanHekthor))
* Refactoring context (WIP) (PR [#3792](https://github.com/javaparser/javaparser/pull/3792) by [@jlerbsc](https://github.com/jlerbsc))
* Refactoring context (WIP) (PR [#3782](https://github.com/javaparser/javaparser/pull/3782) by [@jlerbsc](https://github.com/jlerbsc))
* Refactoring convert to usage (PR [#3774](https://github.com/javaparser/javaparser/pull/3774) by [@jlerbsc](https://github.com/jlerbsc))
* Simplified usage of class AssociableToAST (PR [#3063](https://github.com/javaparser/javaparser/pull/3063) by [@4everTheOne](https://github.com/4everTheOne))

### Changed

* Revert import related checkstyle rule from error to warning (PR [#3881](https://github.com/javaparser/javaparser/pull/3881) by [@jlerbsc](https://github.com/jlerbsc))
* Minor refactoring for example to get all parameter types (PR [#3879](https://github.com/javaparser/javaparser/pull/3879) by [@jlerbsc](https://github.com/jlerbsc))
* Add header and footer methods in comments instead of using literal st… (PR [#3876](https://github.com/javaparser/javaparser/pull/3876) by [@jlerbsc](https://github.com/jlerbsc))
* In the context of lexical preservation, the CSM token must be added m… (PR [#3874](https://github.com/javaparser/javaparser/pull/3874) by [@jlerbsc](https://github.com/jlerbsc))
* Refactoring: remove useless code that is already implemented (PR [#3869](https://github.com/javaparser/javaparser/pull/3869) by [@jlerbsc](https://github.com/jlerbsc))
* Memory usage improvement when printing a node from the LexicalPreserv… (PR [#3858](https://github.com/javaparser/javaparser/pull/3858) by [@jlerbsc](https://github.com/jlerbsc))
* chore(deps-dev): bump assertj-core from 3.24.1 to 3.24.2 (PR [#3852](https://github.com/javaparser/javaparser/pull/3852) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump maven-checkstyle-plugin from 3.2.0 to 3.2.1 (PR [#3846](https://github.com/javaparser/javaparser/pull/3846) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump maven-dependency-plugin from 3.4.0 to 3.5.0 (PR [#3845](https://github.com/javaparser/javaparser/pull/3845) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update junit5 monorepo to v5.9.2 (PR [#3840](https://github.com/javaparser/javaparser/pull/3840) by [@renovate[bot]](https://github.com/apps/renovate))
* Minor refactoring on Difference class (PR [#3839](https://github.com/javaparser/javaparser/pull/3839) by [@jlerbsc](https://github.com/jlerbsc))
* chore(deps-dev): bump assertj-core from 3.23.1 to 3.24.1 (PR [#3837](https://github.com/javaparser/javaparser/pull/3837) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump actions/checkout from 3.2.0 to 3.3.0 (PR [#3834](https://github.com/javaparser/javaparser/pull/3834) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump checkstyle from 10.5.0 to 10.6.0 (PR [#3829](https://github.com/javaparser/javaparser/pull/3829) by [@dependabot[bot]](https://github.com/apps/dependabot))

### Fixed

* Fix: Method hasScope must return true on NodeWithOptionalScope and No… (PR [#3875](https://github.com/javaparser/javaparser/pull/3875) by [@jlerbsc](https://github.com/jlerbsc))
* fix #3859 UnsupportedOperationException when trying to resolve a type… (PR [#3873](https://github.com/javaparser/javaparser/pull/3873) by [@abego](https://github.com/abego))
* Fix: issue 3866 Symbol solver is unable to resolve inner classes of ancestors when they are prefixed with a subclass (PR [#3868](https://github.com/javaparser/javaparser/pull/3868) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: issue 3703 Allow removing empty parentheses after removing all pairs from an annotation (PR [#3865](https://github.com/javaparser/javaparser/pull/3865) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: One must be able to know if any resolved type is a boxed primiti… (PR [#3864](https://github.com/javaparser/javaparser/pull/3864) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: Issue 2374 Comments of added Nodes are ignored in LexicalPreserv… (PR [#3856](https://github.com/javaparser/javaparser/pull/3856) by [@jlerbsc](https://github.com/jlerbsc))
* Checkstyle for unused import (PR [#3841](https://github.com/javaparser/javaparser/pull/3841) by [@4everTheOne](https://github.com/4everTheOne))
* Update bnd file (PR [#3783](https://github.com/javaparser/javaparser/pull/3783) by [@jlerbsc](https://github.com/jlerbsc))

### Developer Changes

* Update javaparser copyright headers (PR [#3862](https://github.com/javaparser/javaparser/pull/3862) by [@jlerbsc](https://github.com/jlerbsc))

### Uncategorised

* Add test case to verify range calculation on ArrayType (PR [#3828](https://github.com/javaparser/javaparser/pull/3828) by [@jlerbsc](https://github.com/jlerbsc))
* Add test case to verify that LexicalPreservation supports TextBlock (PR [#3827](https://github.com/javaparser/javaparser/pull/3827) by [@jlerbsc](https://github.com/jlerbsc))
* Refactoring: Removing useless method convertToUsage in JavaParserFacade (PR [#3780](https://github.com/javaparser/javaparser/pull/3780) by [@jlerbsc](https://github.com/jlerbsc))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@vanHekthor](https://github.com/vanHekthor)
* [@abego](https://github.com/abego)
* [@jlerbsc](https://github.com/jlerbsc)
* [@marcluque](https://github.com/marcluque)
* [@4everTheOne](https://github.com/4everTheOne)


Version 3.24.10
---------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/194?closed=1)

### Added

* Add a method in LexicalPreservingPrinter to know if LPP is available/activated on the specified node (PR [#3823](https://github.com/javaparser/javaparser/pull/3823) by [@jlerbsc](https://github.com/jlerbsc))
* Handle nested records (PR [#3814](https://github.com/javaparser/javaparser/pull/3814) by [@mernst](https://github.com/mernst))
* Source printer import ordering strategy (PR [#3807](https://github.com/javaparser/javaparser/pull/3807) by [@4everTheOne](https://github.com/4everTheOne))

### Changed

* chore(deps): bump versions-maven-plugin from 2.14.1 to 2.14.2 (PR [#3817](https://github.com/javaparser/javaparser/pull/3817) by [@dependabot[bot]](https://github.com/apps/dependabot))
* Enabled import validation (PR [#3812](https://github.com/javaparser/javaparser/pull/3812) by [@4everTheOne](https://github.com/4everTheOne))
* Part 5 | Import organization (PR [#3805](https://github.com/javaparser/javaparser/pull/3805) by [@4everTheOne](https://github.com/4everTheOne))
* Part 4 | Import organization (PR [#3804](https://github.com/javaparser/javaparser/pull/3804) by [@4everTheOne](https://github.com/4everTheOne))
* Part 3 | Import organization (PR [#3803](https://github.com/javaparser/javaparser/pull/3803) by [@4everTheOne](https://github.com/4everTheOne))
* Part 2 | Import organization (PR [#3802](https://github.com/javaparser/javaparser/pull/3802) by [@4everTheOne](https://github.com/4everTheOne))
* Part 1 | Import organization (PR [#3801](https://github.com/javaparser/javaparser/pull/3801) by [@4everTheOne](https://github.com/4everTheOne))
* Checkstyle configuration tweaks (PR [#3799](https://github.com/javaparser/javaparser/pull/3799) by [@4everTheOne](https://github.com/4everTheOne))
* chore(deps): bump versions-maven-plugin from 2.13.0 to 2.14.1 (PR [#3797](https://github.com/javaparser/javaparser/pull/3797) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump actions/checkout from 3.1.0 to 3.2.0 (PR [#3789](https://github.com/javaparser/javaparser/pull/3789) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump checkstyle from 8.45.1 to 10.5.0 (PR [#3788](https://github.com/javaparser/javaparser/pull/3788) by [@dependabot[bot]](https://github.com/apps/dependabot))

### Fixed

* explicit use asString for performance (PR [#3821](https://github.com/javaparser/javaparser/pull/3821) by [@dencat](https://github.com/dencat))
* Fix: issue #3818 Wrong range calculation on ArrayType with multiple d… (PR [#3820](https://github.com/javaparser/javaparser/pull/3820) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: Lexical Preserving Fails To Remove Comment (PR [#3810](https://github.com/javaparser/javaparser/pull/3810) by [@jlerbsc](https://github.com/jlerbsc))

### Developer Changes

* chore(deps): bump versions-maven-plugin from 2.13.0 to 2.14.0 (PR [#3794](https://github.com/javaparser/javaparser/pull/3794) by [@dependabot[bot]](https://github.com/apps/dependabot))
* Basic CheckStyle validation (PR [#3781](https://github.com/javaparser/javaparser/pull/3781) by [@4everTheOne](https://github.com/4everTheOne))

### Uncategorised

* Fix: 3412 Remove walkmod again (PR [#3806](https://github.com/javaparser/javaparser/pull/3806) by [@jlerbsc](https://github.com/jlerbsc))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@dencat](https://github.com/dencat)
* [@jlerbsc](https://github.com/jlerbsc)
* [@mernst](https://github.com/mernst)
* [@4everTheOne](https://github.com/4everTheOne)


Version 3.24.9
---------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/193?closed=1)

### Highlights

* Remove "executable" bit from code files (PR [#3755](https://github.com/javaparser/javaparser/pull/3755) by [@icmdaf](https://github.com/icmdaf))

### Added

* Created TypeSolverBuilder (PR [#3421](https://github.com/javaparser/javaparser/pull/3421) by [@4everTheOne](https://github.com/4everTheOne))

### Changed

* Changing, in test classes, the initialization of the lexical preserva… (PR [#3779](https://github.com/javaparser/javaparser/pull/3779) by [@jlerbsc](https://github.com/jlerbsc))
* chore(deps): bump maven-dependency-plugin from 3.3.0 to 3.4.0 (PR [#3770](https://github.com/javaparser/javaparser/pull/3770) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): bump maven-install-plugin from 3.0.1 to 3.1.0 (PR [#3756](https://github.com/javaparser/javaparser/pull/3756) by [@dependabot[bot]](https://github.com/apps/dependabot))

### Fixed

* Fix: #3195 Resolved methods in outer classes not inferred correcly (PR [#3778](https://github.com/javaparser/javaparser/pull/3778) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: #3681 LineComment alwaysing trimming content (PR [#3777](https://github.com/javaparser/javaparser/pull/3777) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: #3773 Replacing nodes causes error in lexical preserving printer… (PR [#3776](https://github.com/javaparser/javaparser/pull/3776) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: #2517 Modifying some nodes with the lexicalPreservation enabled … (PR [#3775](https://github.com/javaparser/javaparser/pull/3775) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: #3725 JavaParserFacade var type in for-each loop cannot be resolved (PR [#3768](https://github.com/javaparser/javaparser/pull/3768) by [@abego](https://github.com/abego))
* Fix: #3216 LexicalPreservingPrinter add Wrong indentation when removing comments (PR [#3766](https://github.com/javaparser/javaparser/pull/3766) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: #3472 Line comment removal causes IllegalStateException with LexicalPreservingPrinter (PR [#3765](https://github.com/javaparser/javaparser/pull/3765) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: #3441 LexicalPreservingPrinter prints wrong output with line com… (PR [#3764](https://github.com/javaparser/javaparser/pull/3764) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: #2137 ClassOrInterfaceDeclaration addMember using index (PR [#3763](https://github.com/javaparser/javaparser/pull/3763) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: #3761 Lexical preserving corrupts source when adding a modifier in first position (PR [#3762](https://github.com/javaparser/javaparser/pull/3762) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: #3693 Removing modifiers from method declaration results in loss… (PR [#3760](https://github.com/javaparser/javaparser/pull/3760) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: #3750 Lexical preserving corrupts source (PR [#3759](https://github.com/javaparser/javaparser/pull/3759) by [@jlerbsc](https://github.com/jlerbsc))
* Fix: Fix the indentation generated by the LexicalPreservingPrinter wh… (PR [#3758](https://github.com/javaparser/javaparser/pull/3758) by [@jlerbsc](https://github.com/jlerbsc))

### Security

* Remove "executable" bit from code files (PR [#3755](https://github.com/javaparser/javaparser/pull/3755) by [@icmdaf](https://github.com/icmdaf))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@abego](https://github.com/abego)
* [@jlerbsc](https://github.com/jlerbsc)
* [@icmdaf](https://github.com/icmdaf)
* [@4everTheOne](https://github.com/4everTheOne)


Version 3.24.8
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/192?closed=1)

### Added

* [Fixes #3099] Added ability to solve type with a list of expected type arguments (PR [#3213](https://github.com/javaparser/javaparser/pull/3213) by [@4everTheOne](https://github.com/4everTheOne))
* [Suggestion] NonNull generator for parameters (PR [#3127](https://github.com/javaparser/javaparser/pull/3127) by [@4everTheOne](https://github.com/4everTheOne))

### Changed

* Updated workflow to only run one job per PR (PR [#3744](https://github.com/javaparser/javaparser/pull/3744) by [@4everTheOne](https://github.com/4everTheOne))
* Remove or comment system.out.println statement in unit tests (PR [#3741](https://github.com/javaparser/javaparser/pull/3741) by [@jlerbsc](https://github.com/jlerbsc))
* Added Optional method in SymbolReference (PR [#3740](https://github.com/javaparser/javaparser/pull/3740) by [@4everTheOne](https://github.com/4everTheOne))
* Centralized management of symbol solver exceptions to prevent exception type Erasion (PR [#3731](https://github.com/javaparser/javaparser/pull/3731) by [@jlerbsc](https://github.com/jlerbsc))

### Fixed

* Fix issue #1827 Issue resolving a constructor of a class using generics (PR [#3752](https://github.com/javaparser/javaparser/pull/3752) by [@jlerbsc](https://github.com/jlerbsc))
* Fix issue #3728 ParseProblemException (PR [#3743](https://github.com/javaparser/javaparser/pull/3743) by [@jlerbsc](https://github.com/jlerbsc))
* Updated Badge for Build and Coverage (PR [#3742](https://github.com/javaparser/javaparser/pull/3742) by [@4everTheOne](https://github.com/4everTheOne))
* Position (PR [#3734](https://github.com/javaparser/javaparser/pull/3734) by [@ameliagenova](https://github.com/ameliagenova))
* Fix part of issue #3721 UnsupportedOperationException while trying to modify the type of a variable (PR [#3726](https://github.com/javaparser/javaparser/pull/3726) by [@jlerbsc](https://github.com/jlerbsc))
* Implemented isReferenceType in `ResolvedTypeDeclaration` and isTypeParameter in `ResolvedTypeParameterDeclaration` (PR [#3206](https://github.com/javaparser/javaparser/pull/3206) by [@4everTheOne](https://github.com/4everTheOne))

### Developer Changes

* chore(deps): bump versions-maven-plugin from 2.12.0 to 2.13.0 (PR [#3727](https://github.com/javaparser/javaparser/pull/3727) by [@dependabot[bot]](https://github.com/apps/dependabot))
* Fix maven wrapper not found in generator scripts (PR [#3717](https://github.com/javaparser/javaparser/pull/3717) by [@PPazderski](https://github.com/PPazderski))
* chore(deps): bump actions/checkout from 3.0.2 to 3.1.0 (PR [#3716](https://github.com/javaparser/javaparser/pull/3716) by [@dependabot[bot]](https://github.com/apps/dependabot))

### Uncategorised

* Change issue 1945 test to paramaterized (PR [#3739](https://github.com/javaparser/javaparser/pull/3739) by [@flanbino](https://github.com/flanbino))
* More unit tests for JavaToken and CodeGenerationUtils (PR [#3736](https://github.com/javaparser/javaparser/pull/3736) by [@ameliagenova](https://github.com/ameliagenova))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@flanbino](https://github.com/flanbino)
* [@PPazderski](https://github.com/PPazderski)
* [@ameliagenova](https://github.com/ameliagenova)
* [@jlerbsc](https://github.com/jlerbsc)
* [@4everTheOne](https://github.com/4everTheOne)



Version 3.24.7
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/191?closed=1)

### Highlights

* Issue #3415 (PR [#3722](https://github.com/javaparser/javaparser/pull/3722) by [@nelson-ng-96](https://github.com/nelson-ng-96))

### Changed

* Refactoring - use of existing methods (PR [#3697](https://github.com/javaparser/javaparser/pull/3697) by [@jlerbsc](https://github.com/jlerbsc))
* Refactoring adding convenient methods to know if a DifferenceElement is added, removed or kept (PR [#3695](https://github.com/javaparser/javaparser/pull/3695) by [@jlerbsc](https://github.com/jlerbsc))

### Deprecated

* Issue #3415 (PR [#3722](https://github.com/javaparser/javaparser/pull/3722) by [@nelson-ng-96](https://github.com/nelson-ng-96))

### Fixed

* Fix for ReflectionAnnotationDeclaration getClassName() (PR [#3723](https://github.com/javaparser/javaparser/pull/3723) by [@Blackgen](https://github.com/Blackgen))
* Fix some yield expressions not recognized (PR [#3714](https://github.com/javaparser/javaparser/pull/3714) by [@PPazderski](https://github.com/PPazderski))
* Accept final in instanceof pattern (PR [#3713](https://github.com/javaparser/javaparser/pull/3713) by [@PPazderski](https://github.com/PPazderski))
* [Fix] Avoid test failure due to line separator differences on windows host (PR [#3711](https://github.com/javaparser/javaparser/pull/3711) by [@jlerbsc](https://github.com/jlerbsc))
* Fix issue #3700 Removing last statement with LexicalPreservingPrinter results in loss of indendation (PR [#3704](https://github.com/javaparser/javaparser/pull/3704) by [@jlerbsc](https://github.com/jlerbsc))
* Fix issue #3678 Function accepts a configuration but it does not do anything (PR [#3692](https://github.com/javaparser/javaparser/pull/3692) by [@jlerbsc](https://github.com/jlerbsc))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@PPazderski](https://github.com/PPazderski)
* [@nelson-ng-96](https://github.com/nelson-ng-96)
* [@Blackgen](https://github.com/Blackgen)
* [@jlerbsc](https://github.com/jlerbsc)


Version 3.24.6
--------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/190?closed=1)

### API or Behaviour Change

* Issue #3405 thread safety of pre/postprocessors (incl. breaking change to `Processor` with pre/post processor methods). (PR [#3515](https://github.com/javaparser/javaparser/pull/3515) by [@matozoid](https://github.com/matozoid))

### Changed

* chore(deps): bump javassist from 3.29.0-GA to 3.29.1-GA (PR [#3661](https://github.com/javaparser/javaparser/pull/3661) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update junit5 monorepo to v5.9.0 (PR [#3645](https://github.com/javaparser/javaparser/pull/3645) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): bump maven-resources-plugin from 3.2.0 to 3.3.0 (PR [#3644](https://github.com/javaparser/javaparser/pull/3644) by [@dependabot[bot]](https://github.com/apps/dependabot))
* Flexible symbol resolution for declaration types (PR [#3634](https://github.com/javaparser/javaparser/pull/3634) by [@Col-E](https://github.com/Col-E))
* Minor refactoring to manage check in range and use hasRange method in class CommentsInserter (PR [#3587](https://github.com/javaparser/javaparser/pull/3587) by [@jlerbsc](https://github.com/jlerbsc))
* Renaming PACKAGE_PRIVATE to NONE (this refers to the discussion in the issue #2242) (PR [#3573](https://github.com/javaparser/javaparser/pull/3573) by [@jlerbsc](https://github.com/jlerbsc))

### Fixed

* Fix typos (PR [#3675](https://github.com/javaparser/javaparser/pull/3675) by [@mernst](https://github.com/mernst))
* Fix issue #3614 UnsolvedSymbolException when package declaration contains comment (PR [#3671](https://github.com/javaparser/javaparser/pull/3671) by [@jlerbsc](https://github.com/jlerbsc))
* chore(deps): update dependency org.apache.maven.plugins:maven-install-plugin to v3.0.0 (PR [#3640](https://github.com/javaparser/javaparser/pull/3640) by [@renovate[bot]](https://github.com/apps/renovate))
* Fix documentation of `JAVA_17` (PR [#3623](https://github.com/javaparser/javaparser/pull/3623) by [@mernst](https://github.com/mernst))
* Fix issue 3631 NameExpr.resolve() does not take end of inner block scopes into account (PR [#3613](https://github.com/javaparser/javaparser/pull/3613) by [@jlerbsc](https://github.com/jlerbsc))
* Fix issue #3588 Modifier is removed when removing an annotation (PR [#3600](https://github.com/javaparser/javaparser/pull/3600) by [@jlerbsc](https://github.com/jlerbsc))
* Fix lambda generic types that are always resolved to the first type param (PR [#3595](https://github.com/javaparser/javaparser/pull/3595) by [@johannescoetzee](https://github.com/johannescoetzee))
* Fix issue #3489 SourceRoot.tryToParse() fails if the root path ends with a directory that is not a java identifier (PR [#3551](https://github.com/javaparser/javaparser/pull/3551) by [@jlerbsc](https://github.com/jlerbsc))
* Default pretty printer should print inner-class receiver parameters on constructors (PR [#3527](https://github.com/javaparser/javaparser/pull/3527) by [@kelloggm](https://github.com/kelloggm))
* Issue #3405 thread safety of pre/postprocessors (incl. breaking change to `Processor` with pre/post processor methods). (PR [#3515](https://github.com/javaparser/javaparser/pull/3515) by [@matozoid](https://github.com/matozoid))

### Developer Changes

* chore(deps): update dependency org.apache.maven.plugins:maven-install-plugin to v3.0.1 (PR [#3641](https://github.com/javaparser/javaparser/pull/3641) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-deploy-plugin to v3.0.0 (PR [#3639](https://github.com/javaparser/javaparser/pull/3639) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): bump exec-maven-plugin from 3.0.0 to 3.1.0 (PR [#3637](https://github.com/javaparser/javaparser/pull/3637) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update dependency com.squareup.okhttp3:okhttp to v4.10.0 (PR [#3612](https://github.com/javaparser/javaparser/pull/3612) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency biz.aqute.bnd:bnd-maven-plugin to v6.3.1 (PR [#3607](https://github.com/javaparser/javaparser/pull/3607) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-surefire-plugin to v3.0.0-m7 (PR [#3605](https://github.com/javaparser/javaparser/pull/3605) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-inline to v4.6.1 (PR [#3601](https://github.com/javaparser/javaparser/pull/3601) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency biz.aqute.bnd:bnd-maven-plugin to v6.3.0 (PR [#3598](https://github.com/javaparser/javaparser/pull/3598) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.assertj:assertj-core to v3.23.1 (PR [#3596](https://github.com/javaparser/javaparser/pull/3596) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.assertj:assertj-core to v3.23.0 (PR [#3594](https://github.com/javaparser/javaparser/pull/3594) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-scm-plugin to v1.13.0 (PR [#3593](https://github.com/javaparser/javaparser/pull/3593) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-inline to v4.6.0 (PR [#3589](https://github.com/javaparser/javaparser/pull/3589) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.codehaus.mojo:versions-maven-plugin to v2.11.0 (PR [#3585](https://github.com/javaparser/javaparser/pull/3585) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update dependency org.javassist:javassist to v3.29.0-ga (PR [#3581](https://github.com/javaparser/javaparser/pull/3581) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.jbehave:jbehave-core to v4.8.3 (PR [#3574](https://github.com/javaparser/javaparser/pull/3574) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): bump codecov/codecov-action from 3.0.0 to 3.1.0 (PR [#3567](https://github.com/javaparser/javaparser/pull/3567) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update actions/checkout action to v3.0.2 (PR [#3565](https://github.com/javaparser/javaparser/pull/3565) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-inline to v4.5.1 (PR [#3564](https://github.com/javaparser/javaparser/pull/3564) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-site-plugin to v3.12.0 (PR [#3561](https://github.com/javaparser/javaparser/pull/3561) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-javadoc-plugin to v3.4.0 (PR [#3560](https://github.com/javaparser/javaparser/pull/3560) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-inline to v4.5.0 (PR [#3557](https://github.com/javaparser/javaparser/pull/3557) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update actions/checkout action to v3.0.1 (PR [#3555](https://github.com/javaparser/javaparser/pull/3555) by [@renovate[bot]](https://github.com/apps/renovate))
* official Apache Maven wrapper (PR [#3552](https://github.com/javaparser/javaparser/pull/3552) by [@sullis](https://github.com/sullis))
* chore(deps): update codecov/codecov-action action to v3 (PR [#3545](https://github.com/javaparser/javaparser/pull/3545) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.jacoco:jacoco-maven-plugin to v0.8.8 (PR [#3544](https://github.com/javaparser/javaparser/pull/3544) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-clean-plugin to v3.2.0 (PR [#3542](https://github.com/javaparser/javaparser/pull/3542) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-surefire-plugin to v3.0.0-m6 (PR [#3541](https://github.com/javaparser/javaparser/pull/3541) by [@renovate[bot]](https://github.com/apps/renovate))

### Uncategorised

* Implemented JavaParserTypeVariableDeclaration getAncestors method  (PR [#3060](https://github.com/javaparser/javaparser/pull/3060) by [@4everTheOne](https://github.com/4everTheOne))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@sullis](https://github.com/sullis)
* [@johannescoetzee](https://github.com/johannescoetzee)
* [@kelloggm](https://github.com/kelloggm)
* [@jlerbsc](https://github.com/jlerbsc)
* [@mernst](https://github.com/mernst)
* [@Col-E](https://github.com/Col-E)
* [@matozoid](https://github.com/matozoid)
* [@4everTheOne](https://github.com/4everTheOne)


Version 3.24.4 - Repeat of 3.24.3
---------------------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/190?closed=1)

GPG Fingerprint: `253E8E4C6FB28D11748115C1249DEE8E2C07A0A2`

### API or Behaviour Change

* Issue #3405 thread safety of pre/postprocessors (incl. breaking change to `Processor` with pre/post processor methods). (PR [#3515](https://github.com/javaparser/javaparser/pull/3515) by [@matozoid](https://github.com/matozoid))

### Changed

* chore(deps): update junit5 monorepo to v5.9.0 (PR [#3645](https://github.com/javaparser/javaparser/pull/3645) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): bump maven-resources-plugin from 3.2.0 to 3.3.0 (PR [#3644](https://github.com/javaparser/javaparser/pull/3644) by [@dependabot[bot]](https://github.com/apps/dependabot))
* Flexible symbol resolution for declaration types (PR [#3634](https://github.com/javaparser/javaparser/pull/3634) by [@Col-E](https://github.com/Col-E))
* Minor refactoring to manage check in range and use hasRange method in class CommentsInserter (PR [#3587](https://github.com/javaparser/javaparser/pull/3587) by [@jlerbsc](https://github.com/jlerbsc))
* Renaming PACKAGE_PRIVATE to NONE (this refers to the discussion in the issue #2242) (PR [#3573](https://github.com/javaparser/javaparser/pull/3573) by [@jlerbsc](https://github.com/jlerbsc))

### Fixed

* chore(deps): update dependency org.apache.maven.plugins:maven-install-plugin to v3.0.0 (PR [#3640](https://github.com/javaparser/javaparser/pull/3640) by [@renovate[bot]](https://github.com/apps/renovate))
* Fix documentation of `JAVA_17` (PR [#3623](https://github.com/javaparser/javaparser/pull/3623) by [@mernst](https://github.com/mernst))
* Fix issue 3631 NameExpr.resolve() does not take end of inner block scopes into account (PR [#3613](https://github.com/javaparser/javaparser/pull/3613) by [@jlerbsc](https://github.com/jlerbsc))
* Fix issue #3588 Modifier is removed when removing an annotation (PR [#3600](https://github.com/javaparser/javaparser/pull/3600) by [@jlerbsc](https://github.com/jlerbsc))
* Fix lambda generic types that are always resolved to the first type param (PR [#3595](https://github.com/javaparser/javaparser/pull/3595) by [@johannescoetzee](https://github.com/johannescoetzee))
* Fix issue #3489 SourceRoot.tryToParse() fails if the root path ends with a directory that is not a java identifier (PR [#3551](https://github.com/javaparser/javaparser/pull/3551) by [@jlerbsc](https://github.com/jlerbsc))
* Default pretty printer should print inner-class receiver parameters on constructors (PR [#3527](https://github.com/javaparser/javaparser/pull/3527) by [@kelloggm](https://github.com/kelloggm))
* Issue #3405 thread safety of pre/postprocessors (incl. breaking change to `Processor` with pre/post processor methods). (PR [#3515](https://github.com/javaparser/javaparser/pull/3515) by [@matozoid](https://github.com/matozoid))

### Developer Changes

* chore(deps): update dependency org.apache.maven.plugins:maven-install-plugin to v3.0.1 (PR [#3641](https://github.com/javaparser/javaparser/pull/3641) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-deploy-plugin to v3.0.0 (PR [#3639](https://github.com/javaparser/javaparser/pull/3639) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): bump exec-maven-plugin from 3.0.0 to 3.1.0 (PR [#3637](https://github.com/javaparser/javaparser/pull/3637) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update dependency com.squareup.okhttp3:okhttp to v4.10.0 (PR [#3612](https://github.com/javaparser/javaparser/pull/3612) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency biz.aqute.bnd:bnd-maven-plugin to v6.3.1 (PR [#3607](https://github.com/javaparser/javaparser/pull/3607) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-surefire-plugin to v3.0.0-m7 (PR [#3605](https://github.com/javaparser/javaparser/pull/3605) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-inline to v4.6.1 (PR [#3601](https://github.com/javaparser/javaparser/pull/3601) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency biz.aqute.bnd:bnd-maven-plugin to v6.3.0 (PR [#3598](https://github.com/javaparser/javaparser/pull/3598) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.assertj:assertj-core to v3.23.1 (PR [#3596](https://github.com/javaparser/javaparser/pull/3596) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.assertj:assertj-core to v3.23.0 (PR [#3594](https://github.com/javaparser/javaparser/pull/3594) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-scm-plugin to v1.13.0 (PR [#3593](https://github.com/javaparser/javaparser/pull/3593) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-inline to v4.6.0 (PR [#3589](https://github.com/javaparser/javaparser/pull/3589) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.codehaus.mojo:versions-maven-plugin to v2.11.0 (PR [#3585](https://github.com/javaparser/javaparser/pull/3585) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update dependency org.javassist:javassist to v3.29.0-ga (PR [#3581](https://github.com/javaparser/javaparser/pull/3581) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.jbehave:jbehave-core to v4.8.3 (PR [#3574](https://github.com/javaparser/javaparser/pull/3574) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): bump codecov/codecov-action from 3.0.0 to 3.1.0 (PR [#3567](https://github.com/javaparser/javaparser/pull/3567) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update actions/checkout action to v3.0.2 (PR [#3565](https://github.com/javaparser/javaparser/pull/3565) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-inline to v4.5.1 (PR [#3564](https://github.com/javaparser/javaparser/pull/3564) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-site-plugin to v3.12.0 (PR [#3561](https://github.com/javaparser/javaparser/pull/3561) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-javadoc-plugin to v3.4.0 (PR [#3560](https://github.com/javaparser/javaparser/pull/3560) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-inline to v4.5.0 (PR [#3557](https://github.com/javaparser/javaparser/pull/3557) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update actions/checkout action to v3.0.1 (PR [#3555](https://github.com/javaparser/javaparser/pull/3555) by [@renovate[bot]](https://github.com/apps/renovate))
* official Apache Maven wrapper (PR [#3552](https://github.com/javaparser/javaparser/pull/3552) by [@sullis](https://github.com/sullis))
* chore(deps): update codecov/codecov-action action to v3 (PR [#3545](https://github.com/javaparser/javaparser/pull/3545) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.jacoco:jacoco-maven-plugin to v0.8.8 (PR [#3544](https://github.com/javaparser/javaparser/pull/3544) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-clean-plugin to v3.2.0 (PR [#3542](https://github.com/javaparser/javaparser/pull/3542) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-surefire-plugin to v3.0.0-m6 (PR [#3541](https://github.com/javaparser/javaparser/pull/3541) by [@renovate[bot]](https://github.com/apps/renovate))

### Uncategorised

* Implemented JavaParserTypeVariableDeclaration getAncestors method  (PR [#3060](https://github.com/javaparser/javaparser/pull/3060) by [@4everTheOne](https://github.com/4everTheOne))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@sullis](https://github.com/sullis)
* [@johannescoetzee](https://github.com/johannescoetzee)
* [@kelloggm](https://github.com/kelloggm)
* [@jlerbsc](https://github.com/jlerbsc)
* [@mernst](https://github.com/mernst)
* [@Col-E](https://github.com/Col-E)
* [@matozoid](https://github.com/matozoid)
* [@4everTheOne](https://github.com/4everTheOne)


Version 3.24.3
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/190?closed=1)

### API or Behaviour Change

* Issue #3405 thread safety of pre/postprocessors (incl. breaking change to `Processor` with pre/post processor methods). (PR [#3515](https://github.com/javaparser/javaparser/pull/3515) by [@matozoid](https://github.com/matozoid))

### Changed

* Minor refactoring to manage check in range and use hasRange method in class CommentsInserter (PR [#3587](https://github.com/javaparser/javaparser/pull/3587) by [@jlerbsc](https://github.com/jlerbsc))
* Renaming PACKAGE_PRIVATE to NONE (this refers to the discussion in the issue #2242) (PR [#3573](https://github.com/javaparser/javaparser/pull/3573) by [@jlerbsc](https://github.com/jlerbsc))

### Fixed

* Fix documentation of `JAVA_17` (PR [#3623](https://github.com/javaparser/javaparser/pull/3623) by [@mernst](https://github.com/mernst))
* Fix issue 3631 NameExpr.resolve() does not take end of inner block scopes into account (PR [#3613](https://github.com/javaparser/javaparser/pull/3613) by [@jlerbsc](https://github.com/jlerbsc))
* Fix issue #3588 Modifier is removed when removing an annotation (PR [#3600](https://github.com/javaparser/javaparser/pull/3600) by [@jlerbsc](https://github.com/jlerbsc))
* Fix lambda generic types that are always resolved to the first type param (PR [#3595](https://github.com/javaparser/javaparser/pull/3595) by [@johannescoetzee](https://github.com/johannescoetzee))
* Fix issue #3489 SourceRoot.tryToParse() fails if the root path ends with a directory that is not a java identifier (PR [#3551](https://github.com/javaparser/javaparser/pull/3551) by [@jlerbsc](https://github.com/jlerbsc))
* Default pretty printer should print inner-class receiver parameters on constructors (PR [#3527](https://github.com/javaparser/javaparser/pull/3527) by [@kelloggm](https://github.com/kelloggm))
* Issue #3405 thread safety of pre/postprocessors (incl. breaking change to `Processor` with pre/post processor methods). (PR [#3515](https://github.com/javaparser/javaparser/pull/3515) by [@matozoid](https://github.com/matozoid))

### Developer Changes

* chore(deps): update actions/checkout action to v3.0.1 (PR [#3555](https://github.com/javaparser/javaparser/pull/3555) by [@renovate[bot]](https://github.com/apps/renovate))
* official Apache Maven wrapper (PR [#3552](https://github.com/javaparser/javaparser/pull/3552) by [@sullis](https://github.com/sullis))
* chore(deps): update codecov/codecov-action action to v3 (PR [#3545](https://github.com/javaparser/javaparser/pull/3545) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.jacoco:jacoco-maven-plugin to v0.8.8 (PR [#3544](https://github.com/javaparser/javaparser/pull/3544) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-clean-plugin to v3.2.0 (PR [#3542](https://github.com/javaparser/javaparser/pull/3542) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-surefire-plugin to v3.0.0-m6 (PR [#3541](https://github.com/javaparser/javaparser/pull/3541) by [@renovate[bot]](https://github.com/apps/renovate))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@sullis](https://github.com/sullis)
* [@johannescoetzee](https://github.com/johannescoetzee)
* [@kelloggm](https://github.com/kelloggm)
* [@jlerbsc](https://github.com/jlerbsc)
* [@mernst](https://github.com/mernst)
* [@matozoid](https://github.com/matozoid)

Version 3.24.2
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/188?closed=1)

GPG Fingerprint: `253E8E4C6FB28D11748115C1249DEE8E2C07A0A2`

### Added

* Improve unit test for BlockStmtContextResolutionTest (PR [#3530](https://github.com/javaparser/javaparser/pull/3530) by [@jlerbsc](https://github.com/jlerbsc))

### Changed

* Improve Conditional Operator resolution [JLS 15.25] (PR [#3522](https://github.com/javaparser/javaparser/pull/3522) by [@jlerbsc](https://github.com/jlerbsc))

### Fixed

* Fix issue #3526 Variable or FieldDeclaration is not resolved correctl… (PR [#3529](https://github.com/javaparser/javaparser/pull/3529) by [@jlerbsc](https://github.com/jlerbsc))

### Developer Changes

* Bump jbehave-junit-runner from 2.3.0 to 2.3.1 (PR [#3531](https://github.com/javaparser/javaparser/pull/3531) by [@dependabot[bot]](https://github.com/apps/dependabot))
* Bump actions/cache from 2.1.7 to 3 (PR [#3525](https://github.com/javaparser/javaparser/pull/3525) by [@dependabot[bot]](https://github.com/apps/dependabot))
* Update JDK 18 and add JDK 19 feature details to FEATURES.md (PR [#3521](https://github.com/javaparser/javaparser/pull/3521) by [@MysterAitch](https://github.com/MysterAitch))
* Bump maven-dependency-plugin from 3.2.0 to 3.3.0 (PR [#3514](https://github.com/javaparser/javaparser/pull/3514) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update dependency org.apache.maven.plugins:maven-dependency-plugin to v3.3.0 (PR [#3512](https://github.com/javaparser/javaparser/pull/3512) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-compiler-plugin to v3.10.1 (PR [#3511](https://github.com/javaparser/javaparser/pull/3511) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update actions/checkout action (PR [#3508](https://github.com/javaparser/javaparser/pull/3508) by [@renovate[bot]](https://github.com/apps/renovate))
* Bump bnd-maven-plugin from 6.1.0 to 6.2.0 (PR [#3505](https://github.com/javaparser/javaparser/pull/3505) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update dependency biz.aqute.bnd:bnd-maven-plugin to v6.2.0 (PR [#3503](https://github.com/javaparser/javaparser/pull/3503) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update actions/setup-java action to v3 (PR [#3502](https://github.com/javaparser/javaparser/pull/3502) by [@renovate[bot]](https://github.com/apps/renovate))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@MysterAitch](https://github.com/MysterAitch)
* [@jlerbsc](https://github.com/jlerbsc)


Version 3.24.1
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/189?closed=1)

### Fixed

* Adding constructor descriptor (PR [#3499](https://github.com/javaparser/javaparser/pull/3499) by [@kanghj](https://github.com/kanghj))
* Fix issue #3491 Method has a multidimensional arrays argument in jar … (PR [#3493](https://github.com/javaparser/javaparser/pull/3493) by [@jlerbsc](https://github.com/jlerbsc))
* Fix issue #3218 GetSourceRoots() does not return all source roots (PR [#3485](https://github.com/javaparser/javaparser/pull/3485) by [@jlerbsc](https://github.com/jlerbsc))
* Bug in ArrayCreationExpr constructors (PR [#3473](https://github.com/javaparser/javaparser/pull/3473) by [@sergekukharev](https://github.com/sergekukharev))
*  Fix issue 3440 Removing a node with LexicalPreservingPrinter causes UnsupportedOperationException (PR [#3449](https://github.com/javaparser/javaparser/pull/3449) by [@jlerbsc](https://github.com/jlerbsc))

### Developer Changes

* chore(deps): update dependency org.codehaus.mojo:versions-maven-plugin to v2.10.0 (PR [#3517](https://github.com/javaparser/javaparser/pull/3517) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-core to v4.4.0 (PR [#3510](https://github.com/javaparser/javaparser/pull/3510) by [@renovate[bot]](https://github.com/apps/renovate))
* fix(deps): update dependency com.google.guava:guava to v31.1-jre (PR [#3507](https://github.com/javaparser/javaparser/pull/3507) by [@renovate[bot]](https://github.com/apps/renovate))
* Bump guava from 31.0.1-jre to 31.1-jre (PR [#3506](https://github.com/javaparser/javaparser/pull/3506) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update dependency org.apache.maven.plugins:maven-site-plugin to v3.11.0 (PR [#3496](https://github.com/javaparser/javaparser/pull/3496) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-compiler-plugin to v3.10.0 (PR [#3494](https://github.com/javaparser/javaparser/pull/3494) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-javadoc-plugin to v3.3.2 (PR [#3492](https://github.com/javaparser/javaparser/pull/3492) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-core to v4.3.1 (PR [#3481](https://github.com/javaparser/javaparser/pull/3481) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-core to v4.3.0 (PR [#3479](https://github.com/javaparser/javaparser/pull/3479) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.codehaus.mojo:versions-maven-plugin to v2.9.0 (PR [#3477](https://github.com/javaparser/javaparser/pull/3477) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-jar-plugin to v3.2.2 (PR [#3470](https://github.com/javaparser/javaparser/pull/3470) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-compiler-plugin to v3.9.0 (PR [#3469](https://github.com/javaparser/javaparser/pull/3469) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency com.helger.maven:ph-javacc-maven-plugin to v4.1.5 (PR [#3468](https://github.com/javaparser/javaparser/pull/3468) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency com.github.javaparser:javaparser-parent to v3 (PR [#3465](https://github.com/javaparser/javaparser/pull/3465) by [@renovate[bot]](https://github.com/apps/renovate))
* Partial revert of #3462 (removed GitHub Action) (PR [#3464](https://github.com/javaparser/javaparser/pull/3464) by [@MysterAitch](https://github.com/MysterAitch))
* Updated release script to be non-interactive, and added option to use a manually-triggered GitHub Action to build a release (PR [#3462](https://github.com/javaparser/javaparser/pull/3462) by [@MysterAitch](https://github.com/MysterAitch))
* chore(deps): update dependency org.apache.maven.plugins:maven-jar-plugin to v3.2.1 (PR [#3459](https://github.com/javaparser/javaparser/pull/3459) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.codehaus.mojo:build-helper-maven-plugin to v3.3.0 (PR [#3458](https://github.com/javaparser/javaparser/pull/3458) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.assertj:assertj-core to v3.22.0 (PR [#3457](https://github.com/javaparser/javaparser/pull/3457) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-scm-plugin to v1.12.2 (PR [#3456](https://github.com/javaparser/javaparser/pull/3456) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-deploy-plugin to v3.0.0-m2 (PR [#3453](https://github.com/javaparser/javaparser/pull/3453) by [@renovate[bot]](https://github.com/apps/renovate))

### Uncategorised

* Fix the release gha, originally submitted in #3462 (PR [#3463](https://github.com/javaparser/javaparser/pull/3463) by [@MysterAitch](https://github.com/MysterAitch))
* Update changelog.md to contain 3.24.0 changes, and prepare for 3.24.1 (PR [#3461](https://github.com/javaparser/javaparser/pull/3461) by [@MysterAitch](https://github.com/MysterAitch))
* Update changelog.md (PR [#3460](https://github.com/javaparser/javaparser/pull/3460) by [@MysterAitch](https://github.com/MysterAitch))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@MysterAitch](https://github.com/MysterAitch)
* [@jlerbsc](https://github.com/jlerbsc)
* [@kanghj](https://github.com/kanghj)
* [@sergekukharev](https://github.com/sergekukharev)


Version 3.24.0
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/187?closed=1)

### Added

* Add erasure on parametrized type (PR [#3438](https://github.com/javaparser/javaparser/pull/3438) by [@jlerbsc](https://github.com/jlerbsc))
* Add test cases for `NoChange` API (PR [#3431](https://github.com/javaparser/javaparser/pull/3431) by [@jlerbsc](https://github.com/jlerbsc))

### Changed

* Minor refactoring on `LexicalreservingPrinter` especially in the class `Difference` (PR [#3424](https://github.com/javaparser/javaparser/pull/3424) by [@jlerbsc](https://github.com/jlerbsc))
* Update the readme with `@pedrombmachado` 's suggestions (#3357), and also to switch from `mvn` to `mvnw` within some sample instructions (PR [#3420](https://github.com/javaparser/javaparser/pull/3420) by [@MysterAitch](https://github.com/MysterAitch))
* Reducing deeply nested logic in `MethodResolutionLogic` (work in progress) (PR [#3411](https://github.com/javaparser/javaparser/pull/3411) by [@jlerbsc](https://github.com/jlerbsc))
* Reducing deeply nested logic in `MethodResolutionLogic` (PR [#3409](https://github.com/javaparser/javaparser/pull/3409) by [@jlerbsc](https://github.com/jlerbsc))
* Improved `RemoveMethodGenerator` and `ReplaceMethodGenerator` to only override super when needed. (PR [#3248](https://github.com/javaparser/javaparser/pull/3248) by [@4everTheOne](https://github.com/4everTheOne))
* Reduced complexity for methods in `JavaParserFacade` (PR [#3204](https://github.com/javaparser/javaparser/pull/3204) by [@4everTheOne](https://github.com/4everTheOne))

### Fixed

* Fix issue #3436 `getAncestors()`/`getAllAncestors()` does not work if base class starts with the same name (PR [#3437](https://github.com/javaparser/javaparser/pull/3437) by [@jlerbsc](https://github.com/jlerbsc))
* Add a missing `hashCode()` method (PR [#3432](https://github.com/javaparser/javaparser/pull/3432) by [@msridhar](https://github.com/msridhar))
* Call `orElse()` instead of `orElseGet()` (PR [#3430](https://github.com/javaparser/javaparser/pull/3430) by [@msridhar](https://github.com/msridhar))
* Fix issue #3408 `LexicalPreservationPrinter` fails to add annotation to a class field decalared with fully qualified name (PR [#3429](https://github.com/javaparser/javaparser/pull/3429) by [@jlerbsc](https://github.com/jlerbsc))
* Issue #3419 - Fixed bug in `Difference.java`  (PR [#3428](https://github.com/javaparser/javaparser/pull/3428) by [@4everTheOne](https://github.com/4everTheOne))
* Issue #3406 `ParseProblemException` when parsing char `\u005cn` (PR [#3407](https://github.com/javaparser/javaparser/pull/3407) by [@apixandru](https://github.com/apixandru))
* Fix issue #3399 Failed to resolve methods that evaluate as argument (PR [#3401](https://github.com/javaparser/javaparser/pull/3401) by [@jlerbsc](https://github.com/jlerbsc))
* Fix resoure leak due to `File.walk` (PR [#3398](https://github.com/javaparser/javaparser/pull/3398) by [@lujiefsi](https://github.com/lujiefsi))
* Fix issue #2259 Type resolution issue when type of formal parameter is Object (PR [#3397](https://github.com/javaparser/javaparser/pull/3397) by [@jlerbsc](https://github.com/jlerbsc))
* Fixes an issue where `JavaParserTypeSolver` ignores the character encoding configuration. (PR [#3396](https://github.com/javaparser/javaparser/pull/3396) by [@crucoba](https://github.com/crucoba))
* Issue #3272 resolve lambda exp type (PR [#3273](https://github.com/javaparser/javaparser/pull/3273) by [@si-e](https://github.com/si-e))
* Issue #3200 `this` exp in anonymous class (PR [#3268](https://github.com/javaparser/javaparser/pull/3268) by [@si-e](https://github.com/si-e))

### Developer Changes

* Partial revert of #3462 (removed GitHub Action) (PR [#3464](https://github.com/javaparser/javaparser/pull/3462) by [@MysterAitch](https://github.com/MysterAitch))
* Updated release script to be non-interactive, and added option to use a manually-triggered GitHub Action to build a release (PR [#3462](https://github.com/javaparser/javaparser/pull/3462) by [@MysterAitch](https://github.com/MysterAitch))
* chore(deps): update dependency org.apache.maven.plugins:maven-jar-plugin to v3.2.1 (PR [#3459](https://github.com/javaparser/javaparser/pull/3459) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.codehaus.mojo:build-helper-maven-plugin to v3.3.0 (PR [#3458](https://github.com/javaparser/javaparser/pull/3458) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.assertj:assertj-core to v3.22.0 (PR [#3457](https://github.com/javaparser/javaparser/pull/3457) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-scm-plugin to v1.12.2 (PR [#3456](https://github.com/javaparser/javaparser/pull/3456) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-deploy-plugin to v3.0.0-m2 (PR [#3453](https://github.com/javaparser/javaparser/pull/3453) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-site-plugin to v3.10.0 (PR [#3448](https://github.com/javaparser/javaparser/pull/3448) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-core to v4.2.0 (PR [#3442](https://github.com/javaparser/javaparser/pull/3442) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update junit5 monorepo to v5.8.2 (PR [#3425](https://github.com/javaparser/javaparser/pull/3425) by [@renovate[bot]](https://github.com/apps/renovate))
* Update / document `codecov.yml` (PR [#3418](https://github.com/javaparser/javaparser/pull/3418) by [@MysterAitch](https://github.com/MysterAitch))
* chore(deps): update actions/cache action to v2.1.7 (PR [#3417](https://github.com/javaparser/javaparser/pull/3417) by [@renovate[bot]](https://github.com/apps/renovate))
* Bump bnd-maven-plugin from 6.0.0 to 6.1.0 (PR [#3416](https://github.com/javaparser/javaparser/pull/3416) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update dependency biz.aqute.bnd:bnd-maven-plugin to v6.1.0 (PR [#3414](https://github.com/javaparser/javaparser/pull/3414) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency com.squareup.okhttp3:okhttp to v4.9.3 (PR [#3413](https://github.com/javaparser/javaparser/pull/3413) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update actions/checkout action to v2.4.0 (PR [#3402](https://github.com/javaparser/javaparser/pull/3402) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update actions/checkout action to v2.3.5 (PR [#3395](https://github.com/javaparser/javaparser/pull/3395) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-core to v4 (PR [#3393](https://github.com/javaparser/javaparser/pull/3393) by [@renovate[bot]](https://github.com/apps/renovate))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@crucoba](https://github.com/crucoba)
* [@msridhar](https://github.com/msridhar)
* [@MysterAitch](https://github.com/MysterAitch)
* [@lujiefsi](https://github.com/lujiefsi)
* [@apixandru](https://github.com/apixandru)
* [@si-e](https://github.com/si-e)
* [@jlerbsc](https://github.com/jlerbsc)
* [@4everTheOne](https://github.com/4everTheOne)



Version 3.23.1
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/186?closed=1)

### Fixed

* `record` may be used as variable name in Java 16 (PR [#3362](https://github.com/javaparser/javaparser/pull/3362) by [@koppor](github.com/koppor/))

### API or Behaviour Change

* Java 11 is now the most used version (PR [#3301](https://github.com/javaparser/javaparser/pull/3301) by [@matozoid](https://github.com/matozoid))

### Added

* Manage `@Inherited` annotation to prepare the fix on the issue 1843 (PR [#3383](https://github.com/javaparser/javaparser/pull/3383) by [@jlerbsc](https://github.com/jlerbsc))

### Changed

* Configurable caching system for type solvers (PR [#3343](https://github.com/javaparser/javaparser/pull/3343) by [@4everTheOne](https://github.com/4everTheOne))
* Java 11 is now the most used version (PR [#3301](https://github.com/javaparser/javaparser/pull/3301) by [@matozoid](https://github.com/matozoid))

### Fixed

* Fix issue 3387 LexicalPreservingPrinter adds wrong indentation when adding new comments (PR [#3392](https://github.com/javaparser/javaparser/pull/3392) by [@jlerbsc](https://github.com/jlerbsc))
* Fix issue 2360 Symbol Solver is missing promotion of byte, char, and short in unary expressions (PR [#3384](https://github.com/javaparser/javaparser/pull/3384) by [@jlerbsc](https://github.com/jlerbsc))
* Fix "record" as non-type identifier in Java 16 (PR [#3362](https://github.com/javaparser/javaparser/pull/3362) by [@koppor](https://github.com/koppor))
* Fix issue 3358 LexicalPreservingPrinter error on ArrayType (PR [#3359](https://github.com/javaparser/javaparser/pull/3359) by [@jlerbsc](https://github.com/jlerbsc))

### Developer Changes

* generate changelog for milestones - scripts included to do this by milestone id, milestone title, and a github action to add the output to a draft snapshot release (PR [#3391](https://github.com/javaparser/javaparser/pull/3391) by [@MysterAitch](https://github.com/MysterAitch))
* Bump bnd-maven-plugin from 5.3.0 to 6.0.0 (PR [#3390](https://github.com/javaparser/javaparser/pull/3390) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update dependency biz.aqute.bnd:bnd-maven-plugin to v6 (PR [#3389](https://github.com/javaparser/javaparser/pull/3389) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency com.squareup.okhttp3:okhttp to v4.9.2 (PR [#3388](https://github.com/javaparser/javaparser/pull/3388) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency com.google.guava:guava to v31.0.1-jre (PR [#3385](https://github.com/javaparser/javaparser/pull/3385) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency com.google.guava:guava to v31 (PR [#3381](https://github.com/javaparser/javaparser/pull/3381) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update junit5 monorepo to v5.8.1 (PR [#3380](https://github.com/javaparser/javaparser/pull/3380) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.assertj:assertj-core to v3.21.0 (PR [#3378](https://github.com/javaparser/javaparser/pull/3378) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-scm-plugin to v1.12.0 (PR [#3376](https://github.com/javaparser/javaparser/pull/3376) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update codecov/codecov-action action to v2.1.0 (PR [#3373](https://github.com/javaparser/javaparser/pull/3373) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update junit5 monorepo to v5.8.0 (PR [#3372](https://github.com/javaparser/javaparser/pull/3372) by [@renovate[bot]](https://github.com/apps/renovate))
* remove accidentally-added pom release backup files, and added it to gitignore to prevent them being re-added (PR [#3370](https://github.com/javaparser/javaparser/pull/3370) by [@MysterAitch](https://github.com/MysterAitch))
* chore(deps): update dependency org.apache.maven.plugins:maven-javadoc-plugin to v3.3.1 (PR [#3368](https://github.com/javaparser/javaparser/pull/3368) by [@renovate[bot]](https://github.com/apps/renovate))
* Reduce mvn verbosity on GitHub actions (and switch to mvnw) (PR [#3363](https://github.com/javaparser/javaparser/pull/3363) by [@koppor](https://github.com/koppor))

### Uncategorised

* Prepare changelog for next version (PR [#3354](https://github.com/javaparser/javaparser/pull/3354) by [@MysterAitch](https://github.com/MysterAitch))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@MysterAitch](https://github.com/MysterAitch)
* [@jlerbsc](https://github.com/jlerbsc)
* [@koppor](https://github.com/koppor)
* [@4everTheOne](https://github.com/4everTheOne)
* [@matozoid](https://github.com/matozoid)


Version 3.23.0
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/185?closed=1)

### Added

* Improving `toString` on CSM classes (PR [#3315](https://github.com/javaparser/javaparser/pull/3315) by [@jlerbsc](https://github.com/jlerbsc))
* Add test case for issue #2210 Resolution of Method References (PR [#3310](https://github.com/javaparser/javaparser/pull/3310) by [@jlerbsc](https://github.com/jlerbsc))
* Implemented method reference resolution on expressions (PR [#3307](https://github.com/javaparser/javaparser/pull/3307) by [@maartenc](https://github.com/maartenc))
* Define if a field is volatile through the ResolvedFieldDeclaration interface - from issue #3240 (PR [#3276](https://github.com/javaparser/javaparser/pull/3276) by [@jlerbsc](https://github.com/jlerbsc))
* Implemented logic for internalTypes in `JavaParserAnnotationDeclaration` and `JavassistAnnotationDeclaration` (PR [#3215](https://github.com/javaparser/javaparser/pull/3215) by [@4everTheOne](https://github.com/4everTheOne))

### Changed

* Check if ancestor also for super class (PR [#3324](https://github.com/javaparser/javaparser/pull/3324) by [@ReallyLiri](https://github.com/ReallyLiri))
* Remove useless  instanceof usage in Type (PR [#3311](https://github.com/javaparser/javaparser/pull/3311) by [@jlerbsc](https://github.com/jlerbsc))
* Fix Java 11+ AST postprocessing (PR [#3302](https://github.com/javaparser/javaparser/pull/3302) by [@matozoid](https://github.com/matozoid))
* Move duplicate code to JavaParserTypeAdapter (PR [#3267](https://github.com/javaparser/javaparser/pull/3267) by [@maartenc](https://github.com/maartenc))
* Improved performance when resolving types for big source files (PR [#3265](https://github.com/javaparser/javaparser/pull/3265) by [@maartenc](https://github.com/maartenc))
* Optimizations for Node class (CPU time and Memory usage) (PR [#3233](https://github.com/javaparser/javaparser/pull/3233) by [@4everTheOne](https://github.com/4everTheOne))
* Fix Javadoc comment * escaping problem. (PR [#3221](https://github.com/javaparser/javaparser/pull/3221) by [@matozoid](https://github.com/matozoid))
* Remove broken link (PR [#2912](https://github.com/javaparser/javaparser/pull/2912) by [@mernst](https://github.com/mernst))

### Fixed

* Preserving field order when getting the fields declared from a ReferenceType (PR [#3342](https://github.com/javaparser/javaparser/pull/3342) by [@jlerbsc](https://github.com/jlerbsc))
* Fix String Index out of range in TextBlockLiteralExpr (PR [#3337](https://github.com/javaparser/javaparser/pull/3337) by [@134ARG](https://github.com/134ARG))
* Fixed prettyprinting new switch-statements (and switch-expressions). (PR [#3335](https://github.com/javaparser/javaparser/pull/3335) by [@kozsik](https://github.com/kozsik))
* Fix pretty printing of generic records (PR [#3334](https://github.com/javaparser/javaparser/pull/3334) by [@twistedsquare](https://github.com/twistedsquare))
* Fix issue #3317 Comment in the middle of a multi-line single statement (PR [#3318](https://github.com/javaparser/javaparser/pull/3318) by [@jlerbsc](https://github.com/jlerbsc))
* Fix issue 3296 LexicalPreservation bug for array brackets (PR [#3316](https://github.com/javaparser/javaparser/pull/3316) by [@jlerbsc](https://github.com/jlerbsc))
* Fixes Issue #3308 -- stackoverflow when resolving the `FieldAccessExpr` of an `ArrayAccessExpr` (PR [#3312](https://github.com/javaparser/javaparser/pull/3312) by [@MysterAitch](https://github.com/MysterAitch))
* Fix StackOverflow when resolving ClassOrInterfaceType of nested ObjectCreationExpr (PR [#3279](https://github.com/javaparser/javaparser/pull/3279) by [@maartenc](https://github.com/maartenc))
* ResolvedMethods from javassist never had exceptions (PR [#3264](https://github.com/javaparser/javaparser/pull/3264) by [@maartenc](https://github.com/maartenc))
* Issue 3064 conditional nested lambda (PR [#3238](https://github.com/javaparser/javaparser/pull/3238) by [@si-e](https://github.com/si-e))
* Further optimization in resolving in StatementContext (PR [#3185](https://github.com/javaparser/javaparser/pull/3185) by [@Col-E](https://github.com/Col-E))
* Improve type resolution for duplicate names (PR [#3012](https://github.com/javaparser/javaparser/pull/3012) by [@thejk](https://github.com/thejk))

### Developer Changes

* chore(deps): update dependency org.mockito:mockito-core to v3.12.4 (PR [#3350](https://github.com/javaparser/javaparser/pull/3350) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-core to v3.12.3 (PR [#3349](https://github.com/javaparser/javaparser/pull/3349) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update codecov/codecov-action action to v2.0.3 (PR [#3348](https://github.com/javaparser/javaparser/pull/3348) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-core to v3.12.2 (PR [#3347](https://github.com/javaparser/javaparser/pull/3347) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-core to v3.12.1 (PR [#3345](https://github.com/javaparser/javaparser/pull/3345) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-core to v3.12.0 (PR [#3344](https://github.com/javaparser/javaparser/pull/3344) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-scm-plugin to v1.11.3 (PR [#3339](https://github.com/javaparser/javaparser/pull/3339) by [@renovate[bot]](https://github.com/apps/renovate))
* Bump codecov/codecov-action from 1.5.2 to 2.0.2 (PR [#3326](https://github.com/javaparser/javaparser/pull/3326) by [@dependabot[bot]](https://github.com/apps/dependabot))
* chore(deps): update dependency org.mockito:mockito-core to v3.11.2 (PR [#3305](https://github.com/javaparser/javaparser/pull/3305) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.assertj:assertj-core to v3.20.2 (PR [#3297](https://github.com/javaparser/javaparser/pull/3297) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.assertj:assertj-core to v3.20.0 (PR [#3295](https://github.com/javaparser/javaparser/pull/3295) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-dependency-plugin to v3.2.0 (PR [#3294](https://github.com/javaparser/javaparser/pull/3294) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-core to v3.11.1 (PR [#3293](https://github.com/javaparser/javaparser/pull/3293) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update codecov/codecov-action action to v1.5.2 (PR [#3287](https://github.com/javaparser/javaparser/pull/3287) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-core to v3.11.0 (PR [#3285](https://github.com/javaparser/javaparser/pull/3285) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update actions/cache action to v2.1.6 (PR [#3280](https://github.com/javaparser/javaparser/pull/3280) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-javadoc-plugin to v3.3.0 (PR [#3270](https://github.com/javaparser/javaparser/pull/3270) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update junit5 monorepo to v5.7.2 (PR [#3262](https://github.com/javaparser/javaparser/pull/3262) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.apache.maven.plugins:maven-gpg-plugin to v3 (PR [#3250](https://github.com/javaparser/javaparser/pull/3250) by [@renovate[bot]](https://github.com/apps/renovate))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@maartenc](https://github.com/maartenc)
* [@kozsik](https://github.com/kozsik)
* [@ReallyLiri](https://github.com/ReallyLiri)
* [@mernst](https://github.com/mernst)
* [@matozoid](https://github.com/matozoid)
* [@Col-E](https://github.com/Col-E)
* [@134ARG](https://github.com/134ARG)
* [@MysterAitch](https://github.com/MysterAitch)
* [@si-e](https://github.com/si-e)
* [@thejk](https://github.com/thejk)
* [@twistedsquare](https://github.com/twistedsquare)
* [@jlerbsc](https://github.com/jlerbsc)
* [@4everTheOne](https://github.com/4everTheOne)



Version 3.22.1
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/184?closed=1)

### Added

* Recover wrong statements no only to ';', but to '}' (not including) as well (PR [#3247](https://github.com/javaparser/javaparser/pull/3247) by [@32kda](https://github.com/32kda))

### Fixed

* update features.md -- fixed release version and date of records support, status of java 16 sealed classes to 2nd preview, and java 17 features (PR [#3263](https://github.com/javaparser/javaparser/pull/3263) by [@MysterAitch](https://github.com/MysterAitch))
* fixes #3255 -- bugfix grammar case when using `record` to as an identifier (PR [#3256](https://github.com/javaparser/javaparser/pull/3256) by [@MysterAitch](https://github.com/MysterAitch))
* Fixes issue #3113 -- Arrow missing in Switch Expression + jumbled up in LexicalPreservingPrinter (PR [#3235](https://github.com/javaparser/javaparser/pull/3235) by [@Zoom1111](https://github.com/Zoom1111))
* Handle possibility of tokens not being available (PR [#3231](https://github.com/javaparser/javaparser/pull/3231) by [@mernst](https://github.com/mernst))

### Developer Changes

* chore(deps): update dependency org.mockito:mockito-core to v3.10.0 (PR [#3259](https://github.com/javaparser/javaparser/pull/3259) by [@renovate[bot]](https://github.com/apps/renovate))
* Bump codecov/codecov-action from 1 to 1.5.0 (PR [#3258](https://github.com/javaparser/javaparser/pull/3258) by [@dependabot[bot]](https://github.com/apps/dependabot))
* Bump actions/create-release from 1 to 1.1.4 (PR [#3257](https://github.com/javaparser/javaparser/pull/3257) by [@dependabot[bot]](https://github.com/apps/dependabot))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@32kda](https://github.com/32kda)
* [@MysterAitch](https://github.com/MysterAitch)
* [@Zoom1111](https://github.com/Zoom1111)
* [@mernst](https://github.com/mernst)



Version 3.22.0
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/183?closed=1)


### API or Behaviour Change

* Implemented isAssignableBy for VoidType - now return `false` instead of throwing `UnsupportedOperationException` (PR [#3197](https://github.com/javaparser/javaparser/pull/3197) by [@4everTheOne](https://github.com/4everTheOne))
* fixed ellipsis and doublecolon to be categorised as separators not operators (fixes #2897) (PR [#2924](https://github.com/javaparser/javaparser/pull/2924) by [@MysterAitch](https://github.com/MysterAitch))

### Added

* Update parser configuration and validators to include the release of java 16, and java 17 being in development (PR [#3222](https://github.com/javaparser/javaparser/pull/3222) by [@MysterAitch](https://github.com/MysterAitch))
* Adding convenient methods to find out if a method is a variable/fixed arity method (PR [#3196](https://github.com/javaparser/javaparser/pull/3196) by [@jlerbsc](https://github.com/jlerbsc))
* Fix issue #3173: Add isAnnotation() and asAnnotation() methods for ResolvedTypeDeclaration (PR [#3187](https://github.com/javaparser/javaparser/pull/3187) by [@deadlocklogic](https://github.com/deadlocklogic))
* Record support (compilation / parsing only, solving to follow separately) (PR [#3022](https://github.com/javaparser/javaparser/pull/3022) by [@MysterAitch](https://github.com/MysterAitch))

### Changed

* Implemented isAssignableBy for VoidType - now return `false` instead of throwing `UnsupportedOperationException` (PR [#3197](https://github.com/javaparser/javaparser/pull/3197) by [@4everTheOne](https://github.com/4everTheOne))
* Simplify how to find the package name from AstResolutionUtils (PR [#3193](https://github.com/javaparser/javaparser/pull/3193) by [@jlerbsc](https://github.com/jlerbsc))
* Type resolution improvment (PR [#3189](https://github.com/javaparser/javaparser/pull/3189) by [@jlerbsc](https://github.com/jlerbsc))
* Memory optimization for JarTypeSolver (Up to 42% less memory) (PR [#3188](https://github.com/javaparser/javaparser/pull/3188) by [@4everTheOne](https://github.com/4everTheOne))
* Fixes #3048 (`JavaParserSymbolDeclaration#localVar` returning old declaration) and adds tests for `JavaParserSymbolDeclaration` (PR [#3049](https://github.com/javaparser/javaparser/pull/3049) by [@4everTheOne](https://github.com/4everTheOne))

### Fixed

* Fix issue #3244 OrphanComment in BlockStmt not appearing (PR [#3245](https://github.com/javaparser/javaparser/pull/3245) by [@jlerbsc](https://github.com/jlerbsc))
* fix Log.error() throwing NullPointerException (PR [#3243](https://github.com/javaparser/javaparser/pull/3243) by [@CD4017BE](https://github.com/CD4017BE))
* fixed ellipsis and doublecolon to be categorised as separators not operators (fixes #2897) (PR [#2924](https://github.com/javaparser/javaparser/pull/2924) by [@MysterAitch](https://github.com/MysterAitch))

### Developer Changes

* Include and use a Maven wrapper (PR [#3254](https://github.com/javaparser/javaparser/pull/3254) by [@MysterAitch](https://github.com/MysterAitch))
* chore(deps): update dependency org.javassist:javassist to v3.28.0-ga (PR [#3249](https://github.com/javaparser/javaparser/pull/3249) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.jacoco:jacoco-maven-plugin to v0.8.7 (PR [#3246](https://github.com/javaparser/javaparser/pull/3246) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update actions/cache action to v2.1.5 (PR [#3226](https://github.com/javaparser/javaparser/pull/3226) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update dependency org.mockito:mockito-core to v3.9.0 (PR [#3224](https://github.com/javaparser/javaparser/pull/3224) by [@renovate[bot]](https://github.com/apps/renovate))
* chore(deps): update actions/setup-java action to v2 (PR [#3220](https://github.com/javaparser/javaparser/pull/3220) by [@renovate[bot]](https://github.com/apps/renovate))
* Update javaparser copyright headers (PR [#3212](https://github.com/javaparser/javaparser/pull/3212) by [@jlerbsc](https://github.com/jlerbsc))
* Update readme template so that #3096 becomes permanent (PR [#3210](https://github.com/javaparser/javaparser/pull/3210) by [@MysterAitch](https://github.com/MysterAitch))
* Improve tests on `getAllAncestors` method (PR [#3209](https://github.com/javaparser/javaparser/pull/3209) by [@jlerbsc](https://github.com/jlerbsc))
* Fix surefire configuration to allow jacoco to run correctly on JSS tests (PR [#3208](https://github.com/javaparser/javaparser/pull/3208) by [@MysterAitch](https://github.com/MysterAitch))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@MysterAitch](https://github.com/MysterAitch)
* [@CD4017BE](https://github.com/CD4017BE)
* [@jlerbsc](https://github.com/jlerbsc)
* [@deadlocklogic](https://github.com/deadlocklogic)
* [@4everTheOne](https://github.com/4everTheOne)

Version 3.21.2
------------------
**v3.21.1 released as 3.21.2 without change**

Version 3.21.1
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/182?closed=1)

### Added

* Implemented logic for isAssignableBy in JavassistInterfaceDeclaration (PR [#3170](https://github.com/javaparser/javaparser/pull/3170) by [@4everTheOne](https://github.com/4everTheOne))
* Added additional tests to cover isAssignableBy method in JavassistClassDeclaration (PR [#3169](https://github.com/javaparser/javaparser/pull/3169) by [@4everTheOne](https://github.com/4everTheOne))

### Changed

* Update changelog (PR [#3178](https://github.com/javaparser/javaparser/pull/3178) by [@MysterAitch](https://github.com/MysterAitch))
* Minor performance improvement on getCanonicalName method call (PR [#3166](https://github.com/javaparser/javaparser/pull/3166) by [@jlerbsc](https://github.com/jlerbsc))

### Fixed

* Fix Issue #1950 Unambigous ambiguity call with <Void> generics and lambda's (PR [#3168](https://github.com/javaparser/javaparser/pull/3168) by [@jlerbsc](https://github.com/jlerbsc))
* Refactor the javassist implementation to delegate to the typesolver instead of using its own classpool (PR [#3167](https://github.com/javaparser/javaparser/pull/3167) by [@maartenc](https://github.com/maartenc))
* Fixed name resolution in casted lambda expressions (PR [#3165](https://github.com/javaparser/javaparser/pull/3165) by [@maartenc](https://github.com/maartenc))
* Fix issue #3159 JavaParserSymbolDeclaration is used to represent variables, but #isVariable() always returns false (PR [#3160](https://github.com/javaparser/javaparser/pull/3160) by [@jlerbsc](https://github.com/jlerbsc))
* Fix wrong author attribution in changelog for #3072 (PR [#3155](https://github.com/javaparser/javaparser/pull/3155) by [@Col-E](https://github.com/Col-E))
* Fixed #3136 - ThisExpr isn't resolved correctly when it is in the scope of an ObjectCreationExpr (PR [#3137](https://github.com/javaparser/javaparser/pull/3137) by [@deadlocklogic](https://github.com/deadlocklogic))
* Fix race condition in JavaParserTypeSolver (PR [#3091](https://github.com/javaparser/javaparser/pull/3091) by [@4everTheOne](https://github.com/4everTheOne))

### Developer Changes

* Publish to OSSRH rather than Bintray (PR [#3180](https://github.com/javaparser/javaparser/pull/3180) by [@MysterAitch](https://github.com/MysterAitch))
* Remove unused JUnit Pioneer dependency (PR [#3179](https://github.com/javaparser/javaparser/pull/3179) by [@MysterAitch](https://github.com/MysterAitch))
* Verify builds test correctly under JDK16 (PR [#3175](https://github.com/javaparser/javaparser/pull/3175) by [@MysterAitch](https://github.com/MysterAitch))
* update renovate to include "dependencies" label on PRs (PR [#3174](https://github.com/javaparser/javaparser/pull/3174) by [@MysterAitch](https://github.com/MysterAitch))
* chore(deps): update dependency com.google.guava:guava to v30.1.1-jre (PR [#3172](https://github.com/javaparser/javaparser/pull/3172) by [@renovate[bot]](https://github.com/apps/renovate))

### :heart: Contributors

Thank You to all contributors who worked on this release!

* [@maartenc](https://github.com/maartenc)
* [@MysterAitch](https://github.com/MysterAitch)
* [@jlerbsc](https://github.com/jlerbsc)
* [@deadlocklogic](https://github.com/deadlocklogic)
* [@4everTheOne](https://github.com/4everTheOne)
* [@Col-E](https://github.com/Col-E)



Version 3.20.0
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/181?closed=1)

### Added
* Issue #2991 - Added support for Iterables in CombinedTypeSolver
  (PR [#3033](https://github.com/javaparser/javaparser/pull/3033), by [@4everTheOne](https://github.com/4everTheOne))
* Implemented logic for getAllFields in Annotations
  (PR [#3097](https://github.com/javaparser/javaparser/pull/3097), by [@4everTheOne](https://github.com/4everTheOne))
### Changed
* Issue #2717 - Removed "empty" label from break statement and added additional test for BreakStmt
  (PR [#3109](https://github.com/javaparser/javaparser/pull/3109), by [@4everTheOne](https://github.com/4everTheOne))
* Issue #2708 - Improvement to the generated code (removal of redundant casts, and additions of `@Override`)
  (PR [#3124](https://github.com/javaparser/javaparser/pull/3124), by [@4everTheOne](https://github.com/4everTheOne))
* Performance improvement on ResolvedReferenceTypeDeclaration.isJavaLangObject()
  (PR [#3125](https://github.com/javaparser/javaparser/pull/3125), by [@jlerbsc](https://github.com/jlerbsc))
* Optimization to avoid systematically creating a class from javassist when the class has already been created
  (PR [#3126](https://github.com/javaparser/javaparser/pull/3126), by [@jlerbsc](https://github.com/jlerbsc))
* Bump jbehave-core from 4.8.1 to 4.8.2
  (PR [#3043](https://github.com/javaparser/javaparser/pull/3043), by [@dependabot](https://github.com/dependabot))
* Bump assertj-core from 3.18.1 to 3.19.0
  (PR [#3047](https://github.com/javaparser/javaparser/pull/3047), by [@dependabot](https://github.com/dependabot))
* Bump okhttp from 4.9.0 to 4.9.1
  (PR [#3054](https://github.com/javaparser/javaparser/pull/3054), by [@dependabot](https://github.com/dependabot))
* Bump actions/cache from v2 to v2.1.4
  (PR [#3070](https://github.com/javaparser/javaparser/pull/3070), by [@dependabot](https://github.com/dependabot))
* Bump mockito-core from 3.6.28 to 3.8.0
  (PR [#3110](https://github.com/javaparser/javaparser/pull/3110), by [@dependabot](https://github.com/dependabot))
* Bump junit from 4.13.1 to 4.13.2
  (PR [#3129](https://github.com/javaparser/javaparser/pull/3129), by [@dependabot](https://github.com/dependabot))
### Fixed
* Issue #3038 and Issue #3071 - Hanging when certain names are resolved
  (PR [#3072](https://github.com/javaparser/javaparser/pull/3072), by [@col-e](https://github.com/Col-E))
* Javadoc fixes
  (PR [#3082](https://github.com/javaparser/javaparser/pull/3082), by [@mernst](https://github.com/mernst))
* Update readme with correct Java support versions
  (PR [#3096](https://github.com/javaparser/javaparser/pull/3096), by [@MaartenGDev](https://github.com/MaartenGDev))
* Issue #3106 - Wrong descriptor for primitive type long
  (PR [#3107](https://github.com/javaparser/javaparser/pull/3107), by [@jlerbsc](https://github.com/jlerbsc))


Version 3.19.0
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/180?closed=1)

### Added
* Adding test case on PrettyPrinter indentation
  (PR [#2950](https://github.com/javaparser/javaparser/pull/2950), by [@jlerbsc](https://github.com/jlerbsc))
* Adding interface Printable for printer
  (PR [#2971](https://github.com/javaparser/javaparser/pull/2971), by [@jlerbsc](https://github.com/jlerbsc))
* Major update for pretty print, adding interfaces for printer configuration, printer, ... and deprecated old PrettyPrinter API 
  (PR [#2974](https://github.com/javaparser/javaparser/pull/2974), by [@jlerbsc](https://github.com/jlerbsc))
* Adding method descriptor resolution closes #2059
  (PR [#2976](https://github.com/javaparser/javaparser/pull/2976), by [@jlerbsc](https://github.com/jlerbsc))
* Adding management of the poly and standalone expression
  (PR [#2994](https://github.com/javaparser/javaparser/pull/2994), by [@jlerbsc](https://github.com/jlerbsc))
* Add test case for issue #1770 UnaryExpr failing to resolve BITWISE_COMPLEMENT operator   
  (PR [#3005](https://github.com/javaparser/javaparser/pull/3005), by [@jlerbsc](https://github.com/jlerbsc))
* Created additional validators to differentiate between enabling standard and preview features   
  (PR [#3015](https://github.com/javaparser/javaparser/pull/3015), by [@MysterAitch](https://github.com/MysterAitch))
* Added additional tests to TypeSolvers   
  (PR [#3046](https://github.com/javaparser/javaparser/pull/3046), by [@4everTheOne](https://github.com/4everTheOne))
* Improved JavaParserTypeVariableDeclaration tests   
  (PR [#3059](https://github.com/javaparser/javaparser/pull/3059), by [@4everTheOne](https://github.com/4everTheOne))
* Improved coverage for resolved declarations and fixed inconsistencies between them   
  (PR [#3062](https://github.com/javaparser/javaparser/pull/3062), by [@4everTheOne](https://github.com/4everTheOne))
* Additional GenericVisitorWithDefaults and VoidVisitorWithDefaults tests   
  (PR [#3067](https://github.com/javaparser/javaparser/pull/3067), by [@4everTheOne](https://github.com/4everTheOne))
* Additional tests for hash code visitors   
  (PR [#3068](https://github.com/javaparser/javaparser/pull/3068), by [@4everTheOne](https://github.com/4everTheOne))
* Add unit tests to issue #3074 Unable to delete .jar files after parsing and using symbol solver (re: #3074)   
  (PR [#3076](https://github.com/javaparser/javaparser/pull/3076), by [@jlerbsc](https://github.com/jlerbsc))
### Changed
* Minor refactoring regarding indentation management
  (PR [#2969](https://github.com/javaparser/javaparser/pull/2969), by [@jlerbsc](https://github.com/jlerbsc))
* Minor refactoring regarding indentation management (part2)
  (PR [#2970](https://github.com/javaparser/javaparser/pull/2970), by [@jlerbsc](https://github.com/jlerbsc))
* Minor refactoring moving Indentation class to configuration package - preparation for other refactoring on Printer
  (PR [#2972](https://github.com/javaparser/javaparser/pull/2972), by [@jlerbsc](https://github.com/jlerbsc))
* Bump guava from 30.0-jre to 30.1-jre
  (PR [#2977](https://github.com/javaparser/javaparser/pull/2977), by [@dependabot](https://github.com/dependabot))
* Refactoring: relocation of boxing/unboxing methods
  (PR [#2983](https://github.com/javaparser/javaparser/pull/2983), by [@jlerbsc](https://github.com/jlerbsc))
* Improve boxing/unboxing unit tests and remove useless code in isUnbox...
  (PR [#2984](https://github.com/javaparser/javaparser/pull/2984), by [@jlerbsc](https://github.com/jlerbsc))
* Bump jbehave-core from 4.7 to 4.8.1
  (PR [#2989](https://github.com/javaparser/javaparser/pull/2989), by [@dependabot](https://github.com/dependabot))
* Add JVM memory settings for surefire (seems that forked mode is the default running mode)
  (PR [#2999](https://github.com/javaparser/javaparser/pull/2999), by [@jlerbsc](https://github.com/jlerbsc))
* Move unit test Issue2592Test because it's not related to symbol solver
  (PR [#3000](https://github.com/javaparser/javaparser/pull/3000), by [@jlerbsc](https://github.com/jlerbsc))
* Manage memory on test suite (clear internal cache to release memory)
  (PR [#3001](https://github.com/javaparser/javaparser/pull/3001), by [@jlerbsc](https://github.com/jlerbsc))
* Remove the PhantomNodeLogic that generates memory issues when LexicalPreservingPrinter is used. Phantom node is now an attribut of each node. This is an optimization of the JP memory usage.
  (PR [#3002](https://github.com/javaparser/javaparser/pull/3002), by [@jlerbsc](https://github.com/jlerbsc))
* Make the visit order of ModifierVisitor more consistent.
  (PR [#3011](https://github.com/javaparser/javaparser/pull/3011), by [@mernst](https://github.com/mernst))
* Link to the specification, not to a random blog.
  (PR [#3013](https://github.com/javaparser/javaparser/pull/3013), by [@mernst](https://github.com/mernst))
* Minor refactoring change call to getScope().isPresent() to hasScope()
  (PR [#3026](https://github.com/javaparser/javaparser/pull/3026), by [@jlerbsc](https://github.com/jlerbsc))
* Issue #3050 - Minor improvement to thread safety
  (PR [#3052](https://github.com/javaparser/javaparser/pull/3052), by [@jlerbsc](https://github.com/jlerbsc))
### Deprecated
* `PhantomNodeLogic` is now deprecated, with the logic now being handled by the node itself.
  (PR [#3002](https://github.com/javaparser/javaparser/pull/3002), by [@jlerbsc](https://github.com/jlerbsc))
### Fixed
* Fix issue on pretty configuration change
  (PR [#2979](https://github.com/javaparser/javaparser/pull/2979), by [@jlerbsc](https://github.com/jlerbsc))
* Fix trivial poly expression lambda, method reference, and parenthesized expressions
  (PR [#2981](https://github.com/javaparser/javaparser/pull/2981), by [@jlerbsc](https://github.com/jlerbsc))
* Partially fix the issue #1743 ConditionalExpr resolves to wrong type
  (PR [#2982](https://github.com/javaparser/javaparser/pull/2982), by [@jlerbsc](https://github.com/jlerbsc))
* Partially fix issue #1743 ConditionalExpr resolves to wrong type - trying to manage reference condition expression but lub (least upper bound) function is not yet implemented
  (PR [#3004](https://github.com/javaparser/javaparser/pull/3004), by [@jlerbsc](https://github.com/jlerbsc))
* Issue #2987 StackOverflow error 
  (PR [#3006](https://github.com/javaparser/javaparser/pull/3006), by [@jlerbsc](https://github.com/jlerbsc))
* Issue #1774 Ensure the correct type is calculated for all binary expressions and add unary primitive promotion   
  (PR [#3007](https://github.com/javaparser/javaparser/pull/3007), by [@jlerbsc](https://github.com/jlerbsc))
* Issue #2995 Cannot resolve ClassOrInterfaceType of nested ObjectCreationExpr  
  (PR [#3019](https://github.com/javaparser/javaparser/pull/3019), by [@jlerbsc](https://github.com/jlerbsc))
* Issue #1634 Missing EOL when add imports if the class not exist imports before 
  (PR [#3020](https://github.com/javaparser/javaparser/pull/3020), by [@jlerbsc](https://github.com/jlerbsc))
* Issue #3024 methodCallExpr.resolve() StackOverflowError 
  (PR [#3025](https://github.com/javaparser/javaparser/pull/3025), by [@jlerbsc](https://github.com/jlerbsc))
* Issue #3027 Unable to parse class with generic parameter using JavaParserTypeSolver 
  (PR [#3029](https://github.com/javaparser/javaparser/pull/3029), by [@jlerbsc](https://github.com/jlerbsc))
* Issue #3030 NoSuchElementException when solving type 
  (PR [#3031](https://github.com/javaparser/javaparser/pull/3031), by [@4everTheOne](https://github.com/4everTheOne))
* Issue 3028  -- Changed MethodResolutionLogic to deal with multiple candidates with varargs when varargs have not been specified in the call.
  (PR [#3032](https://github.com/javaparser/javaparser/pull/3032), by [@greggers123](https://github.com/greggers123))
* Issue #1834 Improving annotation support: Implement ResolvedAnnotationDeclaration#getDefaultValue()
  (PR [#3055](https://github.com/javaparser/javaparser/pull/3055), by [@jlerbsc](https://github.com/jlerbsc))
* Issue #3057 Removed redundant definition of method to inherit from super
  (PR [#3058](https://github.com/javaparser/javaparser/pull/3058), by [@4everTheOne](https://github.com/4everTheOne))
* Issue #3074 Unable to delete .jar files after parsing
  (PR [#3075](https://github.com/javaparser/javaparser/pull/3075), by [@jlerbsc](https://github.com/jlerbsc))
* Issue #3083 Fix choosing the most specific method in case of java.lang.Object argument type
  (PR [#3084](https://github.com/javaparser/javaparser/pull/3084), by [@jlerbsc](https://github.com/jlerbsc))


Version 3.18.0
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/179?closed=1)

### Added
* Add a convenient method (hasRange) to the interface NodeWithRange  
    (PR [#2929](https://github.com/javaparser/javaparser/pull/2929), by [@jlerbsc](https://github.com/jlerbsc))
* Add test case to issue 1017 LambdaExpr left side too permissive
    (PR [#2946](https://github.com/javaparser/javaparser/pull/2946), by [@jlerbsc](https://github.com/jlerbsc))
* Added Pattern Matching for instanceof (Java 14 preview, Java 15 second preview, Java 16 targeted release)
    (PR [#2654](https://github.com/javaparser/javaparser/pull/2654), by [@MysterAitch](https://github.com/MysterAitch))
* Added java 15 (latest released) and java 16 (bleeding edge) language level options, incl. some validators / post processors / configuration options
    (PR [#2959](https://github.com/javaparser/javaparser/pull/2959), by [@MysterAitch](https://github.com/MysterAitch))
### Changed
* Minor change in PrettyPrinterConfiguration : adding default char in enum IndentType
    (PR [#2948](https://github.com/javaparser/javaparser/pull/2948), by [@jlerbsc](https://github.com/jlerbsc))
* Minor refactoring rename interface Printable to Stringable. Something that has a printable form. I.e., it can be converted to a user-facing String
    (PR [#2949](https://github.com/javaparser/javaparser/pull/2949), by [@jlerbsc](https://github.com/jlerbsc))
* Adding interface Printable for printer
    (PR [#2950](https://github.com/javaparser/javaparser/pull/2950), by [@jlerbsc](https://github.com/jlerbsc))
* Minor refactoring in ResolvedReferenceType and add corresponding tests 
    (PR [#2955](https://github.com/javaparser/javaparser/pull/2955), by [@jlerbsc](https://github.com/jlerbsc))
* Tweak the property generator to add imports when generating and improve the typecastinggenerator's error message
    (PR [#2957](https://github.com/javaparser/javaparser/pull/2957), by [@MysterAitch](https://github.com/MysterAitch))
* Bump mockito-core from 3.6.0 to 3.6.28
    (PR [#2942](https://github.com/javaparser/javaparser/pull/2942), by dependabot
### Removed
* Removed .travis.yml -- per #2919 
    (PR [#2958](https://github.com/javaparser/javaparser/pull/2958), by [@MysterAitch](https://github.com/MysterAitch))
### Fixed
* Issue 2909 Improving search for the most relevant declaration of the specified class  
    (PR [#2927](https://github.com/javaparser/javaparser/pull/2927), by [@jlerbsc](https://github.com/jlerbsc))
* Issue 2926 NoSuchElementException in PhantomNodeLogic after adding node  
    (PR [#2930](https://github.com/javaparser/javaparser/pull/2930), by [@jlerbsc](https://github.com/jlerbsc))
* Issue 2909 try different bottom / up and try with type solver strategies 
    (PR [#2931](https://github.com/javaparser/javaparser/pull/2931), by [@jlerbsc](https://github.com/jlerbsc))
* Issue 2936 Triggering observer notifications for the NodeList iterator
    (PR [#2938](https://github.com/javaparser/javaparser/pull/2938), by [@MysterAitch](https://github.com/MysterAitch))
* Issue 2065 Problem resolving type of lambda with Math method invocation inside 
    (PR [#2945](https://github.com/javaparser/javaparser/pull/2945), by [@jlerbsc](https://github.com/jlerbsc))
* Issue 2740 Issue related to a method call in an anonymous class on a field with a private visibility
    (PR [#2947](https://github.com/javaparser/javaparser/pull/2947), by [@jlerbsc](https://github.com/jlerbsc))
* Issue 2951 Cannot solve function with List<byte[]> argument defined in jar 
    (PR [#2952](https://github.com/javaparser/javaparser/pull/2952), by [@qzchenwl](https://github.com/qzchenwl))
* Issue 2781 Resolve Stack overflow occurs when the name of the interface implemented by the class is the same as the name of the internal class 
    (PR [#2956](https://github.com/javaparser/javaparser/pull/2956), by [@jlerbsc](https://github.com/jlerbsc))
* Issue 2953 UnsolvedSymbolException throw when resolving method in enum class implement in interface by default.  
    (PR [#2954](https://github.com/javaparser/javaparser/pull/2954), by [@qzchenwl](https://github.com/qzchenwl))
* Fixed MethodCallExprContext generic parameter issue. (NullType must not fail matchTypeParameters)
    (PR [#2939](https://github.com/javaparser/javaparser/pull/2939), by [@zcbbpo](https://github.com/zcbbpo))
* Issue 2943 UnsolvedSymbolException thrown on `Stream.<func>(<some lambda>)` 
    (PR [#2961](https://github.com/javaparser/javaparser/pull/2961), by [@qzchenwl](https://github.com/qzchenwl))
* Issue 1945 JavaParser choking on multiple generic method calls on the same line 
    (PR [#2966](https://github.com/javaparser/javaparser/pull/2966), by [@jlerbsc](https://github.com/jlerbsc))


Version 3.17.0
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/178?closed=1)
### Fixed
* BEHAVIOUR CHANGE: Fix ArrayType brackets precedence
    (PR [#2758](https://github.com/javaparser/javaparser/pull/2758), by [@iTakeshi](https://github.com/iTakeshi))
* BEHAVIOUR CHANGE: Issue 2535 Comments within method missing indentation  
    (PR [#2918](https://github.com/javaparser/javaparser/pull/2918), by [@jlerbsc](https://github.com/jlerbsc))
* Issue 2290 Removing the second instance of a cloned statement within a block fails
    (PR [#2892](https://github.com/javaparser/javaparser/pull/2892), by [@jlerbsc](https://github.com/jlerbsc))
* Issue 2393 Apply difference in node text after if condition replacement
    (PR [#2895](https://github.com/javaparser/javaparser/pull/2895), by [@jlerbsc](https://github.com/jlerbsc))
* Issue 2406 Symbol solver fails to solve generic array type 
    (PR [#2896](https://github.com/javaparser/javaparser/pull/2896), by [@jlerbsc](https://github.com/jlerbsc))
* Issue 2489 SymbolSolver choosing wrong method after resolving 
    (PR [#2898](https://github.com/javaparser/javaparser/pull/2898), by [@jlerbsc](https://github.com/jlerbsc))
* Issue 2062 Type inference issue for method arguments 
    (PR [#2900](https://github.com/javaparser/javaparser/pull/2900), by [@jlerbsc](https://github.com/jlerbsc))
* Fix LOOKAHEAD for ReferenceType 
    (PR [#2904](https://github.com/javaparser/javaparser/pull/2904), by [@mernst](https://github.com/mernst))
* Issue 2578 Orphaned Comments exist but not printed on unrelated change to AST 
    (PR [#2916](https://github.com/javaparser/javaparser/pull/2916), by [@jlerbsc](https://github.com/jlerbsc))
* Issue 2909 Unexpected result when solving an outer class reference 
    (PR [#2914](https://github.com/javaparser/javaparser/pull/2914), by [@jlerbsc](https://github.com/jlerbsc))
* Issue 2909 Improving how to resolve inner classes  
    (PR [#2920](https://github.com/javaparser/javaparser/pull/2920), by [@jlerbsc](https://github.com/jlerbsc))
    (PR [#2921](https://github.com/javaparser/javaparser/pull/2921), by [@jlerbsc](https://github.com/jlerbsc))
* Ensure spaces between annotations and types for lexical-preserving printing
    (PR [#2795](https://github.com/javaparser/javaparser/pull/2918), by [@jwaataja](https://github.com/jwaataja))

### Changed
* Updated dependencies, and dependabot config
    (PR [#2893](https://github.com/javaparser/javaparser/pull/2893), by [@mysteraitch](https://github.com/mysteraitch))
    (PR [#2902](https://github.com/javaparser/javaparser/pull/2902), by Dependabot)
* Issue 2613 Auto update the version in the readme 
    (PR [#2903](https://github.com/javaparser/javaparser/pull/2903), by [@mysteraitch](https://github.com/mysteraitch))
* Fix jacoco and enable codecov.io action
    (PR [#2906](https://github.com/javaparser/javaparser/pull/2906), by [@mysteraitch](https://github.com/mysteraitch))
* Minor refactoring of binary numeric promotion 
    (PR [#2915](https://github.com/javaparser/javaparser/pull/2915), by [@jlerbsc](https://github.com/jlerbsc))
* Testcases for logical and/or 
    (PR [#2907](https://github.com/javaparser/javaparser/pull/2907), by [@mysteraitch](https://github.com/mysteraitch))
* Format and document the grammar 
    (PR [#2901](https://github.com/javaparser/javaparser/pull/2901), by [@mysteraitch](https://github.com/mysteraitch))
    (PR [#2913](https://github.com/javaparser/javaparser/pull/2913), by [@mernst](https://github.com/mernst))


Version 3.16.3
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/177?closed=1)
* ADDED: Created MANY test cases for older issues resolved but not directly linked/closed.
    (PRs
    [#2838](https://github.com/javaparser/javaparser/pull/2838), 
    [#2842](https://github.com/javaparser/javaparser/pull/2842), 
    [#2843](https://github.com/javaparser/javaparser/pull/2843), 
    [#2852](https://github.com/javaparser/javaparser/pull/2852), 
    [#2853](https://github.com/javaparser/javaparser/pull/2853), 
    [#2854](https://github.com/javaparser/javaparser/pull/2854), 
    [#2855](https://github.com/javaparser/javaparser/pull/2855), 
    [#2867](https://github.com/javaparser/javaparser/pull/2867), 
    [#2868](https://github.com/javaparser/javaparser/pull/2868), 
    [#2862](https://github.com/javaparser/javaparser/pull/2862), 
    [#2873](https://github.com/javaparser/javaparser/pull/2873), 
    by [@jlerbsc](https://github.com/jlerbsc)
    )
* ADDED: Added helper method to `ResolvedPrimitiveType.java` which checks if it is a boolean
    (PR [#2856](https://github.com/javaparser/javaparser/pull/2856), by [@jlerbsc](https://github.com/jlerbsc))
* ADDED: Added helper method to `ResolvedPrimitiveType.java` which returns all numeric types
    (PR [#2858](https://github.com/javaparser/javaparser/pull/2858), by [@jlerbsc](https://github.com/jlerbsc))
* ADDED/CHANGED: Minor refactoring - formatting code and adding convenient methods to `TypeHelper` and `ResolvedPrimitveType`
    (PR [#2860](https://github.com/javaparser/javaparser/pull/2860), by [@jlerbsc](https://github.com/jlerbsc))
* ADDED: Allow the symbol resolver for a `SymbolSolverCollectionStrategy` to be set via the given parser configuration
    (PR [#2864](https://github.com/javaparser/javaparser/pull/2864), by [@jlerbsc](https://github.com/jlerbsc))
* FIXED: `MethodResolutionLogic.findMostApplicable` not return correct symbol reference when resolving overloaded method
    (PR [#2866](https://github.com/javaparser/javaparser/pull/2866), by [@jlerbsc](https://github.com/jlerbsc))
* FIXED: Updated `AbstractSymbolResolutionTest.java` with better `@BeforeEach`/`@AfterEach`  
    (PR [#2871](https://github.com/javaparser/javaparser/pull/2871), by [@jlerbsc](https://github.com/jlerbsc))
* FIXED: `TypeResolver` fails on method with args to static imported fields
    (PR [#2872](https://github.com/javaparser/javaparser/pull/2872), by [@jlerbsc](https://github.com/jlerbsc))
* FIXED: Fix issue Resolution error for non-generic constructor if generic constructor declared
    (PR [#2874](https://github.com/javaparser/javaparser/pull/2874), by [@jlerbsc](https://github.com/jlerbsc))
* FIXED: Fix issue Fails to calculate the type of a generic return type constructed from a Primitive type
    (PR [#2875](https://github.com/javaparser/javaparser/pull/2875), by [@jlerbsc](https://github.com/jlerbsc))
* FIXED: Fix issue Can't get qualified signature of a resolved method inside a Constant Enum declaration 
    (PR [#2876](https://github.com/javaparser/javaparser/pull/2876), by [@jlerbsc](https://github.com/jlerbsc))
* FIXED: Fix issue Constructor resolution error for overloaded variadic constructor
    (PR [#2877](https://github.com/javaparser/javaparser/pull/2877), by [@jlerbsc](https://github.com/jlerbsc))
* FIXED: Fix issue Unable to find the constructor declaration when the argument list contains multiple `Optional.empty()` for different `Optional<T>`
    (PR [#2880](https://github.com/javaparser/javaparser/pull/2880), by [@jlerbsc](https://github.com/jlerbsc))
* FIXED: Fix issue Solving symbol as value in the case where the scope is a constraint
    (PR [#2883](https://github.com/javaparser/javaparser/pull/2883), by [@jlerbsc](https://github.com/jlerbsc))


Version 3.16.2
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/176?closed=1)
* FIXED: Enhanced the handling of line separator, introducing an enum `LineSeparator` that can be used.
    (PR [#2685](https://github.com/javaparser/javaparser/pull/2685), by [@MysterAitch](https://github.com/MysterAitch))
* FIXED: The generated metamodel classes now have the `@Generated` annotation 
    (PR [#2706](https://github.com/javaparser/javaparser/pull/2706), by [@MysterAitch](https://github.com/MysterAitch))
* various other bugfixes and enhancements


Version 3.16.1
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/175?closed=1)
* FIXED: Fixed typo
    (PR [#2697](https://github.com/javaparser/javaparser/pull/2697), by [@hfreeb](https://github.com/hfreeb))


Version 3.16.0
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/174?closed=1)

There are two breaking changes within this release. 
If you would like assistance with upgrading, get in touch.

* FIXED: Edits to the value of a string value are now correctly handled for use with Lexical Preservation 
    (PR [#2646](https://github.com/javaparser/javaparser/pull/2646), by [@lemoncurry](https://github.com/lemoncurry))
* FIXED: Edits to the value of other literal values also now handled 
    (PR [#2679](https://github.com/javaparser/javaparser/pull/2679), by [@MysterAitch](https://github.com/MysterAitch))
* BREAKING CHANGE: Tokens relating to literal values now have the category of `JavaToken.Category.LITERAL` (previously `JavaToken.Category.KEYWORD`) 
    (PR [#2679](https://github.com/javaparser/javaparser/pull/2679), by [@MysterAitch](https://github.com/MysterAitch))
* FIXED: Add symbol solver support for variadic parameters given zero or more than one argument, and when an array is given
    (PR [#2675](https://github.com/javaparser/javaparser/pull/2675), by [@hfreeb](https://github.com/hfreeb))
* CHANGED: Added the keyword `synchronized` to `JavaParserFacade#get`. This is specifically in response to #2668 - JavaParser is not otherwise threadsafe.  
    (PR [#2694](https://github.com/javaparser/javaparser/pull/2694), by [@MysterAitch](https://github.com/MysterAitch))
* BREAKING CHANGE: The following methods now return `Optional<>` _(as do all classes which implement/extend them)_:
    `ResolvedClassDeclaration#getSuperClass()`, 
    `ResolvedReferenceType#getTypeDeclaration()`.  
    _Note that Converting to use optional should be as simple as adding `.get()`, given that any cases where returning `Optional.empty()` causes problems would  have also previously triggered a `NullPointerException`. 
    You might also use `.orElseThrow()`._  
    (PR [#2693](https://github.com/javaparser/javaparser/pull/2693), by [@MysterAitch](https://github.com/MysterAitch))
* CHANGED: Added some temporary logic to allow tests to use slightly different expected results based on the version of java used _(e.g. `java.lang.Object.registerNatives()` removed in JDK14)_  
    (PR [#2637](https://github.com/javaparser/javaparser/pull/2637), by [@EFregnan](https://github.com/EFregnan))
* FIXED: Fix resolving overloaded methods of external types  
    (PR [#2687](https://github.com/javaparser/javaparser/pull/2687), by [@maartenc](https://github.com/maartenc))
* FIXED: Fix resolving method references on expressions other than ReferenceType::methodname  
    (PR [#2674](https://github.com/javaparser/javaparser/pull/2674), by [@maartenc](https://github.com/maartenc))



Version 3.15.22
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/173?closed=1)
* REVERT: Rollback of upgrade to `ph-javacc-maven-plugin` from v4.1.3 to v4.1.2 
    _(this undoes the transitive dependency update `parser-generator-cc` from v1.1.2 to v1.1.1, which appears to have isuse with handling tokens longer than the buffer length)_  
    ([#2646](https://github.com/javaparser/javaparser/pull/2646))
* ADDED: Support resolving an enum's `valueOf` method
    ([#2652](https://github.com/javaparser/javaparser/pull/2652))
* FIXED: Fixed build warning -- bnd-maven-plugin flagging missing id 
    ([#2605](https://github.com/javaparser/javaparser/pull/2605))
* FIXED: Fixed cases where nodes added after a trailing comment would incorrectly be added to the same line (thus be part of the comment)
    ([#2646](https://github.com/javaparser/javaparser/pull/2646))
* FIXED: Fixed resolving overloaded static method references (e.g. `String::valueOf` in a stream map/filter)
    ([#2662](https://github.com/javaparser/javaparser/pull/2662))


Version 3.15.21
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/172?closed=1)

* DEPRECATED: Deprecated and documented `JarTypeSolver#getJarTypeSolver(String)`, with a view to later removal.
    ([#2598](https://github.com/javaparser/javaparser/pull/2598))
    ([#2622](https://github.com/javaparser/javaparser/pull/2622))
* FIXED: Fix issue #2552 : UnsupportedOperationException caused by resolving inner annotation
    ([#2553](https://github.com/javaparser/javaparser/pull/2553))
* FIXED: Parents of `NodeList`s now correctly retain their parent when a child is replaced 
    ([#2594](https://github.com/javaparser/javaparser/pull/2594))
* FIXED: Fix JavaParserClassDeclaration canBeAssignedTo() to not cause a recursion when a node is its own parent (e.g. `java.lang.Object`)
    ([#2608](https://github.com/javaparser/javaparser/pull/2608))
* FIXED: Fix replacing an expression preceded by a comment (`LexicalPreservation` would previously throw an `UnsupportedOperation`)
    ([#2611](https://github.com/javaparser/javaparser/pull/2611))
* FIXED: The collection strategies now correctly take into account the parser configuration that is passed in via the constructor.
    ([#2619](https://github.com/javaparser/javaparser/pull/2619))


Version 3.15.20
------------------
_skipped_

Version 3.15.19
------------------
_skipped_

Version 3.15.18
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/170?closed=1)

* CHANGED: Dependencies should now all be up-to-date. 
  ([#2572](https://github.com/javaparser/javaparser/pull/2572) / [#2581](https://github.com/javaparser/javaparser/pull/2581))
  - Note that the JavaCC update introduced a breaking change that now requires a StreamProvider to be passed a charset if using an InputStream source.
* FIXED (possible CHANGED/BREAKING): 
  Improvements have been made to method `PositionUtils#nodeContains()` for clarity and precision in behaviour.
  ([#2502](https://github.com/javaparser/javaparser/pull/2502))
  - It is believed that there are no changes to behaviour, but if you do see anything please do reach out.
  - See some additional commentary/thoughts in #2502
* FIXED: Resolving super methodcalls in anonymous inner classes (fixes #1962)
    ([#2585](https://github.com/javaparser/javaparser/pull/2585))
* ADDED: `NodeList#getFirst(): Optional<Node>`
    ([#2502](https://github.com/javaparser/javaparser/pull/2502))
* ADDED: `NodeList#getLast(): Optional<Node>`
    ([#2502](https://github.com/javaparser/javaparser/pull/2502))

Version 3.15.17
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/169?closed=1)

* CHANGED: Merged symbol solver modules, for java 9 module compatibility
    ([#2564](https://github.com/javaparser/javaparser/pull/2564))
* CHANGED: Renamed the pretty printer configuration option `isSpacesBetweenOperators` to `isSpaceAroundOperators` 
    ([#2555](https://github.com/javaparser/javaparser/pull/2555))

Version 3.15.16
------------------
_Version skipped_

Version 3.15.15
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/168?closed=1)

* Often requested, finally implemented by [ReallyLiri](https://github.com/ReallyLiri):
configurable cache sizes for the symbol solver.

Version 3.15.14 (buggy)
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/167?closed=1)

* a suggestion for a new Javadoc parsing API was merged too quickly,
causing issues parsing Javadoc while parsing Java normally. 

Version 3.15.13
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/166?closed=1)

Version 3.15.12
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/165?closed=1)

Version 3.15.11
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/164?closed=1)

Version 3.15.10
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/163?closed=1)

Version 3.15.9
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/161?closed=1)

Version 3.15.8
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/160?closed=1)

Version 3.15.7
------------------
* BREAKING: Range.overlapsWith works slightly different now.

[issues resolved](https://github.com/javaparser/javaparser/milestone/162?closed=1)

Version 3.15.6
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/159?closed=1)

Version 3.15.5
------------------
* BREAKING: bugs have been fixed in how SourceRoot configures parsing,
so behaviour may change (which can be fixed by setting configuration on SourceRoot correctly.)

[issues resolved](https://github.com/javaparser/javaparser/milestone/158?closed=1)

Version 3.15.4
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/157?closed=1)

Version 3.15.3
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/156?closed=1)

Version 3.15.2
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/155?closed=1)

Version 3.15.1
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/154?closed=1)

Version 3.15.0
------------------
- The funny "PI" version number messed up the release order in the maven site,
    so here is a new minor release.
[issues resolved](https://github.com/javaparser/javaparser/milestone/153?closed=1)

Version 3.14.16
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/152?closed=1)

Version 3.14.159265359
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/151?closed=1)

Version 3.14.14 
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/150?closed=1)

Version 3.14.13
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/149?closed=1)

Version 3.14.12
------------------
- BREAKING: `NodeWithConstructors` has been merged into `NodeWithMembers`,
so if you don't have a very specific need to only find nodes that support constructors,
you can use `NodeWithMembers` instead.

[issues resolved](https://github.com/javaparser/javaparser/milestone/148?closed=1)

Version 3.14.11
------------------
- BREAKING: the pseudo-language levels have been turned into constants with the same name in the same place.
With a little luck everything will keep compiling.

[issues resolved](https://github.com/javaparser/javaparser/milestone/147?closed=1)

Version 3.14.10 (buggy!)
------------------
- BREAKING: Java 13: `break` no longer has an expression, this was part of a language preview in Java 12
and has been removed in Java 13.
- BREAKING: Java 13: `YieldStatement` and the keyword `yield` have been added.
This means the token numbers have changed, and this affects serialization.
If you rely on serialized tokens, be sure to deserialize with your current version and serialize with this version.
- Java 13: `TextBlockLiteralExpr` has been added.
- This release is broken because no identifier called `yield` can be used.

[issues resolved](https://github.com/javaparser/javaparser/milestone/146?closed=1)

Version 3.14.9
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/145?closed=1)

Version 3.14.8
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/144?closed=1)

Version 3.14.7
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/143?closed=1)

Version 3.14.6 (oops, failed)
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/142?closed=1)

Version 3.14.5
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/141?closed=1)

Version 3.14.4
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/140?closed=1)

Version 3.14.3
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/139?closed=1)

Version 3.14.2
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/138?closed=1)

Version 3.14.1
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/137?closed=1)

Version 3.14.0
------------------
* BREAKING: `SuperExpr` and `ThisExpr` used to have an `Expression classExpr`.
this has been tightened to `Name typeName` which is more specific and easier to use.
Checking if the expression is a `FieldAccessExpr` or `NameExpr` is no longer needed. 

[issues resolved](https://github.com/javaparser/javaparser/milestone/136?closed=1)

Version 3.13.10
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/135?closed=1)

Version 3.13.9
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/134?closed=1)

Version 3.13.8 (failed)
------------------
(release failed)

Version 3.13.7
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/133?closed=1)

Version 3.13.6
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/132?closed=1)

Version 3.13.5
------------------
* "BREAKING": `ReferenceType.getDirectAncestors()` no longer returns `java.lang.Object` when called on a `ReferenceType` of `java.lang.Object`.
This remedies infinite recursions in certain edge cases. If you relied on the old behavior, you have to add a `ReferenceType` instance of `java.lang.Object`
to the List returned by `ReferenceType.getDirectAncestors()` yourself.

[issues resolved](https://github.com/javaparser/javaparser/milestone/131?closed=1)

Version 3.13.4
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/130?closed=1)

Version 3.13.3
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/129?closed=1)

Version 3.13.2
------------------
* Version 3.13.0 and 3.13.1 contain rather bad bugs that have been fixed here.

[issues resolved](https://github.com/javaparser/javaparser/milestone/128?closed=1)

Version 3.13.1 (buggy!)
------------------
* Slightly breaking: most parameters to Log methods now take consumers to avoid evaluating them when not necessary. 

[issues resolved](https://github.com/javaparser/javaparser/milestone/127?closed=1)

Version 3.13.0 (buggy!)
------------------
* "BREAKING": The static `JavaParser.parse...` methods have moved to `StaticJavaParser.parse...`!

[issues resolved](https://github.com/javaparser/javaparser/milestone/126?closed=1)

Version 3.12.0
------------------
* "BREAKING": all deprecated code was removed.
If you don't know what to do, try version 3.11.0 and read the Javadoc for the deprecated methods.
It tells you what to use instead.

[issues resolved](https://github.com/javaparser/javaparser/milestone/124?closed=1)

Version 3.11.0
------------------
* BREAKING: `SwitchEntryStmt` is now `SwitchEntry`, because it was never a statement.
* BREAKING: a case in a switch can now have multiple labels,
so `SwitchEntry` no longer has an `Expression label`,
but a `NodeList<Expression> label`.
* This completes *parsing* support for Java 12.
Symbol resolution is still to be done.

[issues resolved](https://github.com/javaparser/javaparser/milestone/123?closed=1)

Version 3.10.2
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/122?closed=1)

Version 3.10.1
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/121?closed=1)

Version 3.10.0
------------------
* slightly breaking: besides `break;` and `break [label];` there is now `break [expression];` like
`break 1+2;` or `break "bye!";` . That means that `BreakStmt` no longer has a `label`,
it has a `value` which is of type `Expression`.
This is to prepare for Java 12 switch expressions.
You can find the details in the Javadoc.

[issues resolved](https://github.com/javaparser/javaparser/milestone/120?closed=1)

Version 3.9.1
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/119?closed=1)

Version 3.9.0
------------------
* MAJOR BREAKAGE: modifiers (like public, static, transient) used to be a special case:
they were enums stored in an EnumSet.
This meant they were not true `Node`s, had to be treated in a special way, and missed some information.
This has now been corrected in [PR 1975](https://github.com/javaparser/javaparser/pull/1975). 

[issues resolved](https://github.com/javaparser/javaparser/milestone/118?closed=1)

Version 3.8.3
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/117?closed=1)

Version 3.8.2
------------------
* slightly breaking: `ObjectCreationExpr` no longer gets a diamond when constructed with the default constructor.

[issues resolved](https://github.com/javaparser/javaparser/milestone/116?closed=1)

Version 3.8.1
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/114?closed=1)

Version 3.8.0
------------------
* A Unicode preprocessing filter is now available again.

[issues resolved](https://github.com/javaparser/javaparser/milestone/113?closed=1)

Version 3.7.1
------------------
* slightly breaking: the enum constants in JsonToken are now capitalized.
* slightly breaking: [some obscure methods in the symbol solver changed](https://github.com/javaparser/javaparser/pull/1922) 

[issues resolved](https://github.com/javaparser/javaparser/milestone/115?closed=1)

Version 3.7.0
------------------
* BREAKING: `ForeachStmt` is now correctly capitalized: `ForEachStmt`
* BREAKING: when using modules, everything that was called `...Statement` is now correctly called `...Directive`

[issues resolved](https://github.com/javaparser/javaparser/milestone/112?closed=1)

Version 3.6.27
------------------
* The Json serialization now serializes more fields,
which *should* not impact existing code.

[issues resolved](https://github.com/javaparser/javaparser/milestone/111?closed=1)

Version 3.6.26
------------------
* BREAKING: Node.getData now throws an exception if the data was not set before.
This can be rewritten by checking with Node.containsData before doing getData.

[issues resolved](https://github.com/javaparser/javaparser/milestone/110?closed=1)

Version 3.6.25
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/109?closed=1)

Version 3.6.24
------------------
* `findAncestor(type, predicate)` is now available

[issues resolved](https://github.com/javaparser/javaparser/milestone/108?closed=1)

Version 3.6.23
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/107?closed=1)

Version 3.6.22
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/106?closed=1)

Version 3.6.21
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/105?closed=1)

Version 3.6.20
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/104?closed=1)

Version 3.6.19
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/103?closed=1)

Version 3.6.18
------------------
* Parsing Java 11 is now supported.
* Running on Java 11 is now supported.
* Building on JDK 11 is NOT yet supported.

[issues resolved](https://github.com/javaparser/javaparser/milestone/101?closed=1)

Version 3.6.17
------------------
* A new artifact was added: javaparser-core-serialization.
It contains a JSON serializer, and might get more serializers in the future.

[issues resolved](https://github.com/javaparser/javaparser/milestone/100?closed=1)

Version 3.6.16
------------------
* BREAKING: some parts of the module syntax used `Type` where they should have used `Name`.
This is now fixed, but your code may need to be adapted if you are parsing modules.

[issues resolved](https://github.com/javaparser/javaparser/milestone/99?closed=1)

Version 3.6.15
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/98?closed=1)

Version 3.6.14
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/97?closed=1)

Version 3.6.13
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/96?closed=1)
* JavaParserFacade.getType now can also handle NameExpr referring to types 
while before they were not supported.
See [issue #1491](https://github.com/javaparser/javaparser/issues/1491#issuecomment-403277963)

Version 3.6.12
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/95?closed=1)

Version 3.6.10 & Version 3.6.11
------------------
* A mixup during the release put all the issues in the same milestone:

[issues resolved](https://github.com/javaparser/javaparser/milestone/94?closed=1)

Version 3.6.9
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/93?closed=1)

Version 3.6.8
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/92?closed=1)
* Intellij Idea project files were deleted from the repository,
so if you have a clone of the JP source, your local files will be deleted as well.
Save anything you want to keep.

Version 3.6.7
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/91?closed=1)

Version 3.6.6
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/90?closed=1)
* You can now configure the parser inside JavaParserTypeSolver.

Version 3.6.5
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/89?closed=1)
* Be aware of annotations or indents looking slightly different when output!

Version 3.6.4
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/88?closed=1)

Version 3.6.3
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/87?closed=1)

Version 3.6.2
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/86?closed=1)

Version 3.6.1
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/85?closed=1)
* BREAKING: `SymbolSolverQuickSetup` has been removed in favor of `ProjectRoot` and `SymbolSolverCollectionStrategy`.

Version 3.6.0
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/84?closed=1)
* @daanschipper added `ProjectRoot` which is used for analysing and storing project structure.
* Upgraded version from 3.5.20 to 3.6.0 because people got tired of seeing 3.5.

Version 3.5.20
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/83?closed=1)
* Thanks to @daanschipper for the PR :-)

Version 3.5.19
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/82?closed=1)

Version 3.5.18
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/81?closed=1)

Version 3.5.17
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/80?closed=1)

Version 3.5.16
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/79?closed=1)

Version 3.5.15
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/78?closed=1)
* Java 10 support is complete.
* BREAKING: Java language level support has changed to make Java 10 support possible.
[Here's a little article about it](https://matozoid.github.io/2017/04/11/enable-java-9-support.html)

Version 3.5.14
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/77?closed=1)
* Java 10's `var` can now be parsed and will be turned into a `VarType` node.
It can not be resolved yet.
* `NodeList` now has a pretty complete set of `...First` and `...Last` methods.
Thanks stephenramthun !

Version 3.5.13
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/76?closed=1)
* The Javadoc parser has received a lot of attention.

Version 3.5.12
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/75?closed=1)
* Thanks to un0btanium for fixing the readme file!

Version 3.5.11
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/74?closed=1)
* BREAKING: `AssignExpr.Operator.AND` is now `AssignExpr.Operator.BINARY_AND`.
* BREAKING: `AssignExpr.Operator.OR` is now `AssignExpr.Operator.BINARY_OR`.
* `getPrimaryTypeName` and `getPrimaryType` give access to the type that has the same name as the file it came from.
* Enums will now get their constants aligned vertically if there are more than five.
* You can now convert between `AssignExpr.Operator` and `AssignExpr.Operator` if you like.

Version 3.5.10
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/73?closed=1)
* JavaSymbolSolver is now in the same project as JavaParser, meaning they get released together from now on.
* LexicalPreservingPrinter has had a big speed optimization.

Version 3.5.9
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/72?closed=1)
* BREAKING: the very confusing constructor `NodeList(Node)` (which sets the parent) was removed.
* To avoid using the int type for token kinds, use the new `JavaToken.Kind` enum.
It can convert to and from the int kind. 

Version 3.5.8
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/71?closed=1)
* the module name is now set to com.github.javaparser.core

Version 3.5.7
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/70?closed=1)

Version 3.5.6
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/69?closed=1)
* `toSomeType()` methods have been added for many types that give more functional access to a subtype.
* BETA: the below work on Java Symbol Solver is still ongoing.

Version 3.5.5
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/68?closed=1)
* SourceRoot is now silent by default - look at the Log class if you want to change that. 
* BETA: the below work on Java Symbol Solver is still ongoing.

Version 3.5.4
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/67?closed=1)
* BETA: the below work on Java Symbol Solver is still ongoing.

Version 3.5.3
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/66?closed=1)
* Unicode escapes (`\u1234`) are now retained in the AST,
    but they are now only allowed in comments, string and character literals, and identifiers. 
* BETA: the below work on Java Symbol Solver is still ongoing.

Version 3.5.2
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/65?closed=1)
* The pretty printer now cleans up Javadoc comments.
* BETA: the below work on Java Symbol Solver is still ongoing.

Version 3.5.1
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/64?closed=1)
* BETA: the below work on Java Symbol Solver is still ongoing.

Version 3.5.0
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/63?closed=1)
* A functional visitor API has been added. See [PR 1195](https://github.com/javaparser/javaparser/pull/1195) for now.
* Build is working again on Windows thanks to Leonardo Herrera.
* The pretty printer now has an option to order imports, also thanks to Leonardo Herrera.
* Receiver parameters are now well-supported instead of being a hack. See [issue 1194](https://github.com/javaparser/javaparser/pull/1194) for a description.
* BETA: the below work on Java Symbol Solver is still ongoing.

Version 3.4.4
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/62?closed=1)
* BETA: the below work on Java Symbol Solver is still ongoing.

Version 3.4.3
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/61?closed=1)
* BETA: we're still doing work to integrate parts of [Java Symbol Solver](https://github.com/javaparser/javasymbolsolver) to simplify its API.
* `VisitorMap` is joined by `VisitorSet` and `VisitorList`, 
for when you want to store `Node`s in collection but don't want its default equals/hascode behaviour

Version 3.4.2
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/60?closed=1)
* BETA: we're doing work to integrate parts of [Java Symbol Solver](https://github.com/javaparser/javasymbolsolver) to simplify its API.
* JDK 9 will compile JavaParser now.
* [An official sample Maven setup](https://github.com/javaparser/javaparser-maven-sample) was added.

Version 3.4.1
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/59?closed=1)
* Two visitors were added: `NoCommentEqualsVisitor` and `NoCommentHashCodeVisitor` - 
as the name implies you can use these to compare nodes without considering comments.
Thanks Ryan Beckett!
* `isSomeType()` methods have been added for many types that help avoid `instanceof`.
* `asSomeType()` methods have been added for many types that help avoid casting to that type.
* `ifSomeType()` methods have been added for many types, giving a nice functional way of doing if-is-type-then-cast-to-type-then-use.
* The `LexicalPreservingPrinter` had its API changed a little: setup and printing are now separate things,
so you don't have to drag an instance of `LexicalPreservingPrinter` through your code anymore.  
* `traverseScope` was added to all nodes with a scope, so you can travel through the scope without tripping over (non-)optionality.


Version 3.4.0
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/58?closed=1)
* BREAKING: We missed a Java 9 feature which is now on board: try with resources can now refer to a resource declared outside of the statement.
This means that the node type you get for those resources is now `Expression` instead of `VariableDeclarationExpr`.
For Java 8 and below you can simply cast it to `VariableDeclarationExpr` again.
See also the Javadoc for `TryStmt`.
* You can now inspect the AST by exporting it to XML, JSON, YAML, or a Graphviz's dot diagram, thanks to Ryan Beckett!
* `GenericVisitorWithDefaults` and `VoidVisitorWithDefaults` were added which function like empty visitors, 
but all the visit methods call a default method by default.
* Annotation support was cleaned up, adding some obscure locations where you can have annotations.
* `EnumDeclaration` regained its constructor builder methods. They were accidentally lost around 3.2.2.
* `ArrayType` now has an `origin` field which indicates in which position the array brackets were found.

Version 3.3.5
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/57?closed=1)

Version 3.3.4
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/56?closed=1)
* `SourceZip` has been added.
Use it to read source code from jars or zip files.
Thank you @ryan-beckett !
* JavaCC was upgraded to 7.0.2
* A new option for the pretty printer was added.
You can now wrap-and-column-align parameters of method calls.
Thank you @tarilabs !

Version 3.3.3
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/55?closed=1)
* Parsing a partial java file (like an expression or statement) no longer ignores trailing code.
* New memory saving option: turn off token list.

Version 3.3.2
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/54?closed=1)
* `VisitorMap` lets you override hashcode/equals for nodes when used as a key for a map.

Version 3.3.1
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/53?closed=1)
* The token list is now mutable - see methods on `JavaToken`.
This caused mild breakage - some fields have become `Optional`.

Version 3.3.0
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/52?closed=1)
* Breaking: `TryStmt::tryBlock` and `EnclosedExpr::inner` were optional for no good reason. Now they are required.
* You can now ask a `JavaToken` for its category, which is useful for examining the token list or doing syntax highlighting or so.
* `enum` and `strictfp` can now be used as identifiers on lower Java versions.

Version 3.2.12
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/51?closed=1)

Version 3.2.11
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/50?closed=1)
* We're up to date with the latest Java 9 module system again.

Version 3.2.10
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/49?closed=1)
* `Node.replace(old, new)` was added, including property-specific `X.replaceY(newY)` methods

Version 3.2.9
------------------
Scrapped due to release problem.

Version 3.2.8
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/48?closed=1)
* Added `isInnerClass()` that checks if a `ClassOrInterfaceDeclaration` is an inner class (note: this is different from a nested class!)
* @ryan-beckett contributed a huge [Eclipse setup guide](https://github.com/javaparser/javaparser/wiki/Eclipse-Project-Setup-Guide)

Version 3.2.7
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/47?closed=1)
* We now recover from some parse errors! [Here is an article](https://matozoid.github.io/2017/06/11/parse-error-recovery.html)

Version 3.2.6
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/46?closed=1)
* `EmptyMemberDeclaration` is gone! 
It was deprecated for a while because it was in the AST, but doesn't have any meaning in a Java program. 
`EmptyStmt` was also deprecated, but that has been reverted. 
This node *does* have meaning.

Version 3.2.5
------------------
[issues resolved](https://github.com/javaparser/javaparser/milestone/45?closed=1)
* `NodeWithCondition` was added on all nodes containing a condition.
* Lots of work on improving lexical preservation.
* If a file was parsed from a file system, you can now get path information etc. from `CompilationUnit`
* API BREAKING: every node now points to its start and end token.
Some of the API has started returning `TokenRange` instead of `Range` - you can call `toRange` to get the old object type.
We may still change the naming of some of this code in the following month.

Version 3.2.4
------------------
New style changelog, no more issue numbers, but a link: 
[issues resolved](https://github.com/javaparser/javaparser/milestone/44?closed=1)
and any notable changes:
* the new method `Node.removeForced()` by removing it, or removing the first parent that is optional.
This is different from `Node.remove()`, `remove()` only tries to remove the node from the parent and fails if it can't.
* `FieldAccessExpr.scope` is now a required property.
You might find some `get()`s in your code that are no longer necessary.
* `ReferenceType` no longer has a type parameter, so every `ReferenceType<?>` can be replaced by `ReferenceType` now.

Version 3.2.3
------------------
* 907 906 905 903 911 910 909 908 smaller improvements and fixes

Version 3.2.2
------------------
Beta: `TreeStructureVisitor`.

* 770 902 904 901 smaller improvements and fixes

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
QuickJavaParser.getConfiguration().setValidator(new Java9Validator());
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
