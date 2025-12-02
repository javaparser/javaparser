# JavaParser Developer Guide (AGENTS.md)

This document provides essential information for working effectively in the JavaParser codebase. JavaParser is a Java library for parsing Java source code and creating Abstract Syntax Trees (ASTs).

## Project Overview

JavaParser is a multi-module Maven project that provides:
- **javaparser-core**: Core parsing functionality and AST representation
- **javaparser-symbol-solver**: Symbol resolution capabilities
- **javaparser-core-testing**: JUnit tests for core functionality
- **javaparser-core-testing-bdd**: JBehave BDD tests
- **javaparser-core-generators**: Code generators for visitor patterns
- **javaparser-core-metamodel-generator**: AST metamodel generator
- **javaparser-core-serialization**: JSON serialization support

## Essential Commands

### Building the Project

```bash
# Full clean build with tests
./mvnw clean verify

# Build without tests (faster)
./mvnw clean install -DskipTests

# Run specific module tests
./mvnw test -pl javaparser-core-testing
./mvnw test -pl javaparser-symbol-solver-testing

# Full test suite including slow tests (as used in CI)
./mvnw -B --errors clean test --activate-profiles AlsoSlowTests
```

### Code Generation and Formatting

JavaParser uses extensive code generation. **Always run these before committing:**

```bash
# Complete workflow (recommended)
./run_core_metamodel_generator.sh && ./run_core_generators.sh

# If metamodel changes are needed (rare)
./run_core_metamodel_generator.sh

# If only regenerating visitors/patterns (common)
./run_core_generators.sh

# Manual formatting only (if you can't run shell scripts)
./mvnw spotless:apply
```

The generator scripts:
1. Build the project
2. Run generators (metamodel or visitors)
3. Rebuild with generated code
4. Apply spotless formatting (`run_core_generators.sh` only)

### Code Quality Checks

```bash
# Checkstyle validation
./mvnw checkstyle:check

# Formatting validation (fails if code not formatted)
./mvnw spotless:check

# Run both checks (as done in CI)
./mvnw checkstyle:check
./run_core_metamodel_generator.sh
./run_core_generators.sh
git diff --exit-code  # Ensures no uncommitted changes
```

## Code Organization

### Module Structure

- **javaparser-core/src/main/java/com/github/javaparser/**: Core parsing logic
  - `ast/`: AST node classes (organized by package: `body`, `expr`, `stmt`, `type`, etc.)
  - `printer/`: Code printers (pretty printers, XML, JSON, YAML)
  - `visitor/`: Visitor pattern implementations
  - `metamodel/`: Generated metamodel for AST nodes
  - `resolution/`: Basic resolution support
  - `JavaParser.java`: Main entry point for parsing
  - `StaticJavaParser.java`: Static convenience methods

- **javaparser-symbol-solver-core/**: Advanced symbol resolution
  - Connects AST nodes to their declarations
  - Handles generics, method resolution, type inference

- **javaparser-core-testing/**: JUnit 5 tests following standard patterns
- **javaparser-core-testing-bdd/**: JBehave BDD tests with `.story` files

### Generated Code

Several packages contain generated code that should not be edited manually:

- `com.github.javaparser.ast.visitor.*` visitor classes (except base interfaces)
- `com.github.javaparser.metamodel.*` metamodel classes
- `GeneratedJavaParser` and related parser classes
- `*Constants` classes with token definitions

**Rule: If a class has "Generated" in its name or package, don't edit it manually.**

## Code Style and Conventions

### Formatting

- **Line length**: 120 characters (soft limit)
- **Indentation**: 4 spaces (no tabs)
- **Formatting**: Palantir Java Format (applied via Spotless)
- **Import order**: Custom (see checkstyle config)
  1. Third-party packages
  2. javax.* packages
  3. java.* packages
  4. Static imports
- **Annotations**: Type and method annotations on separate lines

### Licensing Headers

Every source file must include the LGPL/Apache dual-license header:

```java
/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public Package for more details.
 */
```

### API Design Principles

- **Immutability**: AST nodes are immutable after creation
- **Factory methods**: Use static factory methods (e.g., `parse()`, `of()`)
- **Optional**: Return `Optional<T>` instead of null
- **Visitor pattern**: Extend functionality via visitors, not inheritance
- **Fluent APIs**: Builder patterns and method chaining where appropriate

## Testing

### Test Structure

- Unit tests: `javaparser-core-testing/src/test/java/`
- BDD tests: `javaparser-core-testing-bdd/src/test/java/`
- Test resources: `src/test/resources/`
- Each test class corresponds to a source class being tested

### Running Tests

```bash
# Run all tests
./mvnw test

# Run only quick tests (excludes slow tests)
./mvnw test -P!AlsoSlowTests

# Run specific test class
./mvnw test -Dtest=JavaParserTest

# Run specific test method
./mvnw test -Dtest=JavaParserTest#rangeOfAnnotationMemberDeclarationIsCorrect
```

### Test Patterns

- Use JUnit 5 (not JUnit 4)
- Use descriptive test method names (`testWhat_behavior_expected`)
- Test both positive and negative cases
- Test edge cases and boundary conditions
- For parser tests, test various language levels

### BDD Tests

BDD tests use JBehave with `.story` files:
- Stories located in `src/test/resources/`
- Steps implemented in Java classes
- State shared via `Map<String, Object>`

## Common Development Scenarios

### Adding a New AST Node

1. Add the node class to appropriate package under `javaparser-core/src/main/java/com/github/javaparser/ast/`
2. Add proper annotations and Javadoc
3. Run `./run_core_metamodel_generator.sh`
4. Run `./run_core_generators.sh`
5. Add tests for the new node
6. Format and commit

**Important**: Refer to the wiki guide "A Detailed Guide to Adding New Nodes and Fields"

### Modifying Existing AST Nodes

1. Never modify generated code directly
2. If adding fields to AST nodes, follow the guide mentioned above
3. Always regenerate code after structural changes
4. Update affected tests

### Fixing Bugs

1. Write a test that reproduces the bug first
2. Fix the bug
3. Ensure all tests pass
4. Run code generators and formatting
5. Commit with descriptive message referencing the issue (#123)

### Working with Symbol Resolution

- Symbol resolution is in the `javaparser-symbol-solver-core` module
- Resolution logic is in contexts and declarations
- Test with complex generics, nested classes, and imports

## Continuous Integration

### GitHub Actions Workflows

1. **maven_tests.yml**: Runs on Ubuntu, macOS, Windows with JDK 8-18
   - Runs full test suite with slow tests
   - Uploads coverage to CodeCov

2. **formatting_check.yml**: Validates code quality
   - Runs checkstyle
   - Runs code generators and ensures no diff

### Automated Checks

- **Checkstyle**: Validates code style (warnings)
- **Spotless**: Enforces formatting (strict)
- **Tests**: Must pass on multiple OS and JDK versions
- **Diff check**: Ensures all generated code is committed

## Release Process

Releases use Maven release plugin with profiles:

```bash
# Prepare release (updates versions, tags)
./run_release_prepare.sh

# Or non-interactive
./run_release_prepare_non-interactive.sh

# Perform release (builds and deploys)
./run_release_perform.sh
```

Release builds:
- Update readme with version
- Generate sources and javadoc JARs
- Sign artifacts with GPG
- Deploy to Maven Central

## Architecture Notes

### Parsing Flow

1. `JavaParser` or `StaticJavaParser` receives input
2. Input converted to `Provider` (character stream)
3. `GeneratedJavaParser` (JavaCC-generated) performs parsing
4. AST nodes created and returned
5. Comments inserted via `CommentsInserter`

### AST Design

- All nodes extend `Node` base class
- Nodes immutable after creation (use `clone()` or visitors to modify)
- `NodeList` for ordered collections of nodes
- Visitors for traversing and transforming trees
- Lexical preservation for minimal diffs when modifying code

### Symbol Resolution Architecture

- `TypeSolver` implementations resolve symbols from various sources
- `JavaParserFacade` provides high-level resolution API
- Context objects handle scope-aware resolution
- Declaration classes represent resolved symbols

## Gotchas and Non-Obvious Behaviors

### Code Generation Dependencies

- Generators depend on compiled core classes
- Always run generators after modifying AST structure
- Generated code overwrites manual changes

### Parser Configuration

- Language levels affect which Java features are parsed
- Default is typically `CURRENT` (latest stable Java)
- `BLEEDING_EDGE` enables preview features

### Comment Handling

- Comments are stored separately and linked to AST nodes
- `CommentsInserter` runs after parsing to attach comments
- Range/position calculations exclude comments by default

### Lexical Preservation

- Enable with `ParserConfiguration.setLexicalPreservationEnabled(true)`
- Stores all whitespace and tokens for accurate output
- Required for minimal diffs when regenerating code

### Line Endings

- Tests run on multiple OS with different line endings
- Use `LineSeparator` enum for cross-platform compatibility
- Be careful with string comparisons in tests

## Useful Resources

- **Wiki**: https://github.com/javaparser/javaparser/wiki
- **Issues**: https://github.com/javaparser/javaparser/issues
- **JavaDoc**: Build with `./mvnw javadoc:javadoc`
- **Contributing Guide**: See CONTRIBUTING.md
- **Coding Guidelines**: On wiki (referenced in CONTRIBUTING.md)

## Quick Checklist for Pull Requests

Before submitting a PR:

- [ ] Tests added/updated for changes
- [ ] Code generators run (`./run_core_metamodel_generator.sh && ./run_core_generators.sh`)
- [ ] Spotless formatting applied (`./mvnw spotless:apply`)
- [ ] Checkstyle passes (`./mvnw checkstyle:check`)
- [ ] All tests pass (`./mvnw clean verify`)
- [ ] License headers present on all files
- [ ] Related issues referenced (#123)
- [ ] No generated code manually edited
