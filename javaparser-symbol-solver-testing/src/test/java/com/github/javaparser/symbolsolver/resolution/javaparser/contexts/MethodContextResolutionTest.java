/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.resolution.javaparser.contexts;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.StaticJavaParser.parseBlock;
import static com.github.javaparser.StaticJavaParser.parseStatement;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.ConstructorContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.MethodContext;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.MemoryTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.time.Duration;
import java.util.List;
import java.util.Locale;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

/**
 * @author Malte Langkabel
 */
class MethodContextResolutionTest extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @BeforeEach
    void setup() {
        typeSolver = new ReflectionTypeSolver();
    }

    @Test
    void solveTypeRefToLocalClass() {
        CompilationUnit cu = parseSample("MethodWithTypes");
        ClassOrInterfaceDeclaration cd = Navigator.demandClass(cu, "Main");
        MethodDeclaration md = Navigator.demandMethod(cd, "methodWithLocalTypes");
        Context context = new MethodContext(md, new MemoryTypeSolver());

        SymbolReference<ResolvedTypeDeclaration> ref = context.solveType("LocalClass");
        assertEquals(true, ref.isSolved());
    }

    @Test
    void solveTypeRefToLocalClassFindsTheSameDeclarationEveryTime() {
        MethodDeclaration md = methodWithLocalTypes();
        ClassOrInterfaceDeclaration localClass =
                md.findFirst(ClassOrInterfaceDeclaration.class).get();
        for (int lookup = 0; lookup < 2; lookup++) {
            SymbolReference<ResolvedTypeDeclaration> ref = new MethodContext(md, typeSolver).solveType("LocalClass");
            assertSame(localClass, ref.getCorrespondingDeclaration().toAst().get());
        }
    }

    /**
     * A clone carries the data of the node it was cloned from, including the local types found in it. The clone
     * must still resolve to its own local class, not to the original's.
     */
    @Test
    void solveTypeRefToLocalClassInAClonedMethod() {
        MethodDeclaration md = methodWithLocalTypes();
        new MethodContext(md, typeSolver).solveType("LocalClass");
        MethodDeclaration clone = md.clone();
        ClassOrInterfaceDeclaration clonedLocalClass =
                clone.findFirst(ClassOrInterfaceDeclaration.class).get();

        SymbolReference<ResolvedTypeDeclaration> ref = new MethodContext(clone, typeSolver).solveType("LocalClass");
        assertSame(clonedLocalClass, ref.getCorrespondingDeclaration().toAst().get());
    }

    /**
     * Use context lookups here so a previously resolved type node cannot hide a stale list of local classes.
     */
    @Test
    void solveTypeFindsLocalClassAddedAfterAnUnsuccessfulLookup() {
        MethodDeclaration md = methodWithLocalTypes();
        Context context = new MethodContext(md, typeSolver);
        assertFalse(context.solveType("Added").isSolved());

        md.getBody().get().addStatement("class Added {}");

        assertResolvesTo(context, md.findAll(ClassOrInterfaceDeclaration.class).get(1));
        assertResolvesTo(
                new MethodContext(md, typeSolver),
                md.findAll(ClassOrInterfaceDeclaration.class).get(1));
    }

    @Test
    void solveTypeDoesNotFindRemovedLocalClass() {
        MethodDeclaration md = methodWithLocalTypes();
        Context context = new MethodContext(md, typeSolver);
        assertTrue(context.solveType("LocalClass").isSolved());

        md.findFirst(LocalClassDeclarationStmt.class).get().remove();

        assertFalse(context.solveType("LocalClass").isSolved());
    }

    @Test
    void solveTypeFindsReplacementLocalClassWithTheSameName() {
        MethodDeclaration md = methodWithLocalTypes();
        Context context = new MethodContext(md, typeSolver);
        assertTrue(context.solveType("LocalClass").isSolved());
        LocalClassDeclarationStmt replacement =
                parseStatement("class LocalClass {}").asLocalClassDeclarationStmt();

        md.findFirst(LocalClassDeclarationStmt.class).get().replace(replacement);

        assertResolvesTo(context, replacement.getClassDeclaration());
    }

    @Test
    void solveTypeFindsClassesInAReplacementBodyAndItsLaterEdits() {
        MethodDeclaration md = methodWithLocalTypes();
        Context context = new MethodContext(md, typeSolver);
        assertTrue(context.solveType("LocalClass").isSolved());
        BlockStmt body = parseBlock("{ { class Replacement {} } }");
        md.setBody(body);

        assertFalse(context.solveType("LocalClass").isSolved());
        assertResolvesTo(
                context, body.findFirst(ClassOrInterfaceDeclaration.class).get());
        body.getStatement(0).asBlockStmt().addStatement("class Added {}");
        assertResolvesTo(
                context, body.findAll(ClassOrInterfaceDeclaration.class).get(1));
    }

    @Test
    void solveTypeObservesChildrenOfAReplacementStatementList() {
        MethodDeclaration md = methodWithLocalTypes();
        Context context = new MethodContext(md, typeSolver);
        assertTrue(context.solveType("LocalClass").isSolved());
        BlockStmt nested = parseBlock("{ class Replacement {} }");
        md.getBody().get().setStatements(new NodeList<>(nested));

        assertResolvesTo(
                context, nested.findFirst(ClassOrInterfaceDeclaration.class).get());
        nested.addStatement("class Added {}");
        assertResolvesTo(
                context, nested.findAll(ClassOrInterfaceDeclaration.class).get(1));
    }

    @Test
    void solveTypeUpdatesBothMethodsWhenALocalClassIsMoved() {
        CompilationUnit cu = parse("class Example { void source() { class Local {} } void target() {} }");
        List<MethodDeclaration> methods = cu.findAll(MethodDeclaration.class);
        Context source = new MethodContext(methods.get(0), typeSolver);
        Context target = new MethodContext(methods.get(1), typeSolver);
        LocalClassDeclarationStmt local =
                cu.findFirst(LocalClassDeclarationStmt.class).get();
        assertResolvesTo(source, local.getClassDeclaration());
        assertFalse(target.solveType("Local").isSolved());

        assertTrue(local.remove());
        methods.get(1).getBody().get().addStatement(local);

        assertFalse(source.solveType("Local").isSolved());
        assertResolvesTo(target, local.getClassDeclaration());
    }

    @Test
    void solveTypeUpdatesConstructorLocalClassesAfterEdits() {
        CompilationUnit cu = parse("class Example { Example() { class Local {} } }");
        ConstructorDeclaration constructor =
                cu.findFirst(ConstructorDeclaration.class).get();
        Context context = new ConstructorContext(constructor, typeSolver);
        assertTrue(context.solveType("Local").isSolved());

        constructor.setBody(parseBlock("{ class Replacement {} }"));

        assertFalse(context.solveType("Local").isSolved());
        assertResolvesTo(
                context,
                constructor.findFirst(ClassOrInterfaceDeclaration.class).get());
        constructor.getBody().addStatement("class Added {}");
        assertResolvesTo(
                context, constructor.findAll(ClassOrInterfaceDeclaration.class).get(1));
    }

    @Test
    void solveTypeKeepsCloneAndOriginalEditsSeparate() {
        MethodDeclaration md = methodWithLocalTypes();
        Context original = new MethodContext(md, typeSolver);
        assertTrue(original.solveType("LocalClass").isSolved());
        MethodDeclaration clone = md.clone();
        Context cloned = new MethodContext(clone, typeSolver);
        assertResolvesTo(
                cloned, clone.findFirst(ClassOrInterfaceDeclaration.class).get());

        clone.getBody().get().addStatement("class CloneOnly {}");
        md.getBody().get().addStatement("class OriginalOnly {}");

        assertResolvesTo(
                cloned, clone.findAll(ClassOrInterfaceDeclaration.class).get(1));
        assertResolvesTo(original, md.findAll(ClassOrInterfaceDeclaration.class).get(1));
        assertFalse(original.solveType("CloneOnly").isSolved());
        assertFalse(cloned.solveType("OriginalOnly").isSolved());
    }

    @Test
    void solveTypeMatchesAFreshTraversalAfterRepeatedEdits() {
        MethodDeclaration md = methodWithLocalTypes();
        Context context = new MethodContext(md, typeSolver);
        assertTrue(context.solveType("LocalClass").isSolved());

        for (int edit = 0; edit < 25; edit++) {
            BlockStmt nested = parseBlock("{ class First {} class Second {} }");
            md.getBody().get().setStatements(new NodeList<>(nested));
            // Make another edit before looking up a type, while the cache is still cleared.
            nested.addStatement("class Third {}");
            assertFalse(context.solveType("LocalClass").isSolved());
            for (ClassOrInterfaceDeclaration declaration : md.findAll(ClassOrInterfaceDeclaration.class)) {
                assertResolvesTo(context, declaration);
            }

            nested.getStatement(0)
                    .asLocalClassDeclarationStmt()
                    .getClassDeclaration()
                    .setName("Renamed");
            assertFalse(context.solveType("First").isSolved());
            for (ClassOrInterfaceDeclaration declaration : md.findAll(ClassOrInterfaceDeclaration.class)) {
                assertResolvesTo(context, declaration);
            }
            nested.getStatements().clear();
            assertFalse(context.solveType("Renamed").isSolved());
            assertFalse(context.solveType("Second").isSolved());
            assertFalse(context.solveType("Third").isSolved());
        }
    }

    private void assertResolvesTo(Context context, ClassOrInterfaceDeclaration declaration) {
        assertSame(
                declaration,
                context.solveType(declaration.getNameAsString())
                        .getCorrespondingDeclaration()
                        .toAst()
                        .get());
    }

    /**
     * Every type name looked up inside a method is checked against the types declared in it. The method is only
     * walked again after an edit, rather than for every lookup. Before, 10,000 declarations took about 30 seconds.
     */
    @ParameterizedTest
    @ValueSource(ints = {1_000, 5_000, 10_000})
    void resolvingTypesInALargeMethodStaysFast(int size) {
        StringBuilder source = new StringBuilder("class Big {\n    void method() {\n");
        for (int i = 0; i < size; i++) {
            source.append(String.format(Locale.ROOT, "        String s%1$d = \"%1$d\";\n", i));
        }
        source.append("    }\n}\n");
        ParserConfiguration configuration =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        List<VariableDeclarator> variables = new JavaParser(configuration)
                .parse(source.toString())
                .getResult()
                .get()
                .findAll(VariableDeclarator.class);

        assertTimeoutPreemptively(Duration.ofSeconds(10), () -> {
            for (VariableDeclarator variable : variables) {
                assertEquals("java.lang.String", variable.getType().resolve().describe());
            }
        });
    }

    private MethodDeclaration methodWithLocalTypes() {
        CompilationUnit cu = parseSample("MethodWithTypes");
        return Navigator.demandMethod(Navigator.demandClass(cu, "Main"), "methodWithLocalTypes");
    }
}
