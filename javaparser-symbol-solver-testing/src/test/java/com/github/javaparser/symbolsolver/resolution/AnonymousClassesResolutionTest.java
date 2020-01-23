/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.OpenIssueTest;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.DefaultConstructorDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserMethodDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.MemoryTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

class AnonymousClassesResolutionTest extends AbstractResolutionTest {

    @BeforeAll
    static void configureSymbolSolver() {
        // configure symbol solver before parsing
        CombinedTypeSolver typeSolver = new CombinedTypeSolver();
        typeSolver.add(new ReflectionTypeSolver());
        MemoryTypeSolver memoryTypeSolver = new MemoryTypeSolver();

        ResolvedReferenceTypeDeclaration cd = mock(ResolvedReferenceTypeDeclaration.class);
        when(cd.asReferenceType()).thenReturn(cd);
        memoryTypeSolver.addDeclaration("org.springframework.transaction.support.TransactionCallbackWithoutResult",
                cd);

        typeSolver.add(memoryTypeSolver);
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
    }

    @AfterAll
    static void unConfigureSymbolSolver() {
        // unconfigure symbol solver so as not to potentially disturb tests in other classes
        StaticJavaParser.getConfiguration().setSymbolResolver(null);
    }

    // See #1703
    @Test
    void solveAnonymousClassMethodClass() {
        CompilationUnit cu = parseSample("AnonymousClassMethodClass");

        cu.accept(new VoidVisitorAdapter<Object>() {


            @Override
            public void visit(MethodCallExpr m, Object arg) {
                m.getScope().get().asNameExpr().resolve();
            }
        }, null);

    }


    @OpenIssueTest(issueNumber = {1599, 2441})
    @Test
    public void testAnonymousInterfaceImplementationConstructorResolution() {
        CompilationUnit cu = parseSample("AnonymousClasses");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "AnonymousClasses");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testInterFoo");
        ObjectCreationExpr creationExpr = Navigator.findNodeOfGivenClass(method, ObjectCreationExpr.class);

        SymbolReference<? extends ResolvedConstructorDeclaration> ref = JavaParserFacade.get(new ReflectionTypeSolver()).solve(creationExpr);

        assertTrue(ref.isSolved());

        // How exactly should this situation be handled? A default constructor is called here - but what should the
        // wrapped node be? The interface declaration? There should probably be additional assertions here.
    }

    @OpenIssueTest(issueNumber = {1599, 2441})
    @Test
    public void testAnonymousInterfaceImplementationMethodResolution() {
        CompilationUnit cu = parseSample("AnonymousClasses");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "AnonymousClasses");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testInterFoo");
        ObjectCreationExpr creationExpr = Navigator.findNodeOfGivenClass(method, ObjectCreationExpr.class);

        MethodCallExpr methodCallExpr = (MethodCallExpr) method.getBody().get().getStatement(1).getChildNodes().get(0);

        SymbolReference<? extends ResolvedMethodDeclaration> ref = JavaParserFacade.get(new ReflectionTypeSolver()).solve(methodCallExpr);
        JavaParserMethodDeclaration mdec = (JavaParserMethodDeclaration) ref.getCorrespondingDeclaration();

        assertTrue(ref.isSolved());
        assertFalse(mdec.isAbstract());
        assertEquals(mdec.getWrappedNode().asMethodDeclaration().getParentNode().get(), creationExpr);
    }

    @OpenIssueTest(issueNumber = {1599, 2441})
    @Test
    public void testAnonymousClassImplementationConstructorResolution() {
        CompilationUnit cu = parseSample("AnonymousClasses");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "AnonymousClasses");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testClassFoo");
        ObjectCreationExpr creationExpr = Navigator.findNodeOfGivenClass(method, ObjectCreationExpr.class);

        SymbolReference<? extends ResolvedConstructorDeclaration> ref = JavaParserFacade.get(new ReflectionTypeSolver()).solve(creationExpr);

        assertTrue(ref.isSolved());
        assertTrue(ref.getCorrespondingDeclaration() instanceof DefaultConstructorDeclaration);
        assertEquals(((JavaParserClassDeclaration)
                        ref.getCorrespondingDeclaration()
                                .declaringType())
                        .getWrappedNode(),
                clazz.findFirst(ClassOrInterfaceDeclaration.class, c -> c.getNameAsString().equals("ClassFoo")).get());
    }

    @OpenIssueTest(issueNumber = {1599, 2441})
    @Test
    public void testAnonymousClassImplementationMethodResolution() {
        CompilationUnit cu = parseSample("AnonymousClasses");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "AnonymousClasses");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testClassFoo");
        ObjectCreationExpr creationExpr = Navigator.findNodeOfGivenClass(method, ObjectCreationExpr.class);
        ClassOrInterfaceDeclaration classFooDec =
                clazz.findFirst(ClassOrInterfaceDeclaration.class, c -> c.getNameAsString().equals("ClassFoo")).get();

        MethodCallExpr absFooCall = method.findFirst(MethodCallExpr.class, mce -> mce.getNameAsString().equals("foo")).get();
        MethodCallExpr implFooCall = method.findFirst(MethodCallExpr.class, mce -> mce.getNameAsString().equals("implFoo")).get();

        SymbolReference<? extends ResolvedMethodDeclaration> absRef = JavaParserFacade.get(new ReflectionTypeSolver()).solve(absFooCall);
        SymbolReference<? extends ResolvedMethodDeclaration> implRef = JavaParserFacade.get(new ReflectionTypeSolver()).solve(implFooCall);
        JavaParserMethodDeclaration absDec = (JavaParserMethodDeclaration) absRef.getCorrespondingDeclaration();
        JavaParserMethodDeclaration implDec = (JavaParserMethodDeclaration) implRef.getCorrespondingDeclaration();

        assertTrue(absRef.isSolved());
        assertTrue(implRef.isSolved());
        assertFalse(absDec.isAbstract());
        assertFalse(implDec.isAbstract());
        assertEquals(absDec.getWrappedNode().getParentNode().get(), creationExpr);
        assertEquals(implDec.getWrappedNode().getParentNode().get(), classFooDec);
    }

}
