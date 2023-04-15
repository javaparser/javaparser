/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.List;

import static com.github.javaparser.Providers.provider;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

public class Issue2044Test {

    @Test
    public void issue2044_typeVariableExtendsObject() {

        String x = "public class X <K extends Object> {\n" +
                "    private int getPartition(final K key) {\n" +
                "        int x = (new Object()).hashCode();\n" +
                "        return key.hashCode() / getHashes().length;\n" +
                "    }\n" +
                "}";

        doTestSimple(x);
    }


    @Test
    public void issue2044_simpleTypeVariable() {
        String x = "public class X <K> {\n" +
                "    private int getPartition(final K key) {\n" +
                "        int x = (new Object()).hashCode();\n" +
                "        return key.hashCode() / getHashes().length;\n" +
                "    }\n" +
                "}";

        doTestSimple(x);
    }

    private void doTestSimple(String x) {
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver());
        ParserConfiguration configuration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        JavaParser javaParser = new JavaParser(configuration);

        ParseResult<CompilationUnit> result = javaParser.parse(ParseStart.COMPILATION_UNIT, provider(x));
        assumeTrue(result.isSuccessful());

        result.ifSuccessful(compilationUnit -> {
            List<MethodCallExpr> methodCallExprs = compilationUnit.findAll(MethodCallExpr.class);
            assertEquals(3, methodCallExprs.size());

            MethodCallExpr methodCallExpr = methodCallExprs.get(1);

            //// Exception-triggering method calls

            // throws RuntimeException - stack trace below
            methodCallExpr.calculateResolvedType();
/*
java.lang.RuntimeException: Method 'hashCode' cannot be resolved in context key.hashCode() (line: 3) MethodCallExprContext{wrapped=key.hashCode()}. Parameter types: []

	at com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade.solveMethodAsUsage(JavaParserFacade.java:586)
	at com.github.javaparser.symbolsolver.javaparsermodel.TypeExtractor.visit(TypeExtractor.java:267)
	at com.github.javaparser.symbolsolver.javaparsermodel.TypeExtractor.visit(TypeExtractor.java:44)
	at com.github.javaparser.ast.expr.MethodCallExpr.accept(MethodCallExpr.java:115)
	at com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade.getTypeConcrete(JavaParserFacade.java:447)
	at com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade.getType(JavaParserFacade.java:310)
	at com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade.getType(JavaParserFacade.java:292)
	at com.github.javaparser.symbolsolver.JavaSymbolSolver.calculateType(JavaSymbolSolver.java:250)
	at com.github.javaparser.ast.expr.Expression.calculateResolvedType(Expression.java:564)
	at com.github.javaparser.symbolsolver.Issue2044.lambda$null$0(Issue2044.java:81)
	at java.util.ArrayList.forEach(ArrayList.java:1249)
	at com.github.javaparser.symbolsolver.Issue2044.lambda$issue2044$1(Issue2044.java:49)
*/


            // throws UnsolvedSymbolException - stack trace below
            methodCallExpr.resolve();
/*
Unsolved symbol : We are unable to find the method declaration corresponding to key.hashCode()
UnsolvedSymbolException{context='null', name='We are unable to find the method declaration corresponding to key.hashCode()', cause='null'}

	at com.github.javaparser.symbolsolver.JavaSymbolSolver.resolveDeclaration(JavaSymbolSolver.java:146)
	at com.github.javaparser.ast.expr.MethodCallExpr.resolve(MethodCallExpr.java:313)
	at com.github.javaparser.symbolsolver.Issue2044.lambda$null$0(Issue2044.java:101)
*/

        });
    }

    private void doTest(String x) {

        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver());
        ParserConfiguration configuration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        JavaParser javaParser = new JavaParser(configuration);
        ParseResult<CompilationUnit> result = javaParser.parse(ParseStart.COMPILATION_UNIT, provider(x));

        result.ifSuccessful(compilationUnit -> {
            final List<MethodDeclaration> methodDeclarations = compilationUnit.findAll(MethodDeclaration.class);

            methodDeclarations.forEach(methodDeclaration -> {

                // Method declaration
                ResolvedMethodDeclaration resolvedMethodDeclaration = methodDeclaration.resolve();
                String resolvedReturnType = resolvedMethodDeclaration.getReturnType().describe();
                assertEquals("int", resolvedReturnType);

                // Parameters
                NodeList<Parameter> parameters = methodDeclaration.getParameters();
                assertEquals(1, parameters.size());

                Parameter parameter = parameters.get(0);
                assertEquals("K", parameter.getType().asString());
                assertEquals("key", parameter.getName().asString());

                assertEquals("K", parameter.resolve().getType().describe());
                assertEquals("K", parameter.resolve().describeType());


                // Method calls inside declaration
                List<MethodCallExpr> methodCalls = methodDeclaration.findAll(MethodCallExpr.class);
                assertEquals(3, methodCalls.size());

                // (new Object()).hashCode()
                final MethodCallExpr object_hashCode = methodCalls.get(0);
                assertTrue(object_hashCode.hasScope());
                Expression object_hashCode_scope = object_hashCode.getScope().get();
                assertEquals("java.lang.Object", object_hashCode_scope.calculateResolvedType().describe());

                assertEquals("int", object_hashCode.resolve().getReturnType().describe());
                assertEquals("int", object_hashCode.calculateResolvedType().describe());

                // key.hashCode()
                final MethodCallExpr key_hashCode = methodCalls.get(1);
                assertTrue(key_hashCode.hasScope());
                Expression key_hashCode_scope = key_hashCode.getScope().get();
                assertEquals("K", key_hashCode_scope.calculateResolvedType().describe());

                // These shouldn't pass...
//                assertThrows(RuntimeException.class, key_hashCode::calculateResolvedType);
//                assertThrows(UnsolvedSymbolException.class, key_hashCode::resolve);


                // throws RuntimeException - stack trace below
                ResolvedType key_hashCode_resolvedType = ((MethodCallExpr) key_hashCode).calculateResolvedType();
                /*
java.lang.RuntimeException: Method 'hashCode' cannot be resolved in context key.hashCode() (line: 3) MethodCallExprContext{wrapped=key.hashCode()}. Parameter types: []

	at com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade.solveMethodAsUsage(JavaParserFacade.java:586)
	at com.github.javaparser.symbolsolver.javaparsermodel.TypeExtractor.visit(TypeExtractor.java:267)
	at com.github.javaparser.symbolsolver.javaparsermodel.TypeExtractor.visit(TypeExtractor.java:44)
	at com.github.javaparser.ast.expr.MethodCallExpr.accept(MethodCallExpr.java:115)
	at com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade.getTypeConcrete(JavaParserFacade.java:447)
	at com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade.getType(JavaParserFacade.java:310)
	at com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade.getType(JavaParserFacade.java:292)
	at com.github.javaparser.symbolsolver.JavaSymbolSolver.calculateType(JavaSymbolSolver.java:250)
	at com.github.javaparser.ast.expr.Expression.calculateResolvedType(Expression.java:564)
	at com.github.javaparser.symbolsolver.Issue2044.lambda$null$0(Issue2044.java:81)
	at java.util.ArrayList.forEach(ArrayList.java:1249)
	at com.github.javaparser.symbolsolver.Issue2044.lambda$issue2044$1(Issue2044.java:49)
                 */


                // throws UnsolvedSymbolException - stack trace below
                ResolvedMethodDeclaration key_hashCode_resolved = ((MethodCallExpr) key_hashCode).resolve();
                /*
Unsolved symbol : We are unable to find the method declaration corresponding to key.hashCode()
UnsolvedSymbolException{context='null', name='We are unable to find the method declaration corresponding to key.hashCode()', cause='null'}

	at com.github.javaparser.symbolsolver.JavaSymbolSolver.resolveDeclaration(JavaSymbolSolver.java:146)
	at com.github.javaparser.ast.expr.MethodCallExpr.resolve(MethodCallExpr.java:313)
	at com.github.javaparser.symbolsolver.Issue2044.lambda$null$0(Issue2044.java:101)
                 */


                ResolvedType key_hashCode_resolvedReturnType = key_hashCode_resolved.getReturnType();
                String key_hashCode_resolvedReturnTypeString = key_hashCode_resolvedReturnType.describe();


                assertEquals("int", key_hashCode.resolve().getReturnType().describe());


            });
        });
    }

}
