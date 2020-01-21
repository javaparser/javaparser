/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static com.github.javaparser.Providers.provider;
import static org.junit.jupiter.api.Assumptions.assumeTrue;


/**
 * "SymbolResolver on MethodCallExpr fails if method parameter is of kind Class&lt;? extends y&gt;"
 *
 * @see <a href="https://github.com/javaparser/javaparser/issues/2484">https://github.com/javaparser/javaparser/issues/2484</a>
 */
public class Issue2484Test extends AbstractSymbolResolutionTest {

    private JavaParser javaParser;

    private final String x = "public class MyClass {\n" +
        "    private Ibaz m_something;\n" +
        "    \n" +
        "    public class Ibaz {\n" +
        "    }\n" +
        "    \n" +
        "    public void foo(Class<? extends Ibaz> clazz) {\n" +
        "    }\n" +
        "    \n" +
        "    protected void bar() {\n" +
        "        foo(null); // this works\n" +
        "        foo(Ibaz.class); // this works\n" +
        "        \n" +
        "        Class c1 = m_something.getClass();\n" +
        "        foo(c1); // this works\n" +
        "        \n" +
        "        Class<Ibaz> c2 = m_something.getClass();\n" +
        "        foo(c2); // this works\n" +
        "        \n" +
        "        Class<> c3 = m_something.getClass();\n" +
        "        foo(c3); // this works\n" +
        "        \n" +
//        "        Class<Object> c4 = m_something.getClass();\n" +
//        "        foo(c4); // this doesn't work\n" +
        "        \n" +
        "        Object c5 = m_something.getClass();\n" +
        "        foo(c5); // this works\n" +
        "        \n" +
        "        foo(m_something.getClass()); // this doesn't work\n" +
        "    }\n" +
        "}";

    @BeforeEach
    void setUp() {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        ParserConfiguration configuration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));

        javaParser = new JavaParser(configuration);
    }


    @Test
    public void showAll() {

        ParseResult<CompilationUnit> result = javaParser.parse(ParseStart.COMPILATION_UNIT, provider(x));
        assumeTrue(result.isSuccessful());

        result.ifSuccessful(compilationUnit -> {
            List<MethodCallExpr> methodCallExprs = compilationUnit.findAll(MethodCallExpr.class);
            for (int i = 0; i < methodCallExprs.size(); i++) {
                MethodCallExpr methodCallExpr = methodCallExprs.get(i);
                System.out.println();
                System.out.println("methodCallExpr (" + i + ") = " + methodCallExpr);
                System.out.println("methodCallExpr.resolve() = " + methodCallExpr.resolve());
                System.out.println("methodCallExpr.calculateResolvedType() = " + methodCallExpr.calculateResolvedType());
                System.out.println();
            }
        });
    }


    @Test
    public void test_2() {
        String x = "public class MyClass {\n" +
            "    private Ibaz m_something;\n" +
            "    \n" +
            "    public class Ibaz {\n" +
            "    }\n" +
            "    \n" +
            "    public void foo(Class<? extends Ibaz> clazz) {\n" +
            "    }\n" +
            "    \n" +
            "    protected void bar() {\n" +
            "        foo(m_something.getClass()); // this doesn't work\n" +
            "    }\n" +
            "}";

        ParseResult<CompilationUnit> result = javaParser.parse(ParseStart.COMPILATION_UNIT, provider(x));
        assumeTrue(result.isSuccessful());

//        result.getClass();
        result.ifSuccessful(compilationUnit -> {
            List<MethodCallExpr> methodCallExprs = compilationUnit.findAll(MethodCallExpr.class);

            MethodCallExpr methodCall;
            Expression arg;
            ResolvedType argResolvedType;
            ResolvedMethodDeclaration methodResolve;

            //
            System.out.println();
            methodCall = methodCallExprs.get(0);
            System.out.println("methodCall = " + methodCall);

            arg = methodCall.getArgument(0);
            System.out.println("arg = " + arg);

            argResolvedType = arg.calculateResolvedType();
            System.out.println("argResolvedType = " + argResolvedType);

            methodResolve = methodCall.resolve();
            System.out.println("methodResolve = " + methodResolve);
            System.out.println();
            //

        });
    }

    @Test
    public void test() {
        ParseResult<CompilationUnit> result = javaParser.parse(ParseStart.COMPILATION_UNIT, provider(x));
        assumeTrue(result.isSuccessful());

        result.ifSuccessful(compilationUnit -> {
            List<MethodCallExpr> methodCallExprs = compilationUnit.findAll(MethodCallExpr.class);

            MethodCallExpr methodCall;
            Expression arg;
            ResolvedType argResolvedType;
            ResolvedMethodDeclaration methodResolve;

            //
            System.out.println();
            methodCall = methodCallExprs.get(1);
            System.out.println("methodCall = " + methodCall);
            arg = methodCall.getArgument(0);
            System.out.println("arg = " + arg);
            argResolvedType = arg.calculateResolvedType();
            System.out.println("argResolvedType = " + argResolvedType);
            methodResolve = methodCall.resolve();
            System.out.println("methodResolve = " + methodResolve);
            System.out.println();

            //
            System.out.println();
            methodCall = methodCallExprs.get(3);
            System.out.println("methodCall = " + methodCall);
            arg = methodCall.getArgument(0);
            System.out.println("arg = " + arg);
            argResolvedType = arg.calculateResolvedType();
            System.out.println("argResolvedType = " + argResolvedType);
            methodResolve = methodCall.resolve();
            System.out.println("methodResolve = " + methodResolve);
            System.out.println();

            //
            System.out.println();
            methodCall = methodCallExprs.get(5);
            System.out.println("methodCall = " + methodCall);
            arg = methodCall.getArgument(0);
            System.out.println("arg = " + arg);
            argResolvedType = arg.calculateResolvedType();
            System.out.println("argResolvedType = " + argResolvedType);
            methodResolve = methodCall.resolve();
            System.out.println("methodResolve = " + methodResolve);
            System.out.println();

            //
            System.out.println();
            methodCall = methodCallExprs.get(7);
            System.out.println("methodCall = " + methodCall);
            arg = methodCall.getArgument(0);
            System.out.println("arg = " + arg);
            argResolvedType = arg.calculateResolvedType();
            System.out.println("argResolvedType = " + argResolvedType);
            methodResolve = methodCall.resolve();
            System.out.println("methodResolve = " + methodResolve);
            System.out.println();

            //
            System.out.println();
            methodCall = methodCallExprs.get(8);
            System.out.println("methodCall = " + methodCall);
            arg = methodCall.getArgument(0);
            System.out.println("arg = " + arg);
            argResolvedType = arg.calculateResolvedType();
            System.out.println("argResolvedType = " + argResolvedType);
            methodResolve = methodCall.resolve();
            System.out.println("methodResolve = " + methodResolve);
            System.out.println();


//
//
//            String name = "foo";
////            List<ResolvedMethodDeclaration> methodsWithMatchingName = methodCallExprs.stream()
////                .filter(m -> m.getName().equals(name))
////                .collect(Collectors.toList());
//
////            ResolvedType a = methodCall.calculateResolvedType();
//
//            ResolvedMethodDeclaration a = methodCall.resolve();
//            ResolvedMethodDeclaration foo = a.asMethod();
//            int numParams = foo.getNumberOfParams();
//
////            List<ResolvedMethodDeclaration> applicableMethods = methodsWithMatchingName.stream()
////                // Filters out duplicate ResolvedMethodDeclaration by their signature.
////                .filter(distinctByKey(ResolvedMethodDeclaration::getQualifiedSignature))
////                // Checks if ResolvedMethodDeclaration is applicable to argumentsTypes.
////                .filter((m) -> isApplicable(m, name, argumentsTypes, typeSolver, wildcardTolerance))
////                .collect(Collectors.toList());


        });
    }

}
