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

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedUnionType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;


class JavaParserFacadeResolutionTest extends AbstractResolutionTest {

    @Test
    void typeDeclarationSuperClassImplicitlyIncludeObject() {
        CompilationUnit cu = parseSample("Generics");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "Generics");
        ResolvedTypeDeclaration typeDeclaration = JavaParserFacade.get(new ReflectionTypeSolver()).getTypeDeclaration(clazz);
        ResolvedReferenceType superclass = typeDeclaration.asClass().getSuperClass().orElseThrow(() -> new RuntimeException("super class unexpectedly empty"));
        assertEquals(Object.class.getCanonicalName(), superclass.getQualifiedName());
    }

    // See issue 42
    @Test
    void solvingReferenceToUnsupportedOperationException() {
        String code = "public class Bla {\n" +
                "    public void main()\n" +
                "    {\n" +
                "        try\n" +
                "        {\n" +
                "            int i = 0;\n" +
                "        }\n" +
                "        catch (UnsupportedOperationException e)\n" +
                "        {\n" +
                "            String s;\n" +
                "            e.getMessage();\n" +
                "        }\n" +
                "    }\n" +
                "}";
        MethodCallExpr methodCallExpr = Navigator.demandNodeOfGivenClass(parse(code), MethodCallExpr.class);
        MethodUsage methodUsage = JavaParserFacade.get(new ReflectionTypeSolver()).solveMethodAsUsage(methodCallExpr);
        assertEquals("java.lang.Throwable.getMessage()", methodUsage.getQualifiedSignature());
    }

    // See issue 46
    @Test
    void solvingReferenceToCatchClauseParam() {
        String code = "public class Bla {\n" +
                "    public void main()\n" +
                "    {\n" +
                "        try\n" +
                "        {\n" +
                "            int i = 0;\n" +
                "        }\n" +
                "        catch (UnsupportedOperationException e)\n" +
                "        {\n" +
                "            String s;\n" +
                "            e.getMessage();\n" +
                "        }\n" +
                "    }\n" +
                "}";
        MethodCallExpr methodCallExpr = Navigator.demandNodeOfGivenClass(parse(code), MethodCallExpr.class);
        NameExpr nameE = (NameExpr) methodCallExpr.getScope().get();
        SymbolReference<? extends ResolvedValueDeclaration> symbolReference = JavaParserFacade.get(new ReflectionTypeSolver()).solve(nameE);
        assertTrue(symbolReference.isSolved());
        assertTrue(symbolReference.getCorrespondingDeclaration().isParameter());
        assertEquals("e", symbolReference.getCorrespondingDeclaration().asParameter().getName());
        assertEquals("java.lang.UnsupportedOperationException", symbolReference.getCorrespondingDeclaration().asParameter().getType().asReferenceType().getQualifiedName());
    }

    // See issue 47
    @Test
    void solvingReferenceToAnAncestorInternalClass() {
        String code = "public class Foo {\n" +
                "    public class Base {\n" +
                "        public class X {\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public class Derived extends Base {\n" +
                "        public X x = null;\n" +
                "    }\n" +
                "}";
        FieldDeclaration fieldDeclaration = Navigator.demandNodeOfGivenClass(parse(code), FieldDeclaration.class);
        Type jpType = fieldDeclaration.getCommonType();
        ResolvedType jssType = JavaParserFacade.get(new ReflectionTypeSolver()).convertToUsage(jpType);
        assertEquals("Foo.Base.X", jssType.asReferenceType().getQualifiedName());
    }

    // See issue 119
    @Test
    void solveTryWithResourceVariable() {
        String code = "import java.util.Scanner; class A { void foo() { try (Scanner sc = new Scanner(System.in)) {\n" +
                "    sc.nextLine();\n" +
                "} } }";
        CompilationUnit cu = parse(code);
        MethodCallExpr methodCallExpr = Navigator.findMethodCall(cu, "nextLine").get();
        Expression scope = methodCallExpr.getScope().get();
        ResolvedType type = JavaParserFacade.get(new ReflectionTypeSolver()).getType(scope);
        assertTrue(type.isReferenceType());
        assertEquals("java.util.Scanner", type.asReferenceType().getQualifiedName());
    }

    private CompilationUnit parseWithTypeSolver(String code) {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        JavaParser javaParser = new JavaParser(parserConfiguration);
        return javaParser.parse(ParseStart.COMPILATION_UNIT, new StringProvider(code)).getResult().get();
    }

    @Test
    void solveMultiCatchType() {
        String code = "class A {\n" +
                "        public void foo() {\n" +
                "            try {\n" +
                "                \n" +
                "            } catch (IllegalStateException | IllegalArgumentException e) {\n" +
                "                \n" +
                "            }\n" +
                "        }\n" +
                "    }";
        CompilationUnit cu = parseWithTypeSolver(code);
        CatchClause catchClause = Navigator.demandNodeOfGivenClass(cu, CatchClause.class);
        Type jpType = catchClause.getParameter().getType();
        ResolvedType jssType = jpType.resolve();
        assertTrue(jssType instanceof ResolvedUnionType);
    }

    @Test
    void classToResolvedTypeViaReflection() {
        Class<?> clazz = this.getClass();
        ReflectionTypeSolver reflectionTypeSolver = new ReflectionTypeSolver();
        JavaParserFacade facade = JavaParserFacade.get(reflectionTypeSolver);
        ResolvedType resolvedType = facade.classToResolvedType(clazz);

        assertNotNull(resolvedType);
        assertTrue(resolvedType.isReferenceType());
        assertEquals(clazz.getCanonicalName(), resolvedType.asReferenceType().getQualifiedName());
    }
}
