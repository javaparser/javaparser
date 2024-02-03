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
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.declarations.AssociableToAST;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclarationTest;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

class JavaParserVariableDeclarationTest  extends AbstractResolutionTest  implements ResolvedValueDeclarationTest {

    @Override
    public Optional<Node> getWrappedDeclaration(AssociableToAST associableToAST) {
        return Optional.of(
                safeCast(associableToAST, JavaParserVariableDeclaration.class).getWrappedNode()
        );
    }

    @Override
    public JavaParserVariableDeclaration createValue() {
        String code = "class A {a() {String s;}}";
        CompilationUnit cu = JavaParserAdapter.of(
                createParserWithResolver(defaultTypeSolver())).parse(code);
        VariableDeclarator variableDeclarator = cu.findFirst(VariableDeclarator.class).get();
        ReflectionTypeSolver reflectionTypeSolver = new ReflectionTypeSolver();
        return new JavaParserVariableDeclaration(variableDeclarator, reflectionTypeSolver);
    }

    @Override
    public String getCanonicalNameOfExpectedType(ResolvedValueDeclaration resolvedDeclaration) {
        return String.class.getCanonicalName();
    }

    @Test
    void test3631() {
        String code = ""
                + "class InnerScope {\n"
                + "    int x = 0;\n"
                + "    void method() {\n"
                + "        {\n"
                + "            var x = 1;\n"
                + "            System.out.println(x);   // prints 1\n"
                + "        }\n"
                + "        System.out.println(x);       // prints 0\n"
                + "    }\n"
                + "    public static void main(String[] args) {\n"
                + "        new InnerScope().method();\n"
                + "    }\n"
                + "}";

        CompilationUnit cu = JavaParserAdapter.of(
                createParserWithResolver(defaultTypeSolver())).parse(code);

        List<NameExpr> names = cu.findAll(NameExpr.class);
        ResolvedValueDeclaration rvd = names.get(3).resolve();

        String decl = rvd.asField().toAst().get().toString();

        assertTrue("int x = 0;".equals(decl));
    }

}
