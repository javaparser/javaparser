/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.junit.jupiter.api.Test;

public class Issue3916Test extends AbstractResolutionTest {

    @Test
    void issue3916() {

        String code = "enum MyEnum {\n"
                + "        One;\n"
                + "    }\n"
                + "\n"
                + "    class Foo {\n"
                + "        String str;\n"
                + "\n"
                + "        public void setStr(String str) {\n"
                + "            this.str = str;\n"
                + "        }\n"
                + "\n"
                + "        void test(String str) {\n"
                + "            switch (MyEnum.One.valueOf(\"\")) {\n"
                + "            case One:\n"
                + "                setStr(str);\n"
                + "                break;\n"
                + "            }\n"
                + "        }\n"
                + "    }";

        CompilationUnit cu = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver()))
                .parse(code);

        cu.findAll(MethodCallExpr.class).forEach(mce -> {
            if (mce.getNameAsString().equals("setStr")) {
                System.out.println(mce.toString());
                assertEquals("Foo.setStr(java.lang.String)", mce.resolve().getQualifiedSignature());
            }
        });
    }
}
