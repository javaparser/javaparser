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

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.List;
import org.junit.jupiter.api.Test;

public class Issue4503Test extends AbstractResolutionTest {

    @Test
    void test() {
        String code = "import java.util.function.Function;\n"
                + "import java.math.BigDecimal;\n"
                + "public class Test {\n"
                + "    public static <T, R> String logAndCatch(String moduleName, Object filter1, Object filter2, T req, Function<T, R> func) {\n"
                + "        return null;\n"
                + "    }\n"
                + "    public void test(String testModule, String filter1, String filter2) {\n"
                + "        Test.logAndCatch(testModule, filter1, filter2, \"1.2\", this::getAmount);\n"
                + "    }\n"
                + "    public BigDecimal getAmount(String amount) {\n"
                + "        return new BigDecimal(amount);\n"
                + "    }\n"
                + "}";

        ParserConfiguration config = new ParserConfiguration();
        config.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_18);
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        CompilationUnit cu = StaticJavaParser.parse(code);
        List<MethodReferenceExpr> exprs = cu.findAll(MethodReferenceExpr.class);
        for (MethodReferenceExpr expr : exprs) {
            if (expr.getIdentifier().contentEquals("getAmount")) {
                assertEquals("Test.getAmount(java.lang.String)", expr.resolve().getQualifiedSignature());
            }
        }
    }
}
