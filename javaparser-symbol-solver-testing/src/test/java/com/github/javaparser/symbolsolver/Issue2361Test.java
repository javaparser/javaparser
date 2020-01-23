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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.OpenIssueTest;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where a ternary operation has numerical values as the resulting branches, binary numeric promotion (bnp) is applied.
 * <br>
 * <br>
 * 5.6.2 describes the outcome of bnp given the inputs, quoted below:
 * <ul>
 *     <li>If either operand is of type double, the other is converted to double.</li>
 *     <li>Otherwise, if either operand is of type float, the other is converted to float.</li>
 *     <li>Otherwise, if either operand is of type long, the other is converted to long.</li>
 *     <li>Otherwise, both operands are converted to type int.</li>
 * </ul>
 *
 * @see <a href="https://docs.oracle.com/javase/specs/jls/se8/html/jls-5.html#jls-5.6.2">https://docs.oracle.com/javase/specs/jls/se8/html/jls-5.html#jls-5.6.2</a>
 * @see <a href="https://docs.oracle.com/javase/specs/jls/se8/html/jls-15.html#jls-15.25">https://docs.oracle.com/javase/specs/jls/se8/html/jls-15.html#jls-15.25</a>
 * @see <a href="https://github.com/javaparser/javaparser/issues/2361">https://github.com/javaparser/javaparser/issues/2361</a>
 */
public class Issue2361Test {


    @OpenIssueTest(issueNumber = {2361, 2435})
    @Test
    public void doTest_expectingFloat() {
        //language=JAVA
        String src = "" +
                "public class Test\n" +
                "{\n" +
                "   public class InnerClass\n" +
                "   {\n" +
                "       public InnerClass(float f) {}\n" +
                "       public InnerClass(double d) {}\n" +
                "   }\n" +
                "    \n" +
                "   public Test() {\n" +
                "     // Must always evaluate to `InnerClass(double)` " +
                "     // This is due to the presence of a double in one of the ternary operator branches " +
                "     //  -> Per section 5.6.2 of the java spec \n" +
                "     new InnerClass(true ? 1f : 1d); \n" +
                "   }\n" +
                "}\n" +
                "";

        CombinedTypeSolver combinedSolver = new CombinedTypeSolver(new ReflectionTypeSolver());

        ParserConfiguration pc = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(combinedSolver))
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_8);

        StaticJavaParser.setConfiguration(pc);

        new VoidVisitorAdapter<Object>() {
            @Override
            public void visit(ObjectCreationExpr exp, Object arg) {
                String signature = exp.resolve().getSignature();
                assertEquals("InnerClass(double)", signature, "Expected to evaluate to the double variation due to the presence of a double value in one of the branches of the ternary operator.");
            }
        }.visit(StaticJavaParser.parse(src), null);
    }

}
