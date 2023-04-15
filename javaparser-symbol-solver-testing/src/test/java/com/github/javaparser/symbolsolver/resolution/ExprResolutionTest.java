/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.resolution.types.ResolvedPrimitiveType.*;
import static org.junit.jupiter.api.Assertions.assertEquals;

class ExprResolutionTest extends AbstractResolutionTest {

    private TypeSolver ts;
    private ResolvedType stringType;

    @BeforeEach
    void setup() {
        ts = new ReflectionTypeSolver();
        stringType = new ReferenceTypeImpl(ts.solveType(String.class.getCanonicalName()));
    }

    // JLS 5.6.2. Binary Numeric Promotion
    // Widening primitive conversion (§5.1.2) is applied to convert either or both operands as specified by the
    // following rules:
    //
    // * If either operand is of type double, the other is converted to double.
    // * Otherwise, if either operand is of type float, the other is converted to float.
    // * Otherwise, if either operand is of type long, the other is converted to long.
    // * Otherwise, both operands are converted to type int.

    // Related to issue 1589
    @Test
    void typeOfPlusExpressionsDoubleAndByte() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  byte b = (byte)0; "
                        + "  double d = 0.0; "
                        + "  System.out.println( d + b );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(DOUBLE, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1589
    @Test
    void typeOfPlusExpressionsByteAndDouble() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  byte b = (byte)0; "
                        + "  double d = 0.0; "
                        + "  System.out.println( b + d );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(DOUBLE, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1589
    @Test
    void typeOfPlusExpressionsDoubleAndChar() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  char c = 'a'; "
                        + "  double d = 0.0; "
                        + "  System.out.println( d + c );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(DOUBLE, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1589
    @Test
    void typeOfPlusExpressionsCharAndDouble() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  char c = 'a'; "
                        + "  double d = 0.0; "
                        + "  System.out.println( c + d );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(DOUBLE, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1589
    @Test
    void typeOfPlusExpressionsDoubleAndInt() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  int i = 0; "
                        + "  double d = 0.0; "
                        + "  System.out.println( d + i );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(DOUBLE, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1589
    @Test
    void typeOfPlusExpressionsIntAndDouble() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  int i = 0; "
                        + "  double d = 0.0; "
                        + "  System.out.println( i + d );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(DOUBLE, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1589
    @Test
    void typeOfPlusExpressionsfloatAndByte() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  byte b = (byte)0; "
                        + "  float f = 0.0f; "
                        + "  System.out.println( f + b );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(FLOAT, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1589
    @Test
    void typeOfPlusExpressionsByteAndfloat() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  byte b = (byte)0; "
                        + "  float f = 0.0f; "
                        + "  System.out.println( b + f );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(FLOAT, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1589
    @Test
    void typeOfPlusExpressionsfloatAndChar() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  char c = 'a'; "
                        + "  float f = 0.0f; "
                        + "  System.out.println( f + c );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(FLOAT, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1589
    @Test
    void typeOfPlusExpressionsCharAndfloat() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  char c = 'a'; "
                        + "  float f = 0.0f; "
                        + "  System.out.println( c + f );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(FLOAT, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1589
    @Test
    void typeOfPlusExpressionsfloatAndInt() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  int i = 0; "
                        + "  float f = 0.0f; "
                        + "  System.out.println( f + i );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(FLOAT, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1589
    @Test
    void typeOfPlusExpressionsIntAndfloat() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  int i = 0; "
                        + "  float f = 0.0f; "
                        + "  System.out.println( i + f );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(FLOAT, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1589
    @Test
    void typeOfPlusExpressionsDoubleAndFloat() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  float f = 0.0f; "
                        + "  double d = 0.0; "
                        + "  System.out.println( d + f );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(DOUBLE, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1589
    @Test
    void typeOfPlusExpressionsFloatAndDouble() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  float f = 0.0f; "
                        + "  double d = 0.0; "
                        + "  System.out.println( f + d );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(DOUBLE, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1589
    @Test
    void typeOfPlusExpressionsByteAndChar() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  byte b = (byte)0; "
                        + "  char c = 'a'; "
                        + "  System.out.println( b + c );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(INT, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    @Test
    void typeOfPlusExpressionsCharAndByte() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  byte b = (byte)0; "
                        + "  char c = 'a'; "
                        + "  System.out.println( c + b );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(INT, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1731
    @Test
    void typeOfPlusExpressionsDoubleAndString() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  String s1 = \"string1\";"
                        + "  System.out.println( 1.0 + \"a_text\" );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(stringType, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1731
    @Test
    void typeOfPlusExpressionsIntAndString() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  String s1 = \"string1\";"
                        + "  System.out.println( 1 + s1 );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(stringType, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1731
    @Test
    void typeOfPlusExpressionsCharAndString() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  String s1 = \"string1\";"
                        + "  System.out.println( s1.charAt(2) + s1 );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(stringType, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1731
    @Test
    void typeOfPlusExpressionsStringAndDouble() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  String s1 = \"string1\";"
                        + "  System.out.println( \"a_text\" + 1.0 );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(stringType, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1731
    @Test
    void typeOfPlusExpressionsStringAndInt() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  String s1 = \"string1\";"
                        + "  System.out.println( s1 + 1 );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(stringType, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

    // Related to issue 1731
    @Test
    void typeOfPlusExpressionsStringAndChar() {
        CompilationUnit compilationUnit = parse(
                "public class Class1 {"
                        + " public void method1() {"
                        + "  String s1 = \"string1\";"
                        + "  System.out.println( s1 + s1.charAt(2) );"
                        + " }"
                        + "}");

        List<BinaryExpr> bExprs = compilationUnit.findAll(BinaryExpr.class);
        assertEquals(1, bExprs.size());
        assertEquals(stringType, JavaParserFacade.get(ts).getType(bExprs.get(0)));
    }

}
