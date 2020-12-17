/*
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

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.expr.ConditionalExpr;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

class ConditionalExprTest extends AbstractResolutionTest {

    private TypeSolver ts;

    @BeforeEach
    void setup() {
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);
    }

    @Test
    void nullOperandInConditionalExpression() {
        String code = "class A { public void m() { Object o = true ? \"\" : null;}}";
        ResolvedType rt1 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("java.lang.String", rt1.describe());
        code = "class A { public void m() { Object o = true ? null : \"\";}}";
        ResolvedType rt2 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("java.lang.String", rt2.describe());
    }
    
    @Test
    void booleanConditionalExpression() {
        // If the second and third operands are both of type Boolean, the conditional expression has type Boolean.
        String code = "class A { public void m() { boolean r = true ? Boolean.TRUE : Boolean.FALSE;}}";
        ResolvedType rt1 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("java.lang.Boolean", rt1.describe());
        // Otherwise, the conditional expression has type boolean.
        code = "class A { public void m() { boolean r = true ? true : Boolean.FALSE;}}";
        ResolvedType rt2 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("boolean", rt2.describe());
    }
    
    @Test
    void numericConditionalExpression() {
        // If the second and third operands have the same type, then that is the type of the conditional expression.
        String code = "class A { public void m() { int r = true ? 1 : 2;}}";
        ResolvedType rt1 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("int", rt1.describe());
        // If one of the second and third operands is of primitive type T, and the type of the other is the result of
        // applying boxing conversion (§5.1.7) to T, then the type of the conditional expression is T.
        code = "class A { public void m() { int r = true ? 1 : Integer.valueOf(2);}}";
        ResolvedType rt2 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("int", rt2.describe());
        // If one of the operands is of type byte or Byte and the other is of type short or Short, then the type of the
        // conditional expression is short.
        int r = true ? Byte.MIN_VALUE : Short.MIN_VALUE;
        code = "class A { public void m() { short r = true ? Byte.MIN_VALUE : Short.MIN_VALUE;}}";
        ResolvedType rt3 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("short", rt3.describe());
        code = "class A { public void m() { short r = true ? Byte.MIN_VALUE : Short.valueOf(Short.MIN_VALUE);}}";
        ResolvedType rt4 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("short", rt4.describe());
        code = "class A { public void m() { short r = true ? Short.MIN_VALUE : Byte.valueOf(Byte.MIN_VALUE);}}";
        ResolvedType rt5 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("short", rt5.describe());
        // If one of the operands is of type T where T is byte, short, or char, and the other operand is a constant
        // expression (§15.28) of type int whose value is representable in type T, then the type of the conditional
        // expression is T.
        code = "class A { public void m() { byte r = true ? Byte.MIN_VALUE : 1;}}";
        ResolvedType rt6 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("byte", rt6.describe());
        code = "class A { public void m() { short r = true ? Short.MIN_VALUE : 1;}}";
        ResolvedType rt7 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("short", rt7.describe());
        code = "class A { public void m() { char r =  true ? Character.MIN_VALUE : 1;}}";
        ResolvedType rt8 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("char", rt8.describe());
        // If one of the operands is of type T, where T is Byte, Short, or Character,
        // and the other operand is a constant expression of type int whose value is
        // representable in the type U which is the result of applying unboxing
        // conversion to T, then the type of the conditional expression is U.
        code = "class A { public void m() { byte r = true ? Byte.valueOf(Byte.MIN_VALUE) : 1;}}";
        ResolvedType rt9 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("byte", rt9.describe());
        code = "class A { public void m() { short r = true ? Short.valueOf(Short.MIN_VALUE) : 1;}}";
        ResolvedType rt10 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("short", rt10.describe());
        code = "class A { public void m() { char r =  true ? Character.valueOf(Character.MIN_VALUE) : 1;}}";
        ResolvedType rt11 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("char", rt11.describe());
        // Otherwise, binary numeric promotion (§5.6.2) is applied to the operand types,
        // and the type of the conditional expression is the promoted type of the second
        // and third operands.
        code = "class A { public void m() { long r = true ? 1L : 1;}}";
        ResolvedType rt12 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("long", rt12.describe());
        code = "class A { public void m() { long r = true ? 1.0 : 1F;}}";
        ResolvedType rt13 = StaticJavaParser.parse(code).findFirst(ConditionalExpr.class).get().calculateResolvedType();
        assertEquals("double", rt13.describe());
        
    }

}
