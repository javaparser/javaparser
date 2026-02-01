/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2025 The JavaParser Team.
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

package com.github.javaparser.ast.expr;

import static com.github.javaparser.utils.TestUtils.assertExpressionValid;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verifyNoInteractions;

import com.github.javaparser.ast.observer.AstObserver;
import org.junit.jupiter.api.Test;

class MethodReferenceExprTest {

    @Test
    void methodReferenceExprHasAlwaysAScope() {
        assertNotNull(new MethodReferenceExpr().getScope());
    }

    @Test
    void reference1() {
        assertExpressionValid("String::length");
    }

    @Test
    void reference2() {
        assertExpressionValid("System::currentTimeMillis // static method");
    }

    @Test
    void reference3() {
        assertExpressionValid("List<String>::size // explicit type arguments for generic type");
    }

    @Test
    void reference4() {
        assertExpressionValid("List::size // inferred type arguments for generic type");
    }

    @Test
    void reference5() {
        assertExpressionValid("int[]::clone");
    }

    @Test
    void reference6() {
        assertExpressionValid("T::tvarMember");
    }

    @Test
    void reference7() {
        assertExpressionValid("System.out::println");
    }

    @Test
    void reference8() {
        assertExpressionValid("\"abc\"::length");
    }

    @Test
    void reference9() {
        assertExpressionValid("foo[x]::bar");
    }

    @Test
    void reference10() {
        assertExpressionValid("(test ? list.replaceAll(String::trim) : list) :: iterator");
    }

    @Test
    void reference10Annotated1() {
        assertExpressionValid("(test ? list.replaceAll(@A String::trim) : list) :: iterator");
    }

    @Test
    void reference11() {
        assertExpressionValid("String::valueOf // overload resolution needed");
    }

    @Test
    void reference12() {
        assertExpressionValid("Arrays::sort // type arguments inferred from context");
    }

    @Test
    void reference13() {
        assertExpressionValid("Arrays::<String>sort // explicit type arguments");
    }

    @Test
    void reference14() {
        assertExpressionValid("ArrayList<String>::new // constructor for parameterized type");
    }

    @Test
    void reference15() {
        assertExpressionValid("ArrayList::new // inferred type arguments");
    }

    @Test
    void reference16() {
        assertExpressionValid("Foo::<Integer>new // explicit type arguments");
    }

    @Test
    void reference17() {
        assertExpressionValid("Bar<String>::<Integer>new // generic class, generic constructor");
    }

    @Test
    void reference18() {
        assertExpressionValid("Outer.Inner::new // inner class constructor");
    }

    @Test
    void reference19() {
        assertExpressionValid("int[]::new // array creation");
    }

    @Test
    void issue4791Test() {
        String a = new String("Greeter::sayHelloWorld");
        String b = new String("Greeter::sayHelloWorld");
        MethodReferenceExpr expression = new MethodReferenceExpr();
        expression.setIdentifier(a);

        AstObserver observer = mock(AstObserver.class);
        expression.register(observer);

        expression.setIdentifier(b);

        verifyNoInteractions(observer);
    }
}
