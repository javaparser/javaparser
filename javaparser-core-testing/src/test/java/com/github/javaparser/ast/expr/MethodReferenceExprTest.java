package com.github.javaparser.ast.expr;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestUtils.assertExpressionValid;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

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
}
