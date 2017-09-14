package com.github.javaparser.ast.expr;

import org.junit.Test;

import static com.github.javaparser.utils.TestUtils.assertExpressionValid;
import static org.junit.Assert.assertTrue;

public class MethodReferenceExprTest {

    @Test
    public void methodReferenceExprHasAlwaysAScope() {
        assertTrue(new MethodReferenceExpr().getScope() != null);
    }

    @Test
    public void reference1() {
        assertExpressionValid("String::length");
    }
        
    @Test
    public void reference2() {
        assertExpressionValid("System::currentTimeMillis // static method");
    }
        
    @Test
    public void reference3() {
        assertExpressionValid("List<String>::size // explicit type arguments for generic type");
    }
        
    @Test
    public void reference4() {
        assertExpressionValid("List::size // inferred type arguments for generic type");
    }
        
    @Test
    public void reference5() {
        assertExpressionValid("int[]::clone");
    }
        
    @Test
    public void reference6() {
        assertExpressionValid("T::tvarMember");
    }
        
    @Test
    public void reference7() {
        assertExpressionValid("System.out::println");
    }
        
    @Test
    public void reference8() {
        assertExpressionValid("\"abc\"::length");
    }
        
    @Test
    public void reference9() {
        assertExpressionValid("foo[x]::bar");
    }
        
    @Test
    public void reference10() {
        assertExpressionValid("(test ? list.replaceAll(String::trim) : list) :: iterator");
    }
        
    @Test
    public void reference10Annotated1() {
        assertExpressionValid("(test ? list.replaceAll(@A String::trim) : list) :: iterator");
    }
        
    @Test
    public void reference11() {
        assertExpressionValid("String::valueOf // overload resolution needed");
    }
        
    @Test
    public void reference12() {
        assertExpressionValid("Arrays::sort // type arguments inferred from context");
    }
        
    @Test
    public void reference13() {
        assertExpressionValid("Arrays::<String>sort // explicit type arguments");
    }
        
    @Test
    public void reference14() {
        assertExpressionValid("ArrayList<String>::new // constructor for parameterized type");
    }
        
    @Test
    public void reference15() {
        assertExpressionValid("ArrayList::new // inferred type arguments");
    }
        
    @Test
    public void reference16() {
        assertExpressionValid("Foo::<Integer>new // explicit type arguments");
    }
        
    @Test
    public void reference17() {
        assertExpressionValid("Bar<String>::<Integer>new // generic class, generic constructor");
    }
        
    @Test
    public void reference18() {
        assertExpressionValid("Outer.Inner::new // inner class constructor");
    }
        
    @Test
    public void reference19() {
        assertExpressionValid("int[]::new // array creation");
    }
}
