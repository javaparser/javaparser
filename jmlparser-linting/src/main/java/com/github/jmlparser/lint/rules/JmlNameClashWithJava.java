package com.github.jmlparser.lint.rules;

import com.github.javaparser.ast.validator.VisitorValidator;
import com.github.jmlparser.lint.LintRule;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class JmlNameClashWithJava extends VisitorValidator implements LintRule {
    // Type error messages
    public static final String NOT_AN_EXCEPTION_CLASS = "This is not an exception class";
    public static final String PUT_IN_THROWS_CLAUSE = "This exception (or a superclass or subclass of it) should be mentioned in the throws clause of this method";
    public static final String CLASS_REFERENCE_NOT_FOUND = "This class could not be resolved, did you forget to import it?";
    public static final String OVERRIDING_LOCAL_VAR = "You are not allowed to override local variables and parameters";
    public static final String NOT_A_TYPE_NAME = "This is not the name of a primitive type or a class";
    public static final String NO_METHOD_RESULT = "Cannot use \\result here, as this method / constructor does not return anything";
    public static final String NO_ARRAY = "This is not an array";
    public static final String NO_CLASS_INSTANCE = "This should be of type java.lang.Class, maybe you forgot to use .class or .getClass()?";
    public static final String ASSIGNABLE_VAR_IS_FINAL = "This variable is final, so cannot be assigned";

    // java expression visitor error messages
    public static final String NO_ARRAY_SO_NO_ACCESS = "Array access is not allowed as this is not an array";
}
