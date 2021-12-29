package com.github.jmlparser.lint.rules;

import com.github.javaparser.ast.validator.VisitorValidator;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class JmlNameClashWithJava extends VisitorValidator {
    // Semantic error messages
    public static final String REQUIRES_FIRST = "Requires clauses must be placed before all other clauses in a specification as it is a pre-condition";
    public static final String MULTIPLE_SIGNALS_ONLY = "Use a single signals_only clause to avoid confusion";
    public static final String DUPLICATE_MODIFIER = "This modifier has already been used in this specification";
    public static final String MULTIPLE_VISIBILITY_MODIFIERS = "You cannot have multiple visibility modifiers (public, protected or private)";
    public static final String MULTIPLE_SPEC_VISIBILITY_MODIFIERS = "You cannot have multiple specification visibility modifiers (spec_public or spec_protected)";
    public static final String LOOP_INVARIANT_NOT_ABOVE_LOOP = "loop_invariant / maintaining needs to be above a loop";
    public static final String HELPER_NOT_ALLOWED = "The helper modifier is only allowed when the method is private or pure";
    public static final String NOT_SPECIFIED_REDUNDANT = "This clause containing \\not_specified is redundant because you already specified it";
    public static final String STATIC_AND_INSTANCE = "You cannot use both instance and static, choose one";
    public static final String BACKSLASH_RESULT_NOT_ALLOWED = "You can only use \\result in an ensures clause";
    public static final String OLD_EXPR_NOT_ALLOWED = "You can only use an \\old() expressions in ensures and signals clauses, assert and assume statements, and in loop invariants";

    // Type error messages
    public static final String INVALID_EXPR = "Not a valid expression";
    public static final String INCORRECT_REFERENCE = "This is not a correct reference";
    public static final String ASSIGNABLE_ARRAY_ONLY = "You can only use '[*]' on arrays";
    public static final String ASSIGNABLE_CLASS_ONLY = "You can only use '.*' on classes and interfaces";
    public static final String UNASSIGNABLE = "This cannot be assigned";
    public static final String NOT_A_CLASS_NAME = "This is not a class name";
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
    public static final String STRING_NO_END = "A String must end with \"";
    public static final String CHAR_NO_END = "A char must end with '";
    public static final String INCORRECT_SYNTAX = "Incorrect syntax";
    public static final String TYPE_UNKNOWN = "Type unknown, maybe the expression is invalid?";
    public static final String ARRAY_DIM_NO_INT = "Array dimensions should be of type int or something that can be converted to int";
    public static final String ARRAY_INITIALIZER_WRONG_TYPE = "Initializer is not the same type as the array element type";
    public static final String METHOD_UNRESOLVED = "Method could not be resolved, maybe the parameters do not correspond?";
    public static final String CONSTRUCTOR_UNRESOLVED = "Constructor could not be resolved, maybe the parameters do not correspond?";
    public static final String INCOMPATIBLE_CAST = "Incompatible type cast";
    public static final String INVARIANT_WRONG_VISIBILITY = "The (specification) visibility of the reference should be the same as the visibility of the invariant";
    public static final String FIELD_NO_MODIFIERS = "The referenced field has no modifiers, so cannot check visibility constraints";
    public static final String INVARIANT_SHOULD_BE_STATIC = "A static invariant can only see static fields";
    public static final String VARIABLE_EXPECTED = "Variable expected";
    public static final String NOT_A_CLASS = "This is not a class";
    public static final String REFERENCE_UNRESOLVED = "Reference cannot be resolved";
    public static final String METHOD_NOT_PURE = "JML expressions should be pure and this method might not be pure";
    public static final String ASSIGNMENT_NOT_PURE = "JML expressions should be pure and assignments are not pure";


}
