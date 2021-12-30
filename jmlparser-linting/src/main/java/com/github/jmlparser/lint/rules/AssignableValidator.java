package com.github.jmlparser.lint.rules;

import com.github.javaparser.ast.validator.VisitorValidator;
import com.github.jmlparser.lint.LintRule;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class AssignableValidator extends VisitorValidator implements LintRule {
    //Check for final fields
    public static final String UNASSIGNABLE = "This cannot be assigned";
}
