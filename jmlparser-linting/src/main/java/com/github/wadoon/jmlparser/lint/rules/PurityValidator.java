package com.github.wadoon.jmlparser.lint.rules;

import com.github.javaparser.ast.validator.VisitorValidator;
import com.github.wadoon.jmlparser.lint.LintRule;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class PurityValidator extends VisitorValidator implements LintRule {
    public static final String METHOD_NOT_PURE = "JML expressions should be pure and this method might not be pure";
    public static final String ASSIGNMENT_NOT_PURE = "JML expressions should be pure and assignments are not pure";
}
