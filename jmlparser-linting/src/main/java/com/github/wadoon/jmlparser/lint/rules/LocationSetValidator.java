package com.github.wadoon.jmlparser.lint.rules;

import com.github.javaparser.ast.validator.VisitorValidator;
import com.github.wadoon.jmlparser.lint.LintRule;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class LocationSetValidator  extends VisitorValidator implements LintRule {
    public static final String ASSIGNABLE_ARRAY_ONLY = "You can only use '[*]' on arrays";
    public static final String ASSIGNABLE_CLASS_ONLY = "You can only use '.*' on classes and interfaces";
}
