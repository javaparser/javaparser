package com.github.jmlparser.lint.rules;

import com.github.jmlparser.lint.LintRuleVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class LocationSetValidator extends LintRuleVisitor {
    public static final String ASSIGNABLE_ARRAY_ONLY = "You can only use '[*]' on arrays";
    public static final String ASSIGNABLE_CLASS_ONLY = "You can only use '.*' on classes and interfaces";
}
