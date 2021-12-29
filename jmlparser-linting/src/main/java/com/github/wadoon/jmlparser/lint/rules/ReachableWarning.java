package com.github.wadoon.jmlparser.lint.rules;

import com.github.javaparser.ast.jml.stmt.JmlStatement;
import com.github.javaparser.ast.jml.stmt.JmlStatements;
import com.github.javaparser.ast.jml.stmt.JmlUnreachableStmt;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.VisitorValidator;
import com.github.wadoon.jmlparser.lint.LintRule;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class ReachableWarning extends VisitorValidator implements LintRule {
    @Override
    public void visit(JmlUnreachableStmt n, ProblemReporter arg) {
        super.visit(n, arg);
    }
}
