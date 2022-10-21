package com.github.jmlparser.lint.rules;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.jml.clauses.JmlForallClause;
import com.github.javaparser.ast.jml.clauses.JmlSignalsClause;
import com.github.javaparser.ast.jml.clauses.JmlSimpleExprClause;
import com.github.javaparser.jml.JmlUtility;
import com.github.jmlparser.lint.LintProblemReporter;
import com.github.jmlparser.lint.LintRule;
import com.github.jmlparser.lint.LintRuleVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class JmlNameClashWithJava extends LintRuleVisitor {
    public static final LintProblemMeta NOT_AN_EXCEPTION_CLASS
            = new LintProblemMeta("JML-1", "This is not an exception class", LintRule.ERROR);

    @Override
    public void visit(JmlSignalsClause n, LintProblemReporter arg) {
        var rtype = n.getParameter().getType().resolve();
        var exception = JmlUtility.resolveException(n);
        if (exception.isAssignableBy(rtype)) {
            arg.report(NOT_AN_EXCEPTION_CLASS.create(n));
        }
        super.visit(n, arg);
    }


    public static final String PUT_IN_THROWS_CLAUSE = "This exception (or a superclass or subclass of it) should be mentioned in the throws clause of this method";

    public static final String CLASS_REFERENCE_NOT_FOUND = "This class could not be resolved, did you forget to import it?";


    @Override
    public void visit(JmlForallClause n, LintProblemReporter arg) {
        super.visit(n, arg);
    }

    public static final String NOT_A_TYPE_NAME = "This is not the name of a primitive type or a class";
    public static final String NO_ARRAY = "This is not an array";


    @Override
    public void visit(JmlSimpleExprClause n, LintProblemReporter arg) {
        super.visit(n, arg);
    }
}
