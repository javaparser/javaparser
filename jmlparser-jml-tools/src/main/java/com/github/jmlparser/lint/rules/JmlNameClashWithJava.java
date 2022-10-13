package com.github.jmlparser.lint.rules;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.jml.clauses.*;
import com.github.javaparser.jml.JmlUtility;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.jmlparser.lint.LintProblemReporter;
import com.github.jmlparser.lint.LintRuleVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class JmlNameClashWithJava extends LintRuleVisitor {
    public static final String NOT_AN_EXCEPTION_CLASS = "This is not an exception class";

    @Override
    public void visit(JmlSignalsClause n, LintProblemReporter arg) {
        var rtype = n.getParameter().getType().resolve();
        var exception = JmlUtility.resolveException(n);
        if (exception.isAssignableBy(rtype)) {
            arg.error(n.getParameter(), NOT_AN_EXCEPTION_CLASS);
        }
        super.visit(n, arg);
    }


    public static final String PUT_IN_THROWS_CLAUSE = "This exception (or a superclass or subclass of it) should be mentioned in the throws clause of this method";

    public static final String CLASS_REFERENCE_NOT_FOUND = "This class could not be resolved, did you forget to import it?";


    @Override
    public void visit(JmlForallClause n, LintProblemReporter arg) {
        var method = n.findAncestor(MethodDeclaration.class);

        super.visit(n, arg);
    }

    public static final String NOT_A_TYPE_NAME = "This is not the name of a primitive type or a class";
    public static final String NO_ARRAY = "This is not an array";


    @Override
    public void visit(JmlSimpleExprClause n, LintProblemReporter arg) {
        super.visit(n, arg);
    }
}
