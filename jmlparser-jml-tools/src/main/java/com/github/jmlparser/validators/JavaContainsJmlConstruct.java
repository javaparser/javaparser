package com.github.jmlparser.validators;

import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.jml.body.JmlBodyDeclaration;
import com.github.javaparser.ast.jml.stmt.JmlStatement;
import com.github.javaparser.ast.jml.stmt.JmlStatements;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.Validator;

import java.util.function.Predicate;

/**
 * @author Alexander Weigl
 * @version 1 (19.02.22)
 */
public class JavaContainsJmlConstruct implements Validator {
    @Override
    public void accept(Node node, ProblemReporter problemReporter) {
        accept(node, false, problemReporter);
    }

    private void accept(Node current, Boolean inJml, ProblemReporter problemReporter) {
        Predicate<Node> openJml = (Node it) ->
                it instanceof JmlBodyDeclaration ||
                        it instanceof JmlStatement ||
                        it instanceof JmlStatements;

        if (!inJml && (current instanceof Jmlish) && !openJml.test(current)) {
            problemReporter.report(current, "Jml construct used in Java part");
            return;
        }

        for (Node it : current.getChildNodes()) {
            accept(it, inJml || openJml.test(current), problemReporter);
        }
    }
}
