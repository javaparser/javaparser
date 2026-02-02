package com.github.javaparser.jml;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import com.github.javaparser.Processor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.comments.CommentsCollection;
import com.github.javaparser.ast.jml.doc.*;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;
import java.util.List;
import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (2/1/22)
 */
public class JmlWarnRemaingJmlDoc extends Processor {

    @Override
    public void postProcess(ParseResult<? extends Node> result, ParserConfiguration configuration) {
        if (configuration.isProcessJml()) {
            final Optional<? extends Node> r = result.getResult();
            final Optional<CommentsCollection> comments = result.getCommentsCollection();
            if (r.isPresent() && comments.isPresent()) {
                r.get().accept(new JmlWarnRemainingJmlDocVisitor(result.getProblems()), null);
            }
        }
    }

    public static class JmlWarnRemainingJmlDocVisitor extends GenericVisitorAdapter<Void, Void> {

        private static final String FOUND_JML_DOCUMENTATION_COMMENT =
                "JML annotation comment was not removed properly ";

        private final ProblemReporter problems;

        public JmlWarnRemainingJmlDocVisitor(List<Problem> problems) {
            this.problems = new ProblemReporter(problems::add);
        }

        @Override
        public Void visit(JmlDocDeclaration n, Void arg) {
            problems.report(
                    n, FOUND_JML_DOCUMENTATION_COMMENT + n.getMetaModel().getTypeName());
            return null;
        }

        @Override
        public Void visit(JmlDocStmt n, Void arg) {
            problems.report(
                    n, FOUND_JML_DOCUMENTATION_COMMENT + n.getMetaModel().getTypeName());
            return null;
        }

        @Override
        public Void visit(JmlDoc n, Void arg) {
            problems.report(
                    n, FOUND_JML_DOCUMENTATION_COMMENT + n.getMetaModel().getTypeName());
            return null;
        }

        @Override
        public Void visit(Modifier n, Void arg) {
            if (n.getKeyword() instanceof JmlDocModifier) {
                problems.report(
                        n, FOUND_JML_DOCUMENTATION_COMMENT + n.getMetaModel().getTypeName());
            }
            return null;
        }

        @Override
        public Void visit(JmlDocType n, Void arg) {
            problems.report(
                    n, FOUND_JML_DOCUMENTATION_COMMENT + n.getMetaModel().getTypeName());
            return null;
        }
    }
}
