package com.github.javaparser.jml;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Processor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.comments.CommentsCollection;
import com.github.javaparser.ast.jml.doc.JmlDocDeclaration;
import com.github.javaparser.ast.jml.doc.JmlDocModifier;
import com.github.javaparser.ast.jml.doc.JmlDocStmt;
import com.github.javaparser.ast.jml.doc.JmlDocType;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;

/**
 * A post-processor which removes all {@link com.github.javaparser.ast.jml.doc.JmlDocContainer} occurrences in an AST.
 *
 * @author Alexander Weigl
 * @version 1 (2/1/22)
 */
public class JmlDocHardRemover extends Processor {

    @Override
    public void postProcess(ParseResult<? extends Node> result, ParserConfiguration configuration) {
        if (configuration.isProcessJml()) {
            final Optional<? extends Node> r = result.getResult();
            final Optional<CommentsCollection> comments = result.getCommentsCollection();
            if (r.isPresent() && comments.isPresent()) {
                final JmlDocCollectorVisitor v = new JmlDocCollectorVisitor();
                r.get().accept(v, null);
                for (Node doc : v.docs) {
                    doc.remove();
                }
            }
        }
    }

    public static class JmlDocCollectorVisitor extends ModifierVisitor<Void> {

        private final List<Node> docs = new LinkedList<>();

        @Override
        public JmlDocDeclaration visit(JmlDocDeclaration n, Void arg) {
            docs.add(n);
            return n;
        }

        @Override
        public Visitable visit(JmlDocStmt n, Void arg) {
            docs.add(n);
            return n;
        }

        @Override
        public Visitable visit(Modifier n, Void arg) {
            if (n.getKeyword() instanceof JmlDocModifier) {
                docs.add(n);
            }
            return n;
        }

        @Override
        public JmlDocType visit(JmlDocType n, Void arg) {
            docs.add(n);
            return n;
        }
    }
}
