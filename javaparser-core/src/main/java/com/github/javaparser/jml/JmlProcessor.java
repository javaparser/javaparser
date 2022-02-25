package com.github.javaparser.jml;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.comments.CommentsCollection;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.jml.ArbitraryNodeContainer;
import com.github.javaparser.ast.jml.NodeWithContracts;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.jml.doc.*;
import com.github.javaparser.ast.jml.stmt.JmlStatement;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import org.jetbrains.annotations.Nullable;

import java.util.List;
import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (11/20/21)
 */
public class JmlProcessor implements ParseResult.PostProcessor {
    @Override
    public void process(ParseResult<? extends Node> result, ParserConfiguration configuration) {
        if (configuration.isProcessJml()) {
            final Optional<? extends Node> r = result.getResult();
            final Optional<CommentsCollection> comments = result.getCommentsCollection();
            if (r.isPresent() && comments.isPresent()) {
                r.get().accept(new JmlReplaceVisitor(configuration, result.getProblems()), null);
            }
            JmlWarnRemaingJmlDoc warn = new JmlWarnRemaingJmlDoc();
            warn.process(result, configuration);
        }
    }

    private static class JmlReplaceVisitor extends ModifierVisitor<Void> {
        final ProblemReporter reporter;
        final JmlDocSanitizer sanitizer;
        final JavaParser javaParser;
        private final List<Problem> problems;

        private JmlReplaceVisitor(ParserConfiguration config, List<Problem> problems) {
            this.problems = problems;
            this.reporter = new ProblemReporter(this.problems::add);
            javaParser = new JavaParser(config);
            sanitizer = new JmlDocSanitizer(config.getJmlKeys());
        }

        @Nullable
        private ArbitraryNodeContainer parseJmlMethodLevel(NodeList<JmlDoc> jmlDocs) {
            ParseResult<ArbitraryNodeContainer> r = javaParser.parseJmlMethodLevel(sanitizer.asString(jmlDocs));
            problems.addAll(r.getProblems());
            return r.getResult().orElse(null);
        }

        @Nullable
        private ArbitraryNodeContainer parseJmlClasslevel(NodeList<JmlDoc> jmlDocs) {
            ParseResult<ArbitraryNodeContainer> r = javaParser.parseJmlClassLevel(sanitizer.asString(jmlDocs));
            problems.addAll(r.getProblems());
            return r.getResult().orElse(null);
        }

        @Nullable
        private ArbitraryNodeContainer parseJmlTypeLevel(NodeList<JmlDoc> jmlDocs) {
            ParseResult<ArbitraryNodeContainer> r = javaParser.parseJmlTypeLevel(sanitizer.asString(jmlDocs));
            problems.addAll(r.getProblems());
            return r.getResult().orElse(null);
        }

        @Nullable
        private ArbitraryNodeContainer parseJmlModifierLevel(NodeList<JmlDoc> jmlDocs) {
            ParseResult<ArbitraryNodeContainer> r = javaParser.parseJmlModifierLevel(sanitizer.asString(jmlDocs));
            problems.addAll(r.getProblems());
            return r.getResult().orElse(null);
        }

        @Override
        public JmlDocDeclaration visit(JmlDocDeclaration n, Void arg) {
            ArbitraryNodeContainer t = parseJmlClasslevel(n.getJmlComments());
            if (t != null) {
                TypeDeclaration<?> parent = (TypeDeclaration<?>) n.getParentNode().get();
                NodeList<BodyDeclaration<?>> members = parent.getMembers();
                int pos = members.indexOf(n);
                assert pos >= 0;

                if (pos + 1 >= members.size()) {
                    //JML Documentation is last element, therefore it can only refer to upper element.
                    for (Node child : t.getChildren()) {
                        if (child instanceof BodyDeclaration<?>) {
                            members.add(pos, (BodyDeclaration<?>) child);
                        } else if (child instanceof Modifier) {
                            reporter.report(child, "JML modifier does not refer to any construct.");
                        } else if (child instanceof JmlContract) {
                            reporter.report(child, "JML contract without a method found.");
                        } else {
                            reporter.report(child, "JML construct " + child.getClass().getSimpleName() + " not supported at this position.");
                        }
                    }
                } else {
                    BodyDeclaration<?> next = members.get(pos + 1);
                    members.remove(pos);
                    for (Node child : t.getChildren()) {
                        if (child instanceof BodyDeclaration<?>) {
                            members.add(pos, (BodyDeclaration<?>) child);
                        } else if (child instanceof Modifier) {
                            ((NodeWithModifiers<?>) next).getModifiers().add((Modifier) child);
                        } else if (child instanceof JmlContract) {
                            ((NodeWithContracts<?>) next).addContracts((JmlContract) child);
                        } else {
                            reporter.report(child, "JML construct " + child.getClass().getSimpleName()
                                    + " not supported at this position.");
                        }
                    }
                }

                n.remove();
            }
            return n;
        }

        @Override
        public Visitable visit(JmlDocType n, Void arg) {
            ArbitraryNodeContainer t = parseJmlTypeLevel(n.getJmlComments());
            if (t != null) {
                CompilationUnit parent = (CompilationUnit) n.getParentNode().get();
                NodeList<TypeDeclaration<?>> members = parent.getTypes();
                int pos = members.indexOf(n);
                assert pos >= 0;
                TypeDeclaration<?> next = members.get(pos + 1);
                members.remove(pos);
                for (Node child : t.getChildren()) {
                    if (child instanceof ImportDeclaration) {
                        parent.addImport((ImportDeclaration) child);
                    } else {
                        reporter.report(child, "Not JML construct supported");
                    }
                }
            }
            return n;
        }

        @Override
        public BlockStmt visit(BlockStmt n, Void arg) {
            n.getContracts().ifPresent(it -> it.accept(this, arg));
            for (int pos = 0; pos < n.getStatements().size(); pos++) {
                Statement s = n.getStatement(pos);
                if (s.isJmlDocStmt()) {
                    pos = handleJmlStatementLevel(n, (JmlDocStmt) s, pos);
                    //assert !s.getParentNode().isPresent();
                } else {
                    s.accept(this, arg);
                }
            }
            n.getComment().ifPresent(l -> l.accept(this, arg));
            return n;
        }

        private int handleJmlStatementLevel(BlockStmt p, JmlDocStmt n, int pos) {
            ArbitraryNodeContainer t = parseJmlMethodLevel(n.getJmlComments());

            if (t == null) {
                reporter.report(n, "Could not handle the JML comment.");
                return pos;
            }

            // remove this node from the AST
            n.remove();

            // possible the next statement after the given comment
            @Nullable Statement nextStatement = pos < p.getStatements().size() ? p.getStatement(pos) : null;

            //ignore LabeledStatements
            if (nextStatement != null) {
                while (nextStatement.isLabeledStmt()) nextStatement = nextStatement.asLabeledStmt().getStatement();
            }


            // Positon to insert new statements
            int insertPosition = pos;

            for (Node child : t.getChildren()) {
                if (child instanceof JmlStatement) {
                    p.getStatements().add(insertPosition++, (JmlStatement) child);
                } else if (child instanceof Modifier) {
                    if (nextStatement == null) {
                        reporter.report(child, "You passed a modifier but there is following " +
                                "statement to carry it.");
                    } else {
                        try {
                            ((NodeWithModifiers<?>) nextStatement).getModifiers().add((Modifier) child);
                        } catch (ClassCastException e) {
                            reporter.report(nextStatement, "You passed a JML modifier but the following " +
                                    "statement is not able to carry modifiers. " + nextStatement.getMetaModel().getTypeName());
                        }
                    }
                } else if (child instanceof JmlContract) {
                    if (nextStatement == null) {
                        reporter.report(child, "You passed a contract but there is following " +
                                "statement to carry it.");
                    } else {
                        try {
                            ((NodeWithContracts<?>) nextStatement).addContracts((JmlContract) child);
                        } catch (ClassCastException e) {
                            reporter.report(nextStatement, "You passed a JML contract but the following " +
                                    "statement is not able to carry contract. " + nextStatement.getMetaModel().getTypeName());
                        }
                    }
                } else {
                    reporter.report(child, "Not JML " + child.getMetaModel().getTypeName() + " construct supported");
                }
            }
            return insertPosition - 1;
        }


        @Override
        public Visitable visit(Modifier n, Void arg) {
            if (n.getKeyword() instanceof JmlDocModifier) {
                handleModifier(n);
                return null;
            } else {
                return super.visit(n, arg);
            }
        }

        private void handleModifier(Modifier n) {
            JmlDocModifier doc = (JmlDocModifier) n.getKeyword();
            if (n.getParentNode().isPresent()) {
                NodeWithModifiers<?> parent = (NodeWithModifiers<?>) n.getParentNode().get();
                ArbitraryNodeContainer t = parseJmlModifierLevel(doc.getJmlComments());
                if (t == null) return;
                n.remove();
                for (Node child : t.getChildren()) {
                    if (child instanceof Modifier) {
                        parent.getModifiers().add((Modifier) child);
                    } else if (child instanceof AnnotationExpr) {
                        ((NodeWithAnnotations<?>) parent).addAnnotation((AnnotationExpr) child);
                    } else {
                        reporter.report(child, "JML not supported");
                    }
                }
            }
        }
    }
}
