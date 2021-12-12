package com.github.javaparser.jml;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.CommentsCollection;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.jml.ArbitraryNodeContainer;
import com.github.javaparser.ast.jml.NodeWithContracts;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.jml.clauses.JmlContracts;
import com.github.javaparser.ast.jml.doc.*;
import com.github.javaparser.ast.jml.stmt.JmlStatement;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (11/20/21)
 */
public class JmlProcessor implements ParseResult.PostProcessor {
    @Override
    public void process(ParseResult<? extends Node> result, ParserConfiguration configuration) {

        final Optional<? extends Node> r = result.getResult();
        final Optional<CommentsCollection> comments = result.getCommentsCollection();
        if (configuration.isProcessJml() && r.isPresent() && comments.isPresent()) {
            r.get().accept(new JmlReplaceVisitor(configuration, result.getProblems()), null);
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

        private ArbitraryNodeContainer parseJmlMethodLevel(NodeList<JmlDoc> jmlDocs) {
            ParseResult<ArbitraryNodeContainer> r = javaParser.parseJmlMethodLevel(sanitizer.asString(jmlDocs));
            problems.addAll(r.getProblems());
            return r.getResult().orElse(null);
        }

        private ArbitraryNodeContainer parseJmlClasslevel(NodeList<JmlDoc> jmlDocs) {
            ParseResult<ArbitraryNodeContainer> r = javaParser.parseJmlClassLevel(sanitizer.asString(jmlDocs));
            problems.addAll(r.getProblems());
            return r.getResult().orElse(null);
        }

        private ArbitraryNodeContainer parseJmlTypeLevel(NodeList<JmlDoc> jmlDocs) {
            ParseResult<ArbitraryNodeContainer> r = javaParser.parseJmlTypeLevel(sanitizer.asString(jmlDocs));
            problems.addAll(r.getProblems());
            return r.getResult().orElse(null);
        }

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
                BodyDeclaration<?> next = members.get(pos + 1);
                members.remove(pos);
                for (Node child : t.getChildren()) {
                    if (child instanceof BodyDeclaration<?>) {
                        members.add(pos, (BodyDeclaration<?>) child);
                    } else if (child instanceof Modifier) {
                        ((NodeWithModifiers<?>) next).getModifiers().add((Modifier) child);
                    } else if (child instanceof JmlContract) {
                        ((NodeWithContracts<?>) next).addContracts(new JmlContracts(false,
                                new NodeList<>(), new NodeList<>((JmlContract) child)));
                    } else if (child instanceof JmlContracts) {
                        ((NodeWithContracts<?>) next).addContracts((JmlContracts) child);
                    } else {
                        reporter.report(child, "Not JML construct supported");
                    }
                }
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
            n.getContracts().forEach(p -> p.accept(this, arg));
            for (int pos = 0; pos < n.getStatements().size(); pos++) {
                Statement s = n.getStatement(pos);
                if (s.isJmlDocStmt()) {
                    pos = handleJmlStatementLevel(n, (JmlDocStmt) s, pos);
                }
            }
            n.getComment().ifPresent(l -> l.accept(this, arg));
            return n;
        }

        private int handleJmlStatementLevel(BlockStmt p, JmlDocStmt n, int pos) {
            ArbitraryNodeContainer t = parseJmlMethodLevel(n.getJmlComments());
            if (t == null) {
                assert false;    //TODO Error handling
            }

            // remove this node from the AST
            n.remove();
            Statement nextStatement = pos < p.getStatements().size() ? p.getStatement(pos) : null;
            int insertPosition = pos;

            for (Node child : t.getChildren()) {
                if (child instanceof JmlStatement) {
                    p.getStatements().add(insertPosition++, (JmlStatement) child);
                } else if (child instanceof Modifier) {
                    if (nextStatement instanceof NodeWithModifiers<?>) {
                        ((NodeWithModifiers<?>) nextStatement).getModifiers().add((Modifier) child);
                    } else {
                        assert false : "ALERT!";
                    }
                } else if (child instanceof JmlContracts) {
                    if (nextStatement instanceof NodeWithContracts<?>) {
                        ((NodeWithContracts<?>) nextStatement).addContracts((JmlContracts) child);
                    } else {
                        assert false : "ALERT!";
                    }
                } else {
                    reporter.report(child, "Not JML construct supported");
                }
            }
            return insertPosition - 1;
        }


        @Override
        public Visitable visit(Modifier n, Void arg) {
            if (n.getKeyword() instanceof JmlDocModifier) {
                handleModifier(n);
            } else {
                //super.visit(n, arg);
            }
            return n;
        }

        private void handleModifier(Modifier n) {
            JmlDocModifier doc = (JmlDocModifier) n.getKeyword();
            if (n.getParentNode().isPresent()) {
                NodeWithModifiers<?> parent = (NodeWithModifiers<?>) n.getParentNode().get();
                n.remove();

                ArbitraryNodeContainer t = parseJmlModifierLevel(doc.getJmlComments());
                assert t != null;
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

    private void process(CompilationUnit unit) {
        List<Comment> directComments = getDirectComments(unit);
        for (Comment directComment : directComments) {
            System.out.println(directComment);
        }
    }

    private void process(TypeDeclaration unit) {
        List<Comment> directComments = getDirectComments(unit);
        for (Comment directComment : directComments) {
            System.out.println(directComment);
        }
    }

    private void process(BlockStmt unit) {
        List<Comment> directComments = getDirectComments(unit);
        for (Comment directComment : directComments) {
            System.out.println(directComment);
        }
    }

    private List<Comment> getDirectComments(Node unit) {
        final List<Comment> all = unit.getAllContainedComments();
        List<Comment> seq = new ArrayList<>(all.size());

        for (Comment c : all) {
            if (c.getParentNode().get() == unit) {
                seq.add(c);
            }
        }

        return seq;
    }

    private void process(Node node) {
        if (node instanceof CompilationUnit) {
            process((CompilationUnit) node);
        }
        if (node instanceof TypeDeclaration<?>) {
            process((TypeDeclaration<?>) node);
        }
        if (node instanceof BlockStmt) {
            process((BlockStmt) node);
        }

        node.getComment().ifPresent(it -> System.out.println(node.getClass() + " :: " + it.getContent()));
        node.getChildNodes().forEach(it -> process(it));
    }


}
