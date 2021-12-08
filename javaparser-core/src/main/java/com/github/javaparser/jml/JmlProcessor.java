package com.github.javaparser.jml;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.CommentsCollection;
import com.github.javaparser.ast.jml.ArbitraryNodeContainer;
import com.github.javaparser.ast.jml.NodeWithContracts;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.jml.clauses.JmlContracts;
import com.github.javaparser.ast.jml.doc.JmlDoc;
import com.github.javaparser.ast.jml.doc.JmlDocDeclaration;
import com.github.javaparser.ast.jml.doc.JmlDocStmt;
import com.github.javaparser.ast.jml.stmt.JmlStatement;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

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

    private static class JmlReplaceVisitor extends VoidVisitorAdapter<Void> {
        final JmlDocSanitizer sanitizer;
        final JavaParser javaParser;
        private final List<Problem> problems;

        private JmlReplaceVisitor(ParserConfiguration config, List<Problem> problems) {
            this.problems = problems;
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


        @Override
        public void visit(ClassOrInterfaceDeclaration n, Void arg) {
            n.getExtendedTypes().forEach(p -> p.accept(this, arg));
            n.getImplementedTypes().forEach(p -> p.accept(this, arg));
            n.getTypeParameters().forEach(p -> p.accept(this, arg));
            for (BodyDeclaration<?> bodyDeclaration : new ArrayList<>(n.getMembers())) {
                bodyDeclaration.accept(this, arg);
            }
            n.getModifiers().forEach(p -> p.accept(this, arg));
            n.getName().accept(this, arg);
            n.getAnnotations().forEach(p -> p.accept(this, arg));
            n.getComment().ifPresent(l -> l.accept(this, arg));
        }


        @Override
        public void visit(JmlDocDeclaration n, Void arg) {
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
                        System.out.println("contract");
                        //TODO ((NodeWithModifiers<?>) next).
                    }
                }
            }
        }


        @Override
        public void visit(BlockStmt n, Void arg) {
            n.getContracts().forEach(p -> p.accept(this, arg));
            for (int i = 0; i < n.getStatements().size(); i++) {
                Statement s = n.getStatement(i);
                if (s.isJmlDocStmt()) {
                    i = handleJmlStatementLevel(n, (JmlDocStmt) s, i);
                }
            }
            n.getComment().ifPresent(l -> l.accept(this, arg));
        }

        private int handleJmlStatementLevel(BlockStmt p, JmlDocStmt n, int pos) {
            ArbitraryNodeContainer t = parseJmlMethodLevel(n.getJmlComments());
            if (t == null) {
                //TODO Error handling
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
                }
            }
            return insertPosition - 1;
        }

        @Override
        public void visit(JmlDoc n, Void arg) {

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
