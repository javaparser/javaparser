package com.github.javaparser.jml.impl;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.visitor.VoidVisitor;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Arrays;
import java.util.Collection;
import java.util.function.Predicate;


/**
 * @author Alexander Weigl
 * @version 1 (2/1/20)
 */
public class AttachingUtils {
    interface Handler {
        void attach(Node c, @NotNull CompilationUnit ast);
    }

    /*
    //region Utilities
    public static void insertIntoBlock(Node comment, Class<?>... clazzes) {
        Node node = narrowstContainer(comment);
        if (node == null || !(node instanceof BlockStmt)) {
            System.err.println("There is no parent so I am not able to get on following nodes.");
        } else {
            BlockStmt b = (BlockStmt) node;
            //var predicate = createTypePredicate(clazzes);

            int idx = 0;
            for (; idx < b.getStatements().size(); idx++) {
                Node statement = (Node) b.getStatements().get(idx);
                if (statement.getStartPosition() >= comment.getLength() + comment.getStartPosition()) {
                    break;
                }
            }
            final EmptyStatement empty = comment.wrapped().getAST().newEmptyStatement();
            b.statements().add(idx, empty);
            ASTProperties.attachNode(empty, comment);
        }
    }

    public static TypeDeclaration<?> getTypeDeclaration(Node c) {
        CompilationUnit cu = (CompilationUnit) c.getAlternateRoot();
        for (Object o : cu.types()) {
            TypeDeclaration type = (TypeDeclaration) o;
            if (type.getStartPosition() <= c.getStartPosition() &&
                    type.getLength() >= c.getLength()) {
                return type;
            }
        }
        return null;
    }

    public static void attachToNextMethod(Node comment) {
        TypeDeclaration td = getTypeDeclaration(comment);
        if (td != null) {
            MethodDeclaration last = null;
            for (MethodDeclaration method : td.getMethods()) {
                if (method.getStartPosition() <= c.getLength() + c.getStartPosition()) {
                    last = method;
                    continue;
                }
                break;
            }
            if (last != null) {
                ASTProperties.attachNode(last, comment);
            }
        } else {
            System.err.println("Error: Could not attach comment to method.");
        }
    }

    private static void attachToNextNode(Node comment, int... types) {
        Node node = nodeAfter(comment);
        if (node == null) {
            System.err.println("There is no parent so I am not able to get on following nodes.");
        } else {
            var predicate = createTypePredicate(types);
            if (predicate.test(node)) {
                ASTProperties.attachNode(node, comment);
                return;
            }
            var location = node.getLocationInParent();
            if (location.isChildListProperty()) {
                var obj = node.getParent().getStructuralProperty(location);
                System.err.println("Could not attach comment to any of its parent nodes.");
            }
        }
    }

    /**
     * Attaches this comment to its closest parents of the specified type.
     *
     * @param comment
     *
    private static void attachToParent(Comment comment, int... types) {
        Predicate<Node> allowedNode = createTypePredicate(types);
        attachToParent(comment, allowedNode);
    }

    /*
    @NotNull
    private static Predicate<Node> createTypePredicate(int[] types) {
        if (types.length == 0) {
            return it -> true;
        }
        if (types.length == 1) {
            return it -> it.getNodeType() == types[0];
        }
        Arrays.sort(types);
        return Node -> {
            int t = Node.getNodeType();
            int idx = Arrays.binarySearch(types, t);
            return idx > 0 && types[idx] == t;
        };
    }

    private static void attachToParent(Node comment, Predicate<Node> predicate) {
        Node current = nodeAfter(comment);
        do {
            if (current != null && predicate.test(current)) {
                ASTProperties.attachNode(current, comment);
                return;
            }
            current = current != null ? current.getParent() : null;
        } while (current != null);
        System.err.println("Could not attach comment to any of its parent nodes.");
    }

    private @Nullable static Node narrowstContainer(Node comment) {
        Find f = new Find(comment.getStartPosition(), comment.getStartPosition() + comment.getLength());
        comment.wrapped().getAlternateRoot().accept(f);
        return f.lastContainer;
    }

    private static Node nodeAfter(Node comment) {
        Find f = new Find(comment.getStartPosition(), comment.getStartPosition() + comment.getLength());
        comment.wrapped().getAlternateRoot().accept(f);
        return f.found;
    }
    //endregion

    public void attach(@NotNull CompilationUnit ast, @NotNull Collection<Node> Nodes) {
        for (Node c : Nodes) {
            if (c.getAttachingType() == Node.AT_UNKNOWN) {
                System.err.println(
                        format("Given jml comment has to 'attaching type'. Was the IJmlDetection not successful {0}", c.getContent()));
            } else {
                Handler h = handlers.get(c.getAttachingType());
                if (h == null) {
                    System.err.println(
                            format("No attaching is registered for attachment type {0}.", c.getAttachingType()));
                } else {
                    h.attach(c, ast);
                }
            }
        }
    }

    private Predicate<Node> createTypePredicate(Class<?>[] clazzes) {
        if (clazzes.length == 0) {
            return it -> true;
        }

        if (clazzes.length == 1) {
            return it -> it.getClass().isAssignableFrom(clazzes[0]);
        }

        return it -> {
            for (var c : clazzes) {
                if (it.getClass().isAssignableFrom(c)) {
                    return true;
                }
            }
            return false;
        };
    }

    //region Handlers
    public static class ContainingToParent implements Handler {
        @Override
        public void attach(Node c, @NotNull CompilationUnit ast) {
            attachToParent(c, TYPE_DECLARATION);
        }
    }*/

    /*
    public static class NextLoop implements Handler {
        @Override
        public void attach(Node c, @NotNull CompilationUnit ast) {
            attachToNextNode(c, WHILE_STATEMENT, FOR_STATEMENT, ENHANCED_FOR_STATEMENT, DO_STATEMENT);
        }
    }

    public static class NextBlock implements Handler {
        @Override
        public void attach(Node c, @NotNull CompilationUnit ast) {
            attachToNextNode(c, BLOCK);
        }
    }

    public static class NextMethod implements Handler {
        @Override
        public void attach(Node c, @NotNull CompilationUnit ast) {
            attachToNextMethod(c);
        }
    }

    public static class NextDeclaration implements Handler {
        @Override
        public void attach(Node c, @NotNull CompilationUnit ast) {
            attachToNextNode(c, FIELD_DECLARATION, METHOD_DECLARATION);

        }
    }

    public static class NextField implements Handler {
        @Override
        public void attach(Node c, @NotNull CompilationUnit ast) {
            attachToNextNode(c, FIELD_DECLARATION);
        }
    }

    public static class NextStatement implements Handler {
        @Override
        public void attach(Node c, @NotNull CompilationUnit ast) {
            insertIntoBlock(c, Statement.class);
        }
    }
    //endregion
    */
}

/*
class Find implements VoidVisitor<Void> {
    final int start, end;

    int lastContainerSize;
    Node lastContainer;

    Node found;

    Find(int start, int length) {
        this.start = start;
        this.end = length;
    }


    @Override
    public boolean preVisit2(Node node) {
        var nEnd = node.getStartPosition() + node.getLength();
        if (node.getStartPosition() <= start && nEnd >= end) {
            lastContainer = node;
            return true; //go deep
        }

        if (node.getStartPosition() >= start && found == null) {
            found = node;
        }

        return false;
    }
}
*/