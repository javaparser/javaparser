package jml.impl;

import jml.ASTProperties;
import jml.JmlComment;
import jml.services.IJmlAttacher;
import lombok.var;
import org.eclipse.jdt.core.dom.*;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.function.Predicate;

import static java.text.MessageFormat.format;
import static org.eclipse.jdt.core.dom.ASTNode.*;

/**
 * @author Alexander Weigl
 * @version 1 (2/1/20)
 */
public class JmlAttacher implements IJmlAttacher {
    private final HashMap<Integer, Handler> handlers = new HashMap<>();

    public JmlAttacher() {
        handlers.put(JmlComment.AT_CONTAINING_TYPE, new ContainingToParent());
        handlers.put(JmlComment.AT_NEXT_LOOP, new NextLoop());
        handlers.put(JmlComment.AT_NEXT_BLOCK, new NextBlock());
        handlers.put(JmlComment.AT_NEXT_DECLARATION, new NextDeclaration());
        handlers.put(JmlComment.AT_NEXT_FIELD, new NextField());
        handlers.put(JmlComment.AT_NEXT_STATEMENT, new NextStatement());
        handlers.put(JmlComment.AT_NEXT_METHOD, new NextMethod());
    }

    @Override
    public void attach(@NotNull CompilationUnit ast, @NotNull Collection<JmlComment> jmlComments) {
        for (JmlComment c : jmlComments) {
            if (c.getAttachingType() == JmlComment.AT_UNKNOWN) {
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

    @Override
    public void setAttachmentHandler(int type, IJmlAttacher.Handler handler) {
        handlers.put(type, handler);
    }

    //region Handlers
    public static class ContainingToParent implements Handler {
        @Override
        public void attach(JmlComment c, @NotNull CompilationUnit ast) {
            attachToParent(c, TYPE_DECLARATION);
        }
    }

    public static class NextLoop implements Handler {
        @Override
        public void attach(JmlComment c, @NotNull CompilationUnit ast) {
            attachToNextNode(c, WHILE_STATEMENT, FOR_STATEMENT, ENHANCED_FOR_STATEMENT, DO_STATEMENT);
        }
    }

    public static class NextBlock implements Handler {
        @Override
        public void attach(JmlComment c, @NotNull CompilationUnit ast) {
            attachToNextNode(c, BLOCK);
        }
    }

    public static class NextMethod implements Handler {
        @Override
        public void attach(JmlComment c, @NotNull CompilationUnit ast) {
            attachToNextMethod(c);
        }
    }

    public static class NextDeclaration implements Handler {
        @Override
        public void attach(JmlComment c, @NotNull CompilationUnit ast) {
            attachToNextNode(c, FIELD_DECLARATION, METHOD_DECLARATION);

        }
    }

    public static class NextField implements Handler {
        @Override
        public void attach(JmlComment c, @NotNull CompilationUnit ast) {
            attachToNextNode(c, FIELD_DECLARATION);
        }
    }

    public static class NextStatement implements Handler {
        @Override
        public void attach(JmlComment c, @NotNull CompilationUnit ast) {
            insertIntoBlock(c, Statement.class);
        }
    }
    //endregion

    //region Utilities
    private static void insertIntoBlock(JmlComment comment, Class<?>... clazzes) {
        ASTNode node = narrowstContainer(comment);
        if (node == null || !(node instanceof Block)) {
            System.err.println("There is no parent so I am not able to get on following nodes.");
        } else {
            Block b = (Block) node;
            //var predicate = createTypePredicate(clazzes);

            int idx = 0;
            for (; idx < b.statements().size(); idx++) {
                ASTNode statement = (ASTNode) b.statements().get(idx);
                if (statement.getStartPosition() >= comment.getLength() + comment.getStartPosition()) {
                    break;
                }
            }
            final EmptyStatement empty = comment.wrapped().getAST().newEmptyStatement();
            b.statements().add(idx, empty);
            ASTProperties.attachJmlComment(empty, comment);
        }
    }

    private Predicate<ASTNode> createTypePredicate(Class<?>[] clazzes) {
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

    private static TypeDeclaration getTypeDeclaration(JmlComment comment) {
        final Comment c = comment.wrapped();
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

    private static void attachToNextMethod(JmlComment comment) {
        final Comment c = comment.wrapped();
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
                ASTProperties.attachJmlComment(last, comment);
            }
        } else {
            System.err.println("Error: Could not attach comment to method.");
        }
    }

    private static void attachToNextNode(JmlComment comment, int... types) {
        ASTNode node = nodeAfter(comment);
        if (node == null) {
            System.err.println("There is no parent so I am not able to get on following nodes.");
        } else {
            var predicate = createTypePredicate(types);
            if (predicate.test(node)) {
                ASTProperties.attachJmlComment(node, comment);
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
     */
    private static void attachToParent(JmlComment comment, int... types) {
        Predicate<ASTNode> allowedNode = createTypePredicate(types);
        attachToParent(comment, allowedNode);
    }

    @NotNull
    private static Predicate<ASTNode> createTypePredicate(int[] types) {
        if (types.length == 0) {
            return it -> true;
        }
        if (types.length == 1) {
            return it -> it.getNodeType() == types[0];
        }
        Arrays.sort(types);
        return astNode -> {
            int t = astNode.getNodeType();
            int idx = Arrays.binarySearch(types, t);
            return idx > 0 && types[idx] == t;
        };
    }

    private static void attachToParent(JmlComment comment, Predicate<ASTNode> predicate) {
        ASTNode current = nodeAfter(comment);
        do {
            if (current != null && predicate.test(current)) {
                ASTProperties.attachJmlComment(current, comment);
                return;
            }
            current = current != null ? current.getParent() : null;
        } while (current != null);
        System.err.println("Could not attach comment to any of its parent nodes.");
    }

    private @Nullable
    static ASTNode narrowstContainer(JmlComment comment) {
        Find f = new Find(comment.getStartPosition(), comment.getStartPosition() + comment.getLength());
        comment.wrapped().getAlternateRoot().accept(f);
        return f.lastContainer;
    }

    private static ASTNode nodeAfter(JmlComment comment) {
        Find f = new Find(comment.getStartPosition(), comment.getStartPosition() + comment.getLength());
        comment.wrapped().getAlternateRoot().accept(f);
        return f.found;
    }
    //endregion
}

class Find extends ASTVisitor {
    final int start, end;

    int lastContainerSize;
    ASTNode lastContainer;

    ASTNode found;

    Find(int start, int length) {
        this.start = start;
        this.end = length;
    }


    @Override
    public boolean preVisit2(ASTNode node) {
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
