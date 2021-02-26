package com.github.javaparser.jml.impl;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.visitor.TreeVisitor;
import org.jetbrains.annotations.NotNull;

/**
 * @author Alexander Weigl
 * @version 1 (4/10/20)
 */
public class JetbrainsAnnotationSupport {
    public static final String NOT_NULL = "org.jetbrains.annotations.NotNull";
    public static final String NULLABLE = "org.jetbrains.annotations.Nullable";
    public static final String CONTRACT = "org.jetbrains.annotations.Contract";

    public void process(@NotNull CompilationUnit ast) {
        TreeVisitor visitor = new TreeVisitor() {
            @Override
            public void process(Node node) {
                if (node instanceof NodeWithAnnotations<?>) {
                    var n = (NodeWithAnnotations<?>) node;
                    //n.getAnnotationByName()
                }
            }
        };
        visitor.visitPreOrder(ast);
    }

    /*class VisitorImpl extends ASTVisitor {
        private @NotNull AST astFactory = context.get(JmlProject.class).getAstFactory();

        @Override
        @SuppressWarnings("unchecked")
        public boolean visit(FieldDeclaration node) {
            if (node.getType().isAnnotatable()) {
                AnnotatableType atype = (AnnotatableType) node.getType();
                processAnnotation(node, (List<Annotation>) atype.annotations());
            }
            return super.visit(node);
        }

        private void processAnnotation(ASTNode node, List<Annotation> annotations) {
            for (Annotation it : annotations) {
                @Nullable JmlComment c = processAnnotation(it);
                if (c != null)
                    ASTProperties.attachJmlComment(node, c);
            }
        }

        private @Nullable JmlComment processAnnotation(Annotation annotation) {
            switch (annotation.getTypeName().getFullyQualifiedName()) {
                case JetbrainsAnnotationSupport.CONTRACT:
                    return null;
                case JetbrainsAnnotationSupport.NOT_NULL:
                    return createComment("/*@ non_null *");
                case JetbrainsAnnotationSupport.NULLABLE:
                    return createComment("/*@ nullable *");
            }
            return null;
        }

        public JmlComment createComment(String content) {
            BlockComment c = astFactory.newBlockComment();
            JmlComment jc = ASTProperties.wrap(c);
            jc.setContent(content);
            c.setAlternateRoot(compilationUnit);
            compilationUnit.getCommentList().add(c);
            return jc;
        }
    }*/
}
