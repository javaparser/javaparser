package com.github.javaparser.jml.impl;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.jml.Lookup;
import com.github.javaparser.jml.services.IJmlAnnotationProcessor;
import org.jetbrains.annotations.NotNull;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (4/10/20)
 */
public class JetbrainsAnnotationSupport implements IJmlAnnotationProcessor {
    public static final String NOT_NULL = "org.jetbrains.annotations.NotNull";
    public static final String NULLABLE = "org.jetbrains.annotations.Nullable";
    public static final String CONTRACT = "org.jetbrains.annotations.Contract";

    private final Lookup context;
    private final CompilationUnit compilationUnit;

    public JetbrainsAnnotationSupport(Lookup context, CompilationUnit compilationUnit) {
        this.context = context;
        this.compilationUnit = compilationUnit;
    }


    @Override
    public void process(@NotNull CompilationUnit ast) {
        //ast.accept(new VisitorImpl());
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
                    return createComment("/*@ non_null */");
                case JetbrainsAnnotationSupport.NULLABLE:
                    return createComment("/*@ nullable */");
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
