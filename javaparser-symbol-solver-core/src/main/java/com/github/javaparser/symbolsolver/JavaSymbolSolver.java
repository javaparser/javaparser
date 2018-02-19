package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.SymbolResolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.*;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

/**
 * This implementation of the SymbolResolver wraps the functionalities of the library to make them easily usable
 * from JavaParser nodes.
 *
 * An instance of this class should be created once and then injected in all the CompilationUnit for which we
 * want to enable symbol resolution. To do so the method inject can be used.
 *
 * @author Federico Tomassetti
 */
public class JavaSymbolSolver implements SymbolResolver {

    private TypeSolver typeSolver;

    public JavaSymbolSolver(TypeSolver typeSolver) {
        this.typeSolver = typeSolver;
    }

    /**
     * Register this SymbolResolver into a CompilationUnit, so that symbol resolution becomes available to
     * all nodes part of the CompilationUnit.
     */
    public void inject(CompilationUnit destination) {
        destination.setData(Node.SYMBOL_RESOLVER_KEY, this);
    }

    @Override
    public <T> T resolveDeclaration(Node node, Class<T> resultClass) {
        if (node instanceof MethodDeclaration) {
            return resultClass.cast(new JavaParserMethodDeclaration((MethodDeclaration)node, typeSolver));
        }
        if (node instanceof ClassOrInterfaceDeclaration) {
            ResolvedReferenceTypeDeclaration resolved = JavaParserFactory.toTypeDeclaration(node, typeSolver);
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof EnumDeclaration) {
            ResolvedReferenceTypeDeclaration resolved = JavaParserFactory.toTypeDeclaration(node, typeSolver);
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof EnumConstantDeclaration) {
            ResolvedEnumDeclaration enumDeclaration = node.findParent(EnumDeclaration.class).get().resolve().asEnum();
            ResolvedEnumConstantDeclaration resolved = enumDeclaration.getEnumConstants().stream().filter(c -> ((JavaParserEnumConstantDeclaration)c).getWrappedNode() == node).findFirst().get();
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof ConstructorDeclaration) {
            ConstructorDeclaration constructorDeclaration = (ConstructorDeclaration)node;
            ClassOrInterfaceDeclaration classOrInterfaceDeclaration = (ClassOrInterfaceDeclaration)node.getParentNode().get();
            ResolvedClassDeclaration resolvedClass = resolveDeclaration(classOrInterfaceDeclaration, ResolvedClassDeclaration.class).asClass();
            ResolvedConstructorDeclaration resolved =  resolvedClass.getConstructors().stream().filter(c -> ((JavaParserConstructorDeclaration)c).getWrappedNode() == constructorDeclaration).findFirst().get();
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof AnnotationDeclaration) {
            ResolvedReferenceTypeDeclaration resolved = JavaParserFactory.toTypeDeclaration(node, typeSolver);
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof AnnotationMemberDeclaration) {
            ResolvedAnnotationDeclaration annotationDeclaration = node.findParent(AnnotationDeclaration.class).get().resolve();
            ResolvedAnnotationMemberDeclaration resolved = annotationDeclaration.getAnnotationMembers().stream().filter(c -> ((JavaParserAnnotationMemberDeclaration)c).getWrappedNode() == node).findFirst().get();
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof FieldDeclaration) {
            FieldDeclaration fieldDeclaration = (FieldDeclaration)node;
            if (fieldDeclaration.getVariables().size() != 1) {
                throw new RuntimeException("Cannot resolve a Field Declaration including multiple variable declarators. Resolve the single variable declarators");
            }
            ResolvedFieldDeclaration resolved = new JavaParserFieldDeclaration(fieldDeclaration.getVariable(0), typeSolver);
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof VariableDeclarator) {
            ResolvedFieldDeclaration resolved = new JavaParserFieldDeclaration((VariableDeclarator)node, typeSolver);
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof MethodCallExpr) {
            SymbolReference<ResolvedMethodDeclaration> result = JavaParserFacade.get(typeSolver).solve((MethodCallExpr)node);
            if (result.isSolved()) {
                if (resultClass.isInstance(result.getCorrespondingDeclaration())) {
                    return resultClass.cast(result.getCorrespondingDeclaration());
                }
            } else {
                throw new UnsolvedSymbolException("We are unable to find the method declaration corresponding to " + node);
            }
        }
        if (node instanceof NameExpr) {
            SymbolReference<? extends ResolvedValueDeclaration> result = JavaParserFacade.get(typeSolver).solve((NameExpr) node);
            if (result.isSolved()) {
                if (resultClass.isInstance(result.getCorrespondingDeclaration())) {
                    return resultClass.cast(result.getCorrespondingDeclaration());
                }
            } else {
                throw new UnsolvedSymbolException("We are unable to find the value declaration corresponding to " + node);
            }
        }
        if (node instanceof ThisExpr) {
            SymbolReference<ResolvedTypeDeclaration> result = JavaParserFacade.get(typeSolver).solve((ThisExpr) node);
            if (result.isSolved()) {
                if (resultClass.isInstance(result.getCorrespondingDeclaration())) {
                    return resultClass.cast(result.getCorrespondingDeclaration());
                }
            } else {
                throw new UnsolvedSymbolException("We are unable to find the type declaration corresponding to " + node);
            }
        }
        if (node instanceof ExplicitConstructorInvocationStmt) {
            SymbolReference<ResolvedConstructorDeclaration> result = JavaParserFacade.get(typeSolver).solve((ExplicitConstructorInvocationStmt) node);
            if (result.isSolved()) {
                if (resultClass.isInstance(result.getCorrespondingDeclaration())) {
                    return resultClass.cast(result.getCorrespondingDeclaration());
                }
            } else {
                throw new UnsolvedSymbolException("We are unable to find the constructor declaration corresponding to " + node);
            }
        }
        if (node instanceof Parameter) {
            if (ResolvedParameterDeclaration.class.equals(resultClass)) {
                Parameter parameter = (Parameter)node;
                CallableDeclaration callableDeclaration = node.findParent(CallableDeclaration.class).get();
                ResolvedMethodLikeDeclaration resolvedMethodLikeDeclaration;
                if (callableDeclaration.isConstructorDeclaration()) {
                    resolvedMethodLikeDeclaration = callableDeclaration.asConstructorDeclaration().resolve();
                } else {
                    resolvedMethodLikeDeclaration = callableDeclaration.asMethodDeclaration().resolve();
                }
                for (int i=0;i<resolvedMethodLikeDeclaration.getNumberOfParams();i++) {
                    if (resolvedMethodLikeDeclaration.getParam(i).getName().equals(parameter.getNameAsString())) {
                        return resultClass.cast(resolvedMethodLikeDeclaration.getParam(i));
                    }
                }
            }
        }
        throw new UnsupportedOperationException("Unable to find the declaration of type " + resultClass.getSimpleName()
                + " from " + node.getClass().getSimpleName());
    }

    @Override
    public <T> T toResolvedType(Type javaparserType, Class<T> resultClass) {
        ResolvedType resolvedType = JavaParserFacade.get(typeSolver).convertToUsage(javaparserType, javaparserType);
        if (resultClass.isInstance(resolvedType)) {
            return resultClass.cast(resolvedType);
        }
        throw new UnsupportedOperationException("Unable to get the resolved type of class "
                + resultClass.getSimpleName() + " from " + javaparserType);
    }

    @Override
    public ResolvedType calculateType(Expression expression) {
        return JavaParserFacade.get(typeSolver).getType(expression);
    }
}
