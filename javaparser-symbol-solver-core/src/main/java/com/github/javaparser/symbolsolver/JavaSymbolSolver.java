/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver;

import static com.github.javaparser.resolution.Navigator.demandParentNode;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.NodeWithJmlTags;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.quality.NotNull;
import com.github.javaparser.resolution.SymbolResolver;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.Value;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.*;
import java.util.Optional;

/**
 * This implementation of the SymbolResolver wraps the functionality of the library to make them easily usable
 * from JavaParser nodes.
 * <p>
 * An instance of this class should be created once and then injected in all the CompilationUnit for which we
 * want to enable symbol resolution. To do so the method inject can be used, or you can use
 * {@link com.github.javaparser.ParserConfiguration#setSymbolResolver(SymbolResolver)} and the parser will do the
 * injection for you.
 *
 * @author Federico Tomassetti
 */
public class JavaSymbolSolver implements SymbolResolver {
    /**
     * Sometimes you want the old simple Java name resolution without consideration of any JML annotation.
     * For example, to determine name clashes between Java and JML.
     */
    public static boolean ENABLE_JML_RESOLUTION = true;

    /*
     * add possibility to resolve array.length #1695
     */
    private static class ArrayLengthValueDeclaration implements ResolvedValueDeclaration {

        private static final ArrayLengthValueDeclaration INSTANCE = new ArrayLengthValueDeclaration();

        private ArrayLengthValueDeclaration() {}

        @Override
        public String getName() {
            return "length";
        }

        @Override
        public ResolvedType getType() {
            return ResolvedPrimitiveType.INT;
        }
    }

    private TypeSolver typeSolver;

    public JavaSymbolSolver(@NotNull TypeSolver typeSolver) {
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
        T ret = resolveDeclarationImpl(node, resultClass);
        if (ret instanceof AssociableToAST) {
            AssociableToAST r = (AssociableToAST) ret;
            final Optional<? extends Node> ast = r.toAst();
            if (ast.isPresent()) {
                Node n = ast.get();
                if (!inJml(node) && inJml(n)) {
                    throw new JavaRefersToJmlException("Java to JML reference!");
                }
            }
        }
        return ret;
    }

    private boolean inJml(Node node) {
        if (node instanceof NodeWithJmlTags) return true;
        if (node.hasParentNode()) return inJml(node.getParentNode().get());
        return false;
    }

    public <T> T resolveDeclarationImpl(Node node, Class<T> resultClass) {
        if (node instanceof MethodDeclaration) {
            return resultClass.cast(new JavaParserMethodDeclaration((MethodDeclaration) node, typeSolver));
        }
        if (node instanceof ClassOrInterfaceDeclaration) {
            ResolvedReferenceTypeDeclaration resolved = toTypeDeclaration(node);
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof EnumDeclaration) {
            ResolvedReferenceTypeDeclaration resolved = toTypeDeclaration(node);
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof RecordDeclaration) {
            ResolvedReferenceTypeDeclaration resolved = toTypeDeclaration(node);
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof EnumConstantDeclaration) {
            ResolvedEnumDeclaration enumDeclaration =
                    node.findAncestor(EnumDeclaration.class).get().resolve().asEnum();
            ResolvedEnumConstantDeclaration resolved = enumDeclaration.getEnumConstants().stream()
                    .filter(c -> ((JavaParserEnumConstantDeclaration) c).getWrappedNode() == node)
                    .findFirst()
                    .get();
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof ConstructorDeclaration) {
            ConstructorDeclaration constructorDeclaration = (ConstructorDeclaration) node;
            TypeDeclaration<?> typeDeclaration =
                    (TypeDeclaration<?>) node.getParentNode().get();
            ResolvedReferenceTypeDeclaration resolvedTypeDeclaration =
                    resolveDeclaration(typeDeclaration, ResolvedReferenceTypeDeclaration.class);
            ResolvedConstructorDeclaration resolved = resolvedTypeDeclaration.getConstructors().stream()
                    .filter(c -> c instanceof JavaParserConstructorDeclaration)
                    .filter(c -> ((JavaParserConstructorDeclaration<?>) c).getWrappedNode() == constructorDeclaration)
                    .findFirst()
                    .orElseThrow(() ->
                            new RuntimeException("This constructor cannot be found in its parent. This seems wrong"));
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof AnnotationDeclaration) {
            ResolvedReferenceTypeDeclaration resolved = toTypeDeclaration(node);
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof AnnotationMemberDeclaration) {
            ResolvedAnnotationDeclaration annotationDeclaration =
                    node.findAncestor(AnnotationDeclaration.class).get().resolve();
            ResolvedAnnotationMemberDeclaration resolved = annotationDeclaration.getAnnotationMembers().stream()
                    .filter(c -> ((JavaParserAnnotationMemberDeclaration) c).getWrappedNode() == node)
                    .findFirst()
                    .get();
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof FieldDeclaration) {
            FieldDeclaration fieldDeclaration = (FieldDeclaration) node;
            if (fieldDeclaration.getVariables().size() != 1) {
                throw new RuntimeException(
                        "Cannot resolve a Field Declaration including multiple variable declarators. Resolve the single variable declarators");
            }
            ResolvedFieldDeclaration resolved =
                    new JavaParserFieldDeclaration(fieldDeclaration.getVariable(0), typeSolver);
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof VariableDeclarator) {
            ResolvedValueDeclaration resolved;
            if (node.getParentNode().isPresent() && node.getParentNode().get() instanceof FieldDeclaration) {
                resolved = new JavaParserFieldDeclaration((VariableDeclarator) node, typeSolver);
            } else if (node.getParentNode().isPresent()
                    && node.getParentNode().get() instanceof VariableDeclarationExpr) {
                resolved = new JavaParserVariableDeclaration((VariableDeclarator) node, typeSolver);
            } else {
                throw new UnsupportedOperationException("Parent of VariableDeclarator is: " + node.getParentNode());
            }
            if (resultClass.isInstance(resolved)) {
                return resultClass.cast(resolved);
            }
        }
        if (node instanceof MethodCallExpr) {
            SymbolReference<ResolvedMethodDeclaration> result =
                    JavaParserFacade.get(typeSolver).solve((MethodCallExpr) node);
            if (result.isSolved()) {
                if (resultClass.isInstance(result.getCorrespondingDeclaration())) {
                    return resultClass.cast(result.getCorrespondingDeclaration());
                }
            } else {
                throw new UnsolvedSymbolException(
                        "We are unable to find the method declaration corresponding to " + node);
            }
        }
        if (node instanceof ObjectCreationExpr) {
            SymbolReference<ResolvedConstructorDeclaration> result =
                    JavaParserFacade.get(typeSolver).solve((ObjectCreationExpr) node);
            if (result.isSolved()) {
                if (resultClass.isInstance(result.getCorrespondingDeclaration())) {
                    return resultClass.cast(result.getCorrespondingDeclaration());
                }
            } else {
                throw new UnsolvedSymbolException(
                        "We are unable to find the constructor declaration corresponding to " + node);
            }
        }
        if (node instanceof NameExpr) {
            SymbolReference<? extends ResolvedValueDeclaration> result =
                    JavaParserFacade.get(typeSolver).solve((NameExpr) node);
            if (result.isSolved()) {
                if (resultClass.isInstance(result.getCorrespondingDeclaration())) {
                    return resultClass.cast(result.getCorrespondingDeclaration());
                }
            } else {
                throw new UnsolvedSymbolException(
                        "We are unable to find the value declaration corresponding to " + node);
            }
        }
        if (node instanceof MethodReferenceExpr) {
            SymbolReference<ResolvedMethodDeclaration> result =
                    JavaParserFacade.get(typeSolver).solve((MethodReferenceExpr) node);
            if (result.isSolved()) {
                if (resultClass.isInstance(result.getCorrespondingDeclaration())) {
                    return resultClass.cast(result.getCorrespondingDeclaration());
                }
            } else {
                throw new UnsolvedSymbolException(
                        "We are unable to find the method declaration corresponding to " + node);
            }
        }
        if (node instanceof FieldAccessExpr) {
            SymbolReference<? extends ResolvedValueDeclaration> result =
                    JavaParserFacade.get(typeSolver).solve((FieldAccessExpr) node);
            if (result.isSolved()) {
                if (resultClass.isInstance(result.getCorrespondingDeclaration())) {
                    return resultClass.cast(result.getCorrespondingDeclaration());
                }
            } else {
                if ("length".equals(((FieldAccessExpr) node).getName().getId())) {
                    ResolvedType scopeType = ((FieldAccessExpr) node).getScope().calculateResolvedType();
                    if (scopeType.isArray()) {
                        if (resultClass.isInstance(ArrayLengthValueDeclaration.INSTANCE)) {
                            return resultClass.cast(ArrayLengthValueDeclaration.INSTANCE);
                        }
                    }
                }
                throw new UnsolvedSymbolException(
                        "We are unable to find the value declaration corresponding to " + node);
            }
        }
        if (node instanceof ThisExpr) {
            SymbolReference<ResolvedTypeDeclaration> result =
                    JavaParserFacade.get(typeSolver).solve((ThisExpr) node);
            if (result.isSolved()) {
                if (resultClass.isInstance(result.getCorrespondingDeclaration())) {
                    return resultClass.cast(result.getCorrespondingDeclaration());
                }
            } else {
                throw new UnsolvedSymbolException(
                        "We are unable to find the type declaration corresponding to " + node);
            }
        }
        if (node instanceof ExplicitConstructorInvocationStmt) {
            SymbolReference<ResolvedConstructorDeclaration> result =
                    JavaParserFacade.get(typeSolver).solve((ExplicitConstructorInvocationStmt) node);
            if (result.isSolved()) {
                if (resultClass.isInstance(result.getCorrespondingDeclaration())) {
                    return resultClass.cast(result.getCorrespondingDeclaration());
                }
            } else {
                throw new UnsolvedSymbolException(
                        "We are unable to find the constructor declaration corresponding to " + node);
            }
        }
        if (node instanceof Parameter) {
            if (ResolvedParameterDeclaration.class.equals(resultClass)) {
                Parameter parameter = (Parameter) node;
                Optional<Node> parentNode = node.getParentNode();
                if (!parentNode.isPresent()) {
                    throw new UnsolvedSymbolException(
                            "We are unable to resolve the parameter declaration corresponding to " + node);
                }
                Node parent = (Node) parentNode.get();
                if (parent instanceof ConstructorDeclaration) {
                    Optional<ResolvedParameterDeclaration> resolvedParameterDeclaration =
                            resolveParameterDeclaration(((ConstructorDeclaration) parent).resolve(), parameter);
                    return resolvedParameterDeclaration
                            .map(rpd -> resultClass.cast(rpd))
                            .orElseThrow(() -> new UnsolvedSymbolException(
                                    "We are unable to resolve the parameter declaration corresponding to " + node));
                } else if (parent instanceof MethodDeclaration) {
                    Optional<ResolvedParameterDeclaration> resolvedParameterDeclaration =
                            resolveParameterDeclaration(((MethodDeclaration) parent).resolve(), parameter);
                    return resolvedParameterDeclaration
                            .map(rpd -> resultClass.cast(rpd))
                            .orElseThrow(() -> new UnsolvedSymbolException(
                                    "We are unable to resolve the parameter declaration corresponding to " + node));
                } else if (parent instanceof RecordDeclaration) {
                    Optional<ResolvedParameterDeclaration> resolvedParameterDeclaration =
                            resolveParameterDeclaration(((RecordDeclaration) parent).resolve(), parameter);
                    return resolvedParameterDeclaration
                            .map(rpd -> resultClass.cast(rpd))
                            .orElseThrow(() -> new UnsolvedSymbolException(
                                    "We are unable to resolve the parameter declaration corresponding to " + node));
                } else if (parent instanceof LambdaExpr) {
                    Optional<ResolvedParameterDeclaration> resolvedParameterDeclaration =
                            resolveParameterDeclaration(parameter);
                    return resolvedParameterDeclaration
                            .map(rpd -> resultClass.cast(rpd))
                            .orElseThrow(() -> new UnsolvedSymbolException(
                                    "We are unable to resolve the parameter declaration corresponding to " + node));
                } else if (parent instanceof CatchClause) {
                    Optional<ResolvedParameterDeclaration> resolvedParameterDeclaration =
                            resolveParameterDeclaration(parameter);
                    return resolvedParameterDeclaration
                            .map(rpd -> resultClass.cast(rpd))
                            .orElseThrow(() -> new UnsolvedSymbolException(
                                    "We are unable to resolve the parameter declaration corresponding to " + node));
                } else {
                    throw new UnsolvedSymbolException(
                            "We are unable to resolve the parameter declaration corresponding to " + node);
                }
            }
        }
        if (node instanceof AnnotationExpr) {
            SymbolReference<ResolvedAnnotationDeclaration> result =
                    JavaParserFacade.get(typeSolver).solve((AnnotationExpr) node);
            if (result.isSolved()) {
                if (resultClass.isInstance(result.getCorrespondingDeclaration())) {
                    return resultClass.cast(result.getCorrespondingDeclaration());
                }
            } else {
                throw new UnsolvedSymbolException(
                        "We are unable to find the annotation declaration corresponding to " + node);
            }
        }
        if (node instanceof TypePatternExpr) {
            SymbolReference<? extends ResolvedValueDeclaration> result =
                    JavaParserFacade.get(typeSolver).solve((TypePatternExpr) node);
            if (result.isSolved()) {
                if (resultClass.isInstance(result.getCorrespondingDeclaration())) {
                    return resultClass.cast(result.getCorrespondingDeclaration());
                }
            } else {
                throw new UnsolvedSymbolException(
                        "We are unable to find the method declaration corresponding to " + node);
            }
        }
        throw new UnsupportedOperationException("Unable to find the declaration of type " + resultClass.getSimpleName()
                + " from " + node.getClass().getSimpleName());
    }

    /*
     * Resolves constructor or method parameter
     */
    private Optional<ResolvedParameterDeclaration> resolveParameterDeclaration(
            ResolvedMethodLikeDeclaration resolvedMethodLikeDeclaration, Parameter parameter) {
        for (int i = 0; i < resolvedMethodLikeDeclaration.getNumberOfParams(); i++) {
            if (resolvedMethodLikeDeclaration.getParam(i).getName().equals(parameter.getNameAsString())) {
                return Optional.of(resolvedMethodLikeDeclaration.getParam(i));
            }
        }
        return Optional.empty();
    }

    /*
     * Resolves record parameter
     */
    private Optional<ResolvedParameterDeclaration> resolveParameterDeclaration(
            ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration, Parameter parameter) {
        ResolvedFieldDeclaration rfd = resolvedReferenceTypeDeclaration.getField(parameter.getNameAsString());
        if (rfd == null) return Optional.empty();
        ResolvedParameterDeclaration resolvedParameterDeclaration = new ResolvedParameterDeclaration() {

            @Override
            public ResolvedType getType() {
                return rfd.getType();
            }

            @Override
            public String getName() {
                return parameter.getNameAsString();
            }

            @Override
            public boolean isVariadic() {
                return parameter.isVarArgs();
            }
        };
        return Optional.of(resolvedParameterDeclaration);
    }

    /*
     * Resolves lambda expression parameters and catch clause parameters
     */
    private Optional<ResolvedParameterDeclaration> resolveParameterDeclaration(Parameter parameter) {
        ResolvedParameterDeclaration resolvedParameterDeclaration = new ResolvedParameterDeclaration() {

            @Override
            public ResolvedType getType() {
                Node parentNode = parameter.getParentNode().get();
                if (parameter.getType().isUnknownType() && parentNode instanceof LambdaExpr) {
                    Optional<Value> value = JavaParserFactory.getContext(parentNode, typeSolver)
                            .solveSymbolAsValue(parameter.getNameAsString());
                    return value.map(v -> v.getType())
                            .orElseThrow(() -> new UnsolvedSymbolException(
                                    "We are unable to resolve the parameter declaration corresponding to "
                                            + parameter));
                }
                return JavaParserFacade.get(typeSolver).convertToUsage(parameter.getType());
            }

            @Override
            public String getName() {
                return parameter.getNameAsString();
            }

            @Override
            public boolean isVariadic() {
                return parameter.isVarArgs();
            }
        };
        return Optional.of(resolvedParameterDeclaration);
    }

    @Override
    public <T> T toResolvedType(Type javaparserType, Class<T> resultClass) {
        ResolvedType resolvedType = JavaParserFacade.get(typeSolver).convertToUsage(javaparserType);
        if (resultClass.isInstance(resolvedType)) {
            return resultClass.cast(resolvedType);
        }
        throw new UnsupportedOperationException(
                "Unable to get the resolved type of class " + resultClass.getSimpleName() + " from " + javaparserType);
    }

    @Override
    public ResolvedType calculateType(Expression expression) {
        return JavaParserFacade.get(typeSolver).getType(expression);
    }

    @Override
    public ResolvedReferenceTypeDeclaration toTypeDeclaration(Node node) {
        if (node instanceof ClassOrInterfaceDeclaration) {
            if (((ClassOrInterfaceDeclaration) node).isInterface()) {
                return new JavaParserInterfaceDeclaration((ClassOrInterfaceDeclaration) node, typeSolver);
            }
            return new JavaParserClassDeclaration((ClassOrInterfaceDeclaration) node, typeSolver);
        }
        if (node instanceof TypeParameter) {
            return new JavaParserTypeParameter((TypeParameter) node, typeSolver);
        }
        if (node instanceof EnumDeclaration) {
            return new JavaParserEnumDeclaration((EnumDeclaration) node, typeSolver);
        }
        if (node instanceof AnnotationDeclaration) {
            return new JavaParserAnnotationDeclaration((AnnotationDeclaration) node, typeSolver);
        }
        if (node instanceof EnumConstantDeclaration) {
            return new JavaParserEnumDeclaration((EnumDeclaration) demandParentNode(node), typeSolver);
        }
        if (node instanceof RecordDeclaration) {
            return new JavaParserRecordDeclaration((RecordDeclaration) node, typeSolver);
        }
        throw new IllegalArgumentException("Cannot get a reference type declaration from "
                + node.getClass().getCanonicalName());
    }
}
