package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.core.resolution.MethodUsageResolutionCapability;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.logic.AbstractClassDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;

import java.util.*;
import java.util.stream.Collectors;

/**
 * An anonymous class declaration representation.
 */
public class JavaParserAnonymousClassDeclaration extends AbstractClassDeclaration
        implements MethodUsageResolutionCapability {

  private final TypeSolver typeSolver;
  private final ObjectCreationExpr wrappedNode;
  private final ResolvedTypeDeclaration superTypeDeclaration;
  private final String name = "Anonymous-" + UUID.randomUUID();

  public JavaParserAnonymousClassDeclaration(ObjectCreationExpr wrappedNode,
                                             TypeSolver typeSolver) {
    this.typeSolver = typeSolver;
    this.wrappedNode = wrappedNode;

    ClassOrInterfaceType superType = wrappedNode.getType();
    String superTypeName = superType.getName().getId();
    if (superType.getScope().isPresent()) {
      superTypeName = superType.getScope().get().asString() + "." + superTypeName;
    }

    superTypeDeclaration =
        JavaParserFactory.getContext(wrappedNode.getParentNode().get(), typeSolver)
                         .solveType(superTypeName)
                         .getCorrespondingDeclaration();
  }

  public ResolvedTypeDeclaration getSuperTypeDeclaration() {
    return superTypeDeclaration;
  }

  public <T extends Node> List<T> findMembersOfKind(final Class<T> memberClass) {
    if (wrappedNode.getAnonymousClassBody().isPresent()) {
      return wrappedNode
              .getAnonymousClassBody()
              .get()
              .stream()
              .filter(node -> memberClass.isAssignableFrom(node.getClass()))
              .map(memberClass::cast)
              .collect(Collectors.toList());
    } else {
      return Collections.emptyList();
    }
  }
  
  public Context getContext() {
      return JavaParserFactory.getContext(wrappedNode, typeSolver);
  }

  @Override
  public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes,
                                                                boolean staticOnly) {
    return getContext().solveMethod(name, argumentsTypes, staticOnly);
  }

  @Override
  public Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> argumentTypes,
                                                  Context invocationContext, List<ResolvedType> typeParameters) {
    return getContext().solveMethodAsUsage(name, argumentTypes);
  }

  @Override
  protected ResolvedReferenceType object() {
    return new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver);
  }

  @Override
  public ResolvedReferenceType getSuperClass() {
    ResolvedReferenceTypeDeclaration superRRTD = superTypeDeclaration.asReferenceType();
    if (superRRTD == null) {
      throw new RuntimeException("The super ResolvedReferenceTypeDeclaration is not expected to be null");
    }
    return new ReferenceTypeImpl(superRRTD, typeSolver);
  }

  @Override
  public List<ResolvedReferenceType> getInterfaces() {
    return
        superTypeDeclaration
            .asReferenceType().getAncestors()
            .stream()
            .filter(type -> type.getTypeDeclaration().isInterface())
            .collect(Collectors.toList());
  }

  @Override
  public List<ResolvedConstructorDeclaration> getConstructors() {
    return
        findMembersOfKind(com.github.javaparser.ast.body.ConstructorDeclaration.class)
            .stream()
            .map(ctor -> new JavaParserConstructorDeclaration<>(this, ctor, typeSolver))
            .collect(Collectors.toList());
  }

  @Override
  public AccessSpecifier accessSpecifier() {
    return AccessSpecifier.PRIVATE;
  }

  @Override
  public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
    return
        ImmutableList.
            <ResolvedReferenceType>builder()
            .add(getSuperClass())
            .addAll(superTypeDeclaration.asReferenceType().getAncestors(acceptIncompleteList))
            .build();
  }

  @Override
  public List<ResolvedFieldDeclaration> getAllFields() {

    List<JavaParserFieldDeclaration> myFields =
        findMembersOfKind(com.github.javaparser.ast.body.FieldDeclaration.class)
            .stream()
            .flatMap(field ->
                         field.getVariables().stream()
                              .map(variable -> new JavaParserFieldDeclaration(variable,
                                                                              typeSolver)))
            .collect(Collectors.toList());

    List<ResolvedFieldDeclaration> superClassFields =
        getSuperClass().getTypeDeclaration().getAllFields();

    List<ResolvedFieldDeclaration> interfaceFields =
        getInterfaces().stream()
                       .flatMap(inteface -> inteface.getTypeDeclaration().getAllFields().stream())
                       .collect(Collectors.toList());

    return
        ImmutableList
        .<ResolvedFieldDeclaration>builder()
        .addAll(myFields)
        .addAll(superClassFields)
        .addAll(interfaceFields)
        .build();
  }

  @Override
  public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
    return
        findMembersOfKind(com.github.javaparser.ast.body.MethodDeclaration.class)
            .stream()
            .map(method -> new JavaParserMethodDeclaration(method, typeSolver))
            .collect(Collectors.toSet());
  }

  @Override
  public boolean isAssignableBy(ResolvedType type) {
    return false;
  }

  @Override
  public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
    return false;
  }

  @Override
  public boolean hasDirectlyAnnotation(String qualifiedName) {
    return false;
  }

  @Override
  public String getPackageName() {
    return AstResolutionUtils.getPackageName(wrappedNode);
  }

  @Override
  public String getClassName() {
    return AstResolutionUtils.getClassName("", wrappedNode);
  }

  @Override
  public String getQualifiedName() {
    String containerName = AstResolutionUtils.containerName(wrappedNode.getParentNode().orElse(null));
    if (containerName.isEmpty()) {
      return getName();
    } else {
      return containerName + "." + getName();
    }
  }

  @Override
  public Set<ResolvedReferenceTypeDeclaration> internalTypes() {
    return
        findMembersOfKind(com.github.javaparser.ast.body.TypeDeclaration.class)
            .stream()
            .map(typeMember -> JavaParserFacade.get(typeSolver).getTypeDeclaration(typeMember))
            .collect(Collectors.toSet());
  }

  @Override
  public String getName() {
    return name;
  }

  @Override
  public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
    return Lists.newArrayList();
  }

  @Override
  public Optional<ResolvedReferenceTypeDeclaration> containerType() {
    throw new UnsupportedOperationException("containerType is not supported for " + this.getClass().getCanonicalName());
  }

  @Override
  public Optional<Node> toAst() {
    return Optional.of(wrappedNode);
  }

}
