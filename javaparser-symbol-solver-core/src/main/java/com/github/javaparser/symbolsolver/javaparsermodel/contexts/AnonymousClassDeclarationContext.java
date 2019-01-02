package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations
    .JavaParserAnonymousClassDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.MethodResolutionLogic;
import com.google.common.base.Preconditions;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * A symbol resolution context for an object creation node.
 */
public class AnonymousClassDeclarationContext extends AbstractJavaParserContext<ObjectCreationExpr> {

  private final JavaParserAnonymousClassDeclaration myDeclaration =
      new JavaParserAnonymousClassDeclaration(wrappedNode, typeSolver);

  public AnonymousClassDeclarationContext(ObjectCreationExpr node, TypeSolver typeSolver) {
    super(node, typeSolver);
    Preconditions.checkArgument(node.getAnonymousClassBody().isPresent(),
                                "An anonymous class must have a body");
  }

  @Override
  public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name,
                                                                List<ResolvedType> argumentsTypes,
                                                                boolean staticOnly) {
    List<ResolvedMethodDeclaration> candidateMethods =
        myDeclaration
            .getDeclaredMethods()
            .stream()
            .filter(m -> m.getName().equals(name) && (!staticOnly || m.isStatic()))
            .collect(Collectors.toList());

    if (!Object.class.getCanonicalName().equals(myDeclaration.getQualifiedName())) {
      for (ResolvedReferenceType ancestor : myDeclaration.getAncestors()) {
        SymbolReference<ResolvedMethodDeclaration> res =
            MethodResolutionLogic.solveMethodInType(ancestor.getTypeDeclaration(),
                                                    name,
                                                    argumentsTypes,
                                                    staticOnly);
        // consider methods from superclasses and only default methods from interfaces :
        // not true, we should keep abstract as a valid candidate
        // abstract are removed in MethodResolutionLogic.isApplicable is necessary
        if (res.isSolved()) {
          candidateMethods.add(res.getCorrespondingDeclaration());
        }
      }
    }

    // We want to avoid infinite recursion when a class is using its own method
    // see issue #75
    if (candidateMethods.isEmpty()) {
      SymbolReference<ResolvedMethodDeclaration> parentSolution =
          getParent().solveMethod(name, argumentsTypes, staticOnly);
      if (parentSolution.isSolved()) {
        candidateMethods.add(parentSolution.getCorrespondingDeclaration());
      }
    }

    // if is interface and candidate method list is empty, we should check the Object Methods
    if (candidateMethods.isEmpty() && myDeclaration.getSuperTypeDeclaration().isInterface()) {
      SymbolReference<ResolvedMethodDeclaration> res =
          MethodResolutionLogic.solveMethodInType(new ReflectionClassDeclaration(Object.class,
                                                                                 typeSolver),
                                                  name,
                                                  argumentsTypes,
                                                  false);
      if (res.isSolved()) {
        candidateMethods.add(res.getCorrespondingDeclaration());
      }
    }

    return MethodResolutionLogic.findMostApplicable(candidateMethods,
                                                    name,
                                                    argumentsTypes,
                                                    typeSolver);
  }

  @Override
  public SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
    List<com.github.javaparser.ast.body.TypeDeclaration> typeDeclarations =
        myDeclaration
            .findMembersOfKind(com.github.javaparser.ast.body.TypeDeclaration.class);

    Optional<SymbolReference<ResolvedTypeDeclaration>> exactMatch =
        typeDeclarations
            .stream()
            .filter(internalType -> internalType.getName().getId().equals(name))
            .findFirst()
            .map(internalType ->
                     SymbolReference.solved(
                         JavaParserFacade.get(typeSolver).getTypeDeclaration(internalType)));

    if(exactMatch.isPresent()){
      return exactMatch.get();
    }

    Optional<SymbolReference<ResolvedTypeDeclaration>> recursiveMatch =
        typeDeclarations
            .stream()
            .filter(internalType -> name.startsWith(String.format("%s.", internalType.getName())))
            .findFirst()
            .map(internalType ->
                     JavaParserFactory
                         .getContext(internalType, typeSolver)
                         .solveType(name.substring(internalType.getName().getId().length() + 1)));

    if (recursiveMatch.isPresent()) {
      return recursiveMatch.get();
    }

    Optional<SymbolReference<ResolvedTypeDeclaration>> typeArgumentsMatch =
        wrappedNode
            .getTypeArguments()
            .map(nodes ->
                     ((NodeWithTypeArguments<?>) nodes).getTypeArguments()
                                                       .orElse(new NodeList<>()))
            .orElse(new NodeList<>())
            .stream()
            .filter(type -> type.toString().equals(name))
            .findFirst()
            .map(matchingType ->
                     SymbolReference.solved(
                         new JavaParserTypeParameter(new TypeParameter(matchingType.toString()),
                                                     typeSolver)));

    if (typeArgumentsMatch.isPresent()) {
      return typeArgumentsMatch.get();
    }

    // Look into extended classes and implemented interfaces
    for (ResolvedReferenceType ancestor : myDeclaration.getAncestors()) {
      // look at names of extended classes and implemented interfaces (this may not be important because they are checked in CompilationUnitContext)
      if (ancestor.getTypeDeclaration().getName().equals(name)) {
        return SymbolReference.solved(ancestor.getTypeDeclaration());
      } 
      // look into internal types of extended classes and implemented interfaces
      try {
        for (ResolvedTypeDeclaration internalTypeDeclaration : ancestor.getTypeDeclaration().internalTypes()) {
          if (internalTypeDeclaration.getName().equals(name)) {
            return SymbolReference.solved(internalTypeDeclaration);
          }
        }
      } catch (UnsupportedOperationException e) {
        // just continue using the next ancestor
      }
    }
    
    return getParent().solveType(name);
  }

  @Override
  public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
    Preconditions.checkArgument(typeSolver != null);

    if (myDeclaration.hasVisibleField(name)) {
      return SymbolReference.solved(myDeclaration.getVisibleField(name));
    }

    return getParent().solveSymbol(name);
  }

}
