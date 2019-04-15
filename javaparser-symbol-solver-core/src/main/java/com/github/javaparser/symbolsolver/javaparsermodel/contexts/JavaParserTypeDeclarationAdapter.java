package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.ConstructorResolutionLogic;
import com.github.javaparser.symbolsolver.resolution.MethodResolutionLogic;

import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class JavaParserTypeDeclarationAdapter {

    private com.github.javaparser.ast.body.TypeDeclaration<?> wrappedNode;
    private TypeSolver typeSolver;
    private Context context;
    private ResolvedReferenceTypeDeclaration typeDeclaration;

    public JavaParserTypeDeclarationAdapter(com.github.javaparser.ast.body.TypeDeclaration<?> wrappedNode, TypeSolver typeSolver,
                                            ResolvedReferenceTypeDeclaration typeDeclaration,
                                            Context context) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
        this.typeDeclaration = typeDeclaration;
        this.context = context;
    }

    public SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        if (this.wrappedNode.getName().getId().equals(name)) {
            return SymbolReference.solved(JavaParserFacade.get(typeSolver).getTypeDeclaration(wrappedNode));
        }

        // Internal classes
        for (BodyDeclaration<?> member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.TypeDeclaration) {
                com.github.javaparser.ast.body.TypeDeclaration<?> internalType = (com.github.javaparser.ast.body.TypeDeclaration<?>) member;
                if (internalType.getName().getId().equals(name)) {
                    return SymbolReference.solved(JavaParserFacade.get(typeSolver).getTypeDeclaration(internalType));
                } else if (name.startsWith(String.format("%s.%s", wrappedNode.getName(), internalType.getName()))) {
                    return JavaParserFactory.getContext(internalType, typeSolver).solveType(name.substring(wrappedNode.getName().getId().length() + 1));
                } else if (name.startsWith(String.format("%s.", internalType.getName()))) {
                    return JavaParserFactory.getContext(internalType, typeSolver).solveType(name.substring(internalType.getName().getId().length() + 1));
                }
            }
        }

        if (wrappedNode instanceof NodeWithTypeParameters) {
            NodeWithTypeParameters<?> nodeWithTypeParameters = (NodeWithTypeParameters<?>) wrappedNode;
            for (TypeParameter astTpRaw : nodeWithTypeParameters.getTypeParameters()) {
                TypeParameter astTp = astTpRaw;
                if (astTp.getName().getId().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeParameter(astTp, typeSolver));
                }
            }
        }

        // Look into extended classes and implemented interfaces
        ResolvedTypeDeclaration type = checkAncestorsForType(name, this.typeDeclaration);
        return ((type != null) ? SymbolReference.solved(type) : context.getParent().solveType(name));
    }

    /**
     * Recursively checks the ancestors of the {@param declaration} if an internal type is declared with a name equal
     * to {@param name}.
     * @return A ResolvedTypeDeclaration matching the {@param name}, null otherwise
     */
    private ResolvedTypeDeclaration checkAncestorsForType(String name, ResolvedReferenceTypeDeclaration declaration) {
        for (ResolvedReferenceType ancestor : declaration.getAncestors(true)) {
            try {
                for (ResolvedTypeDeclaration internalTypeDeclaration : ancestor.getTypeDeclaration().internalTypes()) {
                    boolean visible = true;
                    if (internalTypeDeclaration instanceof ResolvedReferenceTypeDeclaration) {
                        ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration = internalTypeDeclaration.asReferenceType();
                        if (resolvedReferenceTypeDeclaration instanceof HasAccessSpecifier) {
                            visible = ((HasAccessSpecifier) resolvedReferenceTypeDeclaration).accessSpecifier() != AccessSpecifier.PRIVATE;
                        }
                    }
                    if (internalTypeDeclaration.getName().equals(name)) {
                        if (visible) {
                            return internalTypeDeclaration;
                        } else {
                            return null;
                        }
                    }
                }
                // check recursively the ancestors of this ancestor
                ResolvedTypeDeclaration ancestorDeclaration = checkAncestorsForType(name, ancestor.getTypeDeclaration());
                if (ancestorDeclaration != null) {
                    return ancestorDeclaration;
                }
            } catch (UnsupportedOperationException e) {
                // just continue using the next ancestor
            }
        }
        return null;
    }

    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        List<ResolvedMethodDeclaration> candidateMethods = typeDeclaration.getDeclaredMethods().stream()
                .filter(m -> m.getName().equals(name))
                .filter(m -> !staticOnly || m.isStatic())
                .collect(Collectors.toList());
        // We want to avoid infinite recursion in case of Object having Object as ancestor
        if (!Object.class.getCanonicalName().equals(typeDeclaration.getQualifiedName())) {
            for (ResolvedReferenceType ancestor : typeDeclaration.getAncestors(true)) {
                // Avoid recursion on self
                if (typeDeclaration != ancestor.getTypeDeclaration()) {
                    candidateMethods.addAll(ancestor.getAllMethodsVisibleToInheritors()
                            .stream()
                            .filter(m -> m.getName().equals(name))
                            .collect(Collectors.toList()));
                    SymbolReference<ResolvedMethodDeclaration> res = MethodResolutionLogic
                            .solveMethodInType(ancestor.getTypeDeclaration(), name, argumentsTypes, staticOnly);
                    // consider methods from superclasses and only default methods from interfaces :
                    // not true, we should keep abstract as a valid candidate
                    // abstract are removed in MethodResolutionLogic.isApplicable is necessary
                    if (res.isSolved()) {
                        candidateMethods.add(res.getCorrespondingDeclaration());
                    }
                }
            }
        }
        // We want to avoid infinite recursion when a class is using its own method
        // see issue #75
        if (candidateMethods.isEmpty()) {
            SymbolReference<ResolvedMethodDeclaration> parentSolution = context.getParent().solveMethod(name, argumentsTypes, staticOnly);
            if (parentSolution.isSolved()) {
                candidateMethods.add(parentSolution.getCorrespondingDeclaration());
            }
        }

        // if is interface and candidate method list is empty, we should check the Object Methods
        if (candidateMethods.isEmpty() && typeDeclaration.isInterface()) {
            SymbolReference<ResolvedMethodDeclaration> res = MethodResolutionLogic.solveMethodInType(new ReflectionClassDeclaration(Object.class, typeSolver), name, argumentsTypes, false);
            if (res.isSolved()) {
                candidateMethods.add(res.getCorrespondingDeclaration());
            }
        }

        return MethodResolutionLogic.findMostApplicable(candidateMethods, name, argumentsTypes, typeSolver);
    }

    public SymbolReference<ResolvedConstructorDeclaration> solveConstructor(List<ResolvedType> argumentsTypes) {
        if (typeDeclaration instanceof ResolvedClassDeclaration) {
            return ConstructorResolutionLogic.findMostApplicable(typeDeclaration.getConstructors(), argumentsTypes, typeSolver);
        }
        return SymbolReference.unsolved(ResolvedConstructorDeclaration.class);
    }
}
