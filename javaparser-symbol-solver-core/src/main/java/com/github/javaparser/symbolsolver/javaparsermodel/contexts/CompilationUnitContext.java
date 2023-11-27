/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;


import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.logic.MethodResolutionLogic;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserAnnotationDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserEnumDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserInterfaceDeclaration;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;

import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class CompilationUnitContext extends AbstractJavaParserContext<CompilationUnit> {

    private static final String DEFAULT_PACKAGE = "java.lang";

    ///
    /// Static methods
    ///

    ///
    /// Constructors
    ///

    public CompilationUnitContext(CompilationUnit wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    ///
    /// Public methods
    ///

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {

        // solve absolute references
        String itName = name;
        while (itName.contains(".")) {
            String typeName = getType(itName);
            String memberName = getMember(itName);
            SymbolReference<ResolvedTypeDeclaration> type = this.solveType(typeName);
            if (type.isSolved()) {
                return new SymbolSolver(typeSolver).solveSymbolInType(type.getCorrespondingDeclaration(), memberName);
            }
            itName = typeName;
        }

        // Look among statically imported values
        for (ImportDeclaration importDecl : wrappedNode.getImports()) {
            if (importDecl.isStatic()) {
                if (importDecl.isAsterisk()) {
                    String qName = importDecl.getNameAsString();
                    ResolvedTypeDeclaration importedType = typeSolver.solveType(qName);

                    // avoid infinite recursion
                    if (!isAncestorOf(importedType)) {
                        SymbolReference<? extends ResolvedValueDeclaration> ref = new SymbolSolver(typeSolver).solveSymbolInType(importedType, name);
                        if (ref.isSolved()) {
                            return ref;
                        }
                    }
                } else {
                    String whole = importDecl.getNameAsString();

                    // split in field/method name and type name
                    String memberName = getMember(whole);
                    String typeName = getType(whole);

                    if (memberName.equals(name)) {
                        ResolvedTypeDeclaration importedType = typeSolver.solveType(typeName);
                        return new SymbolSolver(typeSolver).solveSymbolInType(importedType, memberName);
                    }
                }
            }
        }

        return SymbolReference.unsolved();
    }

    @Override
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name, List<ResolvedType> typeArguments) {

        if (wrappedNode.getTypes() != null) {
            // Look for types in this compilation unit. For instance, if the given name is "A", there may be a class or
            // interface in this compilation unit called "A".
            for (TypeDeclaration<?> type : wrappedNode.getTypes()) {
                if (type.getName().getId().equals(name)
                    || type.getFullyQualifiedName().map(qualified -> qualified.equals(name)).orElse(false)) {
                    if (type instanceof ClassOrInterfaceDeclaration) {
                        return SymbolReference.solved(JavaParserFacade.get(typeSolver).getTypeDeclaration((ClassOrInterfaceDeclaration) type));
                    }
                    
                    if (type instanceof AnnotationDeclaration) {
                        return SymbolReference.solved(new JavaParserAnnotationDeclaration((AnnotationDeclaration) type, typeSolver));
                    }
                    
                    if (type instanceof EnumDeclaration) {
                        return SymbolReference.solved(new JavaParserEnumDeclaration((EnumDeclaration) type, typeSolver));
                    }
                    throw new UnsupportedOperationException(type.getClass().getCanonicalName());
                }
            }

            // Look for member classes/interfaces of types in this compilation unit. For instance, if the given name is
            // "A.B", there may be a class or interface in this compilation unit called "A" which has another member
            // class or interface called "B". Since the type that we're looking for can be nested arbitrarily deeply
            // ("A.B.C.D"), we look for the outermost type ("A" in the previous example) first, then recursively invoke
            // this method for the remaining part of the given name.
            if (name.indexOf('.') > -1) {
                SymbolReference<ResolvedTypeDeclaration> ref = null;
                SymbolReference<ResolvedTypeDeclaration> outerMostRef =
                    solveType(name.substring(0, name.indexOf(".")));
                if (outerMostRef != null && outerMostRef.isSolved() &&
                    outerMostRef.getCorrespondingDeclaration() instanceof JavaParserClassDeclaration) {
                    ref = ((JavaParserClassDeclaration) outerMostRef.getCorrespondingDeclaration())
                        .solveType(name.substring(name.indexOf(".") + 1));
                } else if (outerMostRef != null && outerMostRef.isSolved() &&
                    outerMostRef.getCorrespondingDeclaration() instanceof JavaParserInterfaceDeclaration) {
                    ref = ((JavaParserInterfaceDeclaration) outerMostRef.getCorrespondingDeclaration())
                        .solveType(name.substring(name.indexOf(".") + 1));
                }
                if (ref != null && ref.isSolved()) {
                    return ref;
                }
            }
        }

        // Inspect imports for matches, prior to inspecting other classes within the package (per issue #1526)
        int dotPos = name.indexOf('.');
        String prefix = null;
        if (dotPos > -1) {
            prefix = name.substring(0, dotPos);
        }
        // look into single type imports
        for (ImportDeclaration importDecl : wrappedNode.getImports()) {
            if (!importDecl.isAsterisk()) {
                String qName = importDecl.getNameAsString();
                boolean defaultPackage = !importDecl.getName().getQualifier().isPresent();
                boolean found = !defaultPackage && importDecl.getName().getIdentifier().equals(name);
                if (!found && prefix != null) {
                    found = qName.endsWith("." + prefix);
                    if (found) {
                        qName = qName + name.substring(dotPos);
                    }
                }
                if (found) {
                    SymbolReference<ResolvedReferenceTypeDeclaration> ref = typeSolver.tryToSolveType(qName);
                    if (ref != null && ref.isSolved()) {
                        return SymbolReference.adapt(ref, ResolvedTypeDeclaration.class);
                    }
                }
            }
        }

        // Look in current package
        if (this.wrappedNode.getPackageDeclaration().isPresent()) {
            String qName = this.wrappedNode.getPackageDeclaration().get().getNameAsString() + "." + name;
            SymbolReference<ResolvedReferenceTypeDeclaration> ref = typeSolver.tryToSolveType(qName);
            if (ref != null && ref.isSolved()) {
                return SymbolReference.adapt(ref, ResolvedTypeDeclaration.class);
            }
        } else {
            // look for classes in the default package
            String qName = name;
            SymbolReference<ResolvedReferenceTypeDeclaration> ref = typeSolver.tryToSolveType(qName);
            if (ref != null && ref.isSolved()) {
                return SymbolReference.adapt(ref, ResolvedTypeDeclaration.class);
            }
        }

        // look into asterisk imports on demand
        for (ImportDeclaration importDecl : wrappedNode.getImports()) {
            if (importDecl.isAsterisk()) {
                String qName = importDecl.getNameAsString() + "." + name;
                SymbolReference<ResolvedReferenceTypeDeclaration> ref = typeSolver.tryToSolveType(qName);
                if (ref != null && ref.isSolved()) {
                    return SymbolReference.adapt(ref, ResolvedTypeDeclaration.class);
                }
            }
        }

        // Look in the java.lang package
        SymbolReference<ResolvedReferenceTypeDeclaration> ref = typeSolver.tryToSolveType(DEFAULT_PACKAGE+ "." + name);
        if (ref != null && ref.isSolved()) {
            return SymbolReference.adapt(ref, ResolvedTypeDeclaration.class);
        }


        if (isQualifiedName(name)) {
            return SymbolReference.adapt(typeSolver.tryToSolveType(name), ResolvedTypeDeclaration.class);
        }
        return SymbolReference.unsolved();
    }

    private String qName(ClassOrInterfaceType type) {
        if (type.getScope().isPresent()) {
            return qName(type.getScope().get()) + "." + type.getName().getId();
        }
        return type.getName().getId();
    }

    private String qName(Name name) {
        if (name.getQualifier().isPresent()) {
            return qName(name.getQualifier().get()) + "." + name.getId();
        }
        return name.getId();
    }

    private String toSimpleName(String qName) {
        String[] parts = qName.split("\\.");
        return parts[parts.length - 1];
    }

    private String packageName(String qName) {
        int lastDot = qName.lastIndexOf('.');
        if (lastDot == -1) {
            throw new UnsupportedOperationException();
        }
        return qName.substring(0, lastDot);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        for (ImportDeclaration importDecl : wrappedNode.getImports()) {
            if (importDecl.isStatic()) {
                if (importDecl.isAsterisk()) {
                    String importString = importDecl.getNameAsString();

                    if (this.wrappedNode.getPackageDeclaration().isPresent()
                        && this.wrappedNode.getPackageDeclaration().get().getName().getIdentifier().equals(packageName(importString))
                        && this.wrappedNode.getTypes().stream().anyMatch(it -> it.getName().getIdentifier().equals(toSimpleName(importString)))) {
                        // We are using a static import on a type defined in this file. It means the value was not found at
                        // a lower level so this will fail
                        return SymbolReference.unsolved();
                    }

                    ResolvedTypeDeclaration ref = typeSolver.solveType(importString);
                    // avoid infinite recursion
                    if (!isAncestorOf(ref)) {
                        SymbolReference<ResolvedMethodDeclaration> method = MethodResolutionLogic.solveMethodInType(ref, name, argumentsTypes, true);
                        if (method.isSolved()) {
                            return method;
                        }
                    }
                } else {
                    String qName = importDecl.getNameAsString();

                    if (qName.equals(name) || qName.endsWith("." + name)) {
                        String typeName = getType(qName);
                        ResolvedTypeDeclaration ref = typeSolver.solveType(typeName);
                        SymbolReference<ResolvedMethodDeclaration> method = MethodResolutionLogic.solveMethodInType(ref, name, argumentsTypes, true);
                        if (method.isSolved()) {
                            return method;
                        }
                        return SymbolReference.unsolved();
                    }
                }
            }
        }
        return SymbolReference.unsolved();
    }

    @Override
    public List<ResolvedFieldDeclaration> fieldsExposedToChild(Node child) {
        List<ResolvedFieldDeclaration> res = new LinkedList<>();
        // Consider the static imports for static fields
        for (ImportDeclaration importDeclaration : wrappedNode.getImports()) {
            if (importDeclaration.isStatic()) {
                Name typeNameAsNode = importDeclaration.isAsterisk() ? importDeclaration.getName() : importDeclaration.getName().getQualifier().get();
                String typeName = typeNameAsNode.asString();
                ResolvedReferenceTypeDeclaration typeDeclaration = typeSolver.solveType(typeName);
                res.addAll(typeDeclaration.getAllFields().stream()
                               .filter(f -> f.isStatic())
                               .filter(f -> importDeclaration.isAsterisk() || importDeclaration.getName().getIdentifier().equals(f.getName()))
                               .collect(Collectors.toList()));
            }
        }
        return res;
    }

    ///
    /// Private methods
    ///

    private String getType(String qName) {
        int index = qName.lastIndexOf('.');
        if (index == -1) {
            throw new UnsupportedOperationException();
        }
        String typeName = qName.substring(0, index);
        return typeName;
    }

    private String getMember(String qName) {
        int index = qName.lastIndexOf('.');
        if (index == -1) {
            throw new UnsupportedOperationException();
        }
        String memberName = qName.substring(index + 1);
        return memberName;
    }

    private boolean isAncestorOf(ResolvedTypeDeclaration descendant) {
        return descendant.toAst()
                .filter(node -> wrappedNode.isAncestorOf(node))
                .isPresent();
    }

}
