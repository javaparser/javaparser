/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.imports.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserAnnotationDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.MethodDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.ValueDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.resolution.MethodResolutionLogic;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;

import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class CompilationUnitContext extends AbstractJavaParserContext<CompilationUnit> {

    ///
    /// Static methods
    ///

    private static boolean isQualifiedName(String name) {
        return name.contains(".");
    }

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
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {

        // solve absolute references
        String itName = name;
        while (itName.contains(".")) {
            String typeName = getType(itName);
            String memberName = getMember(itName);
            SymbolReference<com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration> type = this.solveType(typeName, typeSolver);
            if (type.isSolved()) {
                return new SymbolSolver(typeSolver).solveSymbolInType(type.getCorrespondingDeclaration(), memberName);
            } else {
                itName = typeName;
            }
        }

        // Look among statically imported values
        if (wrappedNode.getImports() != null) {
            for (ImportDeclaration importDecl : wrappedNode.getImports()) {
                if (importDecl instanceof StaticImportOnDemandDeclaration) {
                    ClassOrInterfaceType classOrInterfaceType = ((StaticImportOnDemandDeclaration) importDecl).getType();
                    String qName = classOrInterfaceType.getName().getId();
                    com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration importedType = typeSolver.solveType(qName);
                    SymbolReference<? extends ValueDeclaration> ref = new SymbolSolver(typeSolver).solveSymbolInType(importedType, name);
                    if (ref.isSolved()) {
                        return ref;
                    }
                } else if (importDecl instanceof SingleStaticImportDeclaration) {
                    ClassOrInterfaceType classOrInterfaceType = ((SingleStaticImportDeclaration) importDecl).getType();
                    String typeName = classOrInterfaceType.getName().getId();

                    // split in field/method name and type name
                    String memberName = ((SingleStaticImportDeclaration) importDecl).getStaticMember();

                    if (memberName.equals(name)) {
                        com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration importedType = typeSolver.solveType(typeName);
                        return new SymbolSolver(typeSolver).solveSymbolInType(importedType, memberName);
                    }
                }
            }
        }

        return SymbolReference.unsolved(ValueDeclaration.class);
    }

    @Override
    public SymbolReference<com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        if (wrappedNode.getTypes() != null) {
            for (TypeDeclaration type : wrappedNode.getTypes()) {
                if (type.getName().getId().equals(name)) {
                    if (type instanceof ClassOrInterfaceDeclaration) {
                        return SymbolReference.solved(JavaParserFacade.get(typeSolver).getTypeDeclaration((ClassOrInterfaceDeclaration) type));
                    } else if (type instanceof AnnotationDeclaration) {
                        return SymbolReference.solved(new JavaParserAnnotationDeclaration((AnnotationDeclaration)type, typeSolver));
                    } else {
                        throw new UnsupportedOperationException(type.getClass().getCanonicalName());
                    }
                }
            }
        }

        if (wrappedNode.getImports() != null) {
            for (ImportDeclaration importDecl : wrappedNode.getImports()) {
                if (importDecl instanceof SingleTypeImportDeclaration) {
                    ClassOrInterfaceType importedType = ((SingleTypeImportDeclaration) importDecl).getType();
                    String qName = qName(importedType);
                    if (qName.equals(name) || qName.endsWith("." + name)) {
                        SymbolReference<com.github.javaparser.symbolsolver.model.declarations.ReferenceTypeDeclaration> ref = typeSolver.tryToSolveType(qName);
                        if (ref.isSolved()) {
                            return SymbolReference.adapt(ref, com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration.class);
                        }
                    }
                } else if (importDecl instanceof TypeImportOnDemandDeclaration) {
                    String packageName = ((TypeImportOnDemandDeclaration) importDecl).getName().getId();
                    String qName = packageName + "." + name;
                    SymbolReference<com.github.javaparser.symbolsolver.model.declarations.ReferenceTypeDeclaration> ref = typeSolver.tryToSolveType(qName);
                    if (ref.isSolved()) {
                        return SymbolReference.adapt(ref, com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration.class);
                    }
                }
            }
        }

        // Look in current package
        if (this.wrappedNode.getPackage().isPresent()) {
            String qName = this.wrappedNode.getPackage().get().getName().toString() + "." + name;
            SymbolReference<com.github.javaparser.symbolsolver.model.declarations.ReferenceTypeDeclaration> ref = typeSolver.tryToSolveType(qName);
            if (ref.isSolved()) {
                return SymbolReference.adapt(ref, com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration.class);
            }
        }

        // Look in the java.lang package
        SymbolReference<com.github.javaparser.symbolsolver.model.declarations.ReferenceTypeDeclaration> ref = typeSolver.tryToSolveType("java.lang." + name);
        if (ref.isSolved()) {
            return SymbolReference.adapt(ref, com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration.class);
        }

        // DO NOT look for absolute name if this name is not qualified: you cannot import classes from the default package
        if (isQualifiedName(name)) {
            return SymbolReference.adapt(typeSolver.tryToSolveType(name), com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration.class);
        } else {
            return SymbolReference.unsolved(com.github.javaparser.symbolsolver.model.declarations.ReferenceTypeDeclaration.class);
        }
    }

    private String qName(ClassOrInterfaceType type) {
        if (type.getScope().isPresent()) {
            return qName(type.getScope().get()) + "." + type.getName().getId();
        } else {
            return type.getName().getId();
        }
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> argumentsTypes, TypeSolver typeSolver) {
        for (ImportDeclaration importDecl : wrappedNode.getImports()) {
            if (importDecl instanceof StaticImportOnDemandDeclaration) {
                StaticImportOnDemandDeclaration staticImportOnDemandDeclaration = (StaticImportOnDemandDeclaration) importDecl;

                String qName = staticImportOnDemandDeclaration.getType().getName().getId();
                com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration ref = typeSolver.solveType(qName);
                SymbolReference<MethodDeclaration> method = MethodResolutionLogic.solveMethodInType(ref, name, argumentsTypes, typeSolver);
                if (method.isSolved()) {
                    return method;
                }
            } else if (importDecl instanceof SingleStaticImportDeclaration) {
                SingleStaticImportDeclaration staticImportOnDemandDeclaration = (SingleStaticImportDeclaration) importDecl;

                String importedTypeName = staticImportOnDemandDeclaration.getType().getNameAsString();
                String qName = importedTypeName + "." + staticImportOnDemandDeclaration.getStaticMember();

                if (qName.equals(name) || qName.endsWith("." + name)) {
                    String typeName = getType(qName);
                    com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration ref = typeSolver.solveType(typeName);
                    SymbolReference<MethodDeclaration> method = MethodResolutionLogic.solveMethodInType(ref, name, argumentsTypes, typeSolver);
                    if (method.isSolved()) {
                        return method;
                    }
                }
            }
        }
        return SymbolReference.unsolved(MethodDeclaration.class);
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
}
