/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution;

import java.util.List;
import java.util.Optional;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedEnumConstantDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserEnumDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserInterfaceDeclaration;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistClassDeclaration;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistEnumDeclaration;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistInterfaceDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionEnumDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;

/**
 * @author Federico Tomassetti
 */
public class SymbolSolver {

    private final TypeSolver typeSolver;

    public SymbolSolver(TypeSolver typeSolver) {
        if (typeSolver == null) {
            throw new IllegalArgumentException("Missing Parameter - Cannot initialise a SymbolSolver, without a way to solve types.");
        }

        this.typeSolver = typeSolver;
    }

    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name, Context context) {
        return context.solveSymbol(name);
    }

    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name, Node node) {
        return solveSymbol(name, JavaParserFactory.getContext(node, typeSolver));
    }

    public Optional<Value> solveSymbolAsValue(String name, Context context) {
        return context.solveSymbolAsValue(name);
    }

    public Optional<Value> solveSymbolAsValue(String name, Node node) {
        Context context = JavaParserFactory.getContext(node, typeSolver);
        return solveSymbolAsValue(name, context);
    }

    public SymbolReference<? extends ResolvedTypeDeclaration> solveType(String name, Context context) {
        return context.solveType(name);
    }

    public SymbolReference<? extends ResolvedTypeDeclaration> solveType(String name, Node node) {
        return solveType(name, JavaParserFactory.getContext(node, typeSolver));
    }

    public MethodUsage solveMethod(String methodName, List<ResolvedType> argumentsTypes, Context context) {
        SymbolReference<ResolvedMethodDeclaration> decl = context.solveMethod(methodName, argumentsTypes, false);
        if (!decl.isSolved()) {
            throw new UnsolvedSymbolException(context.toString(), methodName);
        }
        return new MethodUsage(decl.getCorrespondingDeclaration());
    }

    public MethodUsage solveMethod(String methodName, List<ResolvedType> argumentsTypes, Node node) {
        return solveMethod(methodName, argumentsTypes, JavaParserFactory.getContext(node, typeSolver));
    }

    public ResolvedTypeDeclaration solveType(Type type) {
        if (type instanceof ClassOrInterfaceType) {

            // FIXME should call typesolver here!

            String name = ((ClassOrInterfaceType) type).getNameWithScope();
            SymbolReference<ResolvedTypeDeclaration> ref = JavaParserFactory.getContext(type, typeSolver).solveType(name);
            if (!ref.isSolved()) {
                throw new UnsolvedSymbolException(JavaParserFactory.getContext(type, typeSolver).toString(), name);
            }
            return ref.getCorrespondingDeclaration();
        } else {
            throw new UnsupportedOperationException(type.getClass().getCanonicalName());
        }
    }

    public ResolvedType solveTypeUsage(String name, Context context) {
        Optional<ResolvedType> genericType = context.solveGenericType(name);
        if (genericType.isPresent()) {
            return genericType.get();
        }
        ResolvedReferenceTypeDeclaration typeDeclaration = typeSolver.solveType(name);
        return new ReferenceTypeImpl(typeDeclaration, typeSolver);
    }

    /**
     * Solve any possible visible symbols including: fields, internal types, type variables, the type itself or its
     * containers.
     * <p>
     * It should contain its own private fields but not inherited private fields.
     */
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbolInType(ResolvedTypeDeclaration typeDeclaration, String name) {
        if (typeDeclaration instanceof JavaParserClassDeclaration) {
            Context ctx = ((JavaParserClassDeclaration) typeDeclaration).getContext();
            return ctx.solveSymbol(name);
        }
        if (typeDeclaration instanceof JavaParserInterfaceDeclaration) {
            Context ctx = ((JavaParserInterfaceDeclaration) typeDeclaration).getContext();
            return ctx.solveSymbol(name);
        }
        if (typeDeclaration instanceof JavaParserEnumDeclaration) {
            Context ctx = ((JavaParserEnumDeclaration) typeDeclaration).getContext();
            return ctx.solveSymbol(name);
        }
        if (typeDeclaration instanceof ReflectionClassDeclaration) {
            return ((ReflectionClassDeclaration) typeDeclaration).solveSymbol(name, typeSolver);
        }
        if (typeDeclaration instanceof ReflectionInterfaceDeclaration) {
            return ((ReflectionInterfaceDeclaration) typeDeclaration).solveSymbol(name, typeSolver);
        }
        if (typeDeclaration instanceof ReflectionEnumDeclaration) {
            ResolvedEnumConstantDeclaration  red = ((ReflectionEnumDeclaration) typeDeclaration).getEnumConstant(name);
            return SymbolReference.solved(red);
        }
        if (typeDeclaration instanceof JavassistClassDeclaration) {
            return ((JavassistClassDeclaration) typeDeclaration).solveSymbol(name, typeSolver);
        }
        if (typeDeclaration instanceof JavassistEnumDeclaration) {
            return ((JavassistEnumDeclaration) typeDeclaration).solveSymbol(name, typeSolver);
        }
        if (typeDeclaration instanceof JavassistInterfaceDeclaration) {
            return ((JavassistInterfaceDeclaration) typeDeclaration).solveSymbol(name, typeSolver);
        }
        return SymbolReference.unsolved(ResolvedValueDeclaration.class);
    }

    /**
     * Try to solve a symbol just in the declaration, it does not delegate to the container.
     *
     * @deprecated Similarly to solveType this should eventually disappear as the symbol resolution logic should be more general
     * and do not be specific to JavaParser classes like in this case.
     */
    @Deprecated
    public SymbolReference<ResolvedTypeDeclaration> solveTypeInType(ResolvedTypeDeclaration typeDeclaration, String name) {
        if (typeDeclaration instanceof JavaParserClassDeclaration) {
            return ((JavaParserClassDeclaration) typeDeclaration).solveType(name);
        }
        if (typeDeclaration instanceof JavaParserInterfaceDeclaration) {
            return ((JavaParserInterfaceDeclaration) typeDeclaration).solveType(name);
        }
        return SymbolReference.unsolved(ResolvedReferenceTypeDeclaration.class);
    }
}
