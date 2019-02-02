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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.UnsolvedSymbolException;
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
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;

import java.util.List;
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class SymbolSolver {

    private TypeSolver typeSolver;

    public SymbolSolver(TypeSolver typeSolver) {
        if (typeSolver == null) throw new IllegalArgumentException();

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

    public ResolvedTypeDeclaration solveType(com.github.javaparser.ast.type.Type type) {
        if (type instanceof ClassOrInterfaceType) {

            // FIXME should call typesolver here!

            String name = ((ClassOrInterfaceType) type).getName().getId();
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
