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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.LazyType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;

import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class JavaParserInterfaceDeclaration extends AbstractTypeDeclaration implements ResolvedInterfaceDeclaration {

    private TypeSolver typeSolver;
    private ClassOrInterfaceDeclaration wrappedNode;
    private JavaParserTypeAdapter<ClassOrInterfaceDeclaration> javaParserTypeAdapter;

    public JavaParserInterfaceDeclaration(ClassOrInterfaceDeclaration wrappedNode, TypeSolver typeSolver) {
        if (!wrappedNode.isInterface()) {
            throw new IllegalArgumentException();
        }
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
        this.javaParserTypeAdapter = new JavaParserTypeAdapter<>(wrappedNode, typeSolver);
    }

    @Override
    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        Set<ResolvedMethodDeclaration> methods = new HashSet<>();
        for (BodyDeclaration<?> member : wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.MethodDeclaration) {
                methods.add(new JavaParserMethodDeclaration((com.github.javaparser.ast.body.MethodDeclaration) member, typeSolver));
            }
        }
        return methods;
    }

    public Context getContext() {
        return JavaParserFactory.getContext(wrappedNode, typeSolver);
    }

    public ResolvedType getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        JavaParserInterfaceDeclaration that = (JavaParserInterfaceDeclaration) o;

        if (!wrappedNode.equals(that.wrappedNode)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return wrappedNode.hashCode();
    }

    @Override
    public String getName() {
        return wrappedNode.getName().getId();
    }

    @Override
    public ResolvedInterfaceDeclaration asInterface() {
        return this;
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        for (AnnotationExpr annotationExpr : wrappedNode.getAnnotations()) {
            if (solveType(annotationExpr.getName().getId(), typeSolver).getCorrespondingDeclaration().getQualifiedName().equals(canonicalName)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean isInterface() {
        return true;
    }

    @Override
    public List<ResolvedReferenceType> getInterfacesExtended() {
        List<ResolvedReferenceType> interfaces = new ArrayList<>();
        if (wrappedNode.getImplementedTypes() != null) {
            for (ClassOrInterfaceType t : wrappedNode.getImplementedTypes()) {
                interfaces.add(new ReferenceTypeImpl(solveType(t.getName().getId(), typeSolver).getCorrespondingDeclaration().asInterface(), typeSolver));
            }
        }
        return interfaces;
    }

    @Override
    public String getPackageName() {
        return javaParserTypeAdapter.getPackageName();
    }

    @Override
    public String getClassName() {
        return javaParserTypeAdapter.getClassName();
    }

    @Override
    public String getQualifiedName() {
        return javaParserTypeAdapter.getQualifiedName();
    }

    @Override
    public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        return javaParserTypeAdapter.isAssignableBy(other);
    }

    @Override
    public boolean isAssignableBy(ResolvedType type) {
        return javaParserTypeAdapter.isAssignableBy(type);
    }

    @Override
    public boolean canBeAssignedTo(ResolvedReferenceTypeDeclaration other) {
        // TODO consider generic types
        if (this.getQualifiedName().equals(other.getQualifiedName())) {
            return true;
        }
        if (this.wrappedNode.getExtendedTypes() != null) {
            for (ClassOrInterfaceType type : wrappedNode.getExtendedTypes()) {
                ResolvedReferenceTypeDeclaration ancestor = (ResolvedReferenceTypeDeclaration) new SymbolSolver(typeSolver).solveType(type);
                if (ancestor.canBeAssignedTo(other)) {
                    return true;
                }
            }
        }

        if (this.wrappedNode.getImplementedTypes() != null) {
            for (ClassOrInterfaceType type : wrappedNode.getImplementedTypes()) {
                ResolvedReferenceTypeDeclaration ancestor = (ResolvedReferenceTypeDeclaration) new SymbolSolver(typeSolver).solveType(type);
                if (ancestor.canBeAssignedTo(other)) {
                    return true;
                }
            }
        }

        return false;
    }

    @Override
    public boolean isTypeParameter() {
        return false;
    }

    @Override
    public List<ResolvedFieldDeclaration> getAllFields() {
        List<ResolvedFieldDeclaration> fields = javaParserTypeAdapter.getFieldsForDeclaredVariables();
        
        getAncestors().forEach(ancestor -> ancestor.getTypeDeclaration().getAllFields().forEach(f -> {
            fields.add(new ResolvedFieldDeclaration() {
                
                @Override
                public AccessSpecifier accessSpecifier() {
                    return f.accessSpecifier();
                }
                
                @Override
                public String getName() {
                    return f.getName();
                }
                
                @Override
                public ResolvedType getType() {
                    return ancestor.useThisTypeParametersOnTheGivenType(f.getType());
                }
                
                @Override
                public boolean isStatic() {
                    return f.isStatic();
                }
                
                @Override
                public ResolvedTypeDeclaration declaringType() {
                    return f.declaringType();
                }
            });
        }));
        
        return fields;
    }


    @Override
    public String toString() {
        return "JavaParserInterfaceDeclaration{" +
                "wrappedNode=" + wrappedNode +
                '}';
    }

    @Deprecated
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        if (this.wrappedNode.getName().getId().equals(name)) {
            return SymbolReference.solved(this);
        }
        SymbolReference<ResolvedTypeDeclaration> ref = javaParserTypeAdapter.solveType(name, typeSolver);
        if (ref.isSolved()) {
            return ref;
        }

        String prefix = wrappedNode.getName() + ".";
        if (name.startsWith(prefix) && name.length() > prefix.length()) {
            return new JavaParserInterfaceDeclaration(this.wrappedNode, typeSolver).solveType(name.substring(prefix.length()), typeSolver);
        }

        return getContext().getParent().solveType(name, typeSolver);
    }

    @Override
    public List<ResolvedReferenceType> getAncestors() {
        List<ResolvedReferenceType> ancestors = new ArrayList<>();
        if (wrappedNode.getExtendedTypes() != null) {
            for (ClassOrInterfaceType extended : wrappedNode.getExtendedTypes()) {
                ancestors.add(toReferenceType(extended));
            }
        }
        if (wrappedNode.getImplementedTypes() != null) {
            for (ClassOrInterfaceType implemented : wrappedNode.getImplementedTypes()) {
                ancestors.add(toReferenceType(implemented));
            }
        }
        return ancestors;
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        if (this.wrappedNode.getTypeParameters() == null) {
            return Collections.emptyList();
        } else {
            return this.wrappedNode.getTypeParameters().stream().map(
                    (tp) -> new JavaParserTypeParameter(tp, typeSolver)
            ).collect(Collectors.toList());
        }
    }

    /**
     * Returns the JavaParser node associated with this JavaParserInterfaceDeclaration.
     *
     * @return A visitable JavaParser node wrapped by this object.
     */
    public ClassOrInterfaceDeclaration getWrappedNode() {
        return wrappedNode;
    }

    @Override
    public AccessSpecifier accessSpecifier() {
        return Helper.toAccessLevel(wrappedNode.getModifiers());
    }

    @Override
    public Set<ResolvedReferenceTypeDeclaration> internalTypes() {
        Set<ResolvedReferenceTypeDeclaration> res = new HashSet<>();
        for (BodyDeclaration<?> member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.TypeDeclaration) {
                res.add(JavaParserFacade.get(typeSolver).getTypeDeclaration((com.github.javaparser.ast.body.TypeDeclaration)member));
            }
        }
        return res;
    }

    @Override
    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        return javaParserTypeAdapter.containerType();
    }

    ///
    /// Private methods
    ///

    private ResolvedReferenceType toReferenceType(ClassOrInterfaceType classOrInterfaceType) {
        SymbolReference<? extends ResolvedTypeDeclaration> ref = null;
        if (classOrInterfaceType.toString().indexOf('.') > -1) {
            ref = typeSolver.tryToSolveType(classOrInterfaceType.toString());
        }
        if (ref == null || !ref.isSolved()) {
            ref = solveType(classOrInterfaceType.toString(), typeSolver);
        }
        if (!ref.isSolved()) {
            ref = solveType(classOrInterfaceType.getName().getId(), typeSolver);
        }
        if (!ref.isSolved()) {
            throw new UnsolvedSymbolException(classOrInterfaceType.getName().getId());
        }
        if (!classOrInterfaceType.getTypeArguments().isPresent()) {
            return new ReferenceTypeImpl(ref.getCorrespondingDeclaration().asReferenceType(), typeSolver);
        }
        List<ResolvedType> superClassTypeParameters = classOrInterfaceType.getTypeArguments().get()
                .stream().map(ta -> new LazyType(v -> JavaParserFacade.get(typeSolver).convert(ta, ta)))
                .collect(Collectors.toList());
        return new ReferenceTypeImpl(ref.getCorrespondingDeclaration().asReferenceType(), superClassTypeParameters, typeSolver);
    }
}
