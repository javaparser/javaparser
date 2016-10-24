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

import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserInterfaceDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserMethodDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;
import com.github.javaparser.symbolsolver.model.declarations.AccessLevel;
import com.github.javaparser.symbolsolver.model.declarations.MethodDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.ValueDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.model.typesystem.TypeVariable;
import com.github.javaparser.symbolsolver.resolution.MethodResolutionLogic;
import com.github.javaparser.symbolsolver.resolution.SymbolDeclarator;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class ClassOrInterfaceDeclarationContext extends AbstractJavaParserContext<ClassOrInterfaceDeclaration> {

    public ClassOrInterfaceDeclarationContext(ClassOrInterfaceDeclaration wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        if (typeSolver == null) throw new IllegalArgumentException();

        // first among declared fields
        for (BodyDeclaration member : wrappedNode.getMembers()) {
            if (member instanceof FieldDeclaration) {
                SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(member, typeSolver);
                SymbolReference ref = solveWith(symbolDeclarator, name);
                if (ref.isSolved()) {
                    return ref;
                }
            }
        }

        // then among inherited fields
        for (ReferenceType ancestor : getDeclaration().getAncestors()) {
            SymbolReference ref = new SymbolSolver(typeSolver).solveSymbolInType(ancestor.getTypeDeclaration(), name);
            if (ref.isSolved() && ref.getCorrespondingDeclaration().asField().accessLevel() != AccessLevel.PRIVATE) {
                return ref;
            }
        }

        // then to parent
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        if (typeSolver == null) throw new IllegalArgumentException();

        // first among declared fields
        for (BodyDeclaration member : wrappedNode.getMembers()) {
            if (member instanceof FieldDeclaration) {
                SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(member, typeSolver);
                Optional<Value> ref = solveWithAsValue(symbolDeclarator, name, typeSolver);
                if (ref.isPresent()) {
                    return ref;
                }
            }
        }

        // then among inherited fields
        for (ReferenceType ancestor : getDeclaration().getAncestors()) {
            Optional<Value> ref = ContextHelper.getContext(ancestor.getTypeDeclaration()).solveSymbolAsValue(name, typeSolver);
            if (ref.isPresent()) {
                return ref;
            }
        }

        // then to parent
        return getParent().solveSymbolAsValue(name, typeSolver);
    }

    @Override
    public Optional<Type> solveGenericType(String name, TypeSolver typeSolver) {
        for (com.github.javaparser.ast.type.TypeParameter tp : wrappedNode.getTypeParameters()) {
            if (tp.getName().equals(name)) {
                return Optional.of(new TypeVariable(new JavaParserTypeParameter(tp, typeSolver)));
            }
        }
        return getParent().solveGenericType(name, typeSolver);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        SymbolReference<TypeDeclaration> ref = new SymbolSolver(typeSolver).solveTypeInType(getDeclaration(), name);
        if (ref.isSolved()) {
            return ref;
        }
        return getParent().solveType(name, typeSolver);
    }

    private TypeDeclaration getDeclaration() {
        if (this.wrappedNode.isInterface()) {
            return new JavaParserInterfaceDeclaration(this.wrappedNode, typeSolver);
        } else {
            return new JavaParserClassDeclaration(this.wrappedNode, typeSolver);
        }
    }

    public List<MethodDeclaration> methodsByName(String name) {
        List<MethodDeclaration> candidateMethods = new ArrayList<>();
        for (BodyDeclaration member : this.wrappedNode.getMembers()) {
            if (member instanceof com.github.javaparser.ast.body.MethodDeclaration) {
                com.github.javaparser.ast.body.MethodDeclaration method = (com.github.javaparser.ast.body.MethodDeclaration) member;
                if (method.getName().equals(name)) {
                    candidateMethods.add(new JavaParserMethodDeclaration(method, typeSolver));
                }
            }
        }
        return candidateMethods;
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> argumentsTypes, TypeSolver typeSolver) {
        List<MethodDeclaration> candidateMethods = methodsByName(name);

        if (this.wrappedNode.getExtends() != null && !this.wrappedNode.getExtends().isEmpty()) {
            if (this.wrappedNode.getExtends().size() > 1) {
                throw new UnsupportedOperationException();
            }
            String superclassName = this.wrappedNode.getExtends().get(0).getName();
            SymbolReference<TypeDeclaration> superclass = solveType(superclassName, typeSolver);
            if (!superclass.isSolved()) {
                throw new UnsolvedSymbolException(this, superclassName);
            }
            SymbolReference<MethodDeclaration> res = MethodResolutionLogic.solveMethodInType(superclass.getCorrespondingDeclaration(), name, argumentsTypes, typeSolver);
            if (res.isSolved()) {
                candidateMethods.add(res.getCorrespondingDeclaration());
            }
        } else {
            String superclassName = "java.lang.Object";
            SymbolReference<TypeDeclaration> superclass = solveType(superclassName, typeSolver);
            if (!superclass.isSolved()) {
                throw new UnsolvedSymbolException(this, superclassName);
            }
            SymbolReference<MethodDeclaration> res = MethodResolutionLogic.solveMethodInType(superclass.getCorrespondingDeclaration(), name, argumentsTypes, typeSolver);
            if (res.isSolved()) {
                candidateMethods.add(res.getCorrespondingDeclaration());
            }
        }

        // Consider only default methods from interfaces
        for (ClassOrInterfaceType implemented : this.wrappedNode.getImplements()) {
            String interfaceClassName = implemented.getName();
            SymbolReference<TypeDeclaration> superclass = solveType(interfaceClassName, typeSolver);
            if (!superclass.isSolved()) {
                throw new UnsolvedSymbolException(this, interfaceClassName);
            }
            SymbolReference<MethodDeclaration> res = MethodResolutionLogic.solveMethodInType(superclass.getCorrespondingDeclaration(), name, argumentsTypes, typeSolver);
            if (res.isSolved() && res.getCorrespondingDeclaration().isDefaultMethod()) {
                candidateMethods.add(res.getCorrespondingDeclaration());
            }
        }

        // We want to avoid infinite recursion when a class is using its own method
        // see issue #75
        if (candidateMethods.isEmpty()) {
            SymbolReference<MethodDeclaration> parentSolution = getParent().solveMethod(name, argumentsTypes, typeSolver);
            if (parentSolution.isSolved()) {
                candidateMethods.add(parentSolution.getCorrespondingDeclaration());
            }
        }

        return MethodResolutionLogic.findMostApplicable(candidateMethods, name, argumentsTypes, typeSolver);
    }
}
