/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithParameters;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.observer.AstObserverAdapter;
import com.github.javaparser.ast.observer.Observable;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.resolution.SymbolDeclarator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.Value;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public abstract class AbstractMethodLikeDeclarationContext<
                T extends Node & NodeWithParameters<T> & NodeWithTypeParameters<T>>
        extends AbstractJavaParserContext<T> {

    /**
     * The types declared inside a method or constructor, kept on its node: every type name looked up inside it is
     * checked against them, and finding them means walking the whole declaration.
     */
    private static final DataKey<LocalTypes> LOCAL_TYPES = new DataKey<LocalTypes>() {};

    public AbstractMethodLikeDeclarationContext(T wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public final SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            SymbolReference<? extends ResolvedValueDeclaration> symbolReference =
                    AbstractJavaParserContext.solveWith(sb, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return solveSymbolInParentContext(name);
    }

    @Override
    public final Optional<ResolvedType> solveGenericType(String name) {
        // First check if the method-like declaration has type parameters defined.
        // For example: {@code public <T> boolean containsAll(Collection<T> c);}
        for (TypeParameter tp : wrappedNode.getTypeParameters()) {
            if (tp.getName().getId().equals(name)) {
                return Optional.of(new ResolvedTypeVariable(new JavaParserTypeParameter(tp, typeSolver)));
            }
        }

        // If no generic types on the method declaration, continue to solve elsewhere as usual.
        return solveGenericTypeInParentContext(name);
    }

    @Override
    public final Optional<Value> solveSymbolAsValue(String name) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            Optional<Value> symbolReference = solveWithAsValue(sb, name);
            if (symbolReference.isPresent()) {
                // Perform parameter type substitution as needed
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return solveSymbolAsValueInParentContext(name);
    }

    @Override
    public final SymbolReference<ResolvedTypeDeclaration> solveType(String name, List<ResolvedType> typeArguments) {
        // TODO: Is null check required?
        if (wrappedNode.getTypeParameters() != null) {
            for (TypeParameter tp : wrappedNode.getTypeParameters()) {
                if (tp.getName().getId().equals(name)) {
                    return SymbolReference.solved(new JavaParserTypeParameter(tp, typeSolver));
                }
            }
        }

        // Local types
        for (TypeDeclaration<?> localType : localTypes()) {
            if (localType.getName().getId().equals(name)) {
                return SymbolReference.solved(JavaParserFacade.get(typeSolver).getTypeDeclaration(localType));
            }
            if (name.startsWith(String.format("%s.", localType.getName()))) {
                return JavaParserFactory.getContext(localType, typeSolver)
                        .solveType(name.substring(localType.getName().getId().length() + 1));
            }
        }

        return solveTypeInParentContext(name, typeArguments);
    }

    /**
     * Keep the types in traversal order until the method or constructor is edited.
     */
    private List<TypeDeclaration> localTypes() {
        Optional<LocalTypes> kept = wrappedNode.findData(LOCAL_TYPES);
        // A clone carries the data of the node it was cloned from, but its local types are its own nodes.
        LocalTypes localTypes;
        if (kept.isPresent() && kept.get().declaration == wrappedNode) {
            localTypes = kept.get();
        } else {
            localTypes = new LocalTypes(wrappedNode);
            wrappedNode.setData(LOCAL_TYPES, localTypes);
        }
        return localTypes.getTypes();
    }

    @Override
    public final SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        // TODO: Document why staticOnly is forced to be false.
        return solveMethodInParentContext(name, argumentsTypes, false);
    }

    /**
     * Watch the nodes and lists used to build the cache. Any edit clears it; the next lookup builds a fresh list
     * and watches the new subtree. New nodes do not need observers until then, because the cache is already cleared.
     */
    private static final class LocalTypes extends AstObserverAdapter {

        private final Node declaration;

        private final List<Observable> observed = new ArrayList<>();

        private List<TypeDeclaration> types;

        private LocalTypes(Node declaration) {
            this.declaration = declaration;
        }

        private List<TypeDeclaration> getTypes() {
            if (types == null) {
                // Remove old registrations, including those on nodes that have since been removed or moved.
                observed.forEach(node -> node.unregister(this));
                observed.clear();
                types = declaration.findAll(TypeDeclaration.class);
                declaration.walk(node -> {
                    observe(node);
                    // Lists report additions and removals separately from their parent node.
                    for (PropertyMetaModel property : node.getMetaModel().getAllPropertyMetaModels()) {
                        if (property.isNodeList()) {
                            NodeList<?> list = (NodeList<?>) property.getValue(node);
                            if (list != null) {
                                observe(list);
                            }
                        }
                    }
                });
            }
            return types;
        }

        private void observe(Observable node) {
            node.register(this);
            observed.add(node);
        }

        @Override
        public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
            // Notifications arrive before the edit, so wait until the next lookup to rebuild the list.
            types = null;
        }

        @Override
        public void parentChange(Node observedNode, Node previousParent, Node newParent) {
            types = null;
        }

        @Override
        public void listChange(NodeList<?> observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
            types = null;
        }

        @Override
        public void listReplacement(NodeList<?> observedNode, int index, Node oldNode, Node newNode) {
            types = null;
        }
    }
}
