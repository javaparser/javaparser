package com.github.javaparser.resolution.declarations;

import com.github.javaparser.ast.Node;

import java.util.Optional;

/**
 * A declaration that can be potentially associated with an AST node.
 * @param <N> type of AST Node that can be associated
 */
public interface AssociableToAST<N extends Node> {

    /**
     * If the declaration is associated to an AST node return it, otherwise it return empty.
     * Declaration based on source code have an AST node associated while others don't. Example
     * of other declarations are declarations coming from reflection or JARs.
     *
     * You may wonder how this method is different from the various getWrappedNode.
     * The difference is that toAst is present in all Resolved* declarations (such as
     * ResolvedAnnotationDeclaration), while getWrappedNode is present
     * only on the subclasses of the Resolved* declarations that derive from JP AST nodes (such as
     * JavaParserClassDeclaration). Therefore one
     * which has a Resolved* declaration need to do a downcast before being able to use getWrappedNode.
     *
     * Now, this means that toAst could potentially replace getWrappedNode (but not the other way around!).
     * However toAst return an Optional, which is less convenient than getting the direct node. Also,
     * toAst sometimes have to return a more generic node. This is the case for subclasses of
     * ResolvedClassDeclaration. In those cases toAst return a Node. Why? Because both anonymous
     * class declarations and standard class declarations are subclasses of that. In one case the
     * underlying AST node is an ObjectCreationExpr, while in the other case it is ClassOrInterfaceDeclaration.
     * In these cases getWrappedNode is particularly nice because it returns the right type of AST node,
     * not just a Node.
     */
    default Optional<N> toAst() {
        throw new UnsupportedOperationException();
    }
}
