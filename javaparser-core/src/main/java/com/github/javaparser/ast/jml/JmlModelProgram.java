package com.github.javaparser.ast.jml;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.jml.clauses.JmlContracts;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.OptionalProperty;

import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (12/14/21)
 */
public class JmlModelProgram extends Node implements NodeWithModifiers<JmlModelProgram>,
        NodeWithAnnotations<JmlModelProgram>,
        NodeWithContracts<JmlModelProgram> {

    private Modifier modifiers;
    @OptionalProperty
    private NodeList<JmlContracts> contracts;
    private NodeList<AnnotationExpr> annotations;
    private NodeList<Statement> statements;

    public JmlModelProgram(TokenRange tokenRange) {
        this(null, new NodeList<>(), new NodeList<>(), null, new NodeList<>());
    }

    @AllFieldsConstructor
    public JmlModelProgram(NodeList<Modifier> modifiers, NodeList<AnnotationExpr> annotations, JmlContract contracts, NodeList<Statement> statements) {
        this(null, modifiers, annotations, contracts, statements);
    }

    public JmlModelProgram(TokenRange range, NodeList<Modifier> modifiers, NodeList<AnnotationExpr> annotations, JmlContract contracts, NodeList<Statement> statements) {
        super(range);

    }


    @Override

    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return null;
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {

    }

    @Override
    public Optional<NodeList<JmlContracts>> getContracts() {
        return Optional.of(contracts);
    }

    @Override
    public JmlModelProgram setContracts(NodeList<JmlContracts> contracts) {
        return null;
    }

    @Override
    public NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    @Override
    public JmlModelProgram setAnnotations(NodeList<AnnotationExpr> annotations) {
        return null;
    }

    @Override
    public NodeList<Modifier> getModifiers() {
        return null;
    }

    @Override
    public JmlModelProgram setModifiers(NodeList<Modifier> modifiers) {
        return null;
    }
}
