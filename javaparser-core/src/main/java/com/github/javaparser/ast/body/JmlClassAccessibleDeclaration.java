package com.github.javaparser.ast.body;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlClassAccessibleDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.Generated;

/**
 * @author Alexander Weigl
 * @version 1 (3/11/21)
 */
public class JmlClassAccessibleDeclaration extends JmlClassLevel implements NodeWithModifiers<JmlClassAccessibleDeclaration> {

    /*    private NodeList<Modifier> modifiers;
    private SimpleName id;
    private NodeList<Expression> expressions;
    private Expression measuredBy;
  */
    @AllFieldsConstructor
    public JmlClassAccessibleDeclaration() {
        //NodeList<Modifier> modifiers, SimpleName id,
        //NodeList<Expression> expressions, Expression measuredBy
        //this(null, modifiers, id, expressions, measuredBy);
        //setModifiers(modifiers);
        //setId(id);
        //setExpressions(expressions);
        //setMeasuredBy(measuredBy);
    }

    @Override
    public NodeList<Modifier> getModifiers() {
        return null;
    }

    @Override
    public JmlClassAccessibleDeclaration setModifiers(NodeList<Modifier> modifiers) {
        return null;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlClassAccessibleDeclaration(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlClassAccessibleDeclaration clone() {
        return (JmlClassAccessibleDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlClassAccessibleDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlClassAccessibleDeclarationMetaModel;
    }
}
