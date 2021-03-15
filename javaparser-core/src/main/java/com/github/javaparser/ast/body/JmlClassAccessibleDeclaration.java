package com.github.javaparser.ast.body;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (3/11/21)
 */
public class JmlClassAccessibleDeclaration extends JmlBodyDeclaration<JmlClassAccessibleDeclaration>
        implements NodeWithModifiers<JmlClassAccessibleDeclaration> {


/*    private NodeList<Modifier> modifiers;
    private SimpleName id;
    private NodeList<Expression> expressions;
    private Expression measuredBy;
  */


    @AllFieldsConstructor
    public JmlClassAccessibleDeclaration() {
        //NodeList<Modifier> modifiers, SimpleName id,
//                                         NodeList<Expression> expressions, Expression measuredBy
        //                                         this(null, modifiers, id, expressions, measuredBy);
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
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return null;
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {

    }
}
