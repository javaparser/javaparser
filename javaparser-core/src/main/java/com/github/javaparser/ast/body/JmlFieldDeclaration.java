package com.github.javaparser.ast.body;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.type.Type;

/**
 * @author Alexander Weigl
 * @version 1 (3/11/21)
 */
public class JmlFieldDeclaration extends FieldDeclaration {

    public JmlFieldDeclaration() {
    }

    public JmlFieldDeclaration(NodeList<Modifier> modifiers, VariableDeclarator variable) {
        super(modifiers, variable);
    }

    public JmlFieldDeclaration(NodeList<Modifier> modifiers, NodeList<VariableDeclarator> variables) {
        super(modifiers, variables);
    }

    @AllFieldsConstructor
    public JmlFieldDeclaration(NodeList<Modifier> modifiers, NodeList<AnnotationExpr> annotations, NodeList<VariableDeclarator> variables) {
        super(modifiers, annotations, variables);
    }

    public JmlFieldDeclaration(TokenRange tokenRange, NodeList<Modifier> modifiers, NodeList<AnnotationExpr> annotations, NodeList<VariableDeclarator> variables) {
        super(tokenRange, modifiers, annotations, variables);
    }

    public JmlFieldDeclaration(NodeList<Modifier> modifiers, Type type, String name) {
        super(modifiers, type, name);
    }
}
