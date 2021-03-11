package com.github.javaparser.ast.body;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (2/24/21)
 */
public abstract class JmlBodyDeclaration extends BodyDeclaration<JmlBodyDeclaration> implements Jmlish {
    @AllFieldsConstructor
    public JmlBodyDeclaration() {
        this(null);
    }

    public JmlBodyDeclaration(TokenRange tokenRange) {
        super(tokenRange);
    }
}
