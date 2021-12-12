package com.github.javaparser.ast.jml.clauses;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (12/12/21)
 */
public class JmlOldClause extends JmlClause {
    /* private SimpleName name;
    @OptionalProperty
    @NonEmptyProperty
    private Expression initializer;
    private Type type; */


    private VariableDeclarationExpr declarations;

    @AllFieldsConstructor
    public JmlOldClause(VariableDeclarationExpr declarations) {
        this(null, declarations);
    }

    public JmlOldClause(TokenRange range, VariableDeclarationExpr declarations) {
        super(range);
        this.declarations = declarations;
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return null;
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {

    }
}
