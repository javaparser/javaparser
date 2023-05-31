package com.github.jmlparser.boogie;

import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.body.JmlClassExprDeclaration;
import com.github.javaparser.ast.jml.clauses.JmlMultiExprClause;
import com.github.javaparser.ast.jml.clauses.JmlSimpleExprClause;
import com.github.javaparser.ast.jml.expr.*;
import com.github.javaparser.ast.jml.stmt.JmlExpressionStmt;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;

/**
 * @author Alexander Weigl
 * @version 1 (23.04.23)
 */
public class BoogieExprTranslator extends GenericVisitorAdapter<String, Void> {
    @Override
    public String visit(ArrayAccessExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public String visit(ArrayCreationExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public String visit(ArrayInitializerExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public String visit(AssignExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public String visit(BinaryExpr n, Void arg) {
        return n.getLeft().accept(this, arg)
                + " " + n.getOperator().asString()
                + " " + n.getRight().accept(this, arg);
    }

    @Override
    public String visit(BooleanLiteralExpr n, Void arg) {
        return "" + n.getValue();
    }

    @Override
    public String visit(CastExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public String visit(CharLiteralExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public String visit(ClassExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public String visit(ConditionalExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public String visit(DoubleLiteralExpr n, Void arg) {
        return n.getValue() + "";
    }

    @Override
    public String visit(EnclosedExpr n, Void arg) {
        return "(" + n.getInner().accept(this, arg) + ")";
    }

    @Override
    public String visit(FieldAccessExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public String visit(InstanceOfExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public String visit(IntegerLiteralExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public String visit(LongLiteralExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public String visit(MarkerAnnotationExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public String visit(MethodCallExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public String visit(NameExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public String visit(NormalAnnotationExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(NullLiteralExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(ObjectCreationExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(SingleMemberAnnotationExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(StringLiteralExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(SuperExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(ThisExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(UnaryExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(VariableDeclarationExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(LambdaExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(MethodReferenceExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(TypeExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(SwitchExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(TextBlockLiteralExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(PatternExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(JmlExpressionStmt n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(JmlQuantifiedExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(JmlLabelExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(JmlLetExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(JmlMultiCompareExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(JmlSimpleExprClause n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(JmlClassExprDeclaration n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(JmlBinaryInfixExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(JmlTypeExpr n, Void arg) {
        super.visit(n, arg);
    }

    @Override
    public String visit(JmlMultiExprClause n, Void arg) {
        super.visit(n, arg);
    }
}
