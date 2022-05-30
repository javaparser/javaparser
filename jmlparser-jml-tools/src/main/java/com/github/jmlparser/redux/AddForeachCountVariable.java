package com.github.jmlparser.redux;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.jml.stmt.JmlGhostStmt;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ForEachStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.PrimitiveType;

/**
 * @author Alexander Weigl
 * @version 1 (08.02.22)
 */
public class AddForeachCountVariable {
    public static final String VARIABLE_NAME_COUNT = "\\count";

    public static void addCountVariableInForeach(ForEachStmt forEachStmt) {
        BlockStmt stmt = new BlockStmt();
        forEachStmt.replace(stmt);
        VariableDeclarationExpr vdecl = new VariableDeclarationExpr(PrimitiveType.intType(), VARIABLE_NAME_COUNT);
        JmlGhostStmt decl = new JmlGhostStmt(new NodeList<>(), new ExpressionStmt(vdecl));
        stmt.addStatement(decl);
        stmt.addStatement(forEachStmt);
        Statement loopBody = forEachStmt.getBody();
        final UnaryExpr increment = new UnaryExpr(new NameExpr(VARIABLE_NAME_COUNT), UnaryExpr.Operator.PREFIX_INCREMENT);
        if (loopBody.isBlockStmt()) {
            ((BlockStmt) loopBody).addStatement(0, increment);
        } else {
            BlockStmt newLoopBody = new BlockStmt();
            loopBody.replace(newLoopBody);
            newLoopBody.addStatement(increment);
            newLoopBody.addStatement(loopBody);
        }
    }

}
