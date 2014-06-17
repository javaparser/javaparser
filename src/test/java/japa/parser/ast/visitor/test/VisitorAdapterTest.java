package japa.parser.ast.visitor.test;

import japa.parser.ast.body.VariableDeclarator;
import japa.parser.ast.body.VariableDeclaratorId;
import japa.parser.ast.expr.VariableDeclarationExpr;
import japa.parser.ast.stmt.BlockStmt;
import japa.parser.ast.stmt.TryStmt;
import japa.parser.ast.type.ClassOrInterfaceType;

import java.util.List;

import static java.util.Collections.singletonList;

abstract class VisitorAdapterTest {

    protected static TryStmt givenTryStmtWithResource(String resourceName) {
        ClassOrInterfaceType closeableType = new ClassOrInterfaceType(new ClassOrInterfaceType(new ClassOrInterfaceType(
                "java"), "io"), "Closeable");
        List<VariableDeclarator> variableDeclarators = singletonList(new VariableDeclarator(new VariableDeclaratorId(
                resourceName)));
        List<VariableDeclarationExpr> variableDeclarationExprs = singletonList(
                new VariableDeclarationExpr(closeableType, variableDeclarators));
        return new TryStmt(1, 1, 2, 80, variableDeclarationExprs, new BlockStmt(), null, null);
    }

}
