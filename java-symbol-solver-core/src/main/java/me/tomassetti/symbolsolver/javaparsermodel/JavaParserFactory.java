package me.tomassetti.symbolsolver.javaparsermodel;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.*;
import me.tomassetti.symbolsolver.javaparsermodel.contexts.*;
import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.SymbolDeclarator;
import me.tomassetti.symbolsolver.javaparsermodel.declarators.FieldSymbolDeclarator;
import me.tomassetti.symbolsolver.javaparsermodel.declarators.NoSymbolDeclarator;
import me.tomassetti.symbolsolver.javaparsermodel.declarators.ParameterSymbolDeclarator;
import me.tomassetti.symbolsolver.javaparsermodel.declarators.VariableSymbolDeclarator;

public class JavaParserFactory {

    public static Context getContext(Node node, TypeSolver typeSolver) {
        if (node == null) {
            return null;
        } else if (node instanceof CompilationUnit) {
            return new CompilationUnitContext((CompilationUnit) node, typeSolver);
        } else if (node instanceof ForeachStmt) {
            return new ForechStatementContext((ForeachStmt) node, typeSolver);
        } else if (node instanceof ForStmt) {
            return new ForStatementContext((ForStmt) node, typeSolver);
        } else if (node instanceof LambdaExpr) {
            return new LambdaExprContext((LambdaExpr) node, typeSolver);
        } else if (node instanceof MethodDeclaration) {
            return new MethodContext((MethodDeclaration) node, typeSolver);
        } else if (node instanceof ConstructorDeclaration) {
            return new ConstructorContext((ConstructorDeclaration) node, typeSolver);
        } else if (node instanceof ClassOrInterfaceDeclaration) {
            return new ClassOrInterfaceDeclarationContext((ClassOrInterfaceDeclaration) node, typeSolver);
        } else if (node instanceof MethodCallExpr) {
            return new MethodCallExprContext((MethodCallExpr) node, typeSolver);
        } else if (node instanceof EnumDeclaration) {
            return new EnumDeclarationContext((EnumDeclaration) node, typeSolver);
        } else if (node instanceof FieldAccessExpr) {
            return new FieldAccessContext((FieldAccessExpr) node, typeSolver);
        } else if (node instanceof SwitchEntryStmt) {
            return new SwitchEntryContext((SwitchEntryStmt) node, typeSolver);
        } else if (node instanceof Statement) {
            return new StatementContext((Statement) node, typeSolver);
        } else {
            return getContext(node.getParentNode(), typeSolver);
        }
    }

    public static SymbolDeclarator getSymbolDeclarator(Node node, TypeSolver typeSolver) {
        if (node instanceof FieldDeclaration) {
            return new FieldSymbolDeclarator((FieldDeclaration) node, typeSolver);
        } else if (node instanceof Parameter) {
            return new ParameterSymbolDeclarator((Parameter) node, typeSolver);
        } else if (node instanceof ExpressionStmt) {
            ExpressionStmt expressionStmt = (ExpressionStmt) node;
            if (expressionStmt.getExpression() instanceof VariableDeclarationExpr) {
                return new VariableSymbolDeclarator((VariableDeclarationExpr) (expressionStmt.getExpression()), typeSolver);
            } else {
                return new NoSymbolDeclarator(node, typeSolver);
            }
        } else if (node instanceof IfStmt) {
            return new NoSymbolDeclarator(node, typeSolver);
        } else if (node instanceof ForeachStmt) {
            ForeachStmt foreachStmt = (ForeachStmt) node;
            return new VariableSymbolDeclarator((VariableDeclarationExpr) (foreachStmt.getVariable()), typeSolver);
        } else {
            return new NoSymbolDeclarator(node, typeSolver);
        }
    }

}
