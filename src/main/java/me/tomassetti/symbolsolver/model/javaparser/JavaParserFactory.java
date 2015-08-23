package me.tomassetti.symbolsolver.model.javaparser;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.SymbolDeclarator;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.javaparser.contexts.*;
import me.tomassetti.symbolsolver.model.javaparser.declarators.FieldSymbolDeclarator;
import me.tomassetti.symbolsolver.model.javaparser.declarators.NoSimboyDeclarator;
import me.tomassetti.symbolsolver.model.javaparser.declarators.ParameterSymbolDeclarator;
import me.tomassetti.symbolsolver.model.javaparser.declarators.VariableSymbolDeclarator;

/**
 * Created by federico on 28/07/15.
 */
public class JavaParserFactory {

    public static Context getContext(Node node){
        if (node == null) {
            return null;
        } else if (node instanceof CompilationUnit) {
            return new CompilationUnitContext((CompilationUnit)node);
        } else if (node instanceof Statement) {
            return new StatementContext((Statement) node);
        } else if (node instanceof LambdaExpr){
            return new LambdaExprContext((LambdaExpr) node);
        } else if (node instanceof MethodDeclaration) {
            return new MethodContext((MethodDeclaration)node);
        } else if (node instanceof ClassOrInterfaceDeclaration) {
            return new ClassOrInterfaceDeclarationContext((ClassOrInterfaceDeclaration)node);
        } else if (node instanceof MethodCallExpr) {
            return new MethodCallExprContext((MethodCallExpr)node);
        } else if (node instanceof EnumDeclaration) {
            return new EnumDeclarationContext((EnumDeclaration)node);
        } else if (node instanceof FieldAccessExpr) {
            return new FieldAccessContext((FieldAccessExpr)node);
        } else {
            return getContext(node.getParentNode());
        }
    }

    public static SymbolDeclarator getSymbolDeclarator(Node node, TypeSolver typeSolver){
        if (node instanceof FieldDeclaration) {
            return new FieldSymbolDeclarator((FieldDeclaration) node, typeSolver);
        } else if (node instanceof Parameter) {
            return new ParameterSymbolDeclarator((Parameter) node, typeSolver);
        } else if (node instanceof ExpressionStmt) {
            ExpressionStmt expressionStmt = (ExpressionStmt) node;
            if (expressionStmt.getExpression() instanceof VariableDeclarationExpr) {
                return new VariableSymbolDeclarator((VariableDeclarationExpr) (expressionStmt.getExpression()), typeSolver);
            } else {
                return new NoSimboyDeclarator(node, typeSolver);
            }
        } else if (node instanceof IfStmt) {
            return new NoSimboyDeclarator(node, typeSolver);
        } else {
            throw new UnsupportedOperationException(node.getClass().getCanonicalName());
        }
    }

}
