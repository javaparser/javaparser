package me.tomassetti.symbolsolver.model.javaparser;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.visitor.GenericVisitor;
import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.SymbolDeclarator;

/**
 * Created by federico on 28/07/15.
 */
public class JavaParserFactory {

    public static Context getContext(Node node){
        if (node instanceof CompilationUnit) {
            throw new UnsupportedOperationException();
        } else if (node instanceof Statement) {
            return new StatementContext((Statement)node);
        } else if (node instanceof MethodDeclaration) {
            return new MethodContext((MethodDeclaration)node);
        } else if (node instanceof ClassOrInterfaceDeclaration) {
            return new ClassOrInterfaceDeclarationContext((ClassOrInterfaceDeclaration)node);
        } else if (node instanceof EnumDeclaration) {
            throw new UnsupportedOperationException();
        } else {
            return getContext(node.getParentNode());
        }
    }

    public static SymbolDeclarator getSymbolDeclarator(Node node){
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

}
