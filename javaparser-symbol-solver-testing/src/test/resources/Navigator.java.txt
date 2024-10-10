package me.tomassetti.symbolsolver.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.NameExpr;

import java.util.Optional;

/**
 * This class can be used to conveniently retrieve certain node from a JavaParser AST.
 */
public final class Navigator {

    private Navigator() {
        // prevent instantiation
    }

    public static Optional<TypeDeclaration> findType(CompilationUnit cu, String name) {
        return cu.getTypes().stream().filter((t) -> t.getName().equals(name)).findFirst();
    }

}