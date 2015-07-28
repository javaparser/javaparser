package me.tomassetti.symbolsolver.model.javaparser;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import me.tomassetti.symbolsolver.model.SymbolDeclaration;

/**
 * Created by federico on 28/07/15.
 */
public class JavaParserSymbolDeclaration implements SymbolDeclaration {

    private String name;
    private Node wrappedNode;
    private boolean field;

    public static JavaParserSymbolDeclaration field(VariableDeclarator wrappedNode) {
        return new JavaParserSymbolDeclaration(wrappedNode, wrappedNode.getId().getName(), true);
    }

    private JavaParserSymbolDeclaration(Node wrappedNode, String name, boolean field) {
        this.name = name;
        this.wrappedNode = wrappedNode;
        this.field = field;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public boolean isField() {
        return field;
    }
}
