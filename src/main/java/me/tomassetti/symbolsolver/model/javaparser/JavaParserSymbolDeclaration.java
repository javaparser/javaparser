package me.tomassetti.symbolsolver.model.javaparser;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import me.tomassetti.symbolsolver.model.SymbolDeclaration;

/**
 * Created by federico on 28/07/15.
 */
public class JavaParserSymbolDeclaration implements SymbolDeclaration {

    private String name;
    private Node wrappedNode;
    private boolean field;
    private boolean parameter;

    public static JavaParserSymbolDeclaration field(VariableDeclarator wrappedNode) {
        return new JavaParserSymbolDeclaration(wrappedNode, wrappedNode.getId().getName(), true, false);
    }

    public static JavaParserSymbolDeclaration parameter(Parameter parameter) {
        return new JavaParserSymbolDeclaration(parameter, parameter.getId().getName(), false, true);
    }

    private JavaParserSymbolDeclaration(Node wrappedNode, String name, boolean field, boolean parameter) {
        this.name = name;
        this.wrappedNode = wrappedNode;
        this.field = field;
        this.parameter = parameter;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public boolean isField() {
        return field;
    }

    @Override
    public boolean isParameter() {
        return parameter;
    }

}
