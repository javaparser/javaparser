package me.tomassetti.symbolsolver.model.javaparser.declarations;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.model.*;

/**
 * Created by federico on 28/07/15.
 */
public class JavaParserSymbolDeclaration implements SymbolDeclaration {

    private String name;
    private Node wrappedNode;
    private boolean field;
    private boolean parameter;
    private TypeSolver typeSolver;

    public static JavaParserSymbolDeclaration field(VariableDeclarator wrappedNode, TypeSolver typeSolver) {
        return new JavaParserSymbolDeclaration(wrappedNode, wrappedNode.getId().getName(), typeSolver, true, false);
    }

    public static JavaParserSymbolDeclaration parameter(Parameter parameter, TypeSolver typeSolver) {
        return new JavaParserSymbolDeclaration(parameter, parameter.getId().getName(), typeSolver, false, true);
    }

    @Override
    public String toString() {
        return "JavaParserSymbolDeclaration{" +
                "name='" + name + '\'' +
                ", wrappedNode=" + wrappedNode +
                '}';
    }

    private JavaParserSymbolDeclaration(Node wrappedNode, String name, TypeSolver typeSolver, boolean field, boolean parameter) {
        this.name = name;
        this.wrappedNode = wrappedNode;
        this.field = field;
        this.parameter = parameter;
        this.typeSolver = typeSolver;
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

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public TypeDeclaration asTypeDeclaration() {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeDeclaration getType() {
        if (wrappedNode instanceof Parameter) {
            Parameter parameter = (Parameter) wrappedNode;
            if (wrappedNode.getParentNode() instanceof LambdaExpr){
                int pos = getParamPos(parameter);
                //System.out.println("PARAM to solve "+wrappedNode);
                //System.out.println("LAMBDA");
                //System.out.println(wrappedNode.getParentNode());
                TypeUsage lambdaType = new JavaParserFacade(typeSolver).getType(wrappedNode.getParentNode());

                // TODO understand from the context to which method this corresponds
                //MethodDeclaration methodDeclaration = new JavaParserFacade(typeSolver).getMethodCalled
                //MethodDeclaration methodCalled = new JavaParserFacade(typeSolver).solve()
                throw new UnsupportedOperationException(wrappedNode.getClass().getCanonicalName());
            } else {
                return new SymbolSolver(typeSolver).solveType(parameter.getType());
            }
        } else {
            throw new UnsupportedOperationException(wrappedNode.getClass().getCanonicalName());
        }
    }

    private int getParamPos(Parameter parameter) {
        int pos = 0;
        for (Node node : parameter.getParentNode().getChildrenNodes()) {
            if (node == parameter) {
                return pos;
            } else if (node instanceof Parameter){
                pos++;
            }
        }
        return pos;
    }

}
