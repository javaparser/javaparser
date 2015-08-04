package me.tomassetti.symbolsolver.model.javaparser.declarations;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

/**
 * Created by federico on 28/07/15.
 */
public class JavaParserSymbolDeclaration implements ValueDeclaration {

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
    public TypeDeclaration getType(TypeSolver typeSolver) {
        if (wrappedNode instanceof Parameter) {
            Parameter parameter = (Parameter) wrappedNode;
            if (wrappedNode.getParentNode() instanceof LambdaExpr) {
                int pos = getParamPos(parameter);
                //System.out.println("PARAM to solve "+wrappedNode);
                //System.out.println("LAMBDA");
                //System.out.println(wrappedNode.getParentNode());
                TypeUsage lambdaType = new JavaParserFacade(typeSolver).getType(wrappedNode.getParentNode());

                System.out.println("We should be able to calculate the type parameters");
                System.out.println("LambdaType "+lambdaType);
                // TODO understand from the context to which method this corresponds
                //MethodDeclaration methodDeclaration = new JavaParserFacade(typeSolver).getMethodCalled
                //MethodDeclaration methodCalled = new JavaParserFacade(typeSolver).solve()
                throw new UnsupportedOperationException(wrappedNode.getClass().getCanonicalName());
            } else {
                return new SymbolSolver(typeSolver).solveType(parameter.getType());
            }
        } else if (wrappedNode instanceof VariableDeclarator) {
            VariableDeclarator variableDeclarator = (VariableDeclarator)wrappedNode;
            if (wrappedNode.getParentNode() instanceof VariableDeclarationExpr) {
                VariableDeclarationExpr variableDeclarationExpr = (VariableDeclarationExpr)variableDeclarator.getParentNode();
                return new JavaParserFacade(typeSolver).convert(variableDeclarationExpr.getType(), JavaParserFactory.getContext(wrappedNode));
            } else if (wrappedNode.getParentNode() instanceof FieldDeclaration) {
                FieldDeclaration fieldDeclaration = (FieldDeclaration)variableDeclarator.getParentNode();
                return new JavaParserFacade(typeSolver).convert(fieldDeclaration.getType(), JavaParserFactory.getContext(wrappedNode));
            } else {
                throw new UnsupportedOperationException(wrappedNode.getParentNode().getClass().getCanonicalName());
            }
        } else {
            throw new UnsupportedOperationException(wrappedNode.getClass().getCanonicalName());
        }
    }

    public static int getParamPos(Parameter parameter) {
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

    public static int getParamPos(Node node) {
        if (node.getParentNode() instanceof MethodCallExpr) {
            MethodCallExpr call = (MethodCallExpr)node.getParentNode();
            for (int i=0;i<call.getArgs().size();i++){
                if (call.getArgs().get(i) == node) return i;
            }
            throw new IllegalStateException();
        } else {
            throw new IllegalArgumentException();
        }
    }

    @Override
    public TypeUsage getTypeUsage(TypeSolver typeSolver) {
        return new JavaParserFacade(typeSolver).getType(wrappedNode);
    }
}
