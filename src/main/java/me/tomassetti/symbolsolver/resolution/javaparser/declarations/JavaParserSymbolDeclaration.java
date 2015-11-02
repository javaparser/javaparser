package me.tomassetti.symbolsolver.resolution.javaparser.declarations;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.type.PrimitiveType;
import me.tomassetti.symbolsolver.resolution.javaparser.JavaParserFacade;
import me.tomassetti.symbolsolver.resolution.*;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;

import me.tomassetti.symbolsolver.resolution.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.typesystem.PrimitiveTypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

public class JavaParserSymbolDeclaration implements ValueDeclaration {

    private String name;
    private Node wrappedNode;
    private boolean field;
    private boolean parameter;
    private boolean variable;
    private TypeSolver typeSolver;

    public static JavaParserSymbolDeclaration field(VariableDeclarator wrappedNode, TypeSolver typeSolver) {
        return new JavaParserSymbolDeclaration(wrappedNode, wrappedNode.getId().getName(), typeSolver, true, false, false);
    }

    public static JavaParserSymbolDeclaration parameter(Parameter parameter, TypeSolver typeSolver) {
        return new JavaParserSymbolDeclaration(parameter, parameter.getId().getName(), typeSolver, false, true, false);
    }

    public static JavaParserSymbolDeclaration localVar(VariableDeclarator variableDeclarator, TypeSolver typeSolver) {
        return new JavaParserSymbolDeclaration(variableDeclarator, variableDeclarator.getId().getName(), typeSolver, false, false, true);
    }

    @Override
    public String toString() {
        return "JavaParserSymbolDeclaration{" +
                "name='" + name + '\'' +
                ", wrappedNode=" + wrappedNode +
                '}';
    }

    private JavaParserSymbolDeclaration(Node wrappedNode, String name, TypeSolver typeSolver, boolean field, boolean parameter, boolean variable) {
        this.name = name;
        this.wrappedNode = wrappedNode;
        this.field = field;
        this.variable = variable;
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
    public boolean isVariable() {
        return variable;
    }

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public TypeUsage getType() {
        if (wrappedNode instanceof Parameter) {
            Parameter parameter = (Parameter) wrappedNode;
            if (wrappedNode.getParentNode() instanceof LambdaExpr) {
                int pos = getParamPos(parameter);
                TypeUsage lambdaType = JavaParserFacade.get(typeSolver).getType(wrappedNode.getParentNode());

                // TODO understand from the context to which method this corresponds
                //MethodDeclaration methodDeclaration = JavaParserFacade.get(typeSolver).getMethodCalled
                //MethodDeclaration methodCalled = JavaParserFacade.get(typeSolver).solve()
                throw new UnsupportedOperationException(wrappedNode.getClass().getCanonicalName());
            } else {
                if (parameter.getType() instanceof PrimitiveType) {
                    return PrimitiveTypeUsage.byName(((PrimitiveType) parameter.getType()).getType().name());
                } else {
                    return JavaParserFacade.get(typeSolver).convertToUsage(parameter.getType(), wrappedNode);
                }
            }
        } else if (wrappedNode instanceof VariableDeclarator) {
            VariableDeclarator variableDeclarator = (VariableDeclarator)wrappedNode;
            if (wrappedNode.getParentNode() instanceof VariableDeclarationExpr) {
                VariableDeclarationExpr variableDeclarationExpr = (VariableDeclarationExpr)variableDeclarator.getParentNode();
                return JavaParserFacade.get(typeSolver).convert(variableDeclarationExpr.getType(), JavaParserFactory.getContext(wrappedNode, typeSolver));
            } else if (wrappedNode.getParentNode() instanceof FieldDeclaration) {
                FieldDeclaration fieldDeclaration = (FieldDeclaration)variableDeclarator.getParentNode();
                return JavaParserFacade.get(typeSolver).convert(fieldDeclaration.getType(), JavaParserFactory.getContext(wrappedNode, typeSolver));
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

    /*@Override
    public TypeUsage getTypeUsage(TypeSolver typeSolver) {
        return JavaParserFacade.get(typeSolver).getType(wrappedNode);
    }*/
}
