package me.tomassetti.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.ArrayType;
import me.tomassetti.symbolsolver.model.usages.typesystem.PrimitiveType;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFactory;

public class JavaParserSymbolDeclaration implements ValueDeclaration {

    private String name;
    private Node wrappedNode;
    private boolean field;
    private boolean parameter;
    private boolean variable;
    private TypeSolver typeSolver;

    private JavaParserSymbolDeclaration(Node wrappedNode, String name, TypeSolver typeSolver, boolean field, boolean parameter, boolean variable) {
        this.name = name;
        this.wrappedNode = wrappedNode;
        this.field = field;
        this.variable = variable;
        this.parameter = parameter;
        this.typeSolver = typeSolver;
    }

    public static JavaParserFieldDeclaration field(VariableDeclarator wrappedNode, TypeSolver typeSolver) {
        return new JavaParserFieldDeclaration(wrappedNode, typeSolver);
    }

    public static JavaParserParameterDeclaration parameter(Parameter parameter, TypeSolver typeSolver) {
        return new JavaParserParameterDeclaration(parameter, typeSolver);
    }

    public static JavaParserSymbolDeclaration localVar(VariableDeclarator variableDeclarator, TypeSolver typeSolver) {
        return new JavaParserSymbolDeclaration(variableDeclarator, variableDeclarator.getId().getName(), typeSolver, false, false, true);
    }

    public static int getParamPos(Parameter parameter) {
        int pos = 0;
        for (Node node : parameter.getParentNode().getChildrenNodes()) {
            if (node == parameter) {
                return pos;
            } else if (node instanceof Parameter) {
                pos++;
            }
        }
        return pos;
    }

    public static int getParamPos(Node node) {
        if (node.getParentNode() instanceof MethodCallExpr) {
            MethodCallExpr call = (MethodCallExpr) node.getParentNode();
            for (int i = 0; i < call.getArgs().size(); i++) {
                if (call.getArgs().get(i) == node) return i;
            }
            throw new IllegalStateException();
        } else {
            throw new IllegalArgumentException();
        }
    }

    @Override
    public String toString() {
        return "JavaParserSymbolDeclaration{" +
                "name='" + name + '\'' +
                ", wrappedNode=" + wrappedNode +
                '}';
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
    public Type getType() {
        if (wrappedNode instanceof Parameter) {
            Parameter parameter = (Parameter) wrappedNode;
            if (wrappedNode.getParentNode() instanceof LambdaExpr) {
                int pos = getParamPos(parameter);
                Type lambdaType = JavaParserFacade.get(typeSolver).getType(wrappedNode.getParentNode());

                // TODO understand from the context to which method this corresponds
                //MethodDeclaration methodDeclaration = JavaParserFacade.get(typeSolver).getMethodCalled
                //MethodDeclaration methodCalled = JavaParserFacade.get(typeSolver).solve()
                throw new UnsupportedOperationException(wrappedNode.getClass().getCanonicalName());
            } else {
                Type rawType = null;
                if (parameter.getType() instanceof com.github.javaparser.ast.type.PrimitiveType) {
                    rawType = PrimitiveType.byName(((com.github.javaparser.ast.type.PrimitiveType) parameter.getType()).getType().name());
                } else {
                    rawType = JavaParserFacade.get(typeSolver).convertToUsage(parameter.getType(), wrappedNode);
                }
                if (parameter.isVarArgs()) {
                    return new ArrayType(rawType);
                } else {
                    return rawType;
                }
            }
        } else if (wrappedNode instanceof VariableDeclarator) {
            VariableDeclarator variableDeclarator = (VariableDeclarator) wrappedNode;
            if (wrappedNode.getParentNode() instanceof VariableDeclarationExpr) {
                VariableDeclarationExpr variableDeclarationExpr = (VariableDeclarationExpr) variableDeclarator.getParentNode();
                return JavaParserFacade.get(typeSolver).convert(variableDeclarationExpr.getType(), JavaParserFactory.getContext(wrappedNode, typeSolver));
            } else if (wrappedNode.getParentNode() instanceof FieldDeclaration) {
                FieldDeclaration fieldDeclaration = (FieldDeclaration) variableDeclarator.getParentNode();
                return JavaParserFacade.get(typeSolver).convert(fieldDeclaration.getType(), JavaParserFactory.getContext(wrappedNode, typeSolver));
            } else {
                throw new UnsupportedOperationException(wrappedNode.getParentNode().getClass().getCanonicalName());
            }
        } else {
            throw new UnsupportedOperationException(wrappedNode.getClass().getCanonicalName());
        }
    }

    @Override
    public TypeDeclaration asType() {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName()+": wrapping "+ this.getWrappedNode().getClass().getCanonicalName());
    }

    /**
	 * Returns the JavaParser node associated with this JavaParserSymbolDeclaration.
	 *
	 * @return A visitable JavaParser node wrapped by this object.
	 */
	public Node getWrappedNode()
	{
		return wrappedNode;
	}


}
