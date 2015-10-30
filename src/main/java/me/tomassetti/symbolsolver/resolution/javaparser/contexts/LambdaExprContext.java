package me.tomassetti.symbolsolver.resolution.javaparser.contexts;


import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.resolution.SymbolDeclarator;
import me.tomassetti.symbolsolver.resolution.SymbolReference;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.Value;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.MethodUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.resolution.javaparser.JavaParserFactory;

import java.util.List;
import java.util.Optional;

public class LambdaExprContext extends AbstractJavaParserContext<LambdaExpr> {

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            if (wrappedNode.getParentNode() instanceof MethodCallExpr){
                MethodCallExpr methodCallExpr = (MethodCallExpr)wrappedNode.getParentNode();
                MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(methodCallExpr);
                int i = pos(methodCallExpr, wrappedNode);
                TypeUsage lambdaType = methodUsage.getParamTypes().get(i);
                Value value = new Value(lambdaType.asReferenceTypeUsage().parameters().get(0), name, false);
                return Optional.of(value);
            } else {
                throw new UnsupportedOperationException();
            }
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbolAsValue(name, typeSolver);
    }

    @Override
    public Optional<TypeUsage> solveGenericType(String name, TypeSolver typeSolver) {
        MethodCallExpr parentNode = (MethodCallExpr)wrappedNode.getParentNode();
        int pos = pos(parentNode, wrappedNode);
        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage((MethodCallExpr) parentNode);
        TypeUsage lambda = methodUsage.getParamTypes().get(pos);
        return Optional.of(lambda.asReferenceTypeUsage().parameters().get(0));
    }

    private int pos(MethodCallExpr callExpr, Expression param){
        int i = 0;
        for (Expression p : callExpr.getArgs()) {
            if (p == param) {
                return i;
            }
            i++;
        }
        throw new IllegalArgumentException();
    }

    protected final Optional<Value> solveWithAsValue(SymbolDeclarator symbolDeclarator, String name, TypeSolver typeSolver){
        for (ValueDeclaration decl : symbolDeclarator.getSymbolDeclarations()){
            if (decl.getName().equals(name)){

                throw new UnsupportedOperationException();
            }
        }
        return Optional.empty();
    }

    public LambdaExprContext(LambdaExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            SymbolReference symbolReference = solveWith(sb, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        return getParent().solveType(name, typeSolver);
    }

    @Override
    public SymbolReference<me.tomassetti.symbolsolver.model.declarations.MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        return getParent().solveMethod(name, parameterTypes, typeSolver);
    }

}
