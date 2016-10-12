package me.tomassetti.symbolsolver.javaparsermodel.contexts;


import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.type.Type;

import javaslang.Tuple2;
import me.tomassetti.symbolsolver.logic.FunctionalInterfaceLogic;
import me.tomassetti.symbolsolver.logic.GenericTypeInferenceLogic;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.resolution.TypeParameter;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.resolution.SymbolDeclarator;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.resolution.Value;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFactory;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

public class LambdaExprContext extends AbstractJavaParserContext<LambdaExpr> {

    public LambdaExprContext(LambdaExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            int index = 0;
            for (ValueDeclaration decl : sb.getSymbolDeclarations()) {
                if (decl.getName().equals(name)) {
                    if (wrappedNode.getParentNode() instanceof MethodCallExpr) {
                        MethodCallExpr methodCallExpr = (MethodCallExpr) wrappedNode.getParentNode();
                        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage(methodCallExpr);
                        int i = pos(methodCallExpr, wrappedNode);
                        TypeUsage lambdaType = methodUsage.getParamTypes().get(i);
                        Value value = new Value(lambdaType.asReferenceTypeUsage().parameters().get(0), name, false);
                        return Optional.of(value);
                    } else if (wrappedNode.getParentNode() instanceof VariableDeclarator) {
                        Type declaratorType = null;
                        
                        VariableDeclarator variableDeclarator = (VariableDeclarator) wrappedNode.getParentNode();
                        if (variableDeclarator.getParentNode() instanceof VariableDeclarationExpr) {
                            declaratorType = ((VariableDeclarationExpr) variableDeclarator.getParentNode()).getType();
                        } else if (variableDeclarator.getParentNode() instanceof FieldDeclaration) {
                            declaratorType = ((FieldDeclaration) variableDeclarator.getParentNode()).getType();
                        } else {
                            throw new UnsupportedOperationException();
                        }

                        TypeUsage t = JavaParserFacade.get(typeSolver).convert(declaratorType, declaratorType);
                        Optional<MethodUsage> functionalMethod = FunctionalInterfaceLogic.getFunctionalMethod(t);
                        if (functionalMethod.isPresent()) {
                            TypeUsage lambdaType = functionalMethod.get().getParamType(index, typeSolver);

                            // Replace parameter from declarator
                            if (lambdaType.isReferenceType()) {
                                for (Tuple2<TypeParameter, TypeUsage> entry : lambdaType.asReferenceTypeUsage().getTypeParametersMap()) {
                                    if (entry._2.isTypeVariable() && entry._2.asTypeParameter().declaredOnClass()) {
                                        Optional<TypeUsage> ot = t.asReferenceTypeUsage().getGenericParameterByName(entry._1.getName());
                                        if (ot.isPresent()) {
                                            lambdaType = lambdaType.replaceParam(entry._1.getName(), ot.get());
                                        }
                                    }
                                }
                            } else if (lambdaType.isTypeVariable() && lambdaType.asTypeParameter().declaredOnClass()) {
                                Optional<TypeUsage> ot = t.asReferenceTypeUsage().getGenericParameterByName(lambdaType.asTypeParameter().getName());
                                if (ot.isPresent()) {
                                    lambdaType = ot.get();
                                }
                            }

                            Value value = new Value(lambdaType, name, false);
                            return Optional.of(value);
                        } else {
                            throw new UnsupportedOperationException();
                        }
                    } else {
                        throw new UnsupportedOperationException();
                    }
                }
                index++;
            } 
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbolAsValue(name, typeSolver);
    }

    @Override
    public Optional<TypeUsage> solveGenericType(String name, TypeSolver typeSolver) {
        MethodCallExpr parentNode = (MethodCallExpr) wrappedNode.getParentNode();
        int pos = pos(parentNode, wrappedNode);
        MethodUsage methodUsage = JavaParserFacade.get(typeSolver).solveMethodAsUsage((MethodCallExpr) parentNode);
        TypeUsage lambda = methodUsage.getParamTypes().get(pos);

        List<Tuple2<TypeUsage, TypeUsage>> formalActualTypePairs = new ArrayList<>();
        for (int i=0;i<methodUsage.getDeclaration().getNoParams();i++){
            formalActualTypePairs.add(new Tuple2<>(methodUsage.getDeclaration().getParam(i).getType(), methodUsage.getParamType(i, typeSolver)));
        }
        Map<String, TypeUsage> map = GenericTypeInferenceLogic.inferGenericTypes(formalActualTypePairs);
        if (map.containsKey(name)) {
            return Optional.of(map.get(name));
        } else {
            return Optional.empty();
        }

        //return Optional.of(lambda.asReferenceTypeUsage().parameters().get(0));
    }

    private int pos(MethodCallExpr callExpr, Expression param) {
        int i = 0;
        for (Expression p : callExpr.getArgs()) {
            if (p == param) {
                return i;
            }
            i++;
        }
        throw new IllegalArgumentException();
    }

    protected final Optional<Value> solveWithAsValue(SymbolDeclarator symbolDeclarator, String name, TypeSolver typeSolver) {
        for (ValueDeclaration decl : symbolDeclarator.getSymbolDeclarations()) {
            if (decl.getName().equals(name)) {

                throw new UnsupportedOperationException();
            }
        }
        return Optional.empty();
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (Parameter parameter : wrappedNode.getParameters()) {
            SymbolDeclarator sb = JavaParserFactory.getSymbolDeclarator(parameter, typeSolver);
            SymbolReference<ValueDeclaration> symbolReference = solveWith(sb, name);
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
    public SymbolReference<me.tomassetti.symbolsolver.model.declarations.MethodDeclaration> solveMethod(
            String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        return getParent().solveMethod(name, parameterTypes, typeSolver);
    }

}
