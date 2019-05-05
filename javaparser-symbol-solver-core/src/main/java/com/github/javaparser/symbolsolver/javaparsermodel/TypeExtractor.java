package com.github.javaparser.symbolsolver.javaparsermodel;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedClassDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedVoidType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;
import com.github.javaparser.symbolsolver.logic.FunctionalInterfaceLogic;
import com.github.javaparser.symbolsolver.logic.InferenceContext;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.model.typesystem.*;
import com.github.javaparser.symbolsolver.reflectionmodel.MyObjectProvider;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.utils.Log;
import com.google.common.collect.ImmutableList;

import java.util.List;
import java.util.Optional;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.requireParentNode;
import static com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade.solveGenericTypes;

public class TypeExtractor extends DefaultVisitorAdapter {

    private TypeSolver typeSolver;
    private JavaParserFacade facade;

    public TypeExtractor(TypeSolver typeSolver, JavaParserFacade facade) {
        this.typeSolver = typeSolver;
        this.facade = facade;
    }

    @Override
    public ResolvedType visit(VariableDeclarator node, Boolean solveLambdas) {
        if (requireParentNode(node) instanceof FieldDeclaration) {
            return facade.convertToUsageVariableType(node);
        } else if (requireParentNode(node) instanceof VariableDeclarationExpr) {
            return facade.convertToUsageVariableType(node);
        }
        throw new UnsupportedOperationException(requireParentNode(node).getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(Parameter node, Boolean solveLambdas) {
        if (node.getType() instanceof UnknownType) {
            throw new IllegalStateException("Parameter has unknown type: " + node);
        }
        return facade.convertToUsage(node.getType(), node);
    }


    @Override
    public ResolvedType visit(ArrayAccessExpr node, Boolean solveLambdas) {
        ResolvedType arrayUsageType = node.getName().accept(this, solveLambdas);
        if (arrayUsageType.isArray()) {
            return ((ResolvedArrayType) arrayUsageType).getComponentType();
        }
        return arrayUsageType;
    }

    @Override
    public ResolvedType visit(ArrayCreationExpr node, Boolean solveLambdas) {
        ResolvedType res = facade.convertToUsage(node.getElementType(), JavaParserFactory.getContext(node, typeSolver));
        for (int i = 0; i < node.getLevels().size(); i++) {
            res = new ResolvedArrayType(res);
        }
        return res;
    }

    @Override
    public ResolvedType visit(ArrayInitializerExpr node, Boolean solveLambdas) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(AssignExpr node, Boolean solveLambdas) {
        return node.getTarget().accept(this, solveLambdas);
    }

    @Override
    public ResolvedType visit(BinaryExpr node, Boolean solveLambdas) {
        switch (node.getOperator()) {
            case PLUS:
            case MINUS:
            case DIVIDE:
            case MULTIPLY:
                return facade.getBinaryTypeConcrete(node.getLeft(), node.getRight(), solveLambdas, node.getOperator());
            case LESS_EQUALS:
            case LESS:
            case GREATER:
            case GREATER_EQUALS:
            case EQUALS:
            case NOT_EQUALS:
            case OR:
            case AND:
                return ResolvedPrimitiveType.BOOLEAN;
            case BINARY_AND:
            case BINARY_OR:
            case SIGNED_RIGHT_SHIFT:
            case UNSIGNED_RIGHT_SHIFT:
            case LEFT_SHIFT:
            case REMAINDER:
            case XOR:
                return node.getLeft().accept(this, solveLambdas);
            default:
                throw new UnsupportedOperationException("Operator " + node.getOperator().name());
        }
    }

    @Override
    public ResolvedType visit(CastExpr node, Boolean solveLambdas) {
        return facade.convertToUsage(node.getType(), JavaParserFactory.getContext(node, typeSolver));
    }

    @Override
    public ResolvedType visit(ClassExpr node, Boolean solveLambdas) {
        // This implementation does not regard the actual type argument of the ClassExpr.
        com.github.javaparser.ast.type.Type astType = node.getType();
        ResolvedType jssType = facade.convertToUsage(astType, node.getType());
        return new ReferenceTypeImpl(new ReflectionClassDeclaration(Class.class, typeSolver), ImmutableList.of(jssType), typeSolver);
    }

    @Override
    public ResolvedType visit(ConditionalExpr node, Boolean solveLambdas) {
        return node.getThenExpr().accept(this, solveLambdas);
    }

    @Override
    public ResolvedType visit(EnclosedExpr node, Boolean solveLambdas) {
        return node.getInner().accept(this, solveLambdas);
    }

    /**
     * Java Parser can't differentiate between packages, internal types, and fields.
     * All three are lumped together into FieldAccessExpr. We need to differentiate them.
     */
    private ResolvedType solveDotExpressionType(ResolvedReferenceTypeDeclaration parentType, FieldAccessExpr node) {
        // Fields and internal type declarations cannot have the same name.
        // Thus, these checks will always be mutually exclusive.
        if (parentType.isEnum() && parentType.asEnum().hasEnumConstant(node.getName().getId())) {
            return parentType.asEnum().getEnumConstant(node.getName().getId()).getType();
        } else if (parentType.hasField(node.getName().getId())) {
            return parentType.getField(node.getName().getId()).getType();
        } else if (parentType.hasInternalType(node.getName().getId())) {
            return new ReferenceTypeImpl(parentType.getInternalType(node.getName().getId()), typeSolver);
        } else {
            throw new UnsolvedSymbolException(node.getName().getId());
        }
    }

    @Override
    public ResolvedType visit(FieldAccessExpr node, Boolean solveLambdas) {
        // We should understand if this is a static access
        if (node.getScope() instanceof NameExpr ||
                node.getScope() instanceof FieldAccessExpr) {
            Expression staticValue = node.getScope();
            SymbolReference<ResolvedTypeDeclaration> typeAccessedStatically = JavaParserFactory.getContext(node, typeSolver).solveType(staticValue.toString());
            if (typeAccessedStatically.isSolved()) {
                // TODO here maybe we have to substitute type typeParametersValues
                return solveDotExpressionType(
                        typeAccessedStatically.getCorrespondingDeclaration().asReferenceType(), node);
            }
        } else if (node.getScope() instanceof ThisExpr) {
            // If we are accessing through a 'this' expression, first resolve the type
            // corresponding to 'this'
            SymbolReference<ResolvedTypeDeclaration> solve = facade.solve((ThisExpr) node.getScope());
            // If found get it's declaration and get the field in there
            if (solve.isSolved()) {
                ResolvedTypeDeclaration correspondingDeclaration = solve.getCorrespondingDeclaration();
                if (correspondingDeclaration instanceof ResolvedReferenceTypeDeclaration) {
                    return solveDotExpressionType(correspondingDeclaration.asReferenceType(), node);
                }
            }

        } else if (node.getScope().toString().indexOf('.') > 0) {
            // try to find fully qualified name
            SymbolReference<ResolvedReferenceTypeDeclaration> sr = typeSolver.tryToSolveType(node.getScope().toString());
            if (sr.isSolved()) {
                return solveDotExpressionType(sr.getCorrespondingDeclaration(), node);
            }
        }
        Optional<Value> value = Optional.empty();
        try {
            value = new SymbolSolver(typeSolver).solveSymbolAsValue(node.getName().getId(), node);
        } catch (com.github.javaparser.resolution.UnsolvedSymbolException use) {
            // This node may have a package name as part of its fully qualified name.
            // We should solve for the type declaration inside this package.
            SymbolReference<ResolvedReferenceTypeDeclaration> sref = typeSolver.tryToSolveType(node.toString());
            if (sref.isSolved()) {
                return new ReferenceTypeImpl(sref.getCorrespondingDeclaration(), typeSolver);
            }
        }
        if (value.isPresent()) {
            return value.get().getType();
        }
        throw new com.github.javaparser.resolution.UnsolvedSymbolException(node.getName().getId());
    }

    @Override
    public ResolvedType visit(InstanceOfExpr node, Boolean solveLambdas) {
        return ResolvedPrimitiveType.BOOLEAN;
    }

    @Override
    public ResolvedType visit(StringLiteralExpr node, Boolean solveLambdas) {
        return new ReferenceTypeImpl(new ReflectionTypeSolver().solveType(String.class.getCanonicalName()), typeSolver);
    }

    @Override
    public ResolvedType visit(IntegerLiteralExpr node, Boolean solveLambdas) {
        return ResolvedPrimitiveType.INT;
    }

    @Override
    public ResolvedType visit(LongLiteralExpr node, Boolean solveLambdas) {
        return ResolvedPrimitiveType.LONG;
    }

    @Override
    public ResolvedType visit(CharLiteralExpr node, Boolean solveLambdas) {
        return ResolvedPrimitiveType.CHAR;
    }

    @Override
    public ResolvedType visit(DoubleLiteralExpr node, Boolean solveLambdas) {
        if (node.getValue().toLowerCase().endsWith("f")) {
            return ResolvedPrimitiveType.FLOAT;
        }
        return ResolvedPrimitiveType.DOUBLE;
    }

    @Override
    public ResolvedType visit(BooleanLiteralExpr node, Boolean solveLambdas) {
        return ResolvedPrimitiveType.BOOLEAN;
    }

    @Override
    public ResolvedType visit(NullLiteralExpr node, Boolean solveLambdas) {
        return NullType.INSTANCE;
    }

    @Override
    public ResolvedType visit(MethodCallExpr node, Boolean solveLambdas) {
        Log.trace("getType on method call %s", ()-> node);
        // first solve the method
        MethodUsage ref = facade.solveMethodAsUsage(node);
        Log.trace("getType on method call %s resolved to %s", ()-> node, ()-> ref);
        Log.trace("getType on method call %s return type is %s", ()-> node, ref::returnType);
        return ref.returnType();
        // the type is the return type of the method
    }

    @Override
    public ResolvedType visit(NameExpr node, Boolean solveLambdas) {
        Log.trace("getType on name expr %s", ()-> node);
        Optional<Value> value = new SymbolSolver(typeSolver).solveSymbolAsValue(node.getName().getId(), node);
        if (!value.isPresent()) {
            throw new com.github.javaparser.resolution.UnsolvedSymbolException("Solving " + node, node.getName().getId());
        } else {
            return value.get().getType();
        }
    }

    @Override
    public ResolvedType visit(ObjectCreationExpr node, Boolean solveLambdas) {
        return facade.convertToUsage(node.getType(), node);
    }

    @Override
    public ResolvedType visit(ThisExpr node, Boolean solveLambdas) {
        // If 'this' is prefixed by a class eg. MyClass.this
        if (node.getTypeName().isPresent()) {
            // Get the class name
            String className = node.getTypeName().get().asString();
            // Attempt to resolve using a typeSolver
            SymbolReference<ResolvedReferenceTypeDeclaration> clazz = typeSolver.tryToSolveType(className);
            if (clazz.isSolved()) {
                return new ReferenceTypeImpl(clazz.getCorrespondingDeclaration(), typeSolver);
            }
            // Attempt to resolve locally in Compilation unit
            Optional<CompilationUnit> cu = node.findAncestor(CompilationUnit.class);
            if (cu.isPresent()) {
                Optional<ClassOrInterfaceDeclaration> classByName = cu.get().getClassByName(className);
                if (classByName.isPresent()) {
                    return new ReferenceTypeImpl(facade.getTypeDeclaration(classByName.get()), typeSolver);
                }
            }

        }
        return new ReferenceTypeImpl(facade.getTypeDeclaration(facade.findContainingTypeDeclOrObjectCreationExpr(node)), typeSolver);
    }

    @Override
    public ResolvedType visit(SuperExpr node, Boolean solveLambdas) {
        ResolvedTypeDeclaration typeOfNode = facade.getTypeDeclaration(facade.findContainingTypeDecl(node));
        if (typeOfNode instanceof ResolvedClassDeclaration) {
            return ((ResolvedClassDeclaration) typeOfNode).getSuperClass();
        } else {
            throw new UnsupportedOperationException(node.getClass().getCanonicalName());
        }
    }

    @Override
    public ResolvedType visit(UnaryExpr node, Boolean solveLambdas) {
        switch (node.getOperator()) {
            case MINUS:
            case PLUS:
                return node.getExpression().accept(this, solveLambdas);
            case LOGICAL_COMPLEMENT:
                return ResolvedPrimitiveType.BOOLEAN;
            case POSTFIX_DECREMENT:
            case PREFIX_DECREMENT:
            case POSTFIX_INCREMENT:
            case PREFIX_INCREMENT:
                return node.getExpression().accept(this, solveLambdas);
            default:
                throw new UnsupportedOperationException(node.getOperator().name());
        }
    }

    @Override
    public ResolvedType visit(VariableDeclarationExpr node, Boolean solveLambdas) {
        if (node.getVariables().size() != 1) {
            throw new UnsupportedOperationException();
        }
        return facade.convertToUsageVariableType(node.getVariables().get(0));
    }


    @Override
    public ResolvedType visit(LambdaExpr node, Boolean solveLambdas) {
        if (requireParentNode(node) instanceof MethodCallExpr) {
            MethodCallExpr callExpr = (MethodCallExpr) requireParentNode(node);
            int pos = JavaParserSymbolDeclaration.getParamPos(node);
            SymbolReference<ResolvedMethodDeclaration> refMethod = facade.solve(callExpr);
            if (!refMethod.isSolved()) {
                throw new com.github.javaparser.resolution.UnsolvedSymbolException(requireParentNode(node).toString(), callExpr.getName().getId());
            }
            Log.trace("getType on lambda expr %s", ()-> refMethod.getCorrespondingDeclaration().getName());
            if (solveLambdas) {

                // The type parameter referred here should be the java.util.stream.Stream.T
                ResolvedType result = refMethod.getCorrespondingDeclaration().getParam(pos).getType();

                if (callExpr.getScope().isPresent()) {
                    Expression scope = callExpr.getScope().get();

                    // If it is a static call we should not try to get the type of the scope
                    boolean staticCall = false;
                    if (scope instanceof NameExpr) {
                        NameExpr nameExpr = (NameExpr) scope;
                        try {
                            SymbolReference<ResolvedTypeDeclaration> type = JavaParserFactory.getContext(nameExpr, typeSolver).solveType(nameExpr.getName().getId());
                            if (type.isSolved()) {
                                staticCall = true;
                            }
                        } catch (Exception e) {

                        }
                    }

                    if (!staticCall) {
                        ResolvedType scopeType = facade.getType(scope);
                        if (scopeType.isReferenceType()) {
                            result = scopeType.asReferenceType().useThisTypeParametersOnTheGivenType(result);
                        }
                    }
                }

                // We need to replace the type variables
                Context ctx = JavaParserFactory.getContext(node, typeSolver);
                result = solveGenericTypes(result, ctx);

                //We should find out which is the functional method (e.g., apply) and replace the params of the
                //solveLambdas with it, to derive so the values. We should also consider the value returned by the
                //lambdas
                Optional<MethodUsage> functionalMethod = FunctionalInterfaceLogic.getFunctionalMethod(result);
                if (functionalMethod.isPresent()) {
                    LambdaExpr lambdaExpr = node;

                    InferenceContext lambdaCtx = new InferenceContext(MyObjectProvider.INSTANCE);
                    InferenceContext funcInterfaceCtx = new InferenceContext(MyObjectProvider.INSTANCE);

                    // At this point parameterType
                    // if Function<T=? super Stream.T, ? extends map.R>
                    // we should replace Stream.T
                    ResolvedType functionalInterfaceType = ReferenceTypeImpl.undeterminedParameters(functionalMethod.get().getDeclaration().declaringType(), typeSolver);

                    lambdaCtx.addPair(result, functionalInterfaceType);

                    ResolvedType actualType;

                    if (lambdaExpr.getBody() instanceof ExpressionStmt) {
                        actualType = facade.getType(((ExpressionStmt) lambdaExpr.getBody()).getExpression());
                    } else if (lambdaExpr.getBody() instanceof BlockStmt) {
                        BlockStmt blockStmt = (BlockStmt) lambdaExpr.getBody();

                        // Get all the return statements in the lambda block
                        List<ReturnStmt> returnStmts = blockStmt.findAll(ReturnStmt.class);

                        if (returnStmts.size() > 0) {
                            actualType = returnStmts.stream()
                                    .map(returnStmt -> returnStmt.getExpression().map(e -> facade.getType(e)).orElse(ResolvedVoidType.INSTANCE))
                                    .filter(x -> x != null && !x.isVoid() && !x.isNull())
                                    .findFirst()
                                    .orElse(ResolvedVoidType.INSTANCE);

                        } else {
                            return ResolvedVoidType.INSTANCE;
                        }


                    } else {
                        throw new UnsupportedOperationException();
                    }

                    ResolvedType formalType = functionalMethod.get().returnType();

                    // Infer the functional interfaces' return vs actual type
                    funcInterfaceCtx.addPair(formalType, actualType);
                    // Substitute to obtain a new type
                    ResolvedType functionalTypeWithReturn = funcInterfaceCtx.resolve(funcInterfaceCtx.addSingle(functionalInterfaceType));

                    // if the functional method returns void anyway
                    // we don't need to bother inferring types
                    if (!(formalType instanceof ResolvedVoidType)) {
                        lambdaCtx.addPair(result, functionalTypeWithReturn);
                        result = lambdaCtx.resolve(lambdaCtx.addSingle(result));
                    }
                }

                return result;
            } else {
                return refMethod.getCorrespondingDeclaration().getParam(pos).getType();
            }
        } else {
            throw new UnsupportedOperationException("The type of a lambda expr depends on the position and its return value");
        }
    }

    @Override
    public ResolvedType visit(MethodReferenceExpr node, Boolean solveLambdas) {
        if (requireParentNode(node) instanceof MethodCallExpr) {
            MethodCallExpr callExpr = (MethodCallExpr) requireParentNode(node);
            int pos = JavaParserSymbolDeclaration.getParamPos(node);
            SymbolReference<ResolvedMethodDeclaration> refMethod = facade.solve(callExpr, false);
            if (!refMethod.isSolved()) {
                throw new com.github.javaparser.resolution.UnsolvedSymbolException(requireParentNode(node).toString(), callExpr.getName().getId());
            }
            Log.trace("getType on method reference expr %s", ()-> refMethod.getCorrespondingDeclaration().getName());
            if (solveLambdas) {
                MethodUsage usage = facade.solveMethodAsUsage(callExpr);
                ResolvedType result = usage.getParamType(pos);
                // We need to replace the type variables
                Context ctx = JavaParserFactory.getContext(node, typeSolver);
                result = solveGenericTypes(result, ctx);

                //We should find out which is the functional method (e.g., apply) and replace the params of the
                //solveLambdas with it, to derive so the values. We should also consider the value returned by the
                //lambdas
                if (FunctionalInterfaceLogic.getFunctionalMethod(result).isPresent()) {
                    MethodReferenceExpr methodReferenceExpr = node;

                    ResolvedType actualType = facade.toMethodUsage(methodReferenceExpr).returnType();
                    ResolvedType formalType = FunctionalInterfaceLogic.getFunctionalMethod(result).get().returnType();

                    InferenceContext inferenceContext = new InferenceContext(MyObjectProvider.INSTANCE);
                    inferenceContext.addPair(formalType, actualType);
                    result = inferenceContext.resolve(inferenceContext.addSingle(result));
                }

                return result;
            }
            return refMethod.getCorrespondingDeclaration().getParam(pos).getType();
        }
        throw new UnsupportedOperationException("The type of a method reference expr depends on the position and its return value");
    }

    @Override
    public ResolvedType visit(FieldDeclaration node, Boolean solveLambdas) {
        if (node.getVariables().size() == 1) {
            return node.getVariables().get(0).accept(this, solveLambdas);
        }
        throw new IllegalArgumentException("Cannot resolve the type of a field with multiple variable declarations. Pick one");
    }
}
