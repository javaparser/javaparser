/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.javaparsermodel;

import static com.github.javaparser.ast.expr.Expression.EXCLUDE_ENCLOSED_EXPR;
import static com.github.javaparser.ast.expr.Expression.IS_NOT_ENCLOSED_EXPR;
import static com.github.javaparser.resolution.Navigator.demandParentNode;

import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.resolution.*;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.logic.FunctionalInterfaceLogic;
import com.github.javaparser.resolution.logic.InferenceContext;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.Value;
import com.github.javaparser.resolution.model.typesystem.LazyType;
import com.github.javaparser.resolution.model.typesystem.NullType;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.promotion.ConditionalExprHandler;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedVoidType;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;
import com.github.javaparser.symbolsolver.resolution.promotion.ConditionalExprResolver;
import com.github.javaparser.symbolsolver.resolution.typeinference.LeastUpperBoundLogic;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.Pair;
import com.google.common.collect.ImmutableList;

public class TypeExtractor extends DefaultVisitorAdapter {

    private static final String JAVA_LANG_STRING = String.class.getCanonicalName();
    private final ResolvedType stringReferenceType;

    private TypeSolver typeSolver;
    private JavaParserFacade facade;


    public TypeExtractor(TypeSolver typeSolver, JavaParserFacade facade) {
        this.typeSolver = typeSolver;
        this.facade = facade;
        // pre-calculate the String reference (optimization)
        // consider a LazyType to avoid having to systematically declare a ReflectionTypeSolver
        stringReferenceType = new LazyType(v -> new ReferenceTypeImpl(typeSolver.solveType(JAVA_LANG_STRING)));
    }

    @Override
    public ResolvedType visit(VariableDeclarator node, Boolean solveLambdas) {
        if (demandParentNode(node) instanceof FieldDeclaration) {
            return facade.convertToUsage(node.getType());
        }
        if (demandParentNode(node) instanceof VariableDeclarationExpr) {
            return facade.convertToUsage(node.getType());
        }
        throw new UnsupportedOperationException(demandParentNode(node).getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(Parameter node, Boolean solveLambdas) {
        if (node.getType() instanceof UnknownType) {
            throw new IllegalStateException("Parameter has unknown type: " + node);
        }
        return facade.convertToUsage(node.getType());
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
            case REMAINDER:
            case BINARY_AND:
            case BINARY_OR:
            case XOR:
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
            case SIGNED_RIGHT_SHIFT:
            case UNSIGNED_RIGHT_SHIFT:
            case LEFT_SHIFT:
                ResolvedType rt = node.getLeft().accept(this, solveLambdas);
                // apply unary primitive promotion
                return ResolvedPrimitiveType.unp(rt);
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
        ResolvedType jssType = facade.convertToUsage(node.getType());
        return new ReferenceTypeImpl(typeSolver.solveType(Class.class.getCanonicalName()), ImmutableList.of(jssType));
    }

    /*
     * The conditional operator has three operand expressions. ? appears between the first and second expressions, and
     * : appears between the second and third expressions.
     * There are three kinds of conditional expressions, classified according to the second and third operand
     * expressions: boolean conditional expressions, numeric conditional expressions, and reference conditional
     * expressions.
     * The classification rules are as follows:
     * 1/ If both the second and the third operand expressions are boolean expressions, the conditional expression is a
     * boolean conditional expression.
     * 2/ If both the second and the third operand expressions are numeric expressions, the conditional expression is a
     * numeric conditional expression.
     * 3/ Otherwise, the conditional expression is a reference conditional expression
     */
    @Override
    public ResolvedType visit(ConditionalExpr node, Boolean solveLambdas) {
        ResolvedType thenExpr = node.getThenExpr().accept(this, solveLambdas);
        ResolvedType elseExpr = node.getElseExpr().accept(this, solveLambdas);

        ConditionalExprHandler rce = ConditionalExprResolver.getConditionExprHandler(thenExpr, elseExpr);
        try {
            return rce.resolveType();
        } catch (UnsupportedOperationException e) {
            // There is nothing to do because, for the moment, we want to run actual implementation
        }
        return node.getThenExpr().accept(this, solveLambdas);
    }

    private boolean isCompatible(ResolvedType resolvedType, ResolvedPrimitiveType primitiveType) {
        return (resolvedType.isPrimitive() && resolvedType.asPrimitive().equals(primitiveType))
        || (resolvedType.isReferenceType() && resolvedType.asReferenceType().isUnboxableTo(primitiveType));
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

        if (parentType.isEnum() && parentType.asEnum().hasEnumConstant(node.getName().getId())) {
            return parentType.asEnum().getEnumConstant(node.getName().getId()).getType();
        }
            if (parentType.hasField(node.getName().getId())) {
            return parentType.getField(node.getName().getId()).getType();
        }
            if (parentType.hasInternalType(node.getName().getId())) {
            return new ReferenceTypeImpl(parentType.getInternalType(node.getName().getId()));
        }
        throw new UnsolvedSymbolException(node.getName().getId());
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
            value = createSolver().solveSymbolAsValue(node.getName().getId(), node);
        } catch (UnsolvedSymbolException use) {
            // This node may have a package name as part of its fully qualified name.
            // We should solve for the type declaration inside this package.
            SymbolReference<ResolvedReferenceTypeDeclaration> sref = typeSolver.tryToSolveType(node.toString());
            if (sref.isSolved()) {
                return new ReferenceTypeImpl(sref.getCorrespondingDeclaration());
            }
        }
        if (value.isPresent()) {
            return value.get().getType();
        }
        throw new UnsolvedSymbolException(node.getName().getId());
    }

    @Override
    public ResolvedType visit(InstanceOfExpr node, Boolean solveLambdas) {
        return ResolvedPrimitiveType.BOOLEAN;
    }

    @Override
    public ResolvedType visit(StringLiteralExpr node, Boolean solveLambdas) {
        return stringReferenceType;
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
        Optional<Value> value = createSolver().solveSymbolAsValue(node.getName().getId(), node);
        if (!value.isPresent()) {
            throw new UnsolvedSymbolException("Solving " + node, node.getName().getId());
        }
        return value.get().getType();
    }

    @Override
    public ResolvedType visit(TypeExpr node, Boolean solveLambdas) {
        Log.trace("getType on type expr %s", ()-> node);
        if (!(node.getType() instanceof ClassOrInterfaceType)) {
            throw new UnsupportedOperationException(node.getType().getClass().getCanonicalName());
        }

        ClassOrInterfaceType classOrInterfaceType = (ClassOrInterfaceType) node.getType();
        String nameWithScope = classOrInterfaceType.getNameWithScope();

        // JLS 15.13 - ReferenceType :: [TypeArguments] Identifier
        SymbolReference<ResolvedTypeDeclaration> typeDeclarationSymbolReference = JavaParserFactory
                .getContext(classOrInterfaceType, typeSolver)
                .solveType(nameWithScope);
        if (typeDeclarationSymbolReference.isSolved()) {
            return new ReferenceTypeImpl(typeDeclarationSymbolReference.getCorrespondingDeclaration().asReferenceType());
        }

        // JLS 15.13 - ExpressionName :: [TypeArguments] Identifier
        Optional<Value> value = createSolver().solveSymbolAsValue(nameWithScope, node);
        if (value.isPresent()) {
            return value.get().getType();
        }

        throw new UnsolvedSymbolException("Solving " + node, classOrInterfaceType.getName().getId());
    }

    @Override
    public ResolvedType visit(ObjectCreationExpr node, Boolean solveLambdas) {
        return facade.convertToUsage(node.getType());
    }

    @Override
    public ResolvedType visit(ThisExpr node, Boolean solveLambdas) {
        // If 'this' is prefixed by a class eg. MyClass.this
        if (node.getTypeName().isPresent()) {
            // Get the class name
            String className = node.getTypeName().get().asString();
            // Attempt to resolve locally in Compilation unit
            // first try a buttom/up approach
            try {
                return new ReferenceTypeImpl(
                        facade.getTypeDeclaration(facade.findContainingTypeDeclOrObjectCreationExpr(node, className)));
            } catch (IllegalStateException e) {
                // trying another approach from type solver
                Optional<CompilationUnit> cu = node.findAncestor(CompilationUnit.class);
                SymbolReference<ResolvedReferenceTypeDeclaration> clazz = typeSolver.tryToSolveType(className);
                if (clazz.isSolved()) {
                    return new ReferenceTypeImpl(clazz.getCorrespondingDeclaration());
                }
            }
        }
        return new ReferenceTypeImpl(facade.getTypeDeclaration(facade.findContainingTypeDeclOrObjectCreationExpr(node)));
    }

    @Override
    public ResolvedType visit(SuperExpr node, Boolean solveLambdas) {
        // If 'super' is prefixed by a class eg. MyClass.this
        if (node.getTypeName().isPresent()) {
            String className = node.getTypeName().get().asString();
            SymbolReference<ResolvedTypeDeclaration> resolvedTypeNameRef = JavaParserFactory.getContext(node, typeSolver).solveType(className);
            if (resolvedTypeNameRef.isSolved()) {
                // Cfr JLS $15.12.1
                ResolvedTypeDeclaration resolvedTypeName = resolvedTypeNameRef.getCorrespondingDeclaration();
                if (resolvedTypeName.isInterface()) {
                    return new ReferenceTypeImpl(resolvedTypeName.asInterface());
                }
                            if (resolvedTypeName.isClass()) {
                    // TODO: Maybe include a presence check? e.g. in the case of `java.lang.Object` there will be no superclass.
                    return resolvedTypeName.asClass().getSuperClass().orElseThrow(() -> new RuntimeException("super class unexpectedly empty"));
                }
                throw new UnsupportedOperationException(node.getClass().getCanonicalName());
            }
            throw new UnsolvedSymbolException(className);
        }

        ResolvedTypeDeclaration typeOfNode = facade.getTypeDeclaration(facade.findContainingTypeDeclOrObjectCreationExpr(node));
        if (typeOfNode instanceof ResolvedClassDeclaration) {
            // TODO: Maybe include a presence check? e.g. in the case of `java.lang.Object` there will be no superclass.
            return ((ResolvedClassDeclaration) typeOfNode).getSuperClass().orElseThrow(() -> new RuntimeException("super class unexpectedly empty"));
        }
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(UnaryExpr node, Boolean solveLambdas) {
        switch (node.getOperator()) {
            case MINUS:
            case PLUS:
                return ResolvedPrimitiveType.unp(node.getExpression().accept(this, solveLambdas));
            case LOGICAL_COMPLEMENT:
                return ResolvedPrimitiveType.BOOLEAN;
            case POSTFIX_DECREMENT:
            case PREFIX_DECREMENT:
            case POSTFIX_INCREMENT:
            case PREFIX_INCREMENT:
            case BITWISE_COMPLEMENT:
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
        return facade.convertToUsage(node.getVariables().get(0).getType());
    }


    @Override
    public ResolvedType visit(LambdaExpr node, Boolean solveLambdas) {
        Node parentNode = demandParentNode(node, IS_NOT_ENCLOSED_EXPR);
        if (parentNode instanceof MethodCallExpr) {
            MethodCallExpr callExpr = (MethodCallExpr) parentNode;
            int pos = getParamPos(node);
            SymbolReference<ResolvedMethodDeclaration> refMethod = facade.solve(callExpr);
            if (!refMethod.isSolved()) {
                throw new UnsolvedSymbolException(parentNode.toString(), callExpr.getName().getId());
            }
            Log.trace("getType on lambda expr %s", ()-> refMethod.getCorrespondingDeclaration().getName());

            // The type parameter referred here should be the java.util.stream.Stream.T
            ResolvedType result = refMethod.getCorrespondingDeclaration().getParam(pos).getType();

            if (solveLambdas) {
                if (callExpr.hasScope()) {
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

                result = resolveLambda(node, result);
            }
            return result;
        }
            if (demandParentNode(node) instanceof VariableDeclarator) {
            VariableDeclarator decExpr = (VariableDeclarator) demandParentNode(node);
            ResolvedType result = decExpr.getType().resolve();

            if (solveLambdas) {
                result = resolveLambda(node, result);
            }
            return result;
        }
            if (demandParentNode(node) instanceof AssignExpr) {
            AssignExpr assExpr = (AssignExpr) demandParentNode(node);
            ResolvedType result = assExpr.calculateResolvedType();

            if (solveLambdas) {
                result = resolveLambda(node, result);
            }
            return result;
        }
        throw new UnsupportedOperationException("The type of a lambda expr depends on the position and its return value");
    }

    private ResolvedType resolveLambda(LambdaExpr node, ResolvedType result) {
        // We need to replace the type variables
        Context ctx = JavaParserFactory.getContext(node, typeSolver);
        result = result.solveGenericTypes(ctx);

        //We should find out which is the functional method (e.g., apply) and replace the params of the
        //solveLambdas with it, to derive so the values. We should also consider the value returned by the
        //lambdas
        Optional<MethodUsage> functionalMethod = FunctionalInterfaceLogic.getFunctionalMethod(result);
        if (functionalMethod.isPresent()) {
            LambdaExpr lambdaExpr = node;

            InferenceContext lambdaCtx = new InferenceContext(typeSolver);
            InferenceContext funcInterfaceCtx = new InferenceContext(typeSolver);

            // At this point parameterType
            // if Function<T=? super Stream.T, ? extends map.R>
            // we should replace Stream.T
            ResolvedType functionalInterfaceType = ReferenceTypeImpl.undeterminedParameters(functionalMethod.get().getDeclaration().declaringType());

            lambdaCtx.addPair(result, functionalInterfaceType);

            ResolvedType actualType;

            if (lambdaExpr.getBody() instanceof ExpressionStmt) {
                actualType = facade.getType(((ExpressionStmt) lambdaExpr.getBody()).getExpression());
            } else if (lambdaExpr.getBody() instanceof BlockStmt) {
                BlockStmt blockStmt = (BlockStmt) lambdaExpr.getBody();

                // Get all the return statements in the lambda block
                List<ReturnStmt> returnStmts = blockStmt.findAll(ReturnStmt.class);

                if (returnStmts.size() > 0) {
                	Set<ResolvedType> resolvedTypes = returnStmts.stream()
                          .map(returnStmt -> returnStmt.getExpression()
                        		  .map(e -> facade.getType(e))
                        		  .orElse(ResolvedVoidType.INSTANCE))
                                  .collect(Collectors.toSet());
                	actualType = LeastUpperBoundLogic.of().lub(resolvedTypes);

                } else {
                    actualType = ResolvedVoidType.INSTANCE;
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
    }

    @Override
    public ResolvedType visit(MethodReferenceExpr node, Boolean solveLambdas) {
    	if ("new".equals(node.getIdentifier())) {
			return node.getScope().calculateResolvedType();
		}
        Node parentNode = demandParentNode(node);
        if (parentNode instanceof MethodCallExpr) {
            MethodCallExpr callExpr = (MethodCallExpr) parentNode;
            int pos = getParamPos(node);
            SymbolReference<ResolvedMethodDeclaration> refMethod = facade.solve(callExpr, false);
            if (!refMethod.isSolved()) {
                throw new UnsolvedSymbolException(parentNode.toString(), callExpr.getName().getId());
            }
            Log.trace("getType on method reference expr %s", ()-> refMethod.getCorrespondingDeclaration().getName());
            if (solveLambdas) {
                MethodUsage usage = facade.solveMethodAsUsage(callExpr);
                ResolvedType result = usage.getParamType(pos);
                // We need to replace the type variables
                Context ctx = JavaParserFactory.getContext(node, typeSolver);
                result = result.solveGenericTypes(ctx);

                //We should find out which is the functional method (e.g., apply) and replace the params of the
                //solveLambdas with it, to derive so the values. We should also consider the value returned by the
                //lambdas
                Optional<MethodUsage> functionalMethodOpt = FunctionalInterfaceLogic.getFunctionalMethod(result);
                if (functionalMethodOpt.isPresent()) {
                    MethodUsage functionalMethod = functionalMethodOpt.get();

                    for (Pair<ResolvedTypeParameterDeclaration, ResolvedType> typeParamDecl : result.asReferenceType().getTypeParametersMap()) {
                        functionalMethod = functionalMethod.replaceTypeParameter(typeParamDecl.a, typeParamDecl.b);
                    }

                    // replace wildcards
                    for (int i = 0; i < functionalMethod.getNoParams(); i++) {
                        ResolvedType type = functionalMethod.getParamType(i);
                        if (type.isWildcard()) {
                            ResolvedType boundedType = type.asWildcard().getBoundedType();
                            functionalMethod = functionalMethod.replaceParamType(i, boundedType);
                        }
                    }

                    ResolvedType actualType = facade.toMethodUsage(node, functionalMethod.getParamTypes()).returnType();
                    ResolvedType formalType = functionalMethod.returnType();

                    InferenceContext inferenceContext = new InferenceContext(typeSolver);
                    inferenceContext.addPair(formalType, actualType);
                    result = inferenceContext.resolve(inferenceContext.addSingle(result));
                }

                return result;
            }
			// Since variable parameters are represented by an array, in case we deal with
			// the variadic parameter we have to take into account the base type of the
			// array.
			ResolvedMethodDeclaration rmd = refMethod.getCorrespondingDeclaration();
			if (rmd.hasVariadicParameter() && pos >= rmd.getNumberOfParams() - 1) {
				return rmd.getLastParam().getType().asArrayType().getComponentType();
			}
            return rmd.getParam(pos).getType();
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

    private static int getParamPos(Expression node) {
        Node parentNode = demandParentNode(node, IS_NOT_ENCLOSED_EXPR);
        if (parentNode instanceof MethodCallExpr) {
            MethodCallExpr call = (MethodCallExpr) parentNode;
            return call.getArgumentPosition(node, EXCLUDE_ENCLOSED_EXPR);
        }
        throw new IllegalArgumentException();
    }

    protected Solver createSolver() {
        return new SymbolSolver(typeSolver);
    }
}
