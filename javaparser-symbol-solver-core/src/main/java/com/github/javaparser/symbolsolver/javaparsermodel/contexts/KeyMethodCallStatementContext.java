package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.TypePatternExpr;
import com.github.javaparser.ast.key.KeyExecutionContext;
import com.github.javaparser.ast.key.KeyMethodCallStatement;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.Value;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/14/26)
 */
public class KeyMethodCallStatementContext extends AbstractJavaParserContext<KeyMethodCallStatement> {
    private final Context context;
    private final String selfName;
    private final ResolvedType selfType;

    public KeyMethodCallStatementContext(KeyMethodCallStatement kcr, TypeSolver typeSolver) {
        super(kcr, typeSolver);

        KeyExecutionContext sourceSpecification = (KeyExecutionContext) kcr.getContext();
        var typeName = sourceSpecification.context().toString();
        final var ref = solveTypeInParentContext(typeName);
        if (!ref.isSolved()) {
            throw new RuntimeException("Could not resolve type of method call statement: " + typeName);
        }

        var resolvedType = ref.getCorrespondingDeclaration();
        var typeDeclaration = resolvedType.toAst(TypeDeclaration.class).get();

        context = JavaParserFactory.getContext(typeDeclaration, typeSolver);

        selfType = sourceSpecification.context().convertToUsage(context);

        selfName = sourceSpecification
                .getInstance()
                .flatMap(Expression::toNameExpr)
                .map(NodeWithSimpleName::getNameAsString)
                .orElse(null);
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(
            String name, List<ResolvedType> argumentsTypes, ResolvedReferenceTypeDeclaration invocationContext) {
        return context.solveMethodAsUsage(name, argumentsTypes, invocationContext);
    }

    @Override
    public List<TypePatternExpr> typePatternExprsExposedToChild(Node child) {
        return context.typePatternExprsExposedToChild(child);
    }

    @Override
    public Optional<TypePatternExpr> typePatternExprInScope(String name) {
        return context.typePatternExprInScope(name);
    }

    @Override
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name, List<ResolvedType> typeArguments) {
        return context.solveType(name, typeArguments);
    }

    @Override
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        return context.solveType(name);
    }

    @Override
    public Optional<Value> solveSymbolAsValueInParentContext(String name) {
        return context.solveSymbolAsValueInParentContext(name);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name) {
        if (Objects.equals(name, selfName)) {
            return Optional.of(new Value(selfType, selfName));
        }
        return context.solveSymbolAsValue(name);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        if (Objects.equals(name, selfName)) {
            return getSymbolicReferenceOfSelfName();
        }
        return context.solveSymbol(name);
    }

    private SymbolReference<? extends ResolvedValueDeclaration> getSymbolicReferenceOfSelfName() {
        return SymbolReference.solved(new KeyMethodCallInstanceDeclaration());
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethodInParentContext(
            String name,
            List<ResolvedType> argumentsTypes,
            boolean staticOnly,
            ResolvedReferenceTypeDeclaration invocationContext) {
        return context.solveMethodInParentContext(name, argumentsTypes, staticOnly, invocationContext);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name,
            List<ResolvedType> argumentsTypes,
            boolean staticOnly,
            ResolvedReferenceTypeDeclaration invocationContext) {
        return context.solveMethod(name, argumentsTypes, staticOnly, invocationContext);
    }

    @Override
    public Optional<ResolvedType> solveGenericTypeInParentContext(String name) {
        return context.solveGenericTypeInParentContext(name);
    }

    @Override
    public Optional<ResolvedType> solveGenericType(String name) {
        return context.solveGenericType(name);
    }

    @Override
    public SymbolReference<ResolvedConstructorDeclaration> solveConstructor(List<ResolvedType> argumentsTypes) {
        return context.solveConstructor(argumentsTypes);
    }

    @Override
    public List<Parameter> parametersExposedToChild(Node child) {
        return context.parametersExposedToChild(child);
    }

    @Override
    public Optional<Parameter> parameterDeclarationInScope(String name) {
        return context.parameterDeclarationInScope(name);
    }

    @Override
    public List<VariableDeclarator> localVariablesExposedToChild(Node child) {
        return context.localVariablesExposedToChild(child);
    }

    @Override
    public Optional<VariableDeclarator> localVariableDeclarationInScope(String name) {
        return context.localVariableDeclarationInScope(name);
    }

    @Override
    public List<ResolvedFieldDeclaration> fieldsExposedToChild(Node child) {
        return context.fieldsExposedToChild(child);
    }

    @Override
    public Optional<ResolvedFieldDeclaration> fieldDeclarationInScope(String name) {
        return context.fieldDeclarationInScope(name);
    }

    public final class KeyMethodCallInstanceDeclaration implements ResolvedValueDeclaration {
        @Override
        public ResolvedType getType() {
            return selfType;
        }

        @Override
        public String getName() {
            return selfName;
        }

        @Override
        public Optional<Node> toAst() {
            return Optional.ofNullable(((KeyExecutionContext) wrappedNode.getContext()).instance());
        }
    }
}
