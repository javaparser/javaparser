/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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
package org.javaparser.ast.expr;

import org.javaparser.ast.AllFieldsConstructor;
import org.javaparser.ast.Node;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.metamodel.ExpressionMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.TokenRange;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.ast.Generated;
import java.util.function.Consumer;
import static org.javaparser.utils.CodeGenerationUtils.f;
import java.util.Optional;

/**
 * A base class for all expressions.
 *
 * @author Julio Vilmar Gesser
 */
public abstract class Expression extends Node {

    @AllFieldsConstructor
    public Expression() {
        this(null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public Expression(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public Expression clone() {
        return (Expression) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public ExpressionMetaModel getMetaModel() {
        return JavaParserMetaModel.expressionMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        return super.replace(node, replacementNode);
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isAnnotationExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public AnnotationExpr asAnnotationExpr() {
        throw new IllegalStateException(f("%s is not an AnnotationExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isArrayAccessExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ArrayAccessExpr asArrayAccessExpr() {
        throw new IllegalStateException(f("%s is not an ArrayAccessExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isArrayCreationExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ArrayCreationExpr asArrayCreationExpr() {
        throw new IllegalStateException(f("%s is not an ArrayCreationExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isArrayInitializerExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ArrayInitializerExpr asArrayInitializerExpr() {
        throw new IllegalStateException(f("%s is not an ArrayInitializerExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isAssignExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public AssignExpr asAssignExpr() {
        throw new IllegalStateException(f("%s is not an AssignExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isBinaryExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public BinaryExpr asBinaryExpr() {
        throw new IllegalStateException(f("%s is not an BinaryExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isBooleanLiteralExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public BooleanLiteralExpr asBooleanLiteralExpr() {
        throw new IllegalStateException(f("%s is not an BooleanLiteralExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isCastExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public CastExpr asCastExpr() {
        throw new IllegalStateException(f("%s is not an CastExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isCharLiteralExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public CharLiteralExpr asCharLiteralExpr() {
        throw new IllegalStateException(f("%s is not an CharLiteralExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isClassExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ClassExpr asClassExpr() {
        throw new IllegalStateException(f("%s is not an ClassExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isConditionalExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ConditionalExpr asConditionalExpr() {
        throw new IllegalStateException(f("%s is not an ConditionalExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isDoubleLiteralExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public DoubleLiteralExpr asDoubleLiteralExpr() {
        throw new IllegalStateException(f("%s is not an DoubleLiteralExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isEnclosedExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public EnclosedExpr asEnclosedExpr() {
        throw new IllegalStateException(f("%s is not an EnclosedExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isFieldAccessExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public FieldAccessExpr asFieldAccessExpr() {
        throw new IllegalStateException(f("%s is not an FieldAccessExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isInstanceOfExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public InstanceOfExpr asInstanceOfExpr() {
        throw new IllegalStateException(f("%s is not an InstanceOfExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isIntegerLiteralExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public IntegerLiteralExpr asIntegerLiteralExpr() {
        throw new IllegalStateException(f("%s is not an IntegerLiteralExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isLambdaExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public LambdaExpr asLambdaExpr() {
        throw new IllegalStateException(f("%s is not an LambdaExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isLiteralExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public LiteralExpr asLiteralExpr() {
        throw new IllegalStateException(f("%s is not an LiteralExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isLiteralStringValueExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public LiteralStringValueExpr asLiteralStringValueExpr() {
        throw new IllegalStateException(f("%s is not an LiteralStringValueExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isLongLiteralExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public LongLiteralExpr asLongLiteralExpr() {
        throw new IllegalStateException(f("%s is not an LongLiteralExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isMarkerAnnotationExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public MarkerAnnotationExpr asMarkerAnnotationExpr() {
        throw new IllegalStateException(f("%s is not an MarkerAnnotationExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isMethodCallExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public MethodCallExpr asMethodCallExpr() {
        throw new IllegalStateException(f("%s is not an MethodCallExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isMethodReferenceExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public MethodReferenceExpr asMethodReferenceExpr() {
        throw new IllegalStateException(f("%s is not an MethodReferenceExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isNameExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public NameExpr asNameExpr() {
        throw new IllegalStateException(f("%s is not an NameExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isNormalAnnotationExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public NormalAnnotationExpr asNormalAnnotationExpr() {
        throw new IllegalStateException(f("%s is not an NormalAnnotationExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isNullLiteralExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public NullLiteralExpr asNullLiteralExpr() {
        throw new IllegalStateException(f("%s is not an NullLiteralExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isObjectCreationExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ObjectCreationExpr asObjectCreationExpr() {
        throw new IllegalStateException(f("%s is not an ObjectCreationExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isSingleMemberAnnotationExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public SingleMemberAnnotationExpr asSingleMemberAnnotationExpr() {
        throw new IllegalStateException(f("%s is not an SingleMemberAnnotationExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isStringLiteralExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public StringLiteralExpr asStringLiteralExpr() {
        throw new IllegalStateException(f("%s is not an StringLiteralExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isSuperExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public SuperExpr asSuperExpr() {
        throw new IllegalStateException(f("%s is not an SuperExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isThisExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ThisExpr asThisExpr() {
        throw new IllegalStateException(f("%s is not an ThisExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isTypeExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public TypeExpr asTypeExpr() {
        throw new IllegalStateException(f("%s is not an TypeExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isUnaryExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public UnaryExpr asUnaryExpr() {
        throw new IllegalStateException(f("%s is not an UnaryExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isVariableDeclarationExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public VariableDeclarationExpr asVariableDeclarationExpr() {
        throw new IllegalStateException(f("%s is not an VariableDeclarationExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifAnnotationExpr(Consumer<AnnotationExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifArrayAccessExpr(Consumer<ArrayAccessExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifArrayCreationExpr(Consumer<ArrayCreationExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifArrayInitializerExpr(Consumer<ArrayInitializerExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifAssignExpr(Consumer<AssignExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifBinaryExpr(Consumer<BinaryExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifBooleanLiteralExpr(Consumer<BooleanLiteralExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifCastExpr(Consumer<CastExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifCharLiteralExpr(Consumer<CharLiteralExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifClassExpr(Consumer<ClassExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifConditionalExpr(Consumer<ConditionalExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifDoubleLiteralExpr(Consumer<DoubleLiteralExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifEnclosedExpr(Consumer<EnclosedExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifFieldAccessExpr(Consumer<FieldAccessExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifInstanceOfExpr(Consumer<InstanceOfExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifIntegerLiteralExpr(Consumer<IntegerLiteralExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifLambdaExpr(Consumer<LambdaExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifLiteralExpr(Consumer<LiteralExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifLiteralStringValueExpr(Consumer<LiteralStringValueExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifLongLiteralExpr(Consumer<LongLiteralExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifMarkerAnnotationExpr(Consumer<MarkerAnnotationExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifMethodCallExpr(Consumer<MethodCallExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifMethodReferenceExpr(Consumer<MethodReferenceExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifNameExpr(Consumer<NameExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifNormalAnnotationExpr(Consumer<NormalAnnotationExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifNullLiteralExpr(Consumer<NullLiteralExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifObjectCreationExpr(Consumer<ObjectCreationExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifSingleMemberAnnotationExpr(Consumer<SingleMemberAnnotationExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifStringLiteralExpr(Consumer<StringLiteralExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifSuperExpr(Consumer<SuperExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifThisExpr(Consumer<ThisExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifTypeExpr(Consumer<TypeExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifUnaryExpr(Consumer<UnaryExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifVariableDeclarationExpr(Consumer<VariableDeclarationExpr> action) {
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    public ResolvedType calculateResolvedType() {
        return getSymbolResolver().calculateType(this);
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<AnnotationExpr> toAnnotationExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ArrayAccessExpr> toArrayAccessExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ArrayCreationExpr> toArrayCreationExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ArrayInitializerExpr> toArrayInitializerExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<AssignExpr> toAssignExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<BinaryExpr> toBinaryExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<BooleanLiteralExpr> toBooleanLiteralExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<CastExpr> toCastExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<CharLiteralExpr> toCharLiteralExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ClassExpr> toClassExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ConditionalExpr> toConditionalExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<DoubleLiteralExpr> toDoubleLiteralExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<EnclosedExpr> toEnclosedExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<FieldAccessExpr> toFieldAccessExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<InstanceOfExpr> toInstanceOfExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<IntegerLiteralExpr> toIntegerLiteralExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<LambdaExpr> toLambdaExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<LiteralExpr> toLiteralExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<LiteralStringValueExpr> toLiteralStringValueExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<LongLiteralExpr> toLongLiteralExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<MarkerAnnotationExpr> toMarkerAnnotationExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<MethodCallExpr> toMethodCallExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<MethodReferenceExpr> toMethodReferenceExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<NameExpr> toNameExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<NormalAnnotationExpr> toNormalAnnotationExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<NullLiteralExpr> toNullLiteralExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ObjectCreationExpr> toObjectCreationExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<SingleMemberAnnotationExpr> toSingleMemberAnnotationExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<StringLiteralExpr> toStringLiteralExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<SuperExpr> toSuperExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ThisExpr> toThisExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<TypeExpr> toTypeExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<UnaryExpr> toUnaryExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<VariableDeclarationExpr> toVariableDeclarationExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isSwitchExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public SwitchExpr asSwitchExpr() {
        throw new IllegalStateException(f("%s is not an SwitchExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<SwitchExpr> toSwitchExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifSwitchExpr(Consumer<SwitchExpr> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isTextBlockLiteralExpr() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public TextBlockLiteralExpr asTextBlockLiteralExpr() {
        throw new IllegalStateException(f("%s is not an TextBlockLiteralExpr", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<TextBlockLiteralExpr> toTextBlockLiteralExpr() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifTextBlockLiteralExpr(Consumer<TextBlockLiteralExpr> action) {
    }
}
