/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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
 
package com.github.javaparser.ast.expr;

import com.github.javaparser.Range;
import com.github.javaparser.ast.ArrayCreationLevel;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * <code>new int[5][4][][]</code> or <code>new int[][]{{1},{2,3}}</code>
 * 
 * @author Julio Vilmar Gesser
 */
// NOTE does not implement NodeWithType because setType is problematic
// NOTE does not implement NodeWithElementType because that implies a list of ArrayBracketPairs
public final class ArrayCreationExpr extends Expression {

    private NodeList<ArrayCreationLevel> levels;

    private Type<?> elementType;

    private ArrayInitializerExpr initializer;

    public ArrayCreationExpr() {
        this(Range.UNKNOWN,
                new ClassOrInterfaceType(),
                new NodeList<>(),
                new ArrayInitializerExpr());
    }

    public ArrayCreationExpr(Type<?> elementType, NodeList<ArrayCreationLevel> levels, ArrayInitializerExpr initializer) {
        this(Range.UNKNOWN,
                elementType,
                levels,
                initializer);
    }

    public ArrayCreationExpr(Type<?> elementType) {
        this(Range.UNKNOWN,
                elementType,
                new NodeList<>(),
                new ArrayInitializerExpr());
    }

    public ArrayCreationExpr(Range range, Type<?> elementType) {
        this(range,
                elementType,
                new NodeList<>(),
                new ArrayInitializerExpr());
    }

    public ArrayCreationExpr(Range range, Type<?> elementType, NodeList<ArrayCreationLevel> levels, ArrayInitializerExpr initializer) {
        super(range);
        setLevels(levels);
        setElementType(elementType);
        setInitializer(initializer);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public Optional<ArrayInitializerExpr> getInitializer() {
        return Optional.ofNullable(initializer);
    }

    public Type<?> getElementType() {
        return elementType;
    }

    /**
     * Sets the initializer
     * 
     * @param initializer the initializer, can be null
     * @return this, the ArrayCreationExpr
     */
    public ArrayCreationExpr setInitializer(ArrayInitializerExpr initializer) {
        notifyPropertyChange("initializer", this.initializer, initializer);
        this.initializer = initializer;
		setAsParentNodeOf(this.initializer);
        return this;
    }

    public ArrayCreationExpr setElementType(Type<?> elementType) {
        notifyPropertyChange("elementType", this.elementType, elementType);
        this.elementType = assertNotNull(elementType);
		setAsParentNodeOf(this.elementType);
        return this;
    }

    public NodeList<ArrayCreationLevel> getLevels() {
        return levels;
    }

    public ArrayCreationExpr setLevels(NodeList<ArrayCreationLevel> levels) {
        notifyPropertyChange("levels", this.levels, levels);
        this.levels = assertNotNull(levels);
        setAsParentNodeOf(levels);
        return this;
    }

    /**
     * Takes the element type and wraps it in an ArrayType for every array creation level.
     */
    public Type<?> getType() {
        Type<?> result = elementType;
        for (int i = 0; i < levels.size(); i++) {
            result = new ArrayType(result, new NodeList<>());
        }
        return result;
    }

    /**
     * Sets this type to this class and try to import it to the {@link CompilationUnit} if needed
     *
     * @param typeClass the type
     * @return this
     */
    public ArrayCreationExpr setElementType(Class<?> typeClass) {
        tryAddImportToParentCompilationUnit(typeClass);
        return setElementType(new ClassOrInterfaceType(typeClass.getSimpleName()));
    }

    public ArrayCreationExpr setElementType(final String type) {
        ClassOrInterfaceType classOrInterfaceType = new ClassOrInterfaceType(type);
        return setElementType(classOrInterfaceType);
    }
}
