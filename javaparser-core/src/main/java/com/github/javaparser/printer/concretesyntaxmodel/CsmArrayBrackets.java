/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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
package com.github.javaparser.printer.concretesyntaxmodel;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.nodeTypes.NodeWithVariables;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.printer.SourcePrinter;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * The brackets of an array type, written where the source wrote them.
 * <p>
 * Java allows the brackets of an array on both sides of a declared name: {@code int[] a} and {@code int a[]} declare
 * the same type. The AST keeps this information in {@link ArrayType#getOrigin()}: a level with
 * {@link ArrayType.Origin#TYPE} is written after the element type, a level with {@link ArrayType.Origin#NAME} after
 * the declared name.
 * <p>
 * The lexical preserving printer compares the syntax model of a node with its original tokens, so the model must put
 * the brackets on the same side as the source. This element is therefore used in two places:
 * <ul>
 *     <li>on {@link ArrayType} ({@link #typeSide(CsmElement)}), where it prints the brackets of the level only when
 *     they are written after the element type;</li>
 *     <li>after the name of a declaration ({@link #nameSide()}), where it prints the brackets that the declared type
 *     does not print itself.</li>
 * </ul>
 * Only the brackets are printed after the name: the annotations of a name-side level ({@code int a @A []}) are not.
 */
public class CsmArrayBrackets implements CsmElement {

    /**
     * The syntax of the brackets of an {@link ArrayType}, or {@code null} for the name-side element.
     */
    private final CsmElement typeSideBrackets;

    private CsmArrayBrackets(CsmElement typeSideBrackets) {
        this.typeSideBrackets = typeSideBrackets;
    }

    /**
     * Creates the element used in the syntax of {@link ArrayType}.
     *
     * @param brackets the syntax of the annotations and brackets of the level
     * @return an element printing {@code brackets} only when the level is written after the element type
     */
    public static CsmArrayBrackets typeSide(CsmElement brackets) {
        return new CsmArrayBrackets(brackets);
    }

    /**
     * Creates the element used after the name of a declaration having a {@code TYPE} property
     * ({@link com.github.javaparser.ast.body.Parameter}, {@link VariableDeclarator}).
     *
     * @return an element printing the bracket pairs written after the name, derived from the declared type
     */
    public static CsmArrayBrackets nameSide() {
        return new CsmArrayBrackets(null);
    }

    /**
     * @return {@code true} for the element written after the name of a declaration
     */
    public boolean isNameSide() {
        return typeSideBrackets == null;
    }

    /**
     * @return the syntax of the brackets of an {@link ArrayType}, {@code null} for the name-side element
     */
    public CsmElement getTypeSideBrackets() {
        return typeSideBrackets;
    }

    /**
     * Computes the number of bracket pairs written after the name of a declaration.
     * <p>
     * For a parameter, these are the levels of its type with {@link ArrayType.Origin#NAME}.
     * <p>
     * For a variable declarator in a field or a variable declaration, the type written before the names is the maximum
     * common type of the declaration ({@code int[]} in {@code int[] a, b[]}). That type prints its type-side levels,
     * so the declarator prints all the levels of its own type beyond them, whatever their origin. This also covers a
     * declarator whose type was set to an array type built in code, with the default origin.
     *
     * @param declaration the parameter or variable declarator
     * @param type the type of the declaration; during a change of type, the new type
     * @return the number of {@code []} to write after the name
     */
    public static int nameSideLevels(Node declaration, Object type) {
        if (declaration instanceof VariableDeclarator
                && declaration.getParentNode().isPresent()
                && declaration.getParentNode().get() instanceof NodeWithVariables) {
            NodeWithVariables<?> parent =
                    (NodeWithVariables<?>) declaration.getParentNode().get();
            // The maximum common type the declaration will have once the type of this declarator is changed
            List<Type> types = new ArrayList<>();
            for (VariableDeclarator variable : parent.getVariables()) {
                types.add(variable == declaration ? (Type) type : variable.getType());
            }
            Optional<Type> maximumCommonType = NodeWithVariables.calculateMaximumCommonType(types);
            if (maximumCommonType.isPresent()) {
                return ((Type) type).getArrayLevel() - countLevels(maximumCommonType.get(), ArrayType.Origin.TYPE);
            }
        }
        return countLevels(type, ArrayType.Origin.NAME);
    }

    /**
     * Counts the levels of the given type having the given origin.
     *
     * @param type a type, possibly an {@link ArrayType}
     * @param origin the origin of the levels to count
     * @return the number of {@link ArrayType} levels of {@code type} with {@code origin}
     */
    private static int countLevels(Object type, ArrayType.Origin origin) {
        int levels = 0;
        while (type instanceof ArrayType) {
            ArrayType arrayType = (ArrayType) type;
            if (arrayType.getOrigin() == origin) {
                levels++;
            }
            type = arrayType.getComponentType();
        }
        return levels;
    }

    /**
     * @param origin the origin of an {@link ArrayType} level
     * @return {@code true} when the brackets of the level are written after the element type
     */
    public static boolean isTypeSide(Object origin) {
        return origin != ArrayType.Origin.NAME;
    }

    @Override
    public void prettyPrint(Node node, SourcePrinter printer) {
        if (isNameSide()) {
            int levels = nameSideLevels(node, ObservableProperty.TYPE.getRawValue(node));
            for (int i = 0; i < levels; i++) {
                printer.print("[]");
            }
        } else if (isTypeSide(ObservableProperty.ORIGIN.getRawValue(node))) {
            typeSideBrackets.prettyPrint(node, printer);
        }
    }

    @Override
    public String toString() {
        return isNameSide() ? "CsmArrayBrackets(name side)" : "CsmArrayBrackets(type side)";
    }
}
