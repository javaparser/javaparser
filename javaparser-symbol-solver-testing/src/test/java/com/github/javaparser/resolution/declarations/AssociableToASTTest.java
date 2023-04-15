/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.resolution.declarations;

import com.github.javaparser.ast.Node;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

public interface AssociableToASTTest {

    /**
     * Helper method to cast the instance to the correct {@link Class}.
     *
     * @param instance  The instance to be casted.
     * @param clazz     The expected {@link Class}.
     * @param <T>       The expected type.
     *
     * @return The instance casted as the correct type.
     */
    default <T extends AssociableToAST> T safeCast(AssociableToAST instance, Class<T> clazz) {
        if (clazz.isInstance(instance))
            return clazz.cast(instance);
        throw new UnsupportedOperationException(String.format("Unable to cast %s into %s.", instance.getClass().getName(), clazz.getName()));
    }

    /**
     * Create a new instance of {@link AssociableToAST} to be used for testing.
     *
     * @return The created instance.
     */
    AssociableToAST createValue();

    /**
     * Get the node that can be associated with an AST.
     *
     * @param associableToAST The node that can be associated with an AST.
     *
     * @return The node being wrapped.
     */
    Optional<Node> getWrappedDeclaration(AssociableToAST associableToAST);

    @Test
    default void checkThatToASTMatchesTheCorrectWrappedNode() {
        AssociableToAST associableToAST = createValue();
        Optional<Node> wrappedNode = getWrappedDeclaration(associableToAST);
        if (wrappedNode.isPresent())
            assertEquals(wrappedNode, associableToAST.toAst());
        else
            assertFalse(associableToAST.toAst().isPresent());
    }

    @Test
    default void checkThatToASTWithCorrectTypeMatchesTheCorrectWrappedNode() {
        AssociableToAST associableToAST = createValue();
        Optional<Node> wrappedNode = getWrappedDeclaration(associableToAST);
        if (wrappedNode.isPresent())
            assertEquals(wrappedNode, associableToAST.toAst(wrappedNode.get().getClass()));
        else
            assertFalse(associableToAST.toAst().isPresent());

    }

}
