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

package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.resolution.declarations.HasAccessSpecifier;

import java.util.Arrays;
import java.util.List;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import static com.github.javaparser.ast.NodeList.toNodeList;

/**
 * A Node with Modifiers.
 * Note that not all modifiers may be valid for this node.
 */
public interface NodeWithModifiers<N extends Node> {
    /**
     * Return the modifiers of this variable declaration.
     * Warning: modifying the returned set will not trigger observers,
     * you have to use setModifiers for that.
     *
     * @return modifiers
     * @see Modifier
     */
    NodeList<Modifier> getModifiers();

    N setModifiers(NodeList<Modifier> modifiers);

    @SuppressWarnings("unchecked")
    default N addModifier(Modifier.Keyword... newModifiers) {
        NodeList<Modifier> existingModifiers = new NodeList<>(getModifiers());
        for (Modifier.Keyword newModifier : newModifiers) {
            boolean alreadyPresent = existingModifiers.stream().anyMatch(m -> m.getKeyword() == newModifier);
            if (!alreadyPresent) {
                existingModifiers.add(new Modifier(newModifier));
            }
        }
        setModifiers(existingModifiers);
        return (N) this;
    }

    @SuppressWarnings("unchecked")
    default N removeModifier(Modifier.Keyword... modifiersToRemove) {
        List<Modifier.Keyword> modifiersToRemoveAsList = Arrays.asList(modifiersToRemove);
        NodeList<Modifier> remaining = getModifiers().stream()
                .filter(existingModifier -> !modifiersToRemoveAsList.contains(existingModifier.getKeyword()))
                .collect(toNodeList());
        setModifiers(remaining);
        return (N) this;
    }

    default N setModifier(Modifier.Keyword m, boolean set) {
        if (set) {
            return addModifier(m);
        } else {
            return removeModifier(m);
        }
    }

    default boolean hasModifier(Modifier.Keyword modifier) {
        for (Modifier m : getModifiers()) {
            if (m.getKeyword() == modifier) {
                return true;
            }
        }
        return false;
    }

    /**
     * Creates a list of modifier nodes corresponding to the keywords passed, and set it.
     */
    default N setModifiers(final Modifier.Keyword... modifiers) {
        return setModifiers(Arrays.stream(modifiers).map(Modifier::new).collect(toNodeList()));
    }

    /**
     * @return the access specifier as far as it can be derived from the modifiers.
     * Does not take anything else into account (like "interface methods are implicitly public")
     */
    default AccessSpecifier getAccessSpecifier() {
        for (Modifier modifier : getModifiers()) {
            switch (modifier.getKeyword()) {
                case PUBLIC:
                    return AccessSpecifier.PUBLIC;
                case PROTECTED:
                    return AccessSpecifier.PROTECTED;
                case PRIVATE:
                    return AccessSpecifier.PRIVATE;
            }
        }
        return AccessSpecifier.PACKAGE_PRIVATE;
    }
}