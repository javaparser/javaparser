/*
 *
 *  * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 *  * Copyright (C) 2011, 2013-2023 The JavaParser Team.
 *  *
 *  * This file is part of JavaParser.
 *  *
 *  * JavaParser can be used either under the terms of
 *  * a) the GNU Lesser General Public License as published by
 *  *     the Free Software Foundation, either version 3 of the License, or
 *  *     (at your option) any later version.
 *  * b) the terms of the Apache License
 *  *
 *  * You should have received a copy of both licenses in LICENCE.LGPL and
 *  * LICENCE.APACHE. Please refer to those files for details.
 *  *
 *  * JavaParser is distributed in the hope that it will be useful,
 *  * but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  * GNU Lesser General Public License for more details.
 *
 */

package com.github.javaparser.symbolsolver.utils;

import com.github.javaparser.ast.Modifier.Keyword;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.nodeTypes.modifiers.*;
import javassist.CtClass;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;

public class ModifierUtils {

    private static Method isSealedMethod;

    private static boolean checkedIsSealedMethod = false;

    public static boolean hasModifier(NodeWithModifiers<?> node, Keyword keyword) {
        switch (keyword) {
            case STATIC:
                if (node instanceof NodeWithStaticModifier<?>) {
                    return ((NodeWithStaticModifier<?>) node).isStatic();
                }
                break;
            case FINAL:
                if (node instanceof NodeWithFinalModifier<?>) {
                    return ((NodeWithFinalModifier<?>) node).isFinal();
                }
                break;
            case PROTECTED:
                if (node instanceof NodeWithProtectedModifier<?>) {
                    return ((NodeWithProtectedModifier<?>) node).isProtected();
                }
                break;
            case PUBLIC:
                if (node instanceof NodeWithPublicModifier<?>) {
                    return ((NodeWithPublicModifier<?>) node).isPublic();
                }
                break;
            case PRIVATE:
                if (node instanceof NodeWithPrivateModifier<?>) {
                    return ((NodeWithPrivateModifier<?>) node).isPrivate();
                }
                break;
            case ABSTRACT:
                if (node instanceof NodeWithAbstractModifier<?>) {
                    return ((NodeWithAbstractModifier<?>) node).isAbstract();
                }
                break;
            case STRICTFP:
                if (node instanceof NodeWithStrictfpModifier<?>) {
                    return ((NodeWithStrictfpModifier<?>) node).isStrictfp();
                }
                break;
        }

        return node.hasModifier(keyword);
    }

    public static boolean hasModifier(Object reflectionObject, int modifiers, Keyword keyword) {
        switch (keyword) {
            case DEFAULT:
                if(reflectionObject instanceof Method) {
                    return ((Method) reflectionObject).isDefault();
                }
                break;
            case PUBLIC:
                return Modifier.isPublic(modifiers);
            case PROTECTED:
                return Modifier.isProtected(modifiers);
            case PRIVATE:
                return Modifier.isPrivate(modifiers);
            case ABSTRACT:
                return Modifier.isAbstract(modifiers);
            case STATIC:
                return Modifier.isStatic(modifiers);
            case FINAL:
                return Modifier.isFinal(modifiers);
            case TRANSIENT:
                return Modifier.isTransient(modifiers);
            case VOLATILE:
                return Modifier.isVolatile(modifiers);
            case SYNCHRONIZED:
                return Modifier.isSynchronized(modifiers);
            case NATIVE:
                return Modifier.isNative(modifiers);
            case STRICTFP:
                return Modifier.isStrict(modifiers);
            case TRANSITIVE:
                /*
                 * Only modules can be transitive!
                 */
                return false;
            case SEALED:
            case NON_SEALED:
                if (reflectionObject instanceof Class<?>) {
                    try {
                        if (isSealedMethod == null && !checkedIsSealedMethod) {
                            checkedIsSealedMethod = true;
                            isSealedMethod = ((Class<?>) reflectionObject).getDeclaredMethod("isSealed");
                        }
                        if (isSealedMethod != null) {
                            boolean tempResult = (boolean) isSealedMethod.invoke(reflectionObject);
                            return (keyword == Keyword.SEALED) == tempResult;
                        }
                    } catch (Throwable e) {
                        //If anything goes wrong, then we are probably on a java version below 15 and the method is not present!
                    }
                } else if(reflectionObject instanceof CtClass) {
                    //TODO how can we check this?
                    return false;
                }
                return false;
        }

        return false;
    }
}
