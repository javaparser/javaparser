package com.github.javaparser.generator.metamodel;

import com.github.javaparser.ast.NodeList;

import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.lang.reflect.TypeVariable;
import java.lang.reflect.WildcardType;
import java.util.Optional;

import static java.lang.reflect.Modifier.isAbstract;

/**
 * A hacky thing that collects flags we need from AST types to generate the metamodel.
 */
class AstTypeAnalysis {
    final boolean isAbstract;
    boolean isOptional = false;
    boolean isNodeList = false;
    boolean isSelfType = false;
    Class<?> innerType;

    AstTypeAnalysis(Type type) {
        if (type instanceof Class<?>) {
            TypeVariable<? extends Class<?>>[] typeParameters = ((Class<?>) type).getTypeParameters();
            if (typeParameters.length > 0) {
                isSelfType = true;
            }
        } else {
            while (type instanceof ParameterizedType) {
                ParameterizedType t = (ParameterizedType) type;
                Type currentOuterType = t.getRawType();
                if (currentOuterType == NodeList.class) {
                    isNodeList = true;
                }
                if (currentOuterType == Optional.class) {
                    isOptional = true;
                }

                if (t.getActualTypeArguments()[0] instanceof WildcardType) {
                    type = t.getRawType();
                    isSelfType = true;
                    break;
                }
                type = t.getActualTypeArguments()[0];
            }
        }
        innerType = (Class<?>) type;
        isAbstract = isAbstract(innerType.getModifiers());
    }
}
