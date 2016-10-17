package me.tomassetti.symbolsolver.logic;

import javaslang.Tuple2;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class GenericTypeInferenceLogic {

    public static Map<String, Type> inferGenericTypes(List<Tuple2<Type, Type>> formalActualTypePairs) {
        Map<String, Type> map = new HashMap<>();

        for (Tuple2<Type, Type> formalActualTypePair : formalActualTypePairs) {
            Type formalType = formalActualTypePair._1;
            Type actualType = formalActualTypePair._2;
            consider(map, formalType, actualType);
            // we can infer also in the other direction
            consider(map, actualType, formalType);
        }

        return map;
    }

    private static void consider(Map<String, Type> map, Type formalType, Type actualType) {
        if (formalType == null) {
            throw new IllegalArgumentException();
        }
        if (actualType == null) {
            throw new IllegalArgumentException();
        }
        if (formalType.isTypeVariable()) {
            if (map.containsKey(formalType.asTypeParameter().getName())) {
                if (!actualType.equals(map.get(formalType.asTypeParameter().getName()))) {
                    throw new UnsupportedOperationException("Map already contains " + formalType);
                }
            }
            map.put(formalType.asTypeParameter().getName(), actualType);
        } else if (formalType.isReferenceType()) {
            if (actualType.isReferenceType()) {
                ReferenceType formalTypeAsReference = formalType.asReferenceType();
            	ReferenceType actualTypeAsReference = actualType.asReferenceType();
                if (formalTypeAsReference.getQualifiedName().equals(actualTypeAsReference.getQualifiedName())) {
                    if (!formalTypeAsReference.typeParametersValues().isEmpty()) {
                        if (actualTypeAsReference.isRawType()) {
                            // nothing to do
                        } else {
                            int i = 0;
                            for (Type formalTypeParameter : formalTypeAsReference.typeParametersValues()) {
                                consider(map, formalTypeParameter, actualTypeAsReference.typeParametersValues().get(i));
                                i++;
                            }
                        }
                    }
                }
                // TODO: consider cases where the actual type extends or implements the formal type. Here the number and order of type typeParametersValues can be different.
            } else if (actualType.isTypeVariable()) {
                // nothing to do
            } else if (actualType.isWildcard()) {
                // nothing to do
            } else if (actualType.isPrimitive()) {
                // nothing to do
            } else {
                throw new UnsupportedOperationException(actualType.getClass().getCanonicalName());
            }
        } else if (formalType.isWildcard()) {
            if (actualType.isWildcard()) {
                if (actualType.asWildcard().isExtends() && formalType.asWildcard().isExtends()) {
                    consider(map, formalType.asWildcard().getBoundedType(), actualType.asWildcard().getBoundedType());
                } else if (actualType.asWildcard().isSuper() && formalType.asWildcard().isSuper()) {
                    consider(map, formalType.asWildcard().getBoundedType(), actualType.asWildcard().getBoundedType());
                }
            }
        } else if (formalType.isPrimitive()) {
            // nothing to do
        } else if (formalType.isArray()) {
            if (actualType.isArray()) {
                consider(map, formalType.asArrayType().getComponentType(), actualType.asArrayType().getComponentType());
            }
        } else {
            throw new UnsupportedOperationException(formalType.describe());
        }
    }

}
