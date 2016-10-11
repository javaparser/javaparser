package me.tomassetti.symbolsolver.logic;

import javaslang.Tuple2;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class GenericTypeInferenceLogic {

    public static Map<String, TypeUsage> inferGenericTypes(List<Tuple2<TypeUsage, TypeUsage>> formalActualTypePairs) {
        Map<String, TypeUsage> map = new HashMap<>();

        for (Tuple2<TypeUsage, TypeUsage> formalActualTypePair : formalActualTypePairs) {
            TypeUsage formalType = formalActualTypePair._1;
            TypeUsage actualType = formalActualTypePair._2;
            consider(map, formalType, actualType);
            // we can infer also in the other direction
            consider(map, actualType, formalType);
        }

        return map;
    }

    private static void consider(Map<String, TypeUsage> map, TypeUsage formalType, TypeUsage actualType) {
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
                ReferenceTypeUsage formalTypeAsReference = formalType.asReferenceTypeUsage();
            	ReferenceTypeUsage actualTypeAsReference = actualType.asReferenceTypeUsage();
                if (formalTypeAsReference.getQualifiedName().equals(actualTypeAsReference.getQualifiedName())) {
                    if (!formalTypeAsReference.parameters().isEmpty()) {
                        if (actualTypeAsReference.isRawType()) {
                            // nothing to do
                        } else {
                            int i = 0;
                            for (TypeUsage formalTypeParameter : formalTypeAsReference.parameters()) {
                                consider(map, formalTypeParameter, actualTypeAsReference.parameters().get(i));
                                i++;
                            }
                        }
                    }
                }
                // TODO: consider cases where the actual type extends or implements the formal type. Here the number and order of type parameters can be different.
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
                consider(map, formalType.asArrayTypeUsage().getComponentType(), actualType.asArrayTypeUsage().getComponentType());
            }
        } else {
            throw new UnsupportedOperationException(formalType.describe());
        }
    }

}
