package com.github.javaparser.resolution.types;

/**
 * @author Alexander Weigl
 * @version 1 (3/2/26)
 */
public interface AssignableToPrimitive {

    boolean isAssignableToPrimitive(ResolvedPrimitiveType primitiveType);
}
