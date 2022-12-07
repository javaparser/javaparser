package com.github.javaparser.ast.type;

import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.types.ResolvedType;

/**
 * Convert a {@link Type} into a {@link ResolvedType}.
 *
 */
public interface ConvertibleToUsage {

	ResolvedType convertToUsage(Context context);
}
