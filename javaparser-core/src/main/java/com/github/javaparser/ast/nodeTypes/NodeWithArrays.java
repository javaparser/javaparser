package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.expr.AnnotationExpr;

import java.util.List;

/**
 * A node that has array brackets behind it [][][]
 */
public interface NodeWithArrays<T> {
	int getArrayCount();

	T setArrayCount(int arrayCount);

	/**
	 * <p>Arrays annotations are annotations on the arrays modifiers of the type.
	 * Consider this example:</p>
	 *
	 * <p><pre>
	 * {@code
	 * int @Ann1 [] @Ann2 [] array;
	 * }</pre></p>
	 *
	 * <p>in this this method will return a list with the annotation expressions <pre>@Ann1</pre>
	 * and <pre>@Ann2</pre></p>
	 *
	 * <p>Note that the first list element of arraysAnnotations will refer to the first array modifier encountered.
	 * Considering the example the first element will be a list containing just @Ann1 while the second element will
	 * be a list containing just @Ann2.
	 * </p>
	 *
	 * <p>This property is guaranteed to hold: <pre>{@code getArraysAnnotations().size() == getArrayCount()}</pre>
	 * If a certain array modifier has no annotation the corresponding entry of arraysAnnotations will be null</p>
	 */
	List<List<AnnotationExpr>> getArraysAnnotations();

	/**
	 * For a description of the arrayAnnotations field refer to {@link #getArraysAnnotations()}
	 */
	T setArraysAnnotations(List<List<AnnotationExpr>> arraysAnnotations);
}
