package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.ArrayBracketPair;

import java.util.List;

public interface NodeWithArrayBrackets<T> {
	List<ArrayBracketPair> getArrayBracketPairs();

	T setArrayBracketPairs(List<ArrayBracketPair> arrayBracketPairs);
}
