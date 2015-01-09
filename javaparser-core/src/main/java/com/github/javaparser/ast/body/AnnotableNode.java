package com.github.javaparser.ast.body;

import com.github.javaparser.ast.expr.AnnotationExpr;

import java.util.List;

/**
 * An element which can be the target of annotations.
 *
 * @author Federico Tomassetti
 * @since July 2014
 */
public interface AnnotableNode {
    public List<AnnotationExpr> getAnnotations();
}
