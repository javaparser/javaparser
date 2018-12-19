package com.github.javaparser;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;

import java.util.EnumSet;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Helper class for {@link GeneratedJavaParser}
 */
class ModifierHolder {
    final EnumSet<Modifier> modifiers;
    final NodeList<AnnotationExpr> annotations;
    final JavaToken begin;

    ModifierHolder(JavaToken begin, EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations) {
        this.begin = begin;
        this.modifiers = assertNotNull(modifiers);
        this.annotations = annotations;
    }
}
