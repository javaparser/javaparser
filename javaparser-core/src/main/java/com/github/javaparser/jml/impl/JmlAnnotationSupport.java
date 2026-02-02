package com.github.javaparser.jml.impl;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import com.github.javaparser.Processor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.visitor.TreeVisitor;
import com.github.javaparser.resolution.types.ResolvedType;
import java.util.List;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (4/10/20)
 */
public class JmlAnnotationSupport extends Processor {

    public final JmlAnnotationConfiguration configuration;

    public JmlAnnotationSupport(JmlAnnotationConfiguration configuration) {
        this.configuration = configuration;
    }

    @Override
    public void postProcess(ParseResult<? extends Node> result, ParserConfiguration configuration) {
        if (result.isSuccessful()) {
            Map<String, Modifier.DefaultKeyword> a2m =
                    JmlAnnotationSupport.this.configuration.getAnnotationToModifier();
            TreeVisitor visitor = new JmlAnnotationTranslator(a2m, result.getProblems());
            result.getResult().ifPresent(visitor::visitPreOrder);
        }
    }
}

class JmlAnnotationTranslator extends TreeVisitor {

    private final Map<String, Modifier.DefaultKeyword> a2m;

    private final ProblemReporter problemReport;

    public JmlAnnotationTranslator(Map<String, Modifier.DefaultKeyword> a2m, List<Problem> problems) {
        this.a2m = a2m;
        problemReport = new ProblemReporter(problems::add);
    }

    @Override
    public void process(Node node) {
        if (node instanceof NodeWithAnnotations<?>) {
            NodeWithAnnotations<?> n = (NodeWithAnnotations<?>) node;
            for (AnnotationExpr annotation : n.getAnnotations()) {
                ResolvedType type = annotation.calculateResolvedType();
                String fqn = type.asReferenceType().getQualifiedName();
                if (a2m.containsKey(fqn)) {
                    try {
                        NodeWithModifiers<?> m = (NodeWithModifiers<?>) node;
                        m.addModifier(a2m.get(fqn));
                    } catch (ClassCastException e) {
                        problemReport.report(
                                annotation,
                                "Could not translate annotation %s into a modifier. "
                                        + "Target node '%s' does support modifiers.",
                                annotation.getName(),
                                node.getMetaModel().getTypeName());
                    }
                }
            }
        }
    }
}
