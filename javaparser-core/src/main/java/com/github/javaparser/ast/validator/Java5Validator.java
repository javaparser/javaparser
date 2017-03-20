package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.type.Type;

import java.util.Optional;

/**
 * This validator validates according to Java 5 syntax rules.
 */
public class Java5Validator extends Java1_4Validator {
    protected Validator genericsWithoutDiamondOperator = new TreeVisitorValidator() {
        @Override
        public void process(Node node, ProblemReporter reporter) {
            if (node instanceof NodeWithTypeArguments) {
                Optional<NodeList<Type>> typeArguments = ((NodeWithTypeArguments<? extends Node>) node).getTypeArguments();
                if(typeArguments.isPresent() &&typeArguments.get().isEmpty()){
                    reporter.report(node, "The diamond operator is not supported.");
                }
            }
        }
    };

    public Java5Validator() {
        super();
        replace(noGenerics, genericsWithoutDiamondOperator);
        // TODO validate annotations on classes, fields and methods but nowhere else
        // TODO validate enums
        // TODO validate varargs
        // TODO validate for-each
        // TODO validate static imports
    }
}
