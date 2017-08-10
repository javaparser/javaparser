package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;

import java.util.Optional;

/**
 * This validator validates according to Java 5 syntax rules.
 */
public class Java5Validator extends Java1_4Validator {
    Validator genericsWithoutDiamondOperator = new TreeVisitorValidator((node, reporter) -> {
        if (node instanceof NodeWithTypeArguments) {
            Optional<NodeList<Type>> typeArguments = ((NodeWithTypeArguments<? extends Node>) node).getTypeArguments();
            if (typeArguments.isPresent() && typeArguments.get().isEmpty()) {
                reporter.report(node, "The diamond operator is not supported.");
            }
        }
    });

    protected Validator noPrimitiveGenericArguments = new TreeVisitorValidator((node, reporter) -> {
        if (node instanceof NodeWithTypeArguments) {
            Optional<NodeList<Type>> typeArguments = ((NodeWithTypeArguments<? extends Node>) node).getTypeArguments();
            typeArguments.ifPresent(types -> types.forEach(ty -> {
                if (ty instanceof PrimitiveType) {
                    reporter.report(node, "Type arguments may not be primitive.");
                }
            }));
        }
    });

    protected final Validator enumNotAllowed = new ReservedKeywordValidator("enum");

    public Java5Validator() {
        super();
        replace(noGenerics, genericsWithoutDiamondOperator);
        add(noPrimitiveGenericArguments);
        add(enumNotAllowed);
        
        // TODO validate annotations on classes, fields and methods but nowhere else
        // The following is probably too simple.
        remove(noAnnotations);

        remove(noEnums);
        remove(noVarargs);
        remove(noForEach);
        remove(noStaticImports);
    }
}
