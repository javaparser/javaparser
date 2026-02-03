package com.github.javaparser.generators.key;

import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

import java.util.Set;
import java.util.TreeSet;

/**
 * @author Alexander Weigl
 * @version 1 (11/7/21)
 */
public class TypeRewriter extends ModifierVisitor<Void> {
    public static final Set<String> NODE_TYPES = new TreeSet<>();

    static {
        for (BaseNodeMetaModel nodeMetaModel : JavaParserMetaModel.getNodeMetaModels()) {
            NODE_TYPES.add(nodeMetaModel.getTypeName());
        }
        NODE_TYPES.add("NodeList");
    }

    @Override
    public Visitable visit(ClassOrInterfaceType type, Void arg) {
        String n = type.getNameAsString();

        if (NODE_TYPES.contains(n)) {
            var t = new ClassOrInterfaceType(null, new SimpleName("I" + n),
                    type.getTypeArguments().orElse(null), type.getAnnotations());
            return super.visit(t, arg);
        }

        return super.visit(type, arg);
    }
        /*final var typeArguments = type.getTypeArguments();
        if (typeArguments.isPresent()) {
            for (Type t : typeArguments.get()) {
                String n2 = t.asClassOrInterfaceType().getNameAsString();
                if (t.isClassOrInterfaceType() && nodeTypes.contains(n2)) {
                    c.replace(t, new ClassOrInterfaceType(null,
                            "I" + t.asClassOrInterfaceType().getName()));
                }
            }
        }*/
}
