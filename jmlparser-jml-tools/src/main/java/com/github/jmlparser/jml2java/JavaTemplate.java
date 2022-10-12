package com.github.jmlparser.jml2java;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (10.10.22)
 */
public class JavaTemplate<T extends Node> {
    private final T template;

    public JavaTemplate(T template) {
        this.template = template;
    }

    public static JavaTemplate<BlockStmt> fromBlock(String javaCode) {
        return new JavaTemplate<>(StaticJavaParser.parseBlock(javaCode));
    }

    public static JavaTemplate<Statement> fromStatement(String javaCode) {
        return new JavaTemplate<>(StaticJavaParser.parseStatement(javaCode));
    }

    public static JavaTemplate<TypeDeclaration<?>> fromType(String javaCode) {
        return new JavaTemplate<>(StaticJavaParser.parseTypeDeclaration(javaCode));
    }

    public static JavaTemplate<BodyDeclaration<?>> fromBodyDecl(String javaCode) {
        return new JavaTemplate<>(StaticJavaParser.parseBodyDeclaration(javaCode));
    }

    @SuppressWarnings("unchecked")
    public T instantiate(SubstitutionFactory substitutionFactory) {
        var copy = template.clone();
        replace(copy, substitutionFactory);
        return (T) copy;
    }

    private <R extends Node, O extends Node> void replace(Node node, SubstitutionFactory factory) {
        for (Node childNode : node.getChildNodes()) {
            replace(childNode, factory);
            if (factory.replacable(childNode)) {
                node.replace(childNode, factory.substitutionOf(childNode));
            }
        }
    }

    interface SubstitutionFactory {
        boolean replacable(Node node);

        Node substitutionOf(Node node);
    }

    public static class IdentifierSubstitution implements SubstitutionFactory {
        private final Map<String, String> map;

        public IdentifierSubstitution() {
            this(new HashMap<>());
        }

        public IdentifierSubstitution(Map<String, String> map) {
            this.map = map;
        }

        public void add(String name, String newName) {
            map.put(name, newName);
        }

        @Override
        public boolean replacable(Node node) {
            return node instanceof SimpleName sn && map.containsKey(sn.asString());
        }

        @Override
        public Node substitutionOf(Node node) {
            if (node instanceof SimpleName sn)
                sn.setIdentifier(map.get(sn.asString()));
            return node;
        }
    }
}
