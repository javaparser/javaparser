package com.github.jmlparser.jml2java;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.metamodel.PropertyMetaModel;
import org.jetbrains.annotations.NotNull;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (11.10.22)
 */
public class Pattern<T extends Node> {
    @Nonnull
    private final T pattern;
    @Nonnull
    private final Map<Node, String> placeholders = new IdentityHashMap<>();

    public Pattern(@NotNull T pattern) {
        this.pattern = pattern;
    }


    @Nullable
    public Map<String, Node> match(Node tree) {
        return match(pattern, tree, new HashMap<>());
    }

    @Nullable
    private Map<String, Node> match(Node pattern, Node tree, Map<String, Node> map) {
        if (pattern == null && tree == null) return map;
        if (pattern != null ^ tree != null) return null;

        if (placeholders.containsKey(pattern)) {
            final var key = placeholders.get(pattern);
            if (map.containsKey(key) && !map.get(key).equals(tree))
                return null;
            else
                map.put(key, tree);
            return map;
        }

        if (pattern.getClass() != tree.getClass()) return null;


        for (PropertyMetaModel prop : pattern.getMetaModel().getAllPropertyMetaModels()) {
            final var childPattern = prop.getValue(pattern);
            final var childTree = prop.getValue(tree);

            if (prop.isNode()) {
                map = match((Node) childPattern, (Node) childTree, map);
                if (map == null) return null;
            } else if (prop.isNodeList()) {
                var a = (NodeList<? extends Node>) childPattern;
                var b = (NodeList<? extends Node>) childTree;
                if (a.size() != b.size()) return null;

                for (int i = 0; i < a.size(); i++) {
                    map = match(a.get(i), b.get(i), map);
                    if (map == null) return null;
                }
            } else {
                if (!childPattern.equals(childTree))
                    return null;
            }
        }

        return map;
    }


    public Map<String, Node> find(Node n) {
        var queue = new ArrayDeque<Node>();
        queue.add(n);
        while(!queue.isEmpty()){
            var e = queue.pop();
            var r = match(e);
            if(r!=null) return r;
            queue.addAll(e.getChildNodes());
        }
        return null;
    }

    public void addPlaceholder(Node placeholder, String label) {
        this.placeholders.put(placeholder, label);
    }

}
