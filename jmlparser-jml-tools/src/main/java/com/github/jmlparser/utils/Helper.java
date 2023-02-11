package com.github.jmlparser.utils;

import com.github.javaparser.ast.Node;

import java.util.ArrayDeque;
import java.util.Queue;
import java.util.function.Function;

/**
 * @author Alexander Weigl
 * @version 1 (11.02.23)
 */
public class Helper {
    public static <T extends Node> Node findAndApply(Class<T> clazz, Node node, Function<T, Node> fn) {
        if (clazz.isAssignableFrom(node.getClass())) {
            return fn.apply((T) node);
        }

        Queue<Node> queue = new ArrayDeque<>(1024);
        queue.add(node);

        while (!queue.isEmpty()) {
            var n = queue.poll();
            if (clazz.isAssignableFrom(node.getClass())) {
                var other = fn.apply((T) n);
                if (other != n) {
                    n.replace(n, other);
                }
            } else {
                //traverse
                queue.addAll(node.getChildNodes());
            }
        }

        return node;
    }
}
