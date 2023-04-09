package com.github.jmlparser.utils;

import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.Node;

import java.util.*;
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

    public static List<Node> findAllJmlContainers(Node cu) {
        var queue = new LinkedList<Node>();
        queue.add(cu);
        List<Node> res = new ArrayList<>(128);
        while (!queue.isEmpty()) {
            var n = queue.pollLast();
            if (n instanceof Jmlish) {
                res.add(n);
            } else {
                queue.addAll(n.getChildNodes());
            }
        }
        return res;
    }
}
