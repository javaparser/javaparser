package com.github.javaparser;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;

import static com.github.javaparser.Range.range;

/**
 * Helper class for {@link GeneratedJavaParser}
 */
class RangedList<T extends Node> {
    /* A ranged list MUST be set to a begin and end,
       or these temporary values will leak out */
    Range range = range(0, 0, 0, 0);
    NodeList<T> list;

    RangedList(NodeList<T> list) {
        this.list = list;
    }

    void beginAt(Position begin) {
        range = range.withBegin(begin);
    }

    void endAt(Position end) {
        range = range.withEnd(end);
    }

    void add(T t) {
        if (list == null) {
            list = new NodeList<T>();
        }
        list.add(t);
    }
}
