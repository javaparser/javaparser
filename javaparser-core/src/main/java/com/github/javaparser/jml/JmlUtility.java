package com.github.javaparser.jml;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.jml.NodeWithContracts;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.jml.clauses.JmlSignalsClause;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.types.ResolvedType;
import org.jetbrains.annotations.NotNull;

import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.22)
 */
public class JmlUtility {
    public static void fixRangeContracts(@NotNull NodeWithContracts<? extends Node> n) {
        Optional<JmlContract> first;
        var m = ((Node) n);
        var r = m.getRange();

        if (n.getContracts().isPresent()
                && r.isPresent()
                && (first = n.getContracts().get().getFirst()).isPresent()
                && first.get().getRange().isPresent()) {
            m.setRange(r.get().withBegin(first.get().getRange().get().begin));
        }
    }

    public static ResolvedType resolveException(JmlSignalsClause n) {
        var jle = new ClassOrInterfaceType("java.lang.Exception");
        var rjle = n.getSymbolResolver().toResolvedType(jle, ResolvedType.class);
        return rjle;
    }
}
