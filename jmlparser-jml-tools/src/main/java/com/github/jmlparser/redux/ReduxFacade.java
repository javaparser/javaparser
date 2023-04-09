package com.github.jmlparser.redux;

import com.github.javaparser.ast.Node;

import java.util.ArrayList;
import java.util.List;
import java.util.ServiceLoader;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class ReduxFacade  {
    private final List<Transformer> transformers = new ArrayList<>();
    private final ReduxConfig config;

    public ReduxFacade(ReduxConfig config) {
        this.config = config;
    }

    public ReduxFacade(ReduxConfig config, List<Transformer> transformers) {
        this(config);
        this.transformers.addAll(transformers);
    }

    public static ReduxFacade create(ReduxConfig config) {
        var sl = ServiceLoader.load(Transformer.class);
        return new ReduxFacade(config, sl.stream()
                .filter(it -> config.isEnabled(it.type().toString()))
                .map(ServiceLoader.Provider::get).toList());
    }

    public List<? extends Node> apply(List<? extends Node> nodes) {
        List<Node> n = new ArrayList<>(nodes.size());
        for (Node node : nodes) {
            for (Transformer transformer : transformers) {
                node = transformer.apply(node);
            }
            n.add(node);
        }
        return n;
    }

}
