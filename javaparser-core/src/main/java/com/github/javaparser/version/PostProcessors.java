/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.version;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.Node;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static com.github.javaparser.ParseResult.PostProcessor;

/**
 * A post processor that will call a collection of post processors.
 */
public class PostProcessors implements PostProcessor {
    private final List<PostProcessor> postProcessors = new ArrayList<>();

    public PostProcessors(PostProcessor... postProcessors) {
        this.postProcessors.addAll(Arrays.asList(postProcessors));
    }

    public List<PostProcessor> getPostProcessors() {
        return postProcessors;
    }

    public PostProcessors remove(PostProcessor postProcessor) {
        if (!postProcessors.remove(postProcessor)) {
            throw new AssertionError("Trying to remove a post processor that isn't there.");
        }
        return this;
    }

    public PostProcessors replace(PostProcessor oldProcessor, PostProcessor newProcessor) {
        remove(oldProcessor);
        add(newProcessor);
        return this;
    }

    public PostProcessors add(PostProcessor newProcessor) {
        postProcessors.add(newProcessor);
        return this;
    }

    @Override
    public void process(ParseResult<? extends Node> result, ParserConfiguration configuration) {
        postProcessors.forEach(pp -> pp.process(result, configuration));
    }
}
