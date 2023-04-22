/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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
package com.github.javaparser.ast.validator.postprocessors;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Processor;
import com.github.javaparser.ast.Node;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * A post processor that will call a collection of post processors.
 */
public class PostProcessors {

    private final List<Processor> postProcessors = new ArrayList<>();

    public PostProcessors(Processor... postProcessors) {
        this.postProcessors.addAll(Arrays.asList(postProcessors));
    }

    public List<Processor> getPostProcessors() {
        return postProcessors;
    }

    public PostProcessors remove(Processor postProcessor) {
        if (!postProcessors.remove(postProcessor)) {
            throw new AssertionError("Trying to remove a post processor that isn't there.");
        }
        return this;
    }

    public PostProcessors replace(Processor oldProcessor, Processor newProcessor) {
        remove(oldProcessor);
        add(newProcessor);
        return this;
    }

    public PostProcessors add(Processor newProcessor) {
        postProcessors.add(newProcessor);
        return this;
    }

    public void postProcess(ParseResult<? extends Node> result, ParserConfiguration configuration) {
        postProcessors.forEach(pp -> pp.postProcess(result, configuration));
    }
}
