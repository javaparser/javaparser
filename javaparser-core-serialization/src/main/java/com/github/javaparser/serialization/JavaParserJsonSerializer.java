/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2018 The JavaParser Team.
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
package com.github.javaparser.serialization;

import com.github.javaparser.JavaToken;
import com.github.javaparser.Range;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.Log;

import javax.json.stream.JsonGenerator;
import java.util.EnumSet;

import static java.util.Objects.requireNonNull;

/**
 * Serializes an AST or a partial AST to JSON.
 */
public class JavaParserJsonSerializer {
    public static final String SERIALIZED_CLASS_KEY = "!";

    public void serialize(Node node, JsonGenerator generator) {
        requireNonNull(node);
        Log.info("Serializing Node to JSON.");
        serialize(null, node, generator);
    }

    private void serialize(String nodeName, Node node, JsonGenerator generator) {
        requireNonNull(node);
        BaseNodeMetaModel nodeMetaModel = JavaParserMetaModel.getNodeMetaModel(node.getClass()).orElseThrow(() -> new IllegalStateException("Unknown Node: " + node.getClass()));

        if (nodeName == null) {
            generator.writeStartObject();
        } else {
            generator.writeStartObject(nodeName);
        }
        generator.write(SERIALIZED_CLASS_KEY, node.getClass().getName());
        this.writeNonMetaProperties(node, generator);
        for (PropertyMetaModel propertyMetaModel : nodeMetaModel.getAllPropertyMetaModels()) {
            String name = propertyMetaModel.getName();
            Object value = propertyMetaModel.getValue(node);
            if (value != null) {
                if (propertyMetaModel.isNodeList()) {
                    NodeList<Node> list = (NodeList<Node>) value;
                    generator.writeStartArray(name);
                    for (Node n : list) {
                        serialize(null, n, generator);
                    }
                    generator.writeEnd();
                } else if (propertyMetaModel.isEnumSet()) {
                    EnumSet<? extends Enum> set = (EnumSet<? extends Enum>) value;
                    generator.writeStartArray(name);
                    for (Enum n : set) {
                        generator.write(n.name());
                    }
                    generator.writeEnd();
                } else if (propertyMetaModel.isNode()) {
                    serialize(name, (Node) value, generator);
                } else {
                    generator.write(name, value.toString());
                }
            }
        }
        generator.writeEnd();
    }

    protected void writeNonMetaProperties(Node node, JsonGenerator generator) {
        this.writeRange(node, generator);
        this.writeTokens(node, generator);
    }

    protected void writeRange(Node node, JsonGenerator generator) {
        if (node.getRange().isPresent()) {
            Range range = node.getRange().get();
            generator.writeStartObject("range");
            generator.write("beginLine", range.begin.line);
            generator.write("beginColumn", range.begin.column);
            generator.write("endLine", range.end.line);
            generator.write("endColumn", range.end.column);
            generator.writeEnd();
        }
    }

    protected void writeTokens(Node node, JsonGenerator generator) {
        if (node.getTokenRange().isPresent()) {
            TokenRange tokenRange = node.getTokenRange().get();
            generator.writeStartObject("tokenRange");
            writeToken("beginToken", tokenRange.getBegin(), generator);
            writeToken("endToken", tokenRange.getEnd(), generator);
            generator.writeEnd();
        }
    }

    protected void writeToken(String name, JavaToken token, JsonGenerator generator) {
        generator.writeStartObject(name);
        generator.write("kind", token.getKind());
        generator.write("text", token.getText());
        generator.writeEnd();
    }

}
