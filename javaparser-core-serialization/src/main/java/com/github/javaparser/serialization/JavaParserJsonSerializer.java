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

import static com.github.javaparser.utils.Utils.decapitalize;
import static java.util.Objects.requireNonNull;

/**
 * Serializes an AST or a partial AST to JSON.
 */
public class JavaParserJsonSerializer {

    /**
     * Serializes node and all its children into json. Any node siblings will be ignored.
     *
     * @param node the node that will be the root level json object
     * @param generator the json-p generator for writing the json
     * @see <a href="https://javaee.github.io/jsonp/">json-p</a>
     */
    public void serialize(Node node, JsonGenerator generator) {
        requireNonNull(node);
        Log.info("Serializing Node to JSON.");
        try {
            serialize(null, node, generator);
        } finally {
            generator.close();
        }
    }

    /**
     * Recursive depth-first method that serializes nodes into json
     *
     * @param nodeName nullable String. If null, it is the root object, otherwise it is the property key for the object
     * @param node the current node to be serialized
     * @param generator the json-p generator for writing the json
     */

    private void serialize(String nodeName, Node node, JsonGenerator generator) {
        requireNonNull(node);
        BaseNodeMetaModel nodeMetaModel = JavaParserMetaModel.getNodeMetaModel(node.getClass()).orElseThrow(() -> new IllegalStateException("Unknown Node: " + node.getClass()));

        if (nodeName == null) {
            generator.writeStartObject();
        } else {
            generator.writeStartObject(nodeName);
        }
        generator.write(JsonNode.CLASS.propertyKey, node.getClass().getName());
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
                } else if (propertyMetaModel.isNode()) {
                    serialize(name, (Node) value, generator);
                } else {
                    generator.write(name, value.toString());
                }
            }
        }
        generator.writeEnd();
    }

    /***
     * This method writes json for properties not included in meta model (i.e., RANGE and TOKEN_RANGE).
     * This method could be overriden so that - for example - tokens are not written to json to save space
     *
     * @see com.github.javaparser.metamodel.BaseNodeMetaModel#getAllPropertyMetaModels()
     */

    protected void writeNonMetaProperties(Node node, JsonGenerator generator) {
        this.writeRange(node, generator);
        this.writeTokens(node, generator);
    }

    protected void writeRange(Node node, JsonGenerator generator) {
        if (node.getRange().isPresent()) {
            Range range = node.getRange().get();
            generator.writeStartObject(JsonNode.RANGE.propertyKey);
            generator.write(JsonRange.BEGIN_LINE.propertyKey, range.begin.line);
            generator.write(JsonRange.BEGIN_COLUMN.propertyKey, range.begin.column);
            generator.write(JsonRange.END_LINE.propertyKey, range.end.line);
            generator.write(JsonRange.END_COLUMN.propertyKey, range.end.column);
            generator.writeEnd();
        }
    }

    protected void writeTokens(Node node, JsonGenerator generator) {
        if (node.getTokenRange().isPresent()) {
            TokenRange tokenRange = node.getTokenRange().get();
            generator.writeStartObject(JsonNode.TOKEN_RANGE.propertyKey);
            writeToken(JsonTokenRange.BEGIN_TOKEN.propertyKey, tokenRange.getBegin(), generator);
            writeToken(JsonTokenRange.END_TOKEN.propertyKey, tokenRange.getEnd(), generator);
            generator.writeEnd();
        }
    }

    protected void writeToken(String name, JavaToken token, JsonGenerator generator) {
        generator.writeStartObject(name);
        generator.write(JsonToken.KIND.propertyKey, token.getKind());
        generator.write(JsonToken.TEXT.propertyKey, token.getText());
        generator.writeEnd();
    }

    /**
     * excludes properties from meta model (except comment)
     **/
    public enum JsonNode {
        RANGE("range"),
        TOKEN_RANGE("tokenRange"),
        COMMENT(decapitalize(JavaParserMetaModel.commentMetaModel.getTypeName())),
        CLASS("!");
        final String propertyKey;

        JsonNode(String p) {
            this.propertyKey = p;
        }

        public String toString() {
            return this.propertyKey;
        }
    }

    public enum JsonRange {
        BEGIN_LINE("beginLine"),
        BEGIN_COLUMN("beginColumn"),
        END_LINE("endLine"),
        END_COLUMN("endColumn");
        final String propertyKey;

        JsonRange(String p) {
            this.propertyKey = p;
        }

        public String toString() {
            return this.propertyKey;
        }
    }

    public enum JsonTokenRange {
        BEGIN_TOKEN("beginToken"),
        END_TOKEN("endToken");
        final String propertyKey;

        JsonTokenRange(String p) {
            this.propertyKey = p;
        }

        public String toString() {
            return this.propertyKey;
        }
    }

    public enum JsonToken {
        TEXT("text"),
        KIND("kind");
        final String propertyKey;

        JsonToken(String p) {
            this.propertyKey = p;
        }

        public String toString() {
            return this.propertyKey;
        }
    }
}
