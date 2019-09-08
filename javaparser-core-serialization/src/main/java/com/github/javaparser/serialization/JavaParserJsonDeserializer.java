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

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.Log;

import javax.json.*;
import java.util.*;

import static com.github.javaparser.ast.NodeList.toNodeList;
import static com.github.javaparser.metamodel.JavaParserMetaModel.getNodeMetaModel;
import static com.github.javaparser.serialization.JavaParserJsonSerializer.*;

/**
 * Deserializes the JSON file that was built by {@link JavaParserJsonSerializer}.
 */
public class JavaParserJsonDeserializer {
    /**
     * Deserializes json, contained by JsonReader, into AST node.
     * The root node and all its child nodes will be deserialized.
     * @param reader json-p reader (object-level reader, <a href="https://javaee.github.io/jsonp/">see their docs</a>)
     * @return the root level deserialized node
     */
    public Node deserializeObject(JsonReader reader) {
        Log.info("Deserializing JSON to Node.");
        JsonObject jsonObject = reader.readObject();
        return deserializeObject(jsonObject);
    }

    /**
     * Recursive depth-first deserializing method that creates a Node instance from JsonObject.
     *
     * @param nodeJson json object at current level containg values as properties
     * @return deserialized node including all children.
     * @implNote the Node instance will be constructed by the properties defined in the meta model.
     *           Non meta properties will be set after Node is instantiated.
     * @implNote comment is included in the propertyKey meta model, but not set when constructing the Node instance.
     *           That is, comment is not included in the constructor propertyKey list, and therefore needs to be set
     *           after constructing the node.
     *           See {@link com.github.javaparser.metamodel.BaseNodeMetaModel#construct(Map)} how the node is contructed
     */
    private Node deserializeObject(JsonObject nodeJson) {
        try {
            String serializedNodeType = nodeJson.getString(JsonNode.CLASS.propertyKey);
            BaseNodeMetaModel nodeMetaModel = getNodeMetaModel(Class.forName(serializedNodeType))
                    .orElseThrow(() -> new IllegalStateException("Trying to deserialize an unknown node type: " + serializedNodeType));
            Map<String, Object> parameters = new HashMap<>();
            Map<String, JsonValue> deferredJsonValues = new HashMap<>();

            for (String name : nodeJson.keySet()) {
                if (name.equals(JsonNode.CLASS.propertyKey)) {
                    continue;
                }

                Optional<PropertyMetaModel> optionalPropertyMetaModel = nodeMetaModel.getAllPropertyMetaModels().stream()
                        .filter(mm -> mm.getName().equals(name))
                        .findFirst();
                if (!optionalPropertyMetaModel.isPresent()) {
                    deferredJsonValues.put(name, nodeJson.get(name));
                    continue;
                }

                PropertyMetaModel propertyMetaModel = optionalPropertyMetaModel.get();
                if (propertyMetaModel.isNodeList()) {
                    JsonArray nodeListJson = nodeJson.getJsonArray(name);
                    parameters.put(name, deserializeNodeList(nodeListJson));
                } else if (propertyMetaModel.isNode()) {
                    parameters.put(name, deserializeObject(nodeJson.getJsonObject(name)));
                } else {
                    Class<?> type = propertyMetaModel.getType();
                    if (type == String.class) {
                        parameters.put(name, nodeJson.getString(name));
                    } else if (type == boolean.class) {
                        parameters.put(name, Boolean.parseBoolean(nodeJson.getString(name)));
                    } else if (Enum.class.isAssignableFrom(type)) {
                        parameters.put(name, Enum.valueOf((Class<? extends Enum>) type, nodeJson.getString(name)));
                    } else {
                        throw new IllegalStateException("Don't know how to convert: " + type);
                    }
                }
            }

            Node node = nodeMetaModel.construct(parameters);
            // COMMENT is in the propertyKey meta model, but not required as constructor parameter.
            // Set it after construction
            if (parameters.containsKey(JsonNode.COMMENT.propertyKey)) {
                node.setComment((Comment)parameters.get(JsonNode.COMMENT.propertyKey));
            }

            for (String name : deferredJsonValues.keySet()) {
                if (!readNonMetaProperties(name, deferredJsonValues.get(name), node)) {
                    throw new IllegalStateException("Unknown propertyKey: " + nodeMetaModel.getQualifiedClassName() + "." + name);
                }
            }
            setSymbolResolverIfCompilationUnit(node);

            return node;
        } catch (ClassNotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    private NodeList<?> deserializeNodeList(JsonArray nodeListJson) {
        return nodeListJson.stream().map(nodeJson -> deserializeObject((JsonObject) nodeJson)).collect(toNodeList());
    }

    /**
     * Reads properties from json not included in meta model (i.e., RANGE and TOKEN_RANGE).
     * When read, it sets the deserialized value to the node instance.
     * @param name propertyKey name for json value
     * @param jsonValue json value that needs to be deserialized for this propertyKey
     * @param node instance to which the deserialized value will be set to
     * @return true if propertyKey is read from json and set to Node instance
     */
    protected boolean readNonMetaProperties(String name, JsonValue jsonValue, Node node) {
        return readRange(name, jsonValue, node)
                || readTokenRange(name, jsonValue, node);
    }

    protected boolean readRange(String name, JsonValue jsonValue, Node node) {
        if (name.equals(JsonNode.RANGE.propertyKey)) {
            JsonObject jsonObject = (JsonObject)jsonValue;
            Position begin = new Position(
                    jsonObject.getInt(JsonRange.BEGIN_LINE.propertyKey),
                    jsonObject.getInt(JsonRange.BEGIN_COLUMN.propertyKey)
            );
            Position end = new Position(
                    jsonObject.getInt(JsonRange.END_LINE.propertyKey),
                    jsonObject.getInt(JsonRange.END_COLUMN.propertyKey)
            );
            node.setRange(new Range(begin, end));
            return true;
        }
        return false;
    }

    protected boolean readTokenRange(String name, JsonValue jsonValue, Node node) {
        if (name.equals(JsonNode.TOKEN_RANGE.propertyKey)) {
            JsonObject jsonObject = (JsonObject)jsonValue;
            JavaToken begin = readToken(
                    JsonTokenRange.BEGIN_TOKEN.propertyKey, jsonObject
            );
            JavaToken end = readToken(
                    JsonTokenRange.END_TOKEN.propertyKey, jsonObject
            );
            node.setTokenRange(new TokenRange(begin, end));
            return true;
        }
        return false;
    }

    protected JavaToken readToken(String name, JsonObject jsonObject) {
        JsonObject tokenJson = jsonObject.getJsonObject(name);
        return new JavaToken(
                tokenJson.getInt(JsonToken.KIND.propertyKey),
                tokenJson.getString(JsonToken.TEXT.propertyKey)
        );
    }

    /**
     * This method sets symbol resolver to Node if it is an instance of CompilationUnit
     * and a SymbolResolver is configured in the static configuration. This is necessary to be able to resolve symbols
     * within the cu after deserialization. Normally, when parsing java with JavaParser, the symbol resolver is injected
     * to the cu as a data element with key SYMBOL_RESOLVER_KEY.
     * @param node instance to which symbol resolver will be set to when instance of a Compilation Unit
     * @see com.github.javaparser.ast.Node#SYMBOL_RESOLVER_KEY
     * @see com.github.javaparser.ParserConfiguration#ParserConfiguration()
     */
    private void setSymbolResolverIfCompilationUnit(Node node) {
        if (node instanceof CompilationUnit && StaticJavaParser.getConfiguration().getSymbolResolver().isPresent()) {
            CompilationUnit cu = (CompilationUnit)node;
            cu.setData(Node.SYMBOL_RESOLVER_KEY, StaticJavaParser.getConfiguration().getSymbolResolver().get());
        }
    }


}
