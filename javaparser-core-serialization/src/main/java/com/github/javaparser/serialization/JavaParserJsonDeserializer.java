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
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.PropertyMetaModel;
import com.github.javaparser.utils.Log;

import javax.json.*;
import java.util.*;
import java.util.stream.Collectors;

import static com.github.javaparser.ast.NodeList.toNodeList;
import static com.github.javaparser.metamodel.JavaParserMetaModel.getNodeMetaModel;
import static com.github.javaparser.serialization.JavaParserJsonSerializer.SERIALIZED_CLASS_KEY;

/**
 * Deserializes the JSON file that was built by {@link JavaParserJsonSerializer}.
 */
public class JavaParserJsonDeserializer {

    public Node deserializeObject(JsonReader reader) {
        Log.info("Deserializing JSON to Node.");
        JsonObject jsonObject = reader.readObject();
        return deserializeObject(jsonObject);
    }

    private Node deserializeObject(JsonObject nodeJson) {
        try {
            String serializedNodeType = nodeJson.getString(SERIALIZED_CLASS_KEY);
            BaseNodeMetaModel nodeMetaModel = getNodeMetaModel(Class.forName(serializedNodeType))
                    .orElseThrow(() -> new IllegalStateException("Trying to deserialize an unknown node type: " + serializedNodeType));
            Map<String, Object> parameters = new HashMap<>();
            Map<String, JsonValue> deferredJsonValues = new HashMap<>();

            for (String name : nodeJson.keySet()) {
                if (name.equals(SERIALIZED_CLASS_KEY)) {
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
            // Note: comment is a property meta model, but it is not listed as constructor parameter and not attached to node
            // @see BaseNodeMetaModel.getConstructorParameters
            if (parameters.containsKey("comment")) {
                node.setComment((Comment)parameters.get("comment"));
            }

            for (String name : deferredJsonValues.keySet()) {
                if (!readNonMetaProperties(name, deferredJsonValues.get(name), node)) {
                    throw new IllegalStateException("Unknown property: " + nodeMetaModel.getQualifiedClassName() + "." + name);
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

    protected boolean readNonMetaProperties(String name, JsonValue jsonValue, Node node) {
        return readRange(name, jsonValue, node)
                || readTokenRange(name, jsonValue, node);
    }

    protected boolean readRange(String name, JsonValue jsonValue, Node node) {
        if (name.equals("range")) {
            JsonObject jsonObject = (JsonObject)jsonValue;
            Position begin = new Position(jsonObject.getInt("beginLine"), jsonObject.getInt("beginColumn"));
            Position end = new Position(jsonObject.getInt("endLine"), jsonObject.getInt("endColumn"));
            node.setRange(new Range(begin, end));
            return true;
        }
        return false;
    }

    protected boolean readTokenRange(String name, JsonValue jsonValue, Node node) {
        if (name.equals("tokenRange")) {
            JsonObject jsonObject = (JsonObject)jsonValue;
            JavaToken begin = readToken("beginToken", jsonObject);
            JavaToken end = readToken("endToken", jsonObject);
            node.setTokenRange(new TokenRange(begin, end));
            return true;
        }
        return false;
    }

    protected JavaToken readToken(String name, JsonObject jsonObject) {
        JsonObject tokenJson = jsonObject.getJsonObject(name);
        return new JavaToken(
                tokenJson.getInt("kind"),
                tokenJson.getString("text")
        );
    }

    private void setSymbolResolverIfCompilationUnit(Node node) {
        if (node instanceof CompilationUnit && JavaParser.getStaticConfiguration().getSymbolResolver().isPresent()) {
            CompilationUnit cu = (CompilationUnit)node;
            cu.setData(Node.SYMBOL_RESOLVER_KEY, JavaParser.getStaticConfiguration().getSymbolResolver().get());
        }
    }
}
