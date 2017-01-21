package com.github.javaparser.metamodel;

import java.lang.reflect.Field;

import static com.github.javaparser.generator.utils.GeneratorUtils.getterName;
import static com.github.javaparser.generator.utils.GeneratorUtils.setterName;

/**
 * Meta-data about a property of a node in the AST.
 */
public class PropertyMetaModel {
    private final BaseNodeMetaModel nodeMetaModel;
    private final String name;
    private final Class<?> type;
    //    public Optional<CommentMetaModel> typeReference;
//    public Optional<Class<Integer>> tpe;
    private final Field reflectionField;
    private final boolean isNode;
    private final boolean isOptional;
    private final boolean isNodeList;
    private final boolean isEnumSet;
    private final boolean hasWildcard;

    public PropertyMetaModel(BaseNodeMetaModel nodeMetaModel, String name, Class<?> type, Field reflectionField, boolean isNode, boolean isOptional, boolean isNodeList, boolean isEnumSet, boolean hasWildcard) {
        this.nodeMetaModel = nodeMetaModel;
        this.name = name;
        this.type = type;
        this.reflectionField = reflectionField;
        this.isNode = isNode;
        this.isOptional = isOptional;
        this.isNodeList = isNodeList;
        this.isEnumSet = isEnumSet;
        this.hasWildcard = hasWildcard;
    }

    public boolean is(Class<?> c, String fieldName) {
        return nodeMetaModel.is(c) && name.equals(fieldName);
    }

    public boolean is(String fieldName) {
        return name.equals(fieldName);
    }

    /**
     * @return the name used in the AST for the setter
     */
    public String getSetterMethodName() {
        return setterName(reflectionField);
    }

    /**
     * @return the name used in the AST for the getter
     */
    public String getGetterMethodName() {
        return getterName(reflectionField);
    }

    public BaseNodeMetaModel getNodeMetaModel() {
        return nodeMetaModel;
    }

    public String getName() {
        return name;
    }

    public Class<?> getType() {
        return type;
    }

    public Field getReflectionField() {
        return reflectionField;
    }

    @Deprecated
    public boolean isNode() {
        return isNode;
    }

    public boolean isOptional() {
        return isOptional;
    }

    public boolean isNodeList() {
        return isNodeList;
    }

    public boolean isEnumSet() {
        return isEnumSet;
    }

    public boolean hasWildcard() {
        return hasWildcard;
    }

    @Override
    public String toString() {
        return "(" + type.getSimpleName() + ")\t" + nodeMetaModel + "#" + name;
    }

    @Override
    public int hashCode() {
        return reflectionField.hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        PropertyMetaModel that = (PropertyMetaModel) o;

        if (!reflectionField.equals(that.reflectionField)) return false;

        return true;
    }

    public String getTypeName() {
        if (hasWildcard) {
            return getRawTypeName() + "<?>";
        }
        return getRawTypeName();
    }

    public String getRawTypeName() {
        return type.getSimpleName();
    }

    public String getFullTypeNameForGetter() {
        if (isOptional) {
            return "Optional<" + getFullTypeNameForSetter() + ">";
        }
        return getFullTypeNameForSetter();
    }

    public String getFullTypeNameForSetter() {
        if (isNodeList) {
            return "NodeList<" + getTypeName() + ">";
        }
        if (isEnumSet) {
            return "EnumSet<" + getTypeName() + ">";
        }
        return getTypeName();
    }
}
