package com.github.javaparser.metamodel;

import com.github.javaparser.ast.Node;

import java.lang.reflect.Field;
import java.util.Optional;

import static com.github.javaparser.utils.CodeGenerationUtils.getterName;
import static com.github.javaparser.utils.CodeGenerationUtils.setterName;

/**
 * Meta-data about a property of a node in the AST.
 */
public class PropertyMetaModel {
    private final BaseNodeMetaModel containingNodeMetaModel;
    private final String name;
    private final Class<?> type;
    private final Optional<BaseNodeMetaModel> nodeReference;
    private final boolean isOptional;
    private final boolean isNonEmpty;
    private final boolean isNodeList;
    private final boolean isEnumSet;
    private final boolean hasWildcard;

    public PropertyMetaModel(BaseNodeMetaModel containingNodeMetaModel, String name, Class<?> type, Optional<BaseNodeMetaModel> nodeReference, boolean isOptional, boolean isNonEmpty, boolean isNodeList, boolean isEnumSet, boolean hasWildcard) {
        this.containingNodeMetaModel = containingNodeMetaModel;
        this.name = name;
        this.type = type;
        this.nodeReference = nodeReference;
        this.isOptional = isOptional;
        this.isNonEmpty = isNonEmpty;
        this.isNodeList = isNodeList;
        this.isEnumSet = isEnumSet;
        this.hasWildcard = hasWildcard;
    }

    /**
     * @return is this the field fieldName on class c?
     */
    public boolean is(Class<? extends Node> c, String fieldName) {
        return containingNodeMetaModel.is(c) && name.equals(fieldName);
    }

    /**
     * @return is this fields called fieldName?
     */
    public boolean is(String fieldName) {
        return name.equals(fieldName);
    }

    /**
     * @return the name used in the AST for the setter
     */
    public String getSetterMethodName() {
        return setterName(name);
    }

    /**
     * @return the name used in the AST for the getter
     */
    public String getGetterMethodName() {
        return getterName(type, name);
    }

    /**
     * @return the NodeMetaModel that "has" this property.
     */
    public BaseNodeMetaModel getContainingNodeMetaModel() {
        return containingNodeMetaModel;
    }

    /**
     * @return the name of the property. This is equal to the name of the field in the AST.
     */
    public String getName() {
        return name;
    }

    /**
     * @return if this property is a String or a NodeList: whether it may be empty.
     */
    public boolean isNonEmpty() {
        return isNonEmpty;
    }

    /**
     * @return the class of the field.
     */
    public Class<?> getType() {
        return type;
    }

    /**
     * @return if this property is a Node, this will get the node meta model.
     */
    public Optional<BaseNodeMetaModel> getNodeReference() {
        return nodeReference;
    }

    /**
     * @return whether this property is optional.
     */
    public boolean isOptional() {
        return isOptional;
    }

    /**
     * @return whether this property is not optional.
     */
    public boolean isRequired() {
        return !isOptional;
    }

    /**
     * @return whether this property is contained in a NodeList.
     */
    public boolean isNodeList() {
        return isNodeList;
    }

    /**
     * @return whether this property is contained in an EnumSet.
     */
    public boolean isEnumSet() {
        return isEnumSet;
    }

    /**
     * @return whether this property has a wildcard following it, like BodyDeclaration&lt;?&gt;.
     */
    public boolean hasWildcard() {
        return hasWildcard;
    }

    /**
     * @return whether this property is not a list or set.
     */
    public boolean isSingular() {
        return !(isNodeList || isEnumSet);
    }

    @Override
    public String toString() {
        return "(" + getTypeName() + ")\t" + containingNodeMetaModel + "#" + name;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        PropertyMetaModel that = (PropertyMetaModel) o;

        if (!name.equals(that.name)) return false;
        if (!type.equals(that.type)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        int result = name.hashCode();
        result = 31 * result + type.hashCode();
        return result;
    }

    /**
     * @return the type of a single element of this property, so no Optional or NodeList or EnumSet.
     */
    public String getTypeNameGenerified() {
        if (hasWildcard) {
            return getTypeName() + "<?>";
        }
        return getTypeName();
    }

    /**
     * @return the raw type of a single element of this property, so nothing but the name.
     */
    public String getTypeName() {
        return type.getSimpleName();
    }

    /**
     * @return the type that is returned from getters in the AST.
     */
    public String getTypeNameForGetter() {
        if (isOptional) {
            return "Optional<" + getTypeNameForSetter() + ">";
        }
        return getTypeNameForSetter();
    }

    /**
     * @return the type that is passed to setters in the AST.
     */
    public String getTypeNameForSetter() {
        if (isNodeList) {
            return "NodeList<" + getTypeNameGenerified() + ">";
        }
        if (isEnumSet) {
            return "EnumSet<" + getTypeNameGenerified() + ">";
        }
        return getTypeNameGenerified();
    }

    /**
     * @return is this property an AST Node?
     */
    public boolean isNode() {
        return getNodeReference().isPresent();
    }

    /**
     * The name of the field in the containing BaseNodeMetaModel for this property meta model.
     */
    public String getMetaModelFieldName() {
        return getName() + "PropertyMetaModel";
    }

    /**
     * @return is this property an attribute, meaning: not a node?
     */
    public boolean isAttribute() {
        return !isNode();
    }

    /**
     * Introspects the node to get the value from this field.
     * Note that an optional empty field will return null here.
     */
    public Object getValue(Node node) {
        try {
            for (Class<?> c = node.getClass(); c != null; c = c.getSuperclass()) {
                Field[] fields = c.getDeclaredFields();
                for (Field classField : fields) {
                    if (classField.getName().equals(getName())) {
                        classField.setAccessible(true);
                        return classField.get(node);
                    }
                }
            }
            throw new NoSuchFieldError(getName());
        } catch (IllegalAccessException e) {
            throw new RuntimeException(e);
        }
    }
}
