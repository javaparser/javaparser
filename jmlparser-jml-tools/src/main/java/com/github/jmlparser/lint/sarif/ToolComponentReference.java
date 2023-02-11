
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Identifies a particular toolComponent object, either the driver or an extension.
 */
@Generated("jsonschema2pojo")
public class ToolComponentReference {

    /**
     * The 'name' property of the referenced toolComponent.
     */
    @SerializedName("name")
    @Expose
    private String name;
    /**
     * An index into the referenced toolComponent in tool.extensions.
     */
    @SerializedName("index")
    @Expose
    private int index = -1;
    /**
     * The 'guid' property of the referenced toolComponent.
     */
    @SerializedName("guid")
    @Expose
    private String guid;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public ToolComponentReference() {
    }

    /**
     * @param name
     * @param index
     * @param guid
     * @param properties
     */
    public ToolComponentReference(String name, int index, String guid, PropertyBag properties) {
        super();
        this.name = name;
        this.index = index;
        this.guid = guid;
        this.properties = properties;
    }

    /**
     * The 'name' property of the referenced toolComponent.
     */
    public String getName() {
        return name;
    }

    /**
     * The 'name' property of the referenced toolComponent.
     */
    public void setName(String name) {
        this.name = name;
    }

    public ToolComponentReference withName(String name) {
        this.name = name;
        return this;
    }

    /**
     * An index into the referenced toolComponent in tool.extensions.
     */
    public int getIndex() {
        return index;
    }

    /**
     * An index into the referenced toolComponent in tool.extensions.
     */
    public void setIndex(int index) {
        this.index = index;
    }

    public ToolComponentReference withIndex(int index) {
        this.index = index;
        return this;
    }

    /**
     * The 'guid' property of the referenced toolComponent.
     */
    public String getGuid() {
        return guid;
    }

    /**
     * The 'guid' property of the referenced toolComponent.
     */
    public void setGuid(String guid) {
        this.guid = guid;
    }

    public ToolComponentReference withGuid(String guid) {
        this.guid = guid;
        return this;
    }

    /**
     * Key/value pairs that provide additional information about the object.
     */
    public PropertyBag getProperties() {
        return properties;
    }

    /**
     * Key/value pairs that provide additional information about the object.
     */
    public void setProperties(PropertyBag properties) {
        this.properties = properties;
    }

    public ToolComponentReference withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(ToolComponentReference.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("name");
        sb.append('=');
        sb.append(((this.name == null) ? "<null>" : this.name));
        sb.append(',');
        sb.append("index");
        sb.append('=');
        sb.append(this.index);
        sb.append(',');
        sb.append("guid");
        sb.append('=');
        sb.append(((this.guid == null) ? "<null>" : this.guid));
        sb.append(',');
        sb.append("properties");
        sb.append('=');
        sb.append(((this.properties == null) ? "<null>" : this.properties));
        sb.append(',');
        if (sb.charAt((sb.length() - 1)) == ',') {
            sb.setCharAt((sb.length() - 1), ']');
        } else {
            sb.append(']');
        }
        return sb.toString();
    }

    @Override
    public int hashCode() {
        int result = 1;
        result = ((result * 31) + ((this.name == null) ? 0 : this.name.hashCode()));
        result = ((result * 31) + this.index);
        result = ((result * 31) + ((this.guid == null) ? 0 : this.guid.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof ToolComponentReference) == false) {
            return false;
        }
        ToolComponentReference rhs = ((ToolComponentReference) other);
        return (((((this.name == rhs.name) || ((this.name != null) && this.name.equals(rhs.name))) && (this.index == rhs.index)) && ((this.guid == rhs.guid) || ((this.guid != null) && this.guid.equals(rhs.guid)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
