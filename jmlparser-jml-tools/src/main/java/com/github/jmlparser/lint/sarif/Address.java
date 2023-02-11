
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * A physical or virtual address, or a range of addresses, in an 'addressable region' (memory or a binary file).
 */
@Generated("jsonschema2pojo")
public class Address {

    /**
     * The address expressed as a byte offset from the start of the addressable region.
     */
    @SerializedName("absoluteAddress")
    @Expose
    private int absoluteAddress = -1;
    /**
     * The address expressed as a byte offset from the absolute address of the top-most parent object.
     */
    @SerializedName("relativeAddress")
    @Expose
    private int relativeAddress;
    /**
     * The number of bytes in this range of addresses.
     */
    @SerializedName("length")
    @Expose
    private int length;
    /**
     * An open-ended string that identifies the address kind. 'data', 'function', 'header','instruction', 'module', 'page', 'section', 'segment', 'stack', 'stackFrame', 'table' are well-known values.
     */
    @SerializedName("kind")
    @Expose
    private String kind;
    /**
     * A name that is associated with the address, e.g., '.text'.
     */
    @SerializedName("name")
    @Expose
    private String name;
    /**
     * A human-readable fully qualified name that is associated with the address.
     */
    @SerializedName("fullyQualifiedName")
    @Expose
    private String fullyQualifiedName;
    /**
     * The byte offset of this address from the absolute or relative address of the parent object.
     */
    @SerializedName("offsetFromParent")
    @Expose
    private int offsetFromParent;
    /**
     * The index within run.addresses of the cached object for this address.
     */
    @SerializedName("index")
    @Expose
    private int index = -1;
    /**
     * The index within run.addresses of the parent object.
     */
    @SerializedName("parentIndex")
    @Expose
    private int parentIndex = -1;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public Address() {
    }

    /**
     * @param offsetFromParent
     * @param parentIndex
     * @param relativeAddress
     * @param kind
     * @param length
     * @param name
     * @param index
     * @param fullyQualifiedName
     * @param properties
     * @param absoluteAddress
     */
    public Address(int absoluteAddress, int relativeAddress, int length, String kind, String name, String fullyQualifiedName, int offsetFromParent, int index, int parentIndex, PropertyBag properties) {
        super();
        this.absoluteAddress = absoluteAddress;
        this.relativeAddress = relativeAddress;
        this.length = length;
        this.kind = kind;
        this.name = name;
        this.fullyQualifiedName = fullyQualifiedName;
        this.offsetFromParent = offsetFromParent;
        this.index = index;
        this.parentIndex = parentIndex;
        this.properties = properties;
    }

    /**
     * The address expressed as a byte offset from the start of the addressable region.
     */
    public int getAbsoluteAddress() {
        return absoluteAddress;
    }

    /**
     * The address expressed as a byte offset from the start of the addressable region.
     */
    public void setAbsoluteAddress(int absoluteAddress) {
        this.absoluteAddress = absoluteAddress;
    }

    public Address withAbsoluteAddress(int absoluteAddress) {
        this.absoluteAddress = absoluteAddress;
        return this;
    }

    /**
     * The address expressed as a byte offset from the absolute address of the top-most parent object.
     */
    public int getRelativeAddress() {
        return relativeAddress;
    }

    /**
     * The address expressed as a byte offset from the absolute address of the top-most parent object.
     */
    public void setRelativeAddress(int relativeAddress) {
        this.relativeAddress = relativeAddress;
    }

    public Address withRelativeAddress(int relativeAddress) {
        this.relativeAddress = relativeAddress;
        return this;
    }

    /**
     * The number of bytes in this range of addresses.
     */
    public int getLength() {
        return length;
    }

    /**
     * The number of bytes in this range of addresses.
     */
    public void setLength(int length) {
        this.length = length;
    }

    public Address withLength(int length) {
        this.length = length;
        return this;
    }

    /**
     * An open-ended string that identifies the address kind. 'data', 'function', 'header','instruction', 'module', 'page', 'section', 'segment', 'stack', 'stackFrame', 'table' are well-known values.
     */
    public String getKind() {
        return kind;
    }

    /**
     * An open-ended string that identifies the address kind. 'data', 'function', 'header','instruction', 'module', 'page', 'section', 'segment', 'stack', 'stackFrame', 'table' are well-known values.
     */
    public void setKind(String kind) {
        this.kind = kind;
    }

    public Address withKind(String kind) {
        this.kind = kind;
        return this;
    }

    /**
     * A name that is associated with the address, e.g., '.text'.
     */
    public String getName() {
        return name;
    }

    /**
     * A name that is associated with the address, e.g., '.text'.
     */
    public void setName(String name) {
        this.name = name;
    }

    public Address withName(String name) {
        this.name = name;
        return this;
    }

    /**
     * A human-readable fully qualified name that is associated with the address.
     */
    public String getFullyQualifiedName() {
        return fullyQualifiedName;
    }

    /**
     * A human-readable fully qualified name that is associated with the address.
     */
    public void setFullyQualifiedName(String fullyQualifiedName) {
        this.fullyQualifiedName = fullyQualifiedName;
    }

    public Address withFullyQualifiedName(String fullyQualifiedName) {
        this.fullyQualifiedName = fullyQualifiedName;
        return this;
    }

    /**
     * The byte offset of this address from the absolute or relative address of the parent object.
     */
    public int getOffsetFromParent() {
        return offsetFromParent;
    }

    /**
     * The byte offset of this address from the absolute or relative address of the parent object.
     */
    public void setOffsetFromParent(int offsetFromParent) {
        this.offsetFromParent = offsetFromParent;
    }

    public Address withOffsetFromParent(int offsetFromParent) {
        this.offsetFromParent = offsetFromParent;
        return this;
    }

    /**
     * The index within run.addresses of the cached object for this address.
     */
    public int getIndex() {
        return index;
    }

    /**
     * The index within run.addresses of the cached object for this address.
     */
    public void setIndex(int index) {
        this.index = index;
    }

    public Address withIndex(int index) {
        this.index = index;
        return this;
    }

    /**
     * The index within run.addresses of the parent object.
     */
    public int getParentIndex() {
        return parentIndex;
    }

    /**
     * The index within run.addresses of the parent object.
     */
    public void setParentIndex(int parentIndex) {
        this.parentIndex = parentIndex;
    }

    public Address withParentIndex(int parentIndex) {
        this.parentIndex = parentIndex;
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

    public Address withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Address.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("absoluteAddress");
        sb.append('=');
        sb.append(this.absoluteAddress);
        sb.append(',');
        sb.append("relativeAddress");
        sb.append('=');
        sb.append(this.relativeAddress);
        sb.append(',');
        sb.append("length");
        sb.append('=');
        sb.append(this.length);
        sb.append(',');
        sb.append("kind");
        sb.append('=');
        sb.append(((this.kind == null) ? "<null>" : this.kind));
        sb.append(',');
        sb.append("name");
        sb.append('=');
        sb.append(((this.name == null) ? "<null>" : this.name));
        sb.append(',');
        sb.append("fullyQualifiedName");
        sb.append('=');
        sb.append(((this.fullyQualifiedName == null) ? "<null>" : this.fullyQualifiedName));
        sb.append(',');
        sb.append("offsetFromParent");
        sb.append('=');
        sb.append(this.offsetFromParent);
        sb.append(',');
        sb.append("index");
        sb.append('=');
        sb.append(this.index);
        sb.append(',');
        sb.append("parentIndex");
        sb.append('=');
        sb.append(this.parentIndex);
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
        result = ((result * 31) + this.offsetFromParent);
        result = ((result * 31) + this.parentIndex);
        result = ((result * 31) + this.relativeAddress);
        result = ((result * 31) + ((this.kind == null) ? 0 : this.kind.hashCode()));
        result = ((result * 31) + this.length);
        result = ((result * 31) + ((this.name == null) ? 0 : this.name.hashCode()));
        result = ((result * 31) + this.index);
        result = ((result * 31) + ((this.fullyQualifiedName == null) ? 0 : this.fullyQualifiedName.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        result = ((result * 31) + this.absoluteAddress);
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof Address) == false) {
            return false;
        }
        Address rhs = ((Address) other);
        return ((((((((((this.offsetFromParent == rhs.offsetFromParent) && (this.parentIndex == rhs.parentIndex)) && (this.relativeAddress == rhs.relativeAddress)) && ((this.kind == rhs.kind) || ((this.kind != null) && this.kind.equals(rhs.kind)))) && (this.length == rhs.length)) && ((this.name == rhs.name) || ((this.name != null) && this.name.equals(rhs.name)))) && (this.index == rhs.index)) && ((this.fullyQualifiedName == rhs.fullyQualifiedName) || ((this.fullyQualifiedName != null) && this.fullyQualifiedName.equals(rhs.fullyQualifiedName)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties)))) && (this.absoluteAddress == rhs.absoluteAddress));
    }

}
