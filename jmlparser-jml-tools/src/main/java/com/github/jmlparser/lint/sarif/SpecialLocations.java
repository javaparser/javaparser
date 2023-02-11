
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Defines locations of special significance to SARIF consumers.
 */
@Generated("jsonschema2pojo")
public class SpecialLocations {

    /**
     * Specifies the location of an artifact.
     */
    @SerializedName("displayBase")
    @Expose
    private ArtifactLocation displayBase;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public SpecialLocations() {
    }

    /**
     * @param displayBase
     * @param properties
     */
    public SpecialLocations(ArtifactLocation displayBase, PropertyBag properties) {
        super();
        this.displayBase = displayBase;
        this.properties = properties;
    }

    /**
     * Specifies the location of an artifact.
     */
    public ArtifactLocation getDisplayBase() {
        return displayBase;
    }

    /**
     * Specifies the location of an artifact.
     */
    public void setDisplayBase(ArtifactLocation displayBase) {
        this.displayBase = displayBase;
    }

    public SpecialLocations withDisplayBase(ArtifactLocation displayBase) {
        this.displayBase = displayBase;
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

    public SpecialLocations withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(SpecialLocations.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("displayBase");
        sb.append('=');
        sb.append(((this.displayBase == null) ? "<null>" : this.displayBase));
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
        result = ((result * 31) + ((this.displayBase == null) ? 0 : this.displayBase.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof SpecialLocations) == false) {
            return false;
        }
        SpecialLocations rhs = ((SpecialLocations) other);
        return (((this.displayBase == rhs.displayBase) || ((this.displayBase != null) && this.displayBase.equals(rhs.displayBase))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
