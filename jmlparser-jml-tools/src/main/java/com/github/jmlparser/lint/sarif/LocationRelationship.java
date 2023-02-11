
package com.github.jmlparser.lint.sarif;

import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.Set;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Information about the relation of one location to another.
 */
@Generated("jsonschema2pojo")
public class LocationRelationship {

    /**
     * A reference to the related location.
     * (Required)
     */
    @SerializedName("target")
    @Expose
    private int target;
    /**
     * A set of distinct strings that categorize the relationship. Well-known kinds include 'includes', 'isIncludedBy' and 'relevant'.
     */
    @SerializedName("kinds")
    @Expose
    private Set<String> kinds = new LinkedHashSet<String>(Arrays.asList("relevant"));
    /**
     * Encapsulates a message intended to be read by the end user.
     */
    @SerializedName("description")
    @Expose
    private Message description;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public LocationRelationship() {
    }

    /**
     * @param description
     * @param kinds
     * @param properties
     * @param target
     */
    public LocationRelationship(int target, Set<String> kinds, Message description, PropertyBag properties) {
        super();
        this.target = target;
        this.kinds = kinds;
        this.description = description;
        this.properties = properties;
    }

    /**
     * A reference to the related location.
     * (Required)
     */
    public int getTarget() {
        return target;
    }

    /**
     * A reference to the related location.
     * (Required)
     */
    public void setTarget(int target) {
        this.target = target;
    }

    public LocationRelationship withTarget(int target) {
        this.target = target;
        return this;
    }

    /**
     * A set of distinct strings that categorize the relationship. Well-known kinds include 'includes', 'isIncludedBy' and 'relevant'.
     */
    public Set<String> getKinds() {
        return kinds;
    }

    /**
     * A set of distinct strings that categorize the relationship. Well-known kinds include 'includes', 'isIncludedBy' and 'relevant'.
     */
    public void setKinds(Set<String> kinds) {
        this.kinds = kinds;
    }

    public LocationRelationship withKinds(Set<String> kinds) {
        this.kinds = kinds;
        return this;
    }

    /**
     * Encapsulates a message intended to be read by the end user.
     */
    public Message getDescription() {
        return description;
    }

    /**
     * Encapsulates a message intended to be read by the end user.
     */
    public void setDescription(Message description) {
        this.description = description;
    }

    public LocationRelationship withDescription(Message description) {
        this.description = description;
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

    public LocationRelationship withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(LocationRelationship.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("target");
        sb.append('=');
        sb.append(this.target);
        sb.append(',');
        sb.append("kinds");
        sb.append('=');
        sb.append(((this.kinds == null) ? "<null>" : this.kinds));
        sb.append(',');
        sb.append("description");
        sb.append('=');
        sb.append(((this.description == null) ? "<null>" : this.description));
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
        result = ((result * 31) + ((this.description == null) ? 0 : this.description.hashCode()));
        result = ((result * 31) + ((this.kinds == null) ? 0 : this.kinds.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        result = ((result * 31) + this.target);
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof LocationRelationship) == false) {
            return false;
        }
        LocationRelationship rhs = ((LocationRelationship) other);
        return (((((this.description == rhs.description) || ((this.description != null) && this.description.equals(rhs.description))) && ((this.kinds == rhs.kinds) || ((this.kinds != null) && this.kinds.equals(rhs.kinds)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties)))) && (this.target == rhs.target));
    }

}
