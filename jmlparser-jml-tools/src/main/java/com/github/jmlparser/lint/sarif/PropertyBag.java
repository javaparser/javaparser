
package com.github.jmlparser.lint.sarif;

import java.util.LinkedHashSet;
import java.util.Set;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Key/value pairs that provide additional information about the object.
 */
@Generated("jsonschema2pojo")
public class PropertyBag {

    /**
     * This is a modification, see: https://github.com/joelittlejohn/jsonschema2pojo/issues/186
     */
    @SerializedName("category")
    @Expose
    private String category;
    /**
     * A set of distinct strings that provide additional information.
     */
    @SerializedName("tags")
    @Expose
    private Set<String> tags = new LinkedHashSet<String>();

    /**
     * No args constructor for use in serialization
     */
    public PropertyBag() {
    }

    /**
     * @param category
     * @param tags
     */
    public PropertyBag(String category, Set<String> tags) {
        super();
        this.category = category;
        this.tags = tags;
    }

    /**
     * This is a modification, see: https://github.com/joelittlejohn/jsonschema2pojo/issues/186
     */
    public String getCategory() {
        return category;
    }

    /**
     * This is a modification, see: https://github.com/joelittlejohn/jsonschema2pojo/issues/186
     */
    public void setCategory(String category) {
        this.category = category;
    }

    public PropertyBag withCategory(String category) {
        this.category = category;
        return this;
    }

    /**
     * A set of distinct strings that provide additional information.
     */
    public Set<String> getTags() {
        return tags;
    }

    /**
     * A set of distinct strings that provide additional information.
     */
    public void setTags(Set<String> tags) {
        this.tags = tags;
    }

    public PropertyBag withTags(Set<String> tags) {
        this.tags = tags;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(PropertyBag.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("category");
        sb.append('=');
        sb.append(((this.category == null) ? "<null>" : this.category));
        sb.append(',');
        sb.append("tags");
        sb.append('=');
        sb.append(((this.tags == null) ? "<null>" : this.tags));
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
        result = ((result * 31) + ((this.category == null) ? 0 : this.category.hashCode()));
        result = ((result * 31) + ((this.tags == null) ? 0 : this.tags.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof PropertyBag) == false) {
            return false;
        }
        PropertyBag rhs = ((PropertyBag) other);
        return (((this.category == rhs.category) || ((this.category != null) && this.category.equals(rhs.category))) && ((this.tags == rhs.tags) || ((this.tags != null) && this.tags.equals(rhs.tags))));
    }

}
