
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * The replacement of a single region of an artifact.
 */
@Generated("jsonschema2pojo")
public class Replacement {

    /**
     * A region within an artifact where a result was detected.
     * (Required)
     */
    @SerializedName("deletedRegion")
    @Expose
    private Region deletedRegion;
    /**
     * Represents the contents of an artifact.
     */
    @SerializedName("insertedContent")
    @Expose
    private ArtifactContent insertedContent;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public Replacement() {
    }

    /**
     * @param insertedContent
     * @param deletedRegion
     * @param properties
     */
    public Replacement(Region deletedRegion, ArtifactContent insertedContent, PropertyBag properties) {
        super();
        this.deletedRegion = deletedRegion;
        this.insertedContent = insertedContent;
        this.properties = properties;
    }

    /**
     * A region within an artifact where a result was detected.
     * (Required)
     */
    public Region getDeletedRegion() {
        return deletedRegion;
    }

    /**
     * A region within an artifact where a result was detected.
     * (Required)
     */
    public void setDeletedRegion(Region deletedRegion) {
        this.deletedRegion = deletedRegion;
    }

    public Replacement withDeletedRegion(Region deletedRegion) {
        this.deletedRegion = deletedRegion;
        return this;
    }

    /**
     * Represents the contents of an artifact.
     */
    public ArtifactContent getInsertedContent() {
        return insertedContent;
    }

    /**
     * Represents the contents of an artifact.
     */
    public void setInsertedContent(ArtifactContent insertedContent) {
        this.insertedContent = insertedContent;
    }

    public Replacement withInsertedContent(ArtifactContent insertedContent) {
        this.insertedContent = insertedContent;
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

    public Replacement withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Replacement.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("deletedRegion");
        sb.append('=');
        sb.append(((this.deletedRegion == null) ? "<null>" : this.deletedRegion));
        sb.append(',');
        sb.append("insertedContent");
        sb.append('=');
        sb.append(((this.insertedContent == null) ? "<null>" : this.insertedContent));
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
        result = ((result * 31) + ((this.insertedContent == null) ? 0 : this.insertedContent.hashCode()));
        result = ((result * 31) + ((this.deletedRegion == null) ? 0 : this.deletedRegion.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof Replacement) == false) {
            return false;
        }
        Replacement rhs = ((Replacement) other);
        return ((((this.insertedContent == rhs.insertedContent) || ((this.insertedContent != null) && this.insertedContent.equals(rhs.insertedContent))) && ((this.deletedRegion == rhs.deletedRegion) || ((this.deletedRegion != null) && this.deletedRegion.equals(rhs.deletedRegion)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
