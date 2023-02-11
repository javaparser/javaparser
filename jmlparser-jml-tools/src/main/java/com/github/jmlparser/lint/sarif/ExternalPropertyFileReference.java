
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Contains information that enables a SARIF consumer to locate the external property file that contains the value of an externalized property associated with the run.
 */
@Generated("jsonschema2pojo")
public class ExternalPropertyFileReference {

    /**
     * Specifies the location of an artifact.
     */
    @SerializedName("location")
    @Expose
    private ArtifactLocation location;
    /**
     * A stable, unique identifer for the external property file in the form of a GUID.
     */
    @SerializedName("guid")
    @Expose
    private String guid;
    /**
     * A non-negative integer specifying the number of items contained in the external property file.
     */
    @SerializedName("itemCount")
    @Expose
    private int itemCount = -1;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public ExternalPropertyFileReference() {
    }

    /**
     * @param guid
     * @param location
     * @param properties
     * @param itemCount
     */
    public ExternalPropertyFileReference(ArtifactLocation location, String guid, int itemCount, PropertyBag properties) {
        super();
        this.location = location;
        this.guid = guid;
        this.itemCount = itemCount;
        this.properties = properties;
    }

    /**
     * Specifies the location of an artifact.
     */
    public ArtifactLocation getLocation() {
        return location;
    }

    /**
     * Specifies the location of an artifact.
     */
    public void setLocation(ArtifactLocation location) {
        this.location = location;
    }

    public ExternalPropertyFileReference withLocation(ArtifactLocation location) {
        this.location = location;
        return this;
    }

    /**
     * A stable, unique identifer for the external property file in the form of a GUID.
     */
    public String getGuid() {
        return guid;
    }

    /**
     * A stable, unique identifer for the external property file in the form of a GUID.
     */
    public void setGuid(String guid) {
        this.guid = guid;
    }

    public ExternalPropertyFileReference withGuid(String guid) {
        this.guid = guid;
        return this;
    }

    /**
     * A non-negative integer specifying the number of items contained in the external property file.
     */
    public int getItemCount() {
        return itemCount;
    }

    /**
     * A non-negative integer specifying the number of items contained in the external property file.
     */
    public void setItemCount(int itemCount) {
        this.itemCount = itemCount;
    }

    public ExternalPropertyFileReference withItemCount(int itemCount) {
        this.itemCount = itemCount;
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

    public ExternalPropertyFileReference withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(ExternalPropertyFileReference.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("location");
        sb.append('=');
        sb.append(((this.location == null) ? "<null>" : this.location));
        sb.append(',');
        sb.append("guid");
        sb.append('=');
        sb.append(((this.guid == null) ? "<null>" : this.guid));
        sb.append(',');
        sb.append("itemCount");
        sb.append('=');
        sb.append(this.itemCount);
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
        result = ((result * 31) + ((this.guid == null) ? 0 : this.guid.hashCode()));
        result = ((result * 31) + ((this.location == null) ? 0 : this.location.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        result = ((result * 31) + this.itemCount);
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof ExternalPropertyFileReference) == false) {
            return false;
        }
        ExternalPropertyFileReference rhs = ((ExternalPropertyFileReference) other);
        return (((((this.guid == rhs.guid) || ((this.guid != null) && this.guid.equals(rhs.guid))) && ((this.location == rhs.location) || ((this.location != null) && this.location.equals(rhs.location)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties)))) && (this.itemCount == rhs.itemCount));
    }

}
