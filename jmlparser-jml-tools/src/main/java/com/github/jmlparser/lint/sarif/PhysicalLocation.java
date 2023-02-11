
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * A physical location relevant to a result. Specifies a reference to a programming artifact together with a range of bytes or characters within that artifact.
 */
@Generated("jsonschema2pojo")
public class PhysicalLocation {

    /**
     * A physical or virtual address, or a range of addresses, in an 'addressable region' (memory or a binary file).
     */
    @SerializedName("address")
    @Expose
    private Address address;
    /**
     * Specifies the location of an artifact.
     */
    @SerializedName("artifactLocation")
    @Expose
    private ArtifactLocation artifactLocation;
    /**
     * A region within an artifact where a result was detected.
     */
    @SerializedName("region")
    @Expose
    private Region region;
    /**
     * A region within an artifact where a result was detected.
     */
    @SerializedName("contextRegion")
    @Expose
    private Region contextRegion;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public PhysicalLocation() {
    }

    /**
     * @param address
     * @param contextRegion
     * @param region
     * @param artifactLocation
     * @param properties
     */
    public PhysicalLocation(Address address, ArtifactLocation artifactLocation, Region region, Region contextRegion, PropertyBag properties) {
        super();
        this.address = address;
        this.artifactLocation = artifactLocation;
        this.region = region;
        this.contextRegion = contextRegion;
        this.properties = properties;
    }

    /**
     * A physical or virtual address, or a range of addresses, in an 'addressable region' (memory or a binary file).
     */
    public Address getAddress() {
        return address;
    }

    /**
     * A physical or virtual address, or a range of addresses, in an 'addressable region' (memory or a binary file).
     */
    public void setAddress(Address address) {
        this.address = address;
    }

    public PhysicalLocation withAddress(Address address) {
        this.address = address;
        return this;
    }

    /**
     * Specifies the location of an artifact.
     */
    public ArtifactLocation getArtifactLocation() {
        return artifactLocation;
    }

    /**
     * Specifies the location of an artifact.
     */
    public void setArtifactLocation(ArtifactLocation artifactLocation) {
        this.artifactLocation = artifactLocation;
    }

    public PhysicalLocation withArtifactLocation(ArtifactLocation artifactLocation) {
        this.artifactLocation = artifactLocation;
        return this;
    }

    /**
     * A region within an artifact where a result was detected.
     */
    public Region getRegion() {
        return region;
    }

    /**
     * A region within an artifact where a result was detected.
     */
    public void setRegion(Region region) {
        this.region = region;
    }

    public PhysicalLocation withRegion(Region region) {
        this.region = region;
        return this;
    }

    /**
     * A region within an artifact where a result was detected.
     */
    public Region getContextRegion() {
        return contextRegion;
    }

    /**
     * A region within an artifact where a result was detected.
     */
    public void setContextRegion(Region contextRegion) {
        this.contextRegion = contextRegion;
    }

    public PhysicalLocation withContextRegion(Region contextRegion) {
        this.contextRegion = contextRegion;
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

    public PhysicalLocation withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(PhysicalLocation.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("address");
        sb.append('=');
        sb.append(((this.address == null) ? "<null>" : this.address));
        sb.append(',');
        sb.append("artifactLocation");
        sb.append('=');
        sb.append(((this.artifactLocation == null) ? "<null>" : this.artifactLocation));
        sb.append(',');
        sb.append("region");
        sb.append('=');
        sb.append(((this.region == null) ? "<null>" : this.region));
        sb.append(',');
        sb.append("contextRegion");
        sb.append('=');
        sb.append(((this.contextRegion == null) ? "<null>" : this.contextRegion));
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
        result = ((result * 31) + ((this.contextRegion == null) ? 0 : this.contextRegion.hashCode()));
        result = ((result * 31) + ((this.address == null) ? 0 : this.address.hashCode()));
        result = ((result * 31) + ((this.region == null) ? 0 : this.region.hashCode()));
        result = ((result * 31) + ((this.artifactLocation == null) ? 0 : this.artifactLocation.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof PhysicalLocation) == false) {
            return false;
        }
        PhysicalLocation rhs = ((PhysicalLocation) other);
        return ((((((this.contextRegion == rhs.contextRegion) || ((this.contextRegion != null) && this.contextRegion.equals(rhs.contextRegion))) && ((this.address == rhs.address) || ((this.address != null) && this.address.equals(rhs.address)))) && ((this.region == rhs.region) || ((this.region != null) && this.region.equals(rhs.region)))) && ((this.artifactLocation == rhs.artifactLocation) || ((this.artifactLocation != null) && this.artifactLocation.equals(rhs.artifactLocation)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
