
package com.github.jmlparser.lint.sarif;

import java.util.LinkedHashSet;
import java.util.Set;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * An artifact relevant to a result.
 */
@Generated("jsonschema2pojo")
public class Attachment {

    /**
     * Encapsulates a message intended to be read by the end user.
     */
    @SerializedName("description")
    @Expose
    private Message description;
    /**
     * Specifies the location of an artifact.
     * (Required)
     */
    @SerializedName("artifactLocation")
    @Expose
    private ArtifactLocation artifactLocation;
    /**
     * An array of regions of interest within the attachment.
     */
    @SerializedName("regions")
    @Expose
    private Set<Region> regions = new LinkedHashSet<Region>();
    /**
     * An array of rectangles specifying areas of interest within the image.
     */
    @SerializedName("rectangles")
    @Expose
    private Set<Rectangle> rectangles = new LinkedHashSet<Rectangle>();
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public Attachment() {
    }

    /**
     * @param regions
     * @param rectangles
     * @param description
     * @param artifactLocation
     * @param properties
     */
    public Attachment(Message description, ArtifactLocation artifactLocation, Set<Region> regions, Set<Rectangle> rectangles, PropertyBag properties) {
        super();
        this.description = description;
        this.artifactLocation = artifactLocation;
        this.regions = regions;
        this.rectangles = rectangles;
        this.properties = properties;
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

    public Attachment withDescription(Message description) {
        this.description = description;
        return this;
    }

    /**
     * Specifies the location of an artifact.
     * (Required)
     */
    public ArtifactLocation getArtifactLocation() {
        return artifactLocation;
    }

    /**
     * Specifies the location of an artifact.
     * (Required)
     */
    public void setArtifactLocation(ArtifactLocation artifactLocation) {
        this.artifactLocation = artifactLocation;
    }

    public Attachment withArtifactLocation(ArtifactLocation artifactLocation) {
        this.artifactLocation = artifactLocation;
        return this;
    }

    /**
     * An array of regions of interest within the attachment.
     */
    public Set<Region> getRegions() {
        return regions;
    }

    /**
     * An array of regions of interest within the attachment.
     */
    public void setRegions(Set<Region> regions) {
        this.regions = regions;
    }

    public Attachment withRegions(Set<Region> regions) {
        this.regions = regions;
        return this;
    }

    /**
     * An array of rectangles specifying areas of interest within the image.
     */
    public Set<Rectangle> getRectangles() {
        return rectangles;
    }

    /**
     * An array of rectangles specifying areas of interest within the image.
     */
    public void setRectangles(Set<Rectangle> rectangles) {
        this.rectangles = rectangles;
    }

    public Attachment withRectangles(Set<Rectangle> rectangles) {
        this.rectangles = rectangles;
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

    public Attachment withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Attachment.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("description");
        sb.append('=');
        sb.append(((this.description == null) ? "<null>" : this.description));
        sb.append(',');
        sb.append("artifactLocation");
        sb.append('=');
        sb.append(((this.artifactLocation == null) ? "<null>" : this.artifactLocation));
        sb.append(',');
        sb.append("regions");
        sb.append('=');
        sb.append(((this.regions == null) ? "<null>" : this.regions));
        sb.append(',');
        sb.append("rectangles");
        sb.append('=');
        sb.append(((this.rectangles == null) ? "<null>" : this.rectangles));
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
        result = ((result * 31) + ((this.regions == null) ? 0 : this.regions.hashCode()));
        result = ((result * 31) + ((this.rectangles == null) ? 0 : this.rectangles.hashCode()));
        result = ((result * 31) + ((this.artifactLocation == null) ? 0 : this.artifactLocation.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof Attachment) == false) {
            return false;
        }
        Attachment rhs = ((Attachment) other);
        return ((((((this.description == rhs.description) || ((this.description != null) && this.description.equals(rhs.description))) && ((this.regions == rhs.regions) || ((this.regions != null) && this.regions.equals(rhs.regions)))) && ((this.rectangles == rhs.rectangles) || ((this.rectangles != null) && this.rectangles.equals(rhs.rectangles)))) && ((this.artifactLocation == rhs.artifactLocation) || ((this.artifactLocation != null) && this.artifactLocation.equals(rhs.artifactLocation)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
