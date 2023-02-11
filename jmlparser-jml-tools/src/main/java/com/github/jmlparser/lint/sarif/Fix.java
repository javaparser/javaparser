
package com.github.jmlparser.lint.sarif;

import java.util.LinkedHashSet;
import java.util.Set;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * A proposed fix for the problem represented by a result object. A fix specifies a set of artifacts to modify. For each artifact, it specifies a set of bytes to remove, and provides a set of new bytes to replace them.
 */
@Generated("jsonschema2pojo")
public class Fix {

    /**
     * Encapsulates a message intended to be read by the end user.
     */
    @SerializedName("description")
    @Expose
    private Message description;
    /**
     * One or more artifact changes that comprise a fix for a result.
     * (Required)
     */
    @SerializedName("artifactChanges")
    @Expose
    private Set<ArtifactChange> artifactChanges = new LinkedHashSet<ArtifactChange>();
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public Fix() {
    }

    /**
     * @param artifactChanges
     * @param description
     * @param properties
     */
    public Fix(Message description, Set<ArtifactChange> artifactChanges, PropertyBag properties) {
        super();
        this.description = description;
        this.artifactChanges = artifactChanges;
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

    public Fix withDescription(Message description) {
        this.description = description;
        return this;
    }

    /**
     * One or more artifact changes that comprise a fix for a result.
     * (Required)
     */
    public Set<ArtifactChange> getArtifactChanges() {
        return artifactChanges;
    }

    /**
     * One or more artifact changes that comprise a fix for a result.
     * (Required)
     */
    public void setArtifactChanges(Set<ArtifactChange> artifactChanges) {
        this.artifactChanges = artifactChanges;
    }

    public Fix withArtifactChanges(Set<ArtifactChange> artifactChanges) {
        this.artifactChanges = artifactChanges;
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

    public Fix withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Fix.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("description");
        sb.append('=');
        sb.append(((this.description == null) ? "<null>" : this.description));
        sb.append(',');
        sb.append("artifactChanges");
        sb.append('=');
        sb.append(((this.artifactChanges == null) ? "<null>" : this.artifactChanges));
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
        result = ((result * 31) + ((this.artifactChanges == null) ? 0 : this.artifactChanges.hashCode()));
        result = ((result * 31) + ((this.description == null) ? 0 : this.description.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof Fix) == false) {
            return false;
        }
        Fix rhs = ((Fix) other);
        return ((((this.artifactChanges == rhs.artifactChanges) || ((this.artifactChanges != null) && this.artifactChanges.equals(rhs.artifactChanges))) && ((this.description == rhs.description) || ((this.description != null) && this.description.equals(rhs.description)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
