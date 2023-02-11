
package com.github.jmlparser.lint.sarif;

import java.util.LinkedHashSet;
import java.util.Set;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * A location within a programming artifact.
 */
@Generated("jsonschema2pojo")
public class Location {

    /**
     * Value that distinguishes this location from all other locations within a single result object.
     */
    @SerializedName("id")
    @Expose
    private int id = -1;
    /**
     * A physical location relevant to a result. Specifies a reference to a programming artifact together with a range of bytes or characters within that artifact.
     */
    @SerializedName("physicalLocation")
    @Expose
    private PhysicalLocation physicalLocation;
    /**
     * The logical locations associated with the result.
     */
    @SerializedName("logicalLocations")
    @Expose
    private Set<LogicalLocation> logicalLocations = new LinkedHashSet<LogicalLocation>();
    /**
     * Encapsulates a message intended to be read by the end user.
     */
    @SerializedName("message")
    @Expose
    private Message message;
    /**
     * A set of regions relevant to the location.
     */
    @SerializedName("annotations")
    @Expose
    private Set<Region> annotations = new LinkedHashSet<Region>();
    /**
     * An array of objects that describe relationships between this location and others.
     */
    @SerializedName("relationships")
    @Expose
    private Set<LocationRelationship> relationships = new LinkedHashSet<LocationRelationship>();
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public Location() {
    }

    /**
     * @param relationships
     * @param physicalLocation
     * @param logicalLocations
     * @param annotations
     * @param id
     * @param message
     * @param properties
     */
    public Location(int id, PhysicalLocation physicalLocation, Set<LogicalLocation> logicalLocations, Message message, Set<Region> annotations, Set<LocationRelationship> relationships, PropertyBag properties) {
        super();
        this.id = id;
        this.physicalLocation = physicalLocation;
        this.logicalLocations = logicalLocations;
        this.message = message;
        this.annotations = annotations;
        this.relationships = relationships;
        this.properties = properties;
    }

    /**
     * Value that distinguishes this location from all other locations within a single result object.
     */
    public int getId() {
        return id;
    }

    /**
     * Value that distinguishes this location from all other locations within a single result object.
     */
    public void setId(int id) {
        this.id = id;
    }

    public Location withId(int id) {
        this.id = id;
        return this;
    }

    /**
     * A physical location relevant to a result. Specifies a reference to a programming artifact together with a range of bytes or characters within that artifact.
     */
    public PhysicalLocation getPhysicalLocation() {
        return physicalLocation;
    }

    /**
     * A physical location relevant to a result. Specifies a reference to a programming artifact together with a range of bytes or characters within that artifact.
     */
    public void setPhysicalLocation(PhysicalLocation physicalLocation) {
        this.physicalLocation = physicalLocation;
    }

    public Location withPhysicalLocation(PhysicalLocation physicalLocation) {
        this.physicalLocation = physicalLocation;
        return this;
    }

    /**
     * The logical locations associated with the result.
     */
    public Set<LogicalLocation> getLogicalLocations() {
        return logicalLocations;
    }

    /**
     * The logical locations associated with the result.
     */
    public void setLogicalLocations(Set<LogicalLocation> logicalLocations) {
        this.logicalLocations = logicalLocations;
    }

    public Location withLogicalLocations(Set<LogicalLocation> logicalLocations) {
        this.logicalLocations = logicalLocations;
        return this;
    }

    /**
     * Encapsulates a message intended to be read by the end user.
     */
    public Message getMessage() {
        return message;
    }

    /**
     * Encapsulates a message intended to be read by the end user.
     */
    public void setMessage(Message message) {
        this.message = message;
    }

    public Location withMessage(Message message) {
        this.message = message;
        return this;
    }

    /**
     * A set of regions relevant to the location.
     */
    public Set<Region> getAnnotations() {
        return annotations;
    }

    /**
     * A set of regions relevant to the location.
     */
    public void setAnnotations(Set<Region> annotations) {
        this.annotations = annotations;
    }

    public Location withAnnotations(Set<Region> annotations) {
        this.annotations = annotations;
        return this;
    }

    /**
     * An array of objects that describe relationships between this location and others.
     */
    public Set<LocationRelationship> getRelationships() {
        return relationships;
    }

    /**
     * An array of objects that describe relationships between this location and others.
     */
    public void setRelationships(Set<LocationRelationship> relationships) {
        this.relationships = relationships;
    }

    public Location withRelationships(Set<LocationRelationship> relationships) {
        this.relationships = relationships;
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

    public Location withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Location.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("id");
        sb.append('=');
        sb.append(this.id);
        sb.append(',');
        sb.append("physicalLocation");
        sb.append('=');
        sb.append(((this.physicalLocation == null) ? "<null>" : this.physicalLocation));
        sb.append(',');
        sb.append("logicalLocations");
        sb.append('=');
        sb.append(((this.logicalLocations == null) ? "<null>" : this.logicalLocations));
        sb.append(',');
        sb.append("message");
        sb.append('=');
        sb.append(((this.message == null) ? "<null>" : this.message));
        sb.append(',');
        sb.append("annotations");
        sb.append('=');
        sb.append(((this.annotations == null) ? "<null>" : this.annotations));
        sb.append(',');
        sb.append("relationships");
        sb.append('=');
        sb.append(((this.relationships == null) ? "<null>" : this.relationships));
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
        result = ((result * 31) + ((this.relationships == null) ? 0 : this.relationships.hashCode()));
        result = ((result * 31) + ((this.physicalLocation == null) ? 0 : this.physicalLocation.hashCode()));
        result = ((result * 31) + ((this.logicalLocations == null) ? 0 : this.logicalLocations.hashCode()));
        result = ((result * 31) + ((this.annotations == null) ? 0 : this.annotations.hashCode()));
        result = ((result * 31) + this.id);
        result = ((result * 31) + ((this.message == null) ? 0 : this.message.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof Location) == false) {
            return false;
        }
        Location rhs = ((Location) other);
        return ((((((((this.relationships == rhs.relationships) || ((this.relationships != null) && this.relationships.equals(rhs.relationships))) && ((this.physicalLocation == rhs.physicalLocation) || ((this.physicalLocation != null) && this.physicalLocation.equals(rhs.physicalLocation)))) && ((this.logicalLocations == rhs.logicalLocations) || ((this.logicalLocations != null) && this.logicalLocations.equals(rhs.logicalLocations)))) && ((this.annotations == rhs.annotations) || ((this.annotations != null) && this.annotations.equals(rhs.annotations)))) && (this.id == rhs.id)) && ((this.message == rhs.message) || ((this.message != null) && this.message.equals(rhs.message)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
