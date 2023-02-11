
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Information that describes a run's identity and role within an engineering system process.
 */
@Generated("jsonschema2pojo")
public class RunAutomationDetails {

    /**
     * Encapsulates a message intended to be read by the end user.
     */
    @SerializedName("description")
    @Expose
    private Message description;
    /**
     * A hierarchical string that uniquely identifies this object's containing run object.
     */
    @SerializedName("id")
    @Expose
    private String id;
    /**
     * A stable, unique identifer for this object's containing run object in the form of a GUID.
     */
    @SerializedName("guid")
    @Expose
    private String guid;
    /**
     * A stable, unique identifier for the equivalence class of runs to which this object's containing run object belongs in the form of a GUID.
     */
    @SerializedName("correlationGuid")
    @Expose
    private String correlationGuid;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public RunAutomationDetails() {
    }

    /**
     * @param correlationGuid
     * @param description
     * @param guid
     * @param id
     * @param properties
     */
    public RunAutomationDetails(Message description, String id, String guid, String correlationGuid, PropertyBag properties) {
        super();
        this.description = description;
        this.id = id;
        this.guid = guid;
        this.correlationGuid = correlationGuid;
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

    public RunAutomationDetails withDescription(Message description) {
        this.description = description;
        return this;
    }

    /**
     * A hierarchical string that uniquely identifies this object's containing run object.
     */
    public String getId() {
        return id;
    }

    /**
     * A hierarchical string that uniquely identifies this object's containing run object.
     */
    public void setId(String id) {
        this.id = id;
    }

    public RunAutomationDetails withId(String id) {
        this.id = id;
        return this;
    }

    /**
     * A stable, unique identifer for this object's containing run object in the form of a GUID.
     */
    public String getGuid() {
        return guid;
    }

    /**
     * A stable, unique identifer for this object's containing run object in the form of a GUID.
     */
    public void setGuid(String guid) {
        this.guid = guid;
    }

    public RunAutomationDetails withGuid(String guid) {
        this.guid = guid;
        return this;
    }

    /**
     * A stable, unique identifier for the equivalence class of runs to which this object's containing run object belongs in the form of a GUID.
     */
    public String getCorrelationGuid() {
        return correlationGuid;
    }

    /**
     * A stable, unique identifier for the equivalence class of runs to which this object's containing run object belongs in the form of a GUID.
     */
    public void setCorrelationGuid(String correlationGuid) {
        this.correlationGuid = correlationGuid;
    }

    public RunAutomationDetails withCorrelationGuid(String correlationGuid) {
        this.correlationGuid = correlationGuid;
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

    public RunAutomationDetails withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(RunAutomationDetails.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("description");
        sb.append('=');
        sb.append(((this.description == null) ? "<null>" : this.description));
        sb.append(',');
        sb.append("id");
        sb.append('=');
        sb.append(((this.id == null) ? "<null>" : this.id));
        sb.append(',');
        sb.append("guid");
        sb.append('=');
        sb.append(((this.guid == null) ? "<null>" : this.guid));
        sb.append(',');
        sb.append("correlationGuid");
        sb.append('=');
        sb.append(((this.correlationGuid == null) ? "<null>" : this.correlationGuid));
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
        result = ((result * 31) + ((this.guid == null) ? 0 : this.guid.hashCode()));
        result = ((result * 31) + ((this.id == null) ? 0 : this.id.hashCode()));
        result = ((result * 31) + ((this.correlationGuid == null) ? 0 : this.correlationGuid.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof RunAutomationDetails) == false) {
            return false;
        }
        RunAutomationDetails rhs = ((RunAutomationDetails) other);
        return ((((((this.description == rhs.description) || ((this.description != null) && this.description.equals(rhs.description))) && ((this.guid == rhs.guid) || ((this.guid != null) && this.guid.equals(rhs.guid)))) && ((this.id == rhs.id) || ((this.id != null) && this.id.equals(rhs.id)))) && ((this.correlationGuid == rhs.correlationGuid) || ((this.correlationGuid != null) && this.correlationGuid.equals(rhs.correlationGuid)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
