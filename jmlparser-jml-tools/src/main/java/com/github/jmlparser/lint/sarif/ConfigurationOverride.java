
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Information about how a specific rule or notification was reconfigured at runtime.
 */
@Generated("jsonschema2pojo")
public class ConfigurationOverride {

    /**
     * Information about a rule or notification that can be configured at runtime.
     * (Required)
     */
    @SerializedName("configuration")
    @Expose
    private ReportingConfiguration configuration;
    /**
     * Information about how to locate a relevant reporting descriptor.
     * (Required)
     */
    @SerializedName("descriptor")
    @Expose
    private ReportingDescriptorReference descriptor;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public ConfigurationOverride() {
    }

    /**
     * @param configuration
     * @param descriptor
     * @param properties
     */
    public ConfigurationOverride(ReportingConfiguration configuration, ReportingDescriptorReference descriptor, PropertyBag properties) {
        super();
        this.configuration = configuration;
        this.descriptor = descriptor;
        this.properties = properties;
    }

    /**
     * Information about a rule or notification that can be configured at runtime.
     * (Required)
     */
    public ReportingConfiguration getConfiguration() {
        return configuration;
    }

    /**
     * Information about a rule or notification that can be configured at runtime.
     * (Required)
     */
    public void setConfiguration(ReportingConfiguration configuration) {
        this.configuration = configuration;
    }

    public ConfigurationOverride withConfiguration(ReportingConfiguration configuration) {
        this.configuration = configuration;
        return this;
    }

    /**
     * Information about how to locate a relevant reporting descriptor.
     * (Required)
     */
    public ReportingDescriptorReference getDescriptor() {
        return descriptor;
    }

    /**
     * Information about how to locate a relevant reporting descriptor.
     * (Required)
     */
    public void setDescriptor(ReportingDescriptorReference descriptor) {
        this.descriptor = descriptor;
    }

    public ConfigurationOverride withDescriptor(ReportingDescriptorReference descriptor) {
        this.descriptor = descriptor;
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

    public ConfigurationOverride withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(ConfigurationOverride.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("configuration");
        sb.append('=');
        sb.append(((this.configuration == null) ? "<null>" : this.configuration));
        sb.append(',');
        sb.append("descriptor");
        sb.append('=');
        sb.append(((this.descriptor == null) ? "<null>" : this.descriptor));
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
        result = ((result * 31) + ((this.configuration == null) ? 0 : this.configuration.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        result = ((result * 31) + ((this.descriptor == null) ? 0 : this.descriptor.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof ConfigurationOverride) == false) {
            return false;
        }
        ConfigurationOverride rhs = ((ConfigurationOverride) other);
        return ((((this.configuration == rhs.configuration) || ((this.configuration != null) && this.configuration.equals(rhs.configuration))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties)))) && ((this.descriptor == rhs.descriptor) || ((this.descriptor != null) && this.descriptor.equals(rhs.descriptor))));
    }

}
