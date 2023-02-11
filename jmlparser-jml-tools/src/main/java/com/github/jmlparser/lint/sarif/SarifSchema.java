
package com.github.jmlparser.lint.sarif;

import java.net.URI;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Static Analysis Results Format (SARIF) Version 2.1.0 JSON Schema
 * <p>
 * Static Analysis Results Format (SARIF) Version 2.1.0 JSON Schema: a standard format for the output of static analysis tools.
 */
@Generated("jsonschema2pojo")
public class SarifSchema {

    /**
     * The URI of the JSON schema corresponding to the version.
     */
    @SerializedName("$schema")
    @Expose
    private URI $schema;
    /**
     * The SARIF format version of this log file.
     * (Required)
     */
    @SerializedName("version")
    @Expose
    private Object version;
    /**
     * The set of runs contained in this log file.
     * (Required)
     */
    @SerializedName("runs")
    @Expose
    private List<Run> runs = new ArrayList<Run>();
    /**
     * References to external property files that share data between runs.
     */
    @SerializedName("inlineExternalProperties")
    @Expose
    private Set<ExternalProperties> inlineExternalProperties = new LinkedHashSet<ExternalProperties>();
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public SarifSchema() {
    }

    /**
     * @param inlineExternalProperties
     * @param $schema
     * @param version
     * @param runs
     * @param properties
     */
    public SarifSchema(URI $schema, Object version, List<Run> runs, Set<ExternalProperties> inlineExternalProperties, PropertyBag properties) {
        super();
        this.$schema = $schema;
        this.version = version;
        this.runs = runs;
        this.inlineExternalProperties = inlineExternalProperties;
        this.properties = properties;
    }

    /**
     * The URI of the JSON schema corresponding to the version.
     */
    public URI get$schema() {
        return $schema;
    }

    /**
     * The URI of the JSON schema corresponding to the version.
     */
    public void set$schema(URI $schema) {
        this.$schema = $schema;
    }

    public SarifSchema with$schema(URI $schema) {
        this.$schema = $schema;
        return this;
    }

    /**
     * The SARIF format version of this log file.
     * (Required)
     */
    public Object getVersion() {
        return version;
    }

    /**
     * The SARIF format version of this log file.
     * (Required)
     */
    public void setVersion(Object version) {
        this.version = version;
    }

    public SarifSchema withVersion(Object version) {
        this.version = version;
        return this;
    }

    /**
     * The set of runs contained in this log file.
     * (Required)
     */
    public List<Run> getRuns() {
        return runs;
    }

    /**
     * The set of runs contained in this log file.
     * (Required)
     */
    public void setRuns(List<Run> runs) {
        this.runs = runs;
    }

    public SarifSchema withRuns(List<Run> runs) {
        this.runs = runs;
        return this;
    }

    /**
     * References to external property files that share data between runs.
     */
    public Set<ExternalProperties> getInlineExternalProperties() {
        return inlineExternalProperties;
    }

    /**
     * References to external property files that share data between runs.
     */
    public void setInlineExternalProperties(Set<ExternalProperties> inlineExternalProperties) {
        this.inlineExternalProperties = inlineExternalProperties;
    }

    public SarifSchema withInlineExternalProperties(Set<ExternalProperties> inlineExternalProperties) {
        this.inlineExternalProperties = inlineExternalProperties;
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

    public SarifSchema withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(SarifSchema.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("$schema");
        sb.append('=');
        sb.append(((this.$schema == null) ? "<null>" : this.$schema));
        sb.append(',');
        sb.append("version");
        sb.append('=');
        sb.append(((this.version == null) ? "<null>" : this.version));
        sb.append(',');
        sb.append("runs");
        sb.append('=');
        sb.append(((this.runs == null) ? "<null>" : this.runs));
        sb.append(',');
        sb.append("inlineExternalProperties");
        sb.append('=');
        sb.append(((this.inlineExternalProperties == null) ? "<null>" : this.inlineExternalProperties));
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
        result = ((result * 31) + ((this.inlineExternalProperties == null) ? 0 : this.inlineExternalProperties.hashCode()));
        result = ((result * 31) + ((this.$schema == null) ? 0 : this.$schema.hashCode()));
        result = ((result * 31) + ((this.version == null) ? 0 : this.version.hashCode()));
        result = ((result * 31) + ((this.runs == null) ? 0 : this.runs.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof SarifSchema) == false) {
            return false;
        }
        SarifSchema rhs = ((SarifSchema) other);
        return ((((((this.inlineExternalProperties == rhs.inlineExternalProperties) || ((this.inlineExternalProperties != null) && this.inlineExternalProperties.equals(rhs.inlineExternalProperties))) && ((this.$schema == rhs.$schema) || ((this.$schema != null) && this.$schema.equals(rhs.$schema)))) && ((this.version == rhs.version) || ((this.version != null) && this.version.equals(rhs.version)))) && ((this.runs == rhs.runs) || ((this.runs != null) && this.runs.equals(rhs.runs)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
