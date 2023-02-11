
package com.github.jmlparser.lint.sarif;

import java.net.URI;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * The top-level element of an external property file.
 */
@Generated("jsonschema2pojo")
public class ExternalProperties {

    /**
     * The URI of the JSON schema corresponding to the version of the external property file format.
     */
    @SerializedName("schema")
    @Expose
    private URI schema;
    /**
     * The SARIF format version of this external properties object.
     */
    @SerializedName("version")
    @Expose
    private ExternalProperties.Version version;
    /**
     * A stable, unique identifer for this external properties object, in the form of a GUID.
     */
    @SerializedName("guid")
    @Expose
    private String guid;
    /**
     * A stable, unique identifer for the run associated with this external properties object, in the form of a GUID.
     */
    @SerializedName("runGuid")
    @Expose
    private String runGuid;
    /**
     * Describes how a converter transformed the output of a static analysis tool from the analysis tool's native output format into the SARIF format.
     */
    @SerializedName("conversion")
    @Expose
    private Conversion conversion;
    /**
     * An array of graph objects that will be merged with a separate run.
     */
    @SerializedName("graphs")
    @Expose
    private Set<Graph> graphs = new LinkedHashSet<Graph>();
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("externalizedProperties")
    @Expose
    private PropertyBag externalizedProperties;
    /**
     * An array of artifact objects that will be merged with a separate run.
     */
    @SerializedName("artifacts")
    @Expose
    private Set<Artifact> artifacts = new LinkedHashSet<Artifact>();
    /**
     * Describes the invocation of the analysis tool that will be merged with a separate run.
     */
    @SerializedName("invocations")
    @Expose
    private List<Invocation> invocations = new ArrayList<Invocation>();
    /**
     * An array of logical locations such as namespaces, types or functions that will be merged with a separate run.
     */
    @SerializedName("logicalLocations")
    @Expose
    private Set<LogicalLocation> logicalLocations = new LinkedHashSet<LogicalLocation>();
    /**
     * An array of threadFlowLocation objects that will be merged with a separate run.
     */
    @SerializedName("threadFlowLocations")
    @Expose
    private Set<ThreadFlowLocation> threadFlowLocations = new LinkedHashSet<ThreadFlowLocation>();
    /**
     * An array of result objects that will be merged with a separate run.
     */
    @SerializedName("results")
    @Expose
    private List<Result> results = new ArrayList<Result>();
    /**
     * Tool taxonomies that will be merged with a separate run.
     */
    @SerializedName("taxonomies")
    @Expose
    private Set<ToolComponent> taxonomies = new LinkedHashSet<ToolComponent>();
    /**
     * A component, such as a plug-in or the driver, of the analysis tool that was run.
     */
    @SerializedName("driver")
    @Expose
    private ToolComponent driver;
    /**
     * Tool extensions that will be merged with a separate run.
     */
    @SerializedName("extensions")
    @Expose
    private Set<ToolComponent> extensions = new LinkedHashSet<ToolComponent>();
    /**
     * Tool policies that will be merged with a separate run.
     */
    @SerializedName("policies")
    @Expose
    private Set<ToolComponent> policies = new LinkedHashSet<ToolComponent>();
    /**
     * Tool translations that will be merged with a separate run.
     */
    @SerializedName("translations")
    @Expose
    private Set<ToolComponent> translations = new LinkedHashSet<ToolComponent>();
    /**
     * Addresses that will be merged with a separate run.
     */
    @SerializedName("addresses")
    @Expose
    private List<Address> addresses = new ArrayList<Address>();
    /**
     * Requests that will be merged with a separate run.
     */
    @SerializedName("webRequests")
    @Expose
    private Set<WebRequest> webRequests = new LinkedHashSet<WebRequest>();
    /**
     * Responses that will be merged with a separate run.
     */
    @SerializedName("webResponses")
    @Expose
    private Set<WebResponse> webResponses = new LinkedHashSet<WebResponse>();
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public ExternalProperties() {
    }

    /**
     * @param schema
     * @param addresses
     * @param logicalLocations
     * @param policies
     * @param runGuid
     * @param version
     * @param externalizedProperties
     * @param invocations
     * @param graphs
     * @param extensions
     * @param driver
     * @param taxonomies
     * @param translations
     * @param webResponses
     * @param guid
     * @param webRequests
     * @param results
     * @param threadFlowLocations
     * @param properties
     * @param conversion
     * @param artifacts
     */
    public ExternalProperties(URI schema, ExternalProperties.Version version, String guid, String runGuid, Conversion conversion, Set<Graph> graphs, PropertyBag externalizedProperties, Set<Artifact> artifacts, List<Invocation> invocations, Set<LogicalLocation> logicalLocations, Set<ThreadFlowLocation> threadFlowLocations, List<Result> results, Set<ToolComponent> taxonomies, ToolComponent driver, Set<ToolComponent> extensions, Set<ToolComponent> policies, Set<ToolComponent> translations, List<Address> addresses, Set<WebRequest> webRequests, Set<WebResponse> webResponses, PropertyBag properties) {
        super();
        this.schema = schema;
        this.version = version;
        this.guid = guid;
        this.runGuid = runGuid;
        this.conversion = conversion;
        this.graphs = graphs;
        this.externalizedProperties = externalizedProperties;
        this.artifacts = artifacts;
        this.invocations = invocations;
        this.logicalLocations = logicalLocations;
        this.threadFlowLocations = threadFlowLocations;
        this.results = results;
        this.taxonomies = taxonomies;
        this.driver = driver;
        this.extensions = extensions;
        this.policies = policies;
        this.translations = translations;
        this.addresses = addresses;
        this.webRequests = webRequests;
        this.webResponses = webResponses;
        this.properties = properties;
    }

    /**
     * The URI of the JSON schema corresponding to the version of the external property file format.
     */
    public URI getSchema() {
        return schema;
    }

    /**
     * The URI of the JSON schema corresponding to the version of the external property file format.
     */
    public void setSchema(URI schema) {
        this.schema = schema;
    }

    public ExternalProperties withSchema(URI schema) {
        this.schema = schema;
        return this;
    }

    /**
     * The SARIF format version of this external properties object.
     */
    public ExternalProperties.Version getVersion() {
        return version;
    }

    /**
     * The SARIF format version of this external properties object.
     */
    public void setVersion(ExternalProperties.Version version) {
        this.version = version;
    }

    public ExternalProperties withVersion(ExternalProperties.Version version) {
        this.version = version;
        return this;
    }

    /**
     * A stable, unique identifer for this external properties object, in the form of a GUID.
     */
    public String getGuid() {
        return guid;
    }

    /**
     * A stable, unique identifer for this external properties object, in the form of a GUID.
     */
    public void setGuid(String guid) {
        this.guid = guid;
    }

    public ExternalProperties withGuid(String guid) {
        this.guid = guid;
        return this;
    }

    /**
     * A stable, unique identifer for the run associated with this external properties object, in the form of a GUID.
     */
    public String getRunGuid() {
        return runGuid;
    }

    /**
     * A stable, unique identifer for the run associated with this external properties object, in the form of a GUID.
     */
    public void setRunGuid(String runGuid) {
        this.runGuid = runGuid;
    }

    public ExternalProperties withRunGuid(String runGuid) {
        this.runGuid = runGuid;
        return this;
    }

    /**
     * Describes how a converter transformed the output of a static analysis tool from the analysis tool's native output format into the SARIF format.
     */
    public Conversion getConversion() {
        return conversion;
    }

    /**
     * Describes how a converter transformed the output of a static analysis tool from the analysis tool's native output format into the SARIF format.
     */
    public void setConversion(Conversion conversion) {
        this.conversion = conversion;
    }

    public ExternalProperties withConversion(Conversion conversion) {
        this.conversion = conversion;
        return this;
    }

    /**
     * An array of graph objects that will be merged with a separate run.
     */
    public Set<Graph> getGraphs() {
        return graphs;
    }

    /**
     * An array of graph objects that will be merged with a separate run.
     */
    public void setGraphs(Set<Graph> graphs) {
        this.graphs = graphs;
    }

    public ExternalProperties withGraphs(Set<Graph> graphs) {
        this.graphs = graphs;
        return this;
    }

    /**
     * Key/value pairs that provide additional information about the object.
     */
    public PropertyBag getExternalizedProperties() {
        return externalizedProperties;
    }

    /**
     * Key/value pairs that provide additional information about the object.
     */
    public void setExternalizedProperties(PropertyBag externalizedProperties) {
        this.externalizedProperties = externalizedProperties;
    }

    public ExternalProperties withExternalizedProperties(PropertyBag externalizedProperties) {
        this.externalizedProperties = externalizedProperties;
        return this;
    }

    /**
     * An array of artifact objects that will be merged with a separate run.
     */
    public Set<Artifact> getArtifacts() {
        return artifacts;
    }

    /**
     * An array of artifact objects that will be merged with a separate run.
     */
    public void setArtifacts(Set<Artifact> artifacts) {
        this.artifacts = artifacts;
    }

    public ExternalProperties withArtifacts(Set<Artifact> artifacts) {
        this.artifacts = artifacts;
        return this;
    }

    /**
     * Describes the invocation of the analysis tool that will be merged with a separate run.
     */
    public List<Invocation> getInvocations() {
        return invocations;
    }

    /**
     * Describes the invocation of the analysis tool that will be merged with a separate run.
     */
    public void setInvocations(List<Invocation> invocations) {
        this.invocations = invocations;
    }

    public ExternalProperties withInvocations(List<Invocation> invocations) {
        this.invocations = invocations;
        return this;
    }

    /**
     * An array of logical locations such as namespaces, types or functions that will be merged with a separate run.
     */
    public Set<LogicalLocation> getLogicalLocations() {
        return logicalLocations;
    }

    /**
     * An array of logical locations such as namespaces, types or functions that will be merged with a separate run.
     */
    public void setLogicalLocations(Set<LogicalLocation> logicalLocations) {
        this.logicalLocations = logicalLocations;
    }

    public ExternalProperties withLogicalLocations(Set<LogicalLocation> logicalLocations) {
        this.logicalLocations = logicalLocations;
        return this;
    }

    /**
     * An array of threadFlowLocation objects that will be merged with a separate run.
     */
    public Set<ThreadFlowLocation> getThreadFlowLocations() {
        return threadFlowLocations;
    }

    /**
     * An array of threadFlowLocation objects that will be merged with a separate run.
     */
    public void setThreadFlowLocations(Set<ThreadFlowLocation> threadFlowLocations) {
        this.threadFlowLocations = threadFlowLocations;
    }

    public ExternalProperties withThreadFlowLocations(Set<ThreadFlowLocation> threadFlowLocations) {
        this.threadFlowLocations = threadFlowLocations;
        return this;
    }

    /**
     * An array of result objects that will be merged with a separate run.
     */
    public List<Result> getResults() {
        return results;
    }

    /**
     * An array of result objects that will be merged with a separate run.
     */
    public void setResults(List<Result> results) {
        this.results = results;
    }

    public ExternalProperties withResults(List<Result> results) {
        this.results = results;
        return this;
    }

    /**
     * Tool taxonomies that will be merged with a separate run.
     */
    public Set<ToolComponent> getTaxonomies() {
        return taxonomies;
    }

    /**
     * Tool taxonomies that will be merged with a separate run.
     */
    public void setTaxonomies(Set<ToolComponent> taxonomies) {
        this.taxonomies = taxonomies;
    }

    public ExternalProperties withTaxonomies(Set<ToolComponent> taxonomies) {
        this.taxonomies = taxonomies;
        return this;
    }

    /**
     * A component, such as a plug-in or the driver, of the analysis tool that was run.
     */
    public ToolComponent getDriver() {
        return driver;
    }

    /**
     * A component, such as a plug-in or the driver, of the analysis tool that was run.
     */
    public void setDriver(ToolComponent driver) {
        this.driver = driver;
    }

    public ExternalProperties withDriver(ToolComponent driver) {
        this.driver = driver;
        return this;
    }

    /**
     * Tool extensions that will be merged with a separate run.
     */
    public Set<ToolComponent> getExtensions() {
        return extensions;
    }

    /**
     * Tool extensions that will be merged with a separate run.
     */
    public void setExtensions(Set<ToolComponent> extensions) {
        this.extensions = extensions;
    }

    public ExternalProperties withExtensions(Set<ToolComponent> extensions) {
        this.extensions = extensions;
        return this;
    }

    /**
     * Tool policies that will be merged with a separate run.
     */
    public Set<ToolComponent> getPolicies() {
        return policies;
    }

    /**
     * Tool policies that will be merged with a separate run.
     */
    public void setPolicies(Set<ToolComponent> policies) {
        this.policies = policies;
    }

    public ExternalProperties withPolicies(Set<ToolComponent> policies) {
        this.policies = policies;
        return this;
    }

    /**
     * Tool translations that will be merged with a separate run.
     */
    public Set<ToolComponent> getTranslations() {
        return translations;
    }

    /**
     * Tool translations that will be merged with a separate run.
     */
    public void setTranslations(Set<ToolComponent> translations) {
        this.translations = translations;
    }

    public ExternalProperties withTranslations(Set<ToolComponent> translations) {
        this.translations = translations;
        return this;
    }

    /**
     * Addresses that will be merged with a separate run.
     */
    public List<Address> getAddresses() {
        return addresses;
    }

    /**
     * Addresses that will be merged with a separate run.
     */
    public void setAddresses(List<Address> addresses) {
        this.addresses = addresses;
    }

    public ExternalProperties withAddresses(List<Address> addresses) {
        this.addresses = addresses;
        return this;
    }

    /**
     * Requests that will be merged with a separate run.
     */
    public Set<WebRequest> getWebRequests() {
        return webRequests;
    }

    /**
     * Requests that will be merged with a separate run.
     */
    public void setWebRequests(Set<WebRequest> webRequests) {
        this.webRequests = webRequests;
    }

    public ExternalProperties withWebRequests(Set<WebRequest> webRequests) {
        this.webRequests = webRequests;
        return this;
    }

    /**
     * Responses that will be merged with a separate run.
     */
    public Set<WebResponse> getWebResponses() {
        return webResponses;
    }

    /**
     * Responses that will be merged with a separate run.
     */
    public void setWebResponses(Set<WebResponse> webResponses) {
        this.webResponses = webResponses;
    }

    public ExternalProperties withWebResponses(Set<WebResponse> webResponses) {
        this.webResponses = webResponses;
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

    public ExternalProperties withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(ExternalProperties.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("schema");
        sb.append('=');
        sb.append(((this.schema == null) ? "<null>" : this.schema));
        sb.append(',');
        sb.append("version");
        sb.append('=');
        sb.append(((this.version == null) ? "<null>" : this.version));
        sb.append(',');
        sb.append("guid");
        sb.append('=');
        sb.append(((this.guid == null) ? "<null>" : this.guid));
        sb.append(',');
        sb.append("runGuid");
        sb.append('=');
        sb.append(((this.runGuid == null) ? "<null>" : this.runGuid));
        sb.append(',');
        sb.append("conversion");
        sb.append('=');
        sb.append(((this.conversion == null) ? "<null>" : this.conversion));
        sb.append(',');
        sb.append("graphs");
        sb.append('=');
        sb.append(((this.graphs == null) ? "<null>" : this.graphs));
        sb.append(',');
        sb.append("externalizedProperties");
        sb.append('=');
        sb.append(((this.externalizedProperties == null) ? "<null>" : this.externalizedProperties));
        sb.append(',');
        sb.append("artifacts");
        sb.append('=');
        sb.append(((this.artifacts == null) ? "<null>" : this.artifacts));
        sb.append(',');
        sb.append("invocations");
        sb.append('=');
        sb.append(((this.invocations == null) ? "<null>" : this.invocations));
        sb.append(',');
        sb.append("logicalLocations");
        sb.append('=');
        sb.append(((this.logicalLocations == null) ? "<null>" : this.logicalLocations));
        sb.append(',');
        sb.append("threadFlowLocations");
        sb.append('=');
        sb.append(((this.threadFlowLocations == null) ? "<null>" : this.threadFlowLocations));
        sb.append(',');
        sb.append("results");
        sb.append('=');
        sb.append(((this.results == null) ? "<null>" : this.results));
        sb.append(',');
        sb.append("taxonomies");
        sb.append('=');
        sb.append(((this.taxonomies == null) ? "<null>" : this.taxonomies));
        sb.append(',');
        sb.append("driver");
        sb.append('=');
        sb.append(((this.driver == null) ? "<null>" : this.driver));
        sb.append(',');
        sb.append("extensions");
        sb.append('=');
        sb.append(((this.extensions == null) ? "<null>" : this.extensions));
        sb.append(',');
        sb.append("policies");
        sb.append('=');
        sb.append(((this.policies == null) ? "<null>" : this.policies));
        sb.append(',');
        sb.append("translations");
        sb.append('=');
        sb.append(((this.translations == null) ? "<null>" : this.translations));
        sb.append(',');
        sb.append("addresses");
        sb.append('=');
        sb.append(((this.addresses == null) ? "<null>" : this.addresses));
        sb.append(',');
        sb.append("webRequests");
        sb.append('=');
        sb.append(((this.webRequests == null) ? "<null>" : this.webRequests));
        sb.append(',');
        sb.append("webResponses");
        sb.append('=');
        sb.append(((this.webResponses == null) ? "<null>" : this.webResponses));
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
        result = ((result * 31) + ((this.schema == null) ? 0 : this.schema.hashCode()));
        result = ((result * 31) + ((this.addresses == null) ? 0 : this.addresses.hashCode()));
        result = ((result * 31) + ((this.logicalLocations == null) ? 0 : this.logicalLocations.hashCode()));
        result = ((result * 31) + ((this.policies == null) ? 0 : this.policies.hashCode()));
        result = ((result * 31) + ((this.runGuid == null) ? 0 : this.runGuid.hashCode()));
        result = ((result * 31) + ((this.version == null) ? 0 : this.version.hashCode()));
        result = ((result * 31) + ((this.externalizedProperties == null) ? 0 : this.externalizedProperties.hashCode()));
        result = ((result * 31) + ((this.invocations == null) ? 0 : this.invocations.hashCode()));
        result = ((result * 31) + ((this.graphs == null) ? 0 : this.graphs.hashCode()));
        result = ((result * 31) + ((this.extensions == null) ? 0 : this.extensions.hashCode()));
        result = ((result * 31) + ((this.driver == null) ? 0 : this.driver.hashCode()));
        result = ((result * 31) + ((this.taxonomies == null) ? 0 : this.taxonomies.hashCode()));
        result = ((result * 31) + ((this.translations == null) ? 0 : this.translations.hashCode()));
        result = ((result * 31) + ((this.webResponses == null) ? 0 : this.webResponses.hashCode()));
        result = ((result * 31) + ((this.guid == null) ? 0 : this.guid.hashCode()));
        result = ((result * 31) + ((this.webRequests == null) ? 0 : this.webRequests.hashCode()));
        result = ((result * 31) + ((this.results == null) ? 0 : this.results.hashCode()));
        result = ((result * 31) + ((this.threadFlowLocations == null) ? 0 : this.threadFlowLocations.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        result = ((result * 31) + ((this.conversion == null) ? 0 : this.conversion.hashCode()));
        result = ((result * 31) + ((this.artifacts == null) ? 0 : this.artifacts.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof ExternalProperties) == false) {
            return false;
        }
        ExternalProperties rhs = ((ExternalProperties) other);
        return ((((((((((((((((((((((this.schema == rhs.schema) || ((this.schema != null) && this.schema.equals(rhs.schema))) && ((this.addresses == rhs.addresses) || ((this.addresses != null) && this.addresses.equals(rhs.addresses)))) && ((this.logicalLocations == rhs.logicalLocations) || ((this.logicalLocations != null) && this.logicalLocations.equals(rhs.logicalLocations)))) && ((this.policies == rhs.policies) || ((this.policies != null) && this.policies.equals(rhs.policies)))) && ((this.runGuid == rhs.runGuid) || ((this.runGuid != null) && this.runGuid.equals(rhs.runGuid)))) && ((this.version == rhs.version) || ((this.version != null) && this.version.equals(rhs.version)))) && ((this.externalizedProperties == rhs.externalizedProperties) || ((this.externalizedProperties != null) && this.externalizedProperties.equals(rhs.externalizedProperties)))) && ((this.invocations == rhs.invocations) || ((this.invocations != null) && this.invocations.equals(rhs.invocations)))) && ((this.graphs == rhs.graphs) || ((this.graphs != null) && this.graphs.equals(rhs.graphs)))) && ((this.extensions == rhs.extensions) || ((this.extensions != null) && this.extensions.equals(rhs.extensions)))) && ((this.driver == rhs.driver) || ((this.driver != null) && this.driver.equals(rhs.driver)))) && ((this.taxonomies == rhs.taxonomies) || ((this.taxonomies != null) && this.taxonomies.equals(rhs.taxonomies)))) && ((this.translations == rhs.translations) || ((this.translations != null) && this.translations.equals(rhs.translations)))) && ((this.webResponses == rhs.webResponses) || ((this.webResponses != null) && this.webResponses.equals(rhs.webResponses)))) && ((this.guid == rhs.guid) || ((this.guid != null) && this.guid.equals(rhs.guid)))) && ((this.webRequests == rhs.webRequests) || ((this.webRequests != null) && this.webRequests.equals(rhs.webRequests)))) && ((this.results == rhs.results) || ((this.results != null) && this.results.equals(rhs.results)))) && ((this.threadFlowLocations == rhs.threadFlowLocations) || ((this.threadFlowLocations != null) && this.threadFlowLocations.equals(rhs.threadFlowLocations)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties)))) && ((this.conversion == rhs.conversion) || ((this.conversion != null) && this.conversion.equals(rhs.conversion)))) && ((this.artifacts == rhs.artifacts) || ((this.artifacts != null) && this.artifacts.equals(rhs.artifacts))));
    }


    /**
     * The SARIF format version of this external properties object.
     */
    @Generated("jsonschema2pojo")
    public enum Version {

        @SerializedName("2.1.0")
        _2_1_0("2.1.0");
        private final String value;
        private final static Map<String, ExternalProperties.Version> CONSTANTS = new HashMap<String, ExternalProperties.Version>();

        static {
            for (ExternalProperties.Version c : values()) {
                CONSTANTS.put(c.value, c);
            }
        }

        Version(String value) {
            this.value = value;
        }

        @Override
        public String toString() {
            return this.value;
        }

        public String value() {
            return this.value;
        }

        public static ExternalProperties.Version fromValue(String value) {
            ExternalProperties.Version constant = CONSTANTS.get(value);
            if (constant == null) {
                throw new IllegalArgumentException(value);
            } else {
                return constant;
            }
        }

    }

}
