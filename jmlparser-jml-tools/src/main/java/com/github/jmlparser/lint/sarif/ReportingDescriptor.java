
package com.github.jmlparser.lint.sarif;

import java.net.URI;
import java.util.LinkedHashSet;
import java.util.Set;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * Metadata that describes a specific report produced by the tool, as part of the analysis it provides or its runtime reporting.
 */
@Generated("jsonschema2pojo")
public class ReportingDescriptor {

    /**
     * A stable, opaque identifier for the report.
     * (Required)
     */
    @SerializedName("id")
    @Expose
    private String id;
    /**
     * An array of stable, opaque identifiers by which this report was known in some previous version of the analysis tool.
     */
    @SerializedName("deprecatedIds")
    @Expose
    private Set<String> deprecatedIds = new LinkedHashSet<String>();
    /**
     * A unique identifer for the reporting descriptor in the form of a GUID.
     */
    @SerializedName("guid")
    @Expose
    private String guid;
    /**
     * An array of unique identifies in the form of a GUID by which this report was known in some previous version of the analysis tool.
     */
    @SerializedName("deprecatedGuids")
    @Expose
    private Set<String> deprecatedGuids = new LinkedHashSet<String>();
    /**
     * A report identifier that is understandable to an end user.
     */
    @SerializedName("name")
    @Expose
    private String name;
    /**
     * An array of readable identifiers by which this report was known in some previous version of the analysis tool.
     */
    @SerializedName("deprecatedNames")
    @Expose
    private Set<String> deprecatedNames = new LinkedHashSet<String>();
    /**
     * A message string or message format string rendered in multiple formats.
     */
    @SerializedName("shortDescription")
    @Expose
    private MultiformatMessageString shortDescription;
    /**
     * A message string or message format string rendered in multiple formats.
     */
    @SerializedName("fullDescription")
    @Expose
    private MultiformatMessageString fullDescription;
    /**
     * A set of name/value pairs with arbitrary names. Each value is a multiformatMessageString object, which holds message strings in plain text and (optionally) Markdown format. The strings can include placeholders, which can be used to construct a message in combination with an arbitrary number of additional string arguments.
     */
    @SerializedName("messageStrings")
    @Expose
    private MessageStrings messageStrings;
    /**
     * Information about a rule or notification that can be configured at runtime.
     */
    @SerializedName("defaultConfiguration")
    @Expose
    private ReportingConfiguration defaultConfiguration;
    /**
     * A URI where the primary documentation for the report can be found.
     */
    @SerializedName("helpUri")
    @Expose
    private URI helpUri;
    /**
     * A message string or message format string rendered in multiple formats.
     */
    @SerializedName("help")
    @Expose
    private MultiformatMessageString help;
    /**
     * An array of objects that describe relationships between this reporting descriptor and others.
     */
    @SerializedName("relationships")
    @Expose
    private Set<ReportingDescriptorRelationship> relationships = new LinkedHashSet<ReportingDescriptorRelationship>();
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public ReportingDescriptor() {
    }

    /**
     * @param deprecatedIds
     * @param deprecatedGuids
     * @param shortDescription
     * @param fullDescription
     * @param helpUri
     * @param defaultConfiguration
     * @param help
     * @param relationships
     * @param messageStrings
     * @param name
     * @param guid
     * @param deprecatedNames
     * @param id
     * @param properties
     */
    public ReportingDescriptor(String id, Set<String> deprecatedIds, String guid, Set<String> deprecatedGuids, String name, Set<String> deprecatedNames, MultiformatMessageString shortDescription, MultiformatMessageString fullDescription, MessageStrings messageStrings, ReportingConfiguration defaultConfiguration, URI helpUri, MultiformatMessageString help, Set<ReportingDescriptorRelationship> relationships, PropertyBag properties) {
        super();
        this.id = id;
        this.deprecatedIds = deprecatedIds;
        this.guid = guid;
        this.deprecatedGuids = deprecatedGuids;
        this.name = name;
        this.deprecatedNames = deprecatedNames;
        this.shortDescription = shortDescription;
        this.fullDescription = fullDescription;
        this.messageStrings = messageStrings;
        this.defaultConfiguration = defaultConfiguration;
        this.helpUri = helpUri;
        this.help = help;
        this.relationships = relationships;
        this.properties = properties;
    }

    /**
     * A stable, opaque identifier for the report.
     * (Required)
     */
    public String getId() {
        return id;
    }

    /**
     * A stable, opaque identifier for the report.
     * (Required)
     */
    public void setId(String id) {
        this.id = id;
    }

    public ReportingDescriptor withId(String id) {
        this.id = id;
        return this;
    }

    /**
     * An array of stable, opaque identifiers by which this report was known in some previous version of the analysis tool.
     */
    public Set<String> getDeprecatedIds() {
        return deprecatedIds;
    }

    /**
     * An array of stable, opaque identifiers by which this report was known in some previous version of the analysis tool.
     */
    public void setDeprecatedIds(Set<String> deprecatedIds) {
        this.deprecatedIds = deprecatedIds;
    }

    public ReportingDescriptor withDeprecatedIds(Set<String> deprecatedIds) {
        this.deprecatedIds = deprecatedIds;
        return this;
    }

    /**
     * A unique identifer for the reporting descriptor in the form of a GUID.
     */
    public String getGuid() {
        return guid;
    }

    /**
     * A unique identifer for the reporting descriptor in the form of a GUID.
     */
    public void setGuid(String guid) {
        this.guid = guid;
    }

    public ReportingDescriptor withGuid(String guid) {
        this.guid = guid;
        return this;
    }

    /**
     * An array of unique identifies in the form of a GUID by which this report was known in some previous version of the analysis tool.
     */
    public Set<String> getDeprecatedGuids() {
        return deprecatedGuids;
    }

    /**
     * An array of unique identifies in the form of a GUID by which this report was known in some previous version of the analysis tool.
     */
    public void setDeprecatedGuids(Set<String> deprecatedGuids) {
        this.deprecatedGuids = deprecatedGuids;
    }

    public ReportingDescriptor withDeprecatedGuids(Set<String> deprecatedGuids) {
        this.deprecatedGuids = deprecatedGuids;
        return this;
    }

    /**
     * A report identifier that is understandable to an end user.
     */
    public String getName() {
        return name;
    }

    /**
     * A report identifier that is understandable to an end user.
     */
    public void setName(String name) {
        this.name = name;
    }

    public ReportingDescriptor withName(String name) {
        this.name = name;
        return this;
    }

    /**
     * An array of readable identifiers by which this report was known in some previous version of the analysis tool.
     */
    public Set<String> getDeprecatedNames() {
        return deprecatedNames;
    }

    /**
     * An array of readable identifiers by which this report was known in some previous version of the analysis tool.
     */
    public void setDeprecatedNames(Set<String> deprecatedNames) {
        this.deprecatedNames = deprecatedNames;
    }

    public ReportingDescriptor withDeprecatedNames(Set<String> deprecatedNames) {
        this.deprecatedNames = deprecatedNames;
        return this;
    }

    /**
     * A message string or message format string rendered in multiple formats.
     */
    public MultiformatMessageString getShortDescription() {
        return shortDescription;
    }

    /**
     * A message string or message format string rendered in multiple formats.
     */
    public void setShortDescription(MultiformatMessageString shortDescription) {
        this.shortDescription = shortDescription;
    }

    public ReportingDescriptor withShortDescription(MultiformatMessageString shortDescription) {
        this.shortDescription = shortDescription;
        return this;
    }

    /**
     * A message string or message format string rendered in multiple formats.
     */
    public MultiformatMessageString getFullDescription() {
        return fullDescription;
    }

    /**
     * A message string or message format string rendered in multiple formats.
     */
    public void setFullDescription(MultiformatMessageString fullDescription) {
        this.fullDescription = fullDescription;
    }

    public ReportingDescriptor withFullDescription(MultiformatMessageString fullDescription) {
        this.fullDescription = fullDescription;
        return this;
    }

    /**
     * A set of name/value pairs with arbitrary names. Each value is a multiformatMessageString object, which holds message strings in plain text and (optionally) Markdown format. The strings can include placeholders, which can be used to construct a message in combination with an arbitrary number of additional string arguments.
     */
    public MessageStrings getMessageStrings() {
        return messageStrings;
    }

    /**
     * A set of name/value pairs with arbitrary names. Each value is a multiformatMessageString object, which holds message strings in plain text and (optionally) Markdown format. The strings can include placeholders, which can be used to construct a message in combination with an arbitrary number of additional string arguments.
     */
    public void setMessageStrings(MessageStrings messageStrings) {
        this.messageStrings = messageStrings;
    }

    public ReportingDescriptor withMessageStrings(MessageStrings messageStrings) {
        this.messageStrings = messageStrings;
        return this;
    }

    /**
     * Information about a rule or notification that can be configured at runtime.
     */
    public ReportingConfiguration getDefaultConfiguration() {
        return defaultConfiguration;
    }

    /**
     * Information about a rule or notification that can be configured at runtime.
     */
    public void setDefaultConfiguration(ReportingConfiguration defaultConfiguration) {
        this.defaultConfiguration = defaultConfiguration;
    }

    public ReportingDescriptor withDefaultConfiguration(ReportingConfiguration defaultConfiguration) {
        this.defaultConfiguration = defaultConfiguration;
        return this;
    }

    /**
     * A URI where the primary documentation for the report can be found.
     */
    public URI getHelpUri() {
        return helpUri;
    }

    /**
     * A URI where the primary documentation for the report can be found.
     */
    public void setHelpUri(URI helpUri) {
        this.helpUri = helpUri;
    }

    public ReportingDescriptor withHelpUri(URI helpUri) {
        this.helpUri = helpUri;
        return this;
    }

    /**
     * A message string or message format string rendered in multiple formats.
     */
    public MultiformatMessageString getHelp() {
        return help;
    }

    /**
     * A message string or message format string rendered in multiple formats.
     */
    public void setHelp(MultiformatMessageString help) {
        this.help = help;
    }

    public ReportingDescriptor withHelp(MultiformatMessageString help) {
        this.help = help;
        return this;
    }

    /**
     * An array of objects that describe relationships between this reporting descriptor and others.
     */
    public Set<ReportingDescriptorRelationship> getRelationships() {
        return relationships;
    }

    /**
     * An array of objects that describe relationships between this reporting descriptor and others.
     */
    public void setRelationships(Set<ReportingDescriptorRelationship> relationships) {
        this.relationships = relationships;
    }

    public ReportingDescriptor withRelationships(Set<ReportingDescriptorRelationship> relationships) {
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

    public ReportingDescriptor withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(ReportingDescriptor.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("id");
        sb.append('=');
        sb.append(((this.id == null) ? "<null>" : this.id));
        sb.append(',');
        sb.append("deprecatedIds");
        sb.append('=');
        sb.append(((this.deprecatedIds == null) ? "<null>" : this.deprecatedIds));
        sb.append(',');
        sb.append("guid");
        sb.append('=');
        sb.append(((this.guid == null) ? "<null>" : this.guid));
        sb.append(',');
        sb.append("deprecatedGuids");
        sb.append('=');
        sb.append(((this.deprecatedGuids == null) ? "<null>" : this.deprecatedGuids));
        sb.append(',');
        sb.append("name");
        sb.append('=');
        sb.append(((this.name == null) ? "<null>" : this.name));
        sb.append(',');
        sb.append("deprecatedNames");
        sb.append('=');
        sb.append(((this.deprecatedNames == null) ? "<null>" : this.deprecatedNames));
        sb.append(',');
        sb.append("shortDescription");
        sb.append('=');
        sb.append(((this.shortDescription == null) ? "<null>" : this.shortDescription));
        sb.append(',');
        sb.append("fullDescription");
        sb.append('=');
        sb.append(((this.fullDescription == null) ? "<null>" : this.fullDescription));
        sb.append(',');
        sb.append("messageStrings");
        sb.append('=');
        sb.append(((this.messageStrings == null) ? "<null>" : this.messageStrings));
        sb.append(',');
        sb.append("defaultConfiguration");
        sb.append('=');
        sb.append(((this.defaultConfiguration == null) ? "<null>" : this.defaultConfiguration));
        sb.append(',');
        sb.append("helpUri");
        sb.append('=');
        sb.append(((this.helpUri == null) ? "<null>" : this.helpUri));
        sb.append(',');
        sb.append("help");
        sb.append('=');
        sb.append(((this.help == null) ? "<null>" : this.help));
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
        result = ((result * 31) + ((this.deprecatedIds == null) ? 0 : this.deprecatedIds.hashCode()));
        result = ((result * 31) + ((this.deprecatedGuids == null) ? 0 : this.deprecatedGuids.hashCode()));
        result = ((result * 31) + ((this.shortDescription == null) ? 0 : this.shortDescription.hashCode()));
        result = ((result * 31) + ((this.fullDescription == null) ? 0 : this.fullDescription.hashCode()));
        result = ((result * 31) + ((this.helpUri == null) ? 0 : this.helpUri.hashCode()));
        result = ((result * 31) + ((this.defaultConfiguration == null) ? 0 : this.defaultConfiguration.hashCode()));
        result = ((result * 31) + ((this.help == null) ? 0 : this.help.hashCode()));
        result = ((result * 31) + ((this.relationships == null) ? 0 : this.relationships.hashCode()));
        result = ((result * 31) + ((this.messageStrings == null) ? 0 : this.messageStrings.hashCode()));
        result = ((result * 31) + ((this.name == null) ? 0 : this.name.hashCode()));
        result = ((result * 31) + ((this.guid == null) ? 0 : this.guid.hashCode()));
        result = ((result * 31) + ((this.deprecatedNames == null) ? 0 : this.deprecatedNames.hashCode()));
        result = ((result * 31) + ((this.id == null) ? 0 : this.id.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof ReportingDescriptor) == false) {
            return false;
        }
        ReportingDescriptor rhs = ((ReportingDescriptor) other);
        return (((((((((((((((this.deprecatedIds == rhs.deprecatedIds) || ((this.deprecatedIds != null) && this.deprecatedIds.equals(rhs.deprecatedIds))) && ((this.deprecatedGuids == rhs.deprecatedGuids) || ((this.deprecatedGuids != null) && this.deprecatedGuids.equals(rhs.deprecatedGuids)))) && ((this.shortDescription == rhs.shortDescription) || ((this.shortDescription != null) && this.shortDescription.equals(rhs.shortDescription)))) && ((this.fullDescription == rhs.fullDescription) || ((this.fullDescription != null) && this.fullDescription.equals(rhs.fullDescription)))) && ((this.helpUri == rhs.helpUri) || ((this.helpUri != null) && this.helpUri.equals(rhs.helpUri)))) && ((this.defaultConfiguration == rhs.defaultConfiguration) || ((this.defaultConfiguration != null) && this.defaultConfiguration.equals(rhs.defaultConfiguration)))) && ((this.help == rhs.help) || ((this.help != null) && this.help.equals(rhs.help)))) && ((this.relationships == rhs.relationships) || ((this.relationships != null) && this.relationships.equals(rhs.relationships)))) && ((this.messageStrings == rhs.messageStrings) || ((this.messageStrings != null) && this.messageStrings.equals(rhs.messageStrings)))) && ((this.name == rhs.name) || ((this.name != null) && this.name.equals(rhs.name)))) && ((this.guid == rhs.guid) || ((this.guid != null) && this.guid.equals(rhs.guid)))) && ((this.deprecatedNames == rhs.deprecatedNames) || ((this.deprecatedNames != null) && this.deprecatedNames.equals(rhs.deprecatedNames)))) && ((this.id == rhs.id) || ((this.id != null) && this.id.equals(rhs.id)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
