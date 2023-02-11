
package com.github.jmlparser.lint.sarif;

import java.net.URI;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.Expose;
import com.google.gson.annotations.SerializedName;


/**
 * A component, such as a plug-in or the driver, of the analysis tool that was run.
 */
@Generated("jsonschema2pojo")
public class ToolComponent {

    /**
     * A unique identifer for the tool component in the form of a GUID.
     */
    @SerializedName("guid")
    @Expose
    private String guid;
    /**
     * The name of the tool component.
     * (Required)
     */
    @SerializedName("name")
    @Expose
    private String name;
    /**
     * The organization or company that produced the tool component.
     */
    @SerializedName("organization")
    @Expose
    private String organization;
    /**
     * A product suite to which the tool component belongs.
     */
    @SerializedName("product")
    @Expose
    private String product;
    /**
     * A localizable string containing the name of the suite of products to which the tool component belongs.
     */
    @SerializedName("productSuite")
    @Expose
    private String productSuite;
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
     * The name of the tool component along with its version and any other useful identifying information, such as its locale.
     */
    @SerializedName("fullName")
    @Expose
    private String fullName;
    /**
     * The tool component version, in whatever format the component natively provides.
     */
    @SerializedName("version")
    @Expose
    private String version;
    /**
     * The tool component version in the format specified by Semantic Versioning 2.0.
     */
    @SerializedName("semanticVersion")
    @Expose
    private String semanticVersion;
    /**
     * The binary version of the tool component's primary executable file expressed as four non-negative integers separated by a period (for operating systems that express file versions in this way).
     */
    @SerializedName("dottedQuadFileVersion")
    @Expose
    private String dottedQuadFileVersion;
    /**
     * A string specifying the UTC date (and optionally, the time) of the component's release.
     */
    @SerializedName("releaseDateUtc")
    @Expose
    private String releaseDateUtc;
    /**
     * The absolute URI from which the tool component can be downloaded.
     */
    @SerializedName("downloadUri")
    @Expose
    private URI downloadUri;
    /**
     * The absolute URI at which information about this version of the tool component can be found.
     */
    @SerializedName("informationUri")
    @Expose
    private URI informationUri;
    /**
     * A dictionary, each of whose keys is a resource identifier and each of whose values is a multiformatMessageString object, which holds message strings in plain text and (optionally) Markdown format. The strings can include placeholders, which can be used to construct a message in combination with an arbitrary number of additional string arguments.
     */
    @SerializedName("globalMessageStrings")
    @Expose
    private GlobalMessageStrings globalMessageStrings;
    /**
     * An array of reportingDescriptor objects relevant to the notifications related to the configuration and runtime execution of the tool component.
     */
    @SerializedName("notifications")
    @Expose
    private Set<ReportingDescriptor> notifications = new LinkedHashSet<ReportingDescriptor>();
    /**
     * An array of reportingDescriptor objects relevant to the analysis performed by the tool component.
     */
    @SerializedName("rules")
    @Expose
    private Set<ReportingDescriptor> rules = new LinkedHashSet<ReportingDescriptor>();
    /**
     * An array of reportingDescriptor objects relevant to the definitions of both standalone and tool-defined taxonomies.
     */
    @SerializedName("taxa")
    @Expose
    private Set<ReportingDescriptor> taxa = new LinkedHashSet<ReportingDescriptor>();
    /**
     * An array of the artifactLocation objects associated with the tool component.
     */
    @SerializedName("locations")
    @Expose
    private List<ArtifactLocation> locations = new ArrayList<ArtifactLocation>();
    /**
     * The language of the messages emitted into the log file during this run (expressed as an ISO 639-1 two-letter lowercase language code) and an optional region (expressed as an ISO 3166-1 two-letter uppercase subculture code associated with a country or region). The casing is recommended but not required (in order for this data to conform to RFC5646).
     */
    @SerializedName("language")
    @Expose
    private String language = "en-US";
    /**
     * The kinds of data contained in this object.
     */
    @SerializedName("contents")
    @Expose
    private Set<Object> contents = new LinkedHashSet<Object>(Arrays.asList(null, null));
    /**
     * Specifies whether this object contains a complete definition of the localizable and/or non-localizable data for this component, as opposed to including only data that is relevant to the results persisted to this log file.
     */
    @SerializedName("isComprehensive")
    @Expose
    private boolean isComprehensive = false;
    /**
     * The semantic version of the localized strings defined in this component; maintained by components that provide translations.
     */
    @SerializedName("localizedDataSemanticVersion")
    @Expose
    private String localizedDataSemanticVersion;
    /**
     * The minimum value of localizedDataSemanticVersion required in translations consumed by this component; used by components that consume translations.
     */
    @SerializedName("minimumRequiredLocalizedDataSemanticVersion")
    @Expose
    private String minimumRequiredLocalizedDataSemanticVersion;
    /**
     * Identifies a particular toolComponent object, either the driver or an extension.
     */
    @SerializedName("associatedComponent")
    @Expose
    private ToolComponentReference associatedComponent;
    /**
     * Provides additional metadata related to translation.
     */
    @SerializedName("translationMetadata")
    @Expose
    private TranslationMetadata translationMetadata;
    /**
     * An array of toolComponentReference objects to declare the taxonomies supported by the tool component.
     */
    @SerializedName("supportedTaxonomies")
    @Expose
    private Set<ToolComponentReference> supportedTaxonomies = new LinkedHashSet<ToolComponentReference>();
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public ToolComponent() {
    }

    /**
     * @param releaseDateUtc
     * @param rules
     * @param language
     * @param downloadUri
     * @param supportedTaxonomies
     * @param fullDescription
     * @param informationUri
     * @param associatedComponent
     * @param translationMetadata
     * @param productSuite
     * @param taxa
     * @param product
     * @param isComprehensive
     * @param minimumRequiredLocalizedDataSemanticVersion
     * @param fullName
     * @param shortDescription
     * @param version
     * @param globalMessageStrings
     * @param localizedDataSemanticVersion
     * @param dottedQuadFileVersion
     * @param contents
     * @param organization
     * @param name
     * @param semanticVersion
     * @param guid
     * @param locations
     * @param notifications
     * @param properties
     */
    public ToolComponent(String guid, String name, String organization, String product, String productSuite, MultiformatMessageString shortDescription, MultiformatMessageString fullDescription, String fullName, String version, String semanticVersion, String dottedQuadFileVersion, String releaseDateUtc, URI downloadUri, URI informationUri, GlobalMessageStrings globalMessageStrings, Set<ReportingDescriptor> notifications, Set<ReportingDescriptor> rules, Set<ReportingDescriptor> taxa, List<ArtifactLocation> locations, String language, Set<Object> contents, boolean isComprehensive, String localizedDataSemanticVersion, String minimumRequiredLocalizedDataSemanticVersion, ToolComponentReference associatedComponent, TranslationMetadata translationMetadata, Set<ToolComponentReference> supportedTaxonomies, PropertyBag properties) {
        super();
        this.guid = guid;
        this.name = name;
        this.organization = organization;
        this.product = product;
        this.productSuite = productSuite;
        this.shortDescription = shortDescription;
        this.fullDescription = fullDescription;
        this.fullName = fullName;
        this.version = version;
        this.semanticVersion = semanticVersion;
        this.dottedQuadFileVersion = dottedQuadFileVersion;
        this.releaseDateUtc = releaseDateUtc;
        this.downloadUri = downloadUri;
        this.informationUri = informationUri;
        this.globalMessageStrings = globalMessageStrings;
        this.notifications = notifications;
        this.rules = rules;
        this.taxa = taxa;
        this.locations = locations;
        this.language = language;
        this.contents = contents;
        this.isComprehensive = isComprehensive;
        this.localizedDataSemanticVersion = localizedDataSemanticVersion;
        this.minimumRequiredLocalizedDataSemanticVersion = minimumRequiredLocalizedDataSemanticVersion;
        this.associatedComponent = associatedComponent;
        this.translationMetadata = translationMetadata;
        this.supportedTaxonomies = supportedTaxonomies;
        this.properties = properties;
    }

    /**
     * A unique identifer for the tool component in the form of a GUID.
     */
    public String getGuid() {
        return guid;
    }

    /**
     * A unique identifer for the tool component in the form of a GUID.
     */
    public void setGuid(String guid) {
        this.guid = guid;
    }

    public ToolComponent withGuid(String guid) {
        this.guid = guid;
        return this;
    }

    /**
     * The name of the tool component.
     * (Required)
     */
    public String getName() {
        return name;
    }

    /**
     * The name of the tool component.
     * (Required)
     */
    public void setName(String name) {
        this.name = name;
    }

    public ToolComponent withName(String name) {
        this.name = name;
        return this;
    }

    /**
     * The organization or company that produced the tool component.
     */
    public String getOrganization() {
        return organization;
    }

    /**
     * The organization or company that produced the tool component.
     */
    public void setOrganization(String organization) {
        this.organization = organization;
    }

    public ToolComponent withOrganization(String organization) {
        this.organization = organization;
        return this;
    }

    /**
     * A product suite to which the tool component belongs.
     */
    public String getProduct() {
        return product;
    }

    /**
     * A product suite to which the tool component belongs.
     */
    public void setProduct(String product) {
        this.product = product;
    }

    public ToolComponent withProduct(String product) {
        this.product = product;
        return this;
    }

    /**
     * A localizable string containing the name of the suite of products to which the tool component belongs.
     */
    public String getProductSuite() {
        return productSuite;
    }

    /**
     * A localizable string containing the name of the suite of products to which the tool component belongs.
     */
    public void setProductSuite(String productSuite) {
        this.productSuite = productSuite;
    }

    public ToolComponent withProductSuite(String productSuite) {
        this.productSuite = productSuite;
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

    public ToolComponent withShortDescription(MultiformatMessageString shortDescription) {
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

    public ToolComponent withFullDescription(MultiformatMessageString fullDescription) {
        this.fullDescription = fullDescription;
        return this;
    }

    /**
     * The name of the tool component along with its version and any other useful identifying information, such as its locale.
     */
    public String getFullName() {
        return fullName;
    }

    /**
     * The name of the tool component along with its version and any other useful identifying information, such as its locale.
     */
    public void setFullName(String fullName) {
        this.fullName = fullName;
    }

    public ToolComponent withFullName(String fullName) {
        this.fullName = fullName;
        return this;
    }

    /**
     * The tool component version, in whatever format the component natively provides.
     */
    public String getVersion() {
        return version;
    }

    /**
     * The tool component version, in whatever format the component natively provides.
     */
    public void setVersion(String version) {
        this.version = version;
    }

    public ToolComponent withVersion(String version) {
        this.version = version;
        return this;
    }

    /**
     * The tool component version in the format specified by Semantic Versioning 2.0.
     */
    public String getSemanticVersion() {
        return semanticVersion;
    }

    /**
     * The tool component version in the format specified by Semantic Versioning 2.0.
     */
    public void setSemanticVersion(String semanticVersion) {
        this.semanticVersion = semanticVersion;
    }

    public ToolComponent withSemanticVersion(String semanticVersion) {
        this.semanticVersion = semanticVersion;
        return this;
    }

    /**
     * The binary version of the tool component's primary executable file expressed as four non-negative integers separated by a period (for operating systems that express file versions in this way).
     */
    public String getDottedQuadFileVersion() {
        return dottedQuadFileVersion;
    }

    /**
     * The binary version of the tool component's primary executable file expressed as four non-negative integers separated by a period (for operating systems that express file versions in this way).
     */
    public void setDottedQuadFileVersion(String dottedQuadFileVersion) {
        this.dottedQuadFileVersion = dottedQuadFileVersion;
    }

    public ToolComponent withDottedQuadFileVersion(String dottedQuadFileVersion) {
        this.dottedQuadFileVersion = dottedQuadFileVersion;
        return this;
    }

    /**
     * A string specifying the UTC date (and optionally, the time) of the component's release.
     */
    public String getReleaseDateUtc() {
        return releaseDateUtc;
    }

    /**
     * A string specifying the UTC date (and optionally, the time) of the component's release.
     */
    public void setReleaseDateUtc(String releaseDateUtc) {
        this.releaseDateUtc = releaseDateUtc;
    }

    public ToolComponent withReleaseDateUtc(String releaseDateUtc) {
        this.releaseDateUtc = releaseDateUtc;
        return this;
    }

    /**
     * The absolute URI from which the tool component can be downloaded.
     */
    public URI getDownloadUri() {
        return downloadUri;
    }

    /**
     * The absolute URI from which the tool component can be downloaded.
     */
    public void setDownloadUri(URI downloadUri) {
        this.downloadUri = downloadUri;
    }

    public ToolComponent withDownloadUri(URI downloadUri) {
        this.downloadUri = downloadUri;
        return this;
    }

    /**
     * The absolute URI at which information about this version of the tool component can be found.
     */
    public URI getInformationUri() {
        return informationUri;
    }

    /**
     * The absolute URI at which information about this version of the tool component can be found.
     */
    public void setInformationUri(URI informationUri) {
        this.informationUri = informationUri;
    }

    public ToolComponent withInformationUri(URI informationUri) {
        this.informationUri = informationUri;
        return this;
    }

    /**
     * A dictionary, each of whose keys is a resource identifier and each of whose values is a multiformatMessageString object, which holds message strings in plain text and (optionally) Markdown format. The strings can include placeholders, which can be used to construct a message in combination with an arbitrary number of additional string arguments.
     */
    public GlobalMessageStrings getGlobalMessageStrings() {
        return globalMessageStrings;
    }

    /**
     * A dictionary, each of whose keys is a resource identifier and each of whose values is a multiformatMessageString object, which holds message strings in plain text and (optionally) Markdown format. The strings can include placeholders, which can be used to construct a message in combination with an arbitrary number of additional string arguments.
     */
    public void setGlobalMessageStrings(GlobalMessageStrings globalMessageStrings) {
        this.globalMessageStrings = globalMessageStrings;
    }

    public ToolComponent withGlobalMessageStrings(GlobalMessageStrings globalMessageStrings) {
        this.globalMessageStrings = globalMessageStrings;
        return this;
    }

    /**
     * An array of reportingDescriptor objects relevant to the notifications related to the configuration and runtime execution of the tool component.
     */
    public Set<ReportingDescriptor> getNotifications() {
        return notifications;
    }

    /**
     * An array of reportingDescriptor objects relevant to the notifications related to the configuration and runtime execution of the tool component.
     */
    public void setNotifications(Set<ReportingDescriptor> notifications) {
        this.notifications = notifications;
    }

    public ToolComponent withNotifications(Set<ReportingDescriptor> notifications) {
        this.notifications = notifications;
        return this;
    }

    /**
     * An array of reportingDescriptor objects relevant to the analysis performed by the tool component.
     */
    public Set<ReportingDescriptor> getRules() {
        return rules;
    }

    /**
     * An array of reportingDescriptor objects relevant to the analysis performed by the tool component.
     */
    public void setRules(Set<ReportingDescriptor> rules) {
        this.rules = rules;
    }

    public ToolComponent withRules(Set<ReportingDescriptor> rules) {
        this.rules = rules;
        return this;
    }

    /**
     * An array of reportingDescriptor objects relevant to the definitions of both standalone and tool-defined taxonomies.
     */
    public Set<ReportingDescriptor> getTaxa() {
        return taxa;
    }

    /**
     * An array of reportingDescriptor objects relevant to the definitions of both standalone and tool-defined taxonomies.
     */
    public void setTaxa(Set<ReportingDescriptor> taxa) {
        this.taxa = taxa;
    }

    public ToolComponent withTaxa(Set<ReportingDescriptor> taxa) {
        this.taxa = taxa;
        return this;
    }

    /**
     * An array of the artifactLocation objects associated with the tool component.
     */
    public List<ArtifactLocation> getLocations() {
        return locations;
    }

    /**
     * An array of the artifactLocation objects associated with the tool component.
     */
    public void setLocations(List<ArtifactLocation> locations) {
        this.locations = locations;
    }

    public ToolComponent withLocations(List<ArtifactLocation> locations) {
        this.locations = locations;
        return this;
    }

    /**
     * The language of the messages emitted into the log file during this run (expressed as an ISO 639-1 two-letter lowercase language code) and an optional region (expressed as an ISO 3166-1 two-letter uppercase subculture code associated with a country or region). The casing is recommended but not required (in order for this data to conform to RFC5646).
     */
    public String getLanguage() {
        return language;
    }

    /**
     * The language of the messages emitted into the log file during this run (expressed as an ISO 639-1 two-letter lowercase language code) and an optional region (expressed as an ISO 3166-1 two-letter uppercase subculture code associated with a country or region). The casing is recommended but not required (in order for this data to conform to RFC5646).
     */
    public void setLanguage(String language) {
        this.language = language;
    }

    public ToolComponent withLanguage(String language) {
        this.language = language;
        return this;
    }

    /**
     * The kinds of data contained in this object.
     */
    public Set<Object> getContents() {
        return contents;
    }

    /**
     * The kinds of data contained in this object.
     */
    public void setContents(Set<Object> contents) {
        this.contents = contents;
    }

    public ToolComponent withContents(Set<Object> contents) {
        this.contents = contents;
        return this;
    }

    /**
     * Specifies whether this object contains a complete definition of the localizable and/or non-localizable data for this component, as opposed to including only data that is relevant to the results persisted to this log file.
     */
    public boolean isIsComprehensive() {
        return isComprehensive;
    }

    /**
     * Specifies whether this object contains a complete definition of the localizable and/or non-localizable data for this component, as opposed to including only data that is relevant to the results persisted to this log file.
     */
    public void setIsComprehensive(boolean isComprehensive) {
        this.isComprehensive = isComprehensive;
    }

    public ToolComponent withIsComprehensive(boolean isComprehensive) {
        this.isComprehensive = isComprehensive;
        return this;
    }

    /**
     * The semantic version of the localized strings defined in this component; maintained by components that provide translations.
     */
    public String getLocalizedDataSemanticVersion() {
        return localizedDataSemanticVersion;
    }

    /**
     * The semantic version of the localized strings defined in this component; maintained by components that provide translations.
     */
    public void setLocalizedDataSemanticVersion(String localizedDataSemanticVersion) {
        this.localizedDataSemanticVersion = localizedDataSemanticVersion;
    }

    public ToolComponent withLocalizedDataSemanticVersion(String localizedDataSemanticVersion) {
        this.localizedDataSemanticVersion = localizedDataSemanticVersion;
        return this;
    }

    /**
     * The minimum value of localizedDataSemanticVersion required in translations consumed by this component; used by components that consume translations.
     */
    public String getMinimumRequiredLocalizedDataSemanticVersion() {
        return minimumRequiredLocalizedDataSemanticVersion;
    }

    /**
     * The minimum value of localizedDataSemanticVersion required in translations consumed by this component; used by components that consume translations.
     */
    public void setMinimumRequiredLocalizedDataSemanticVersion(String minimumRequiredLocalizedDataSemanticVersion) {
        this.minimumRequiredLocalizedDataSemanticVersion = minimumRequiredLocalizedDataSemanticVersion;
    }

    public ToolComponent withMinimumRequiredLocalizedDataSemanticVersion(String minimumRequiredLocalizedDataSemanticVersion) {
        this.minimumRequiredLocalizedDataSemanticVersion = minimumRequiredLocalizedDataSemanticVersion;
        return this;
    }

    /**
     * Identifies a particular toolComponent object, either the driver or an extension.
     */
    public ToolComponentReference getAssociatedComponent() {
        return associatedComponent;
    }

    /**
     * Identifies a particular toolComponent object, either the driver or an extension.
     */
    public void setAssociatedComponent(ToolComponentReference associatedComponent) {
        this.associatedComponent = associatedComponent;
    }

    public ToolComponent withAssociatedComponent(ToolComponentReference associatedComponent) {
        this.associatedComponent = associatedComponent;
        return this;
    }

    /**
     * Provides additional metadata related to translation.
     */
    public TranslationMetadata getTranslationMetadata() {
        return translationMetadata;
    }

    /**
     * Provides additional metadata related to translation.
     */
    public void setTranslationMetadata(TranslationMetadata translationMetadata) {
        this.translationMetadata = translationMetadata;
    }

    public ToolComponent withTranslationMetadata(TranslationMetadata translationMetadata) {
        this.translationMetadata = translationMetadata;
        return this;
    }

    /**
     * An array of toolComponentReference objects to declare the taxonomies supported by the tool component.
     */
    public Set<ToolComponentReference> getSupportedTaxonomies() {
        return supportedTaxonomies;
    }

    /**
     * An array of toolComponentReference objects to declare the taxonomies supported by the tool component.
     */
    public void setSupportedTaxonomies(Set<ToolComponentReference> supportedTaxonomies) {
        this.supportedTaxonomies = supportedTaxonomies;
    }

    public ToolComponent withSupportedTaxonomies(Set<ToolComponentReference> supportedTaxonomies) {
        this.supportedTaxonomies = supportedTaxonomies;
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

    public ToolComponent withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(ToolComponent.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("guid");
        sb.append('=');
        sb.append(((this.guid == null) ? "<null>" : this.guid));
        sb.append(',');
        sb.append("name");
        sb.append('=');
        sb.append(((this.name == null) ? "<null>" : this.name));
        sb.append(',');
        sb.append("organization");
        sb.append('=');
        sb.append(((this.organization == null) ? "<null>" : this.organization));
        sb.append(',');
        sb.append("product");
        sb.append('=');
        sb.append(((this.product == null) ? "<null>" : this.product));
        sb.append(',');
        sb.append("productSuite");
        sb.append('=');
        sb.append(((this.productSuite == null) ? "<null>" : this.productSuite));
        sb.append(',');
        sb.append("shortDescription");
        sb.append('=');
        sb.append(((this.shortDescription == null) ? "<null>" : this.shortDescription));
        sb.append(',');
        sb.append("fullDescription");
        sb.append('=');
        sb.append(((this.fullDescription == null) ? "<null>" : this.fullDescription));
        sb.append(',');
        sb.append("fullName");
        sb.append('=');
        sb.append(((this.fullName == null) ? "<null>" : this.fullName));
        sb.append(',');
        sb.append("version");
        sb.append('=');
        sb.append(((this.version == null) ? "<null>" : this.version));
        sb.append(',');
        sb.append("semanticVersion");
        sb.append('=');
        sb.append(((this.semanticVersion == null) ? "<null>" : this.semanticVersion));
        sb.append(',');
        sb.append("dottedQuadFileVersion");
        sb.append('=');
        sb.append(((this.dottedQuadFileVersion == null) ? "<null>" : this.dottedQuadFileVersion));
        sb.append(',');
        sb.append("releaseDateUtc");
        sb.append('=');
        sb.append(((this.releaseDateUtc == null) ? "<null>" : this.releaseDateUtc));
        sb.append(',');
        sb.append("downloadUri");
        sb.append('=');
        sb.append(((this.downloadUri == null) ? "<null>" : this.downloadUri));
        sb.append(',');
        sb.append("informationUri");
        sb.append('=');
        sb.append(((this.informationUri == null) ? "<null>" : this.informationUri));
        sb.append(',');
        sb.append("globalMessageStrings");
        sb.append('=');
        sb.append(((this.globalMessageStrings == null) ? "<null>" : this.globalMessageStrings));
        sb.append(',');
        sb.append("notifications");
        sb.append('=');
        sb.append(((this.notifications == null) ? "<null>" : this.notifications));
        sb.append(',');
        sb.append("rules");
        sb.append('=');
        sb.append(((this.rules == null) ? "<null>" : this.rules));
        sb.append(',');
        sb.append("taxa");
        sb.append('=');
        sb.append(((this.taxa == null) ? "<null>" : this.taxa));
        sb.append(',');
        sb.append("locations");
        sb.append('=');
        sb.append(((this.locations == null) ? "<null>" : this.locations));
        sb.append(',');
        sb.append("language");
        sb.append('=');
        sb.append(((this.language == null) ? "<null>" : this.language));
        sb.append(',');
        sb.append("contents");
        sb.append('=');
        sb.append(((this.contents == null) ? "<null>" : this.contents));
        sb.append(',');
        sb.append("isComprehensive");
        sb.append('=');
        sb.append(this.isComprehensive);
        sb.append(',');
        sb.append("localizedDataSemanticVersion");
        sb.append('=');
        sb.append(((this.localizedDataSemanticVersion == null) ? "<null>" : this.localizedDataSemanticVersion));
        sb.append(',');
        sb.append("minimumRequiredLocalizedDataSemanticVersion");
        sb.append('=');
        sb.append(((this.minimumRequiredLocalizedDataSemanticVersion == null) ? "<null>" : this.minimumRequiredLocalizedDataSemanticVersion));
        sb.append(',');
        sb.append("associatedComponent");
        sb.append('=');
        sb.append(((this.associatedComponent == null) ? "<null>" : this.associatedComponent));
        sb.append(',');
        sb.append("translationMetadata");
        sb.append('=');
        sb.append(((this.translationMetadata == null) ? "<null>" : this.translationMetadata));
        sb.append(',');
        sb.append("supportedTaxonomies");
        sb.append('=');
        sb.append(((this.supportedTaxonomies == null) ? "<null>" : this.supportedTaxonomies));
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
        result = ((result * 31) + ((this.releaseDateUtc == null) ? 0 : this.releaseDateUtc.hashCode()));
        result = ((result * 31) + ((this.rules == null) ? 0 : this.rules.hashCode()));
        result = ((result * 31) + ((this.language == null) ? 0 : this.language.hashCode()));
        result = ((result * 31) + ((this.downloadUri == null) ? 0 : this.downloadUri.hashCode()));
        result = ((result * 31) + ((this.supportedTaxonomies == null) ? 0 : this.supportedTaxonomies.hashCode()));
        result = ((result * 31) + ((this.fullDescription == null) ? 0 : this.fullDescription.hashCode()));
        result = ((result * 31) + ((this.informationUri == null) ? 0 : this.informationUri.hashCode()));
        result = ((result * 31) + ((this.associatedComponent == null) ? 0 : this.associatedComponent.hashCode()));
        result = ((result * 31) + ((this.translationMetadata == null) ? 0 : this.translationMetadata.hashCode()));
        result = ((result * 31) + ((this.productSuite == null) ? 0 : this.productSuite.hashCode()));
        result = ((result * 31) + ((this.taxa == null) ? 0 : this.taxa.hashCode()));
        result = ((result * 31) + ((this.product == null) ? 0 : this.product.hashCode()));
        result = ((result * 31) + (this.isComprehensive ? 1 : 0));
        result = ((result * 31) + ((this.minimumRequiredLocalizedDataSemanticVersion == null) ? 0 : this.minimumRequiredLocalizedDataSemanticVersion.hashCode()));
        result = ((result * 31) + ((this.fullName == null) ? 0 : this.fullName.hashCode()));
        result = ((result * 31) + ((this.shortDescription == null) ? 0 : this.shortDescription.hashCode()));
        result = ((result * 31) + ((this.version == null) ? 0 : this.version.hashCode()));
        result = ((result * 31) + ((this.globalMessageStrings == null) ? 0 : this.globalMessageStrings.hashCode()));
        result = ((result * 31) + ((this.localizedDataSemanticVersion == null) ? 0 : this.localizedDataSemanticVersion.hashCode()));
        result = ((result * 31) + ((this.dottedQuadFileVersion == null) ? 0 : this.dottedQuadFileVersion.hashCode()));
        result = ((result * 31) + ((this.contents == null) ? 0 : this.contents.hashCode()));
        result = ((result * 31) + ((this.organization == null) ? 0 : this.organization.hashCode()));
        result = ((result * 31) + ((this.name == null) ? 0 : this.name.hashCode()));
        result = ((result * 31) + ((this.semanticVersion == null) ? 0 : this.semanticVersion.hashCode()));
        result = ((result * 31) + ((this.guid == null) ? 0 : this.guid.hashCode()));
        result = ((result * 31) + ((this.locations == null) ? 0 : this.locations.hashCode()));
        result = ((result * 31) + ((this.notifications == null) ? 0 : this.notifications.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof ToolComponent) == false) {
            return false;
        }
        ToolComponent rhs = ((ToolComponent) other);
        return (((((((((((((((((((((((((((((this.releaseDateUtc == rhs.releaseDateUtc) || ((this.releaseDateUtc != null) && this.releaseDateUtc.equals(rhs.releaseDateUtc))) && ((this.rules == rhs.rules) || ((this.rules != null) && this.rules.equals(rhs.rules)))) && ((this.language == rhs.language) || ((this.language != null) && this.language.equals(rhs.language)))) && ((this.downloadUri == rhs.downloadUri) || ((this.downloadUri != null) && this.downloadUri.equals(rhs.downloadUri)))) && ((this.supportedTaxonomies == rhs.supportedTaxonomies) || ((this.supportedTaxonomies != null) && this.supportedTaxonomies.equals(rhs.supportedTaxonomies)))) && ((this.fullDescription == rhs.fullDescription) || ((this.fullDescription != null) && this.fullDescription.equals(rhs.fullDescription)))) && ((this.informationUri == rhs.informationUri) || ((this.informationUri != null) && this.informationUri.equals(rhs.informationUri)))) && ((this.associatedComponent == rhs.associatedComponent) || ((this.associatedComponent != null) && this.associatedComponent.equals(rhs.associatedComponent)))) && ((this.translationMetadata == rhs.translationMetadata) || ((this.translationMetadata != null) && this.translationMetadata.equals(rhs.translationMetadata)))) && ((this.productSuite == rhs.productSuite) || ((this.productSuite != null) && this.productSuite.equals(rhs.productSuite)))) && ((this.taxa == rhs.taxa) || ((this.taxa != null) && this.taxa.equals(rhs.taxa)))) && ((this.product == rhs.product) || ((this.product != null) && this.product.equals(rhs.product)))) && (this.isComprehensive == rhs.isComprehensive)) && ((this.minimumRequiredLocalizedDataSemanticVersion == rhs.minimumRequiredLocalizedDataSemanticVersion) || ((this.minimumRequiredLocalizedDataSemanticVersion != null) && this.minimumRequiredLocalizedDataSemanticVersion.equals(rhs.minimumRequiredLocalizedDataSemanticVersion)))) && ((this.fullName == rhs.fullName) || ((this.fullName != null) && this.fullName.equals(rhs.fullName)))) && ((this.shortDescription == rhs.shortDescription) || ((this.shortDescription != null) && this.shortDescription.equals(rhs.shortDescription)))) && ((this.version == rhs.version) || ((this.version != null) && this.version.equals(rhs.version)))) && ((this.globalMessageStrings == rhs.globalMessageStrings) || ((this.globalMessageStrings != null) && this.globalMessageStrings.equals(rhs.globalMessageStrings)))) && ((this.localizedDataSemanticVersion == rhs.localizedDataSemanticVersion) || ((this.localizedDataSemanticVersion != null) && this.localizedDataSemanticVersion.equals(rhs.localizedDataSemanticVersion)))) && ((this.dottedQuadFileVersion == rhs.dottedQuadFileVersion) || ((this.dottedQuadFileVersion != null) && this.dottedQuadFileVersion.equals(rhs.dottedQuadFileVersion)))) && ((this.contents == rhs.contents) || ((this.contents != null) && this.contents.equals(rhs.contents)))) && ((this.organization == rhs.organization) || ((this.organization != null) && this.organization.equals(rhs.organization)))) && ((this.name == rhs.name) || ((this.name != null) && this.name.equals(rhs.name)))) && ((this.semanticVersion == rhs.semanticVersion) || ((this.semanticVersion != null) && this.semanticVersion.equals(rhs.semanticVersion)))) && ((this.guid == rhs.guid) || ((this.guid != null) && this.guid.equals(rhs.guid)))) && ((this.locations == rhs.locations) || ((this.locations != null) && this.locations.equals(rhs.locations)))) && ((this.notifications == rhs.notifications) || ((this.notifications != null) && this.notifications.equals(rhs.notifications)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }

}
