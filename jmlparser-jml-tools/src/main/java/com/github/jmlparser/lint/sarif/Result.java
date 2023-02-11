
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
 * A result produced by an analysis tool.
 */
@Generated("jsonschema2pojo")
public class Result {

    /**
     * The stable, unique identifier of the rule, if any, to which this notification is relevant. This member can be used to retrieve rule metadata from the rules dictionary, if it exists.
     */
    @SerializedName("ruleId")
    @Expose
    private String ruleId;
    /**
     * The index within the tool component rules array of the rule object associated with this result.
     */
    @SerializedName("ruleIndex")
    @Expose
    private int ruleIndex = -1;
    /**
     * Information about how to locate a relevant reporting descriptor.
     */
    @SerializedName("rule")
    @Expose
    private ReportingDescriptorReference rule;
    /**
     * A value that categorizes results by evaluation state.
     */
    @SerializedName("kind")
    @Expose
    private Object kind = null;
    /**
     * A value specifying the severity level of the result.
     */
    @SerializedName("level")
    @Expose
    private Object level = null;
    /**
     * Encapsulates a message intended to be read by the end user.
     * (Required)
     */
    @SerializedName("message")
    @Expose
    private Message message;
    /**
     * Specifies the location of an artifact.
     */
    @SerializedName("analysisTarget")
    @Expose
    private ArtifactLocation analysisTarget;
    /**
     * The set of locations where the result was detected. Specify only one location unless the problem indicated by the result can only be corrected by making a change at every specified location.
     */
    @SerializedName("locations")
    @Expose
    private List<Location> locations = new ArrayList<Location>();
    /**
     * A stable, unique identifer for the result in the form of a GUID.
     */
    @SerializedName("guid")
    @Expose
    private String guid;
    /**
     * A stable, unique identifier for the equivalence class of logically identical results to which this result belongs, in the form of a GUID.
     */
    @SerializedName("correlationGuid")
    @Expose
    private String correlationGuid;
    /**
     * A positive integer specifying the number of times this logically unique result was observed in this run.
     */
    @SerializedName("occurrenceCount")
    @Expose
    private int occurrenceCount;
    /**
     * A set of strings that contribute to the stable, unique identity of the result.
     */
    @SerializedName("partialFingerprints")
    @Expose
    private PartialFingerprints partialFingerprints;
    /**
     * A set of strings each of which individually defines a stable, unique identity for the result.
     */
    @SerializedName("fingerprints")
    @Expose
    private Fingerprints fingerprints;
    /**
     * An array of 'stack' objects relevant to the result.
     */
    @SerializedName("stacks")
    @Expose
    private Set<Stack> stacks = new LinkedHashSet<Stack>();
    /**
     * An array of 'codeFlow' objects relevant to the result.
     */
    @SerializedName("codeFlows")
    @Expose
    private List<CodeFlow> codeFlows = new ArrayList<CodeFlow>();
    /**
     * An array of zero or more unique graph objects associated with the result.
     */
    @SerializedName("graphs")
    @Expose
    private Set<Graph> graphs = new LinkedHashSet<Graph>();
    /**
     * An array of one or more unique 'graphTraversal' objects.
     */
    @SerializedName("graphTraversals")
    @Expose
    private Set<GraphTraversal> graphTraversals = new LinkedHashSet<GraphTraversal>();
    /**
     * A set of locations relevant to this result.
     */
    @SerializedName("relatedLocations")
    @Expose
    private Set<Location> relatedLocations = new LinkedHashSet<Location>();
    /**
     * A set of suppressions relevant to this result.
     */
    @SerializedName("suppressions")
    @Expose
    private Set<Suppression> suppressions = new LinkedHashSet<Suppression>();
    /**
     * The state of a result relative to a baseline of a previous run.
     */
    @SerializedName("baselineState")
    @Expose
    private Result.BaselineState baselineState;
    /**
     * A number representing the priority or importance of the result.
     */
    @SerializedName("rank")
    @Expose
    private double rank = -1.0D;
    /**
     * A set of artifacts relevant to the result.
     */
    @SerializedName("attachments")
    @Expose
    private Set<Attachment> attachments = new LinkedHashSet<Attachment>();
    /**
     * An absolute URI at which the result can be viewed.
     */
    @SerializedName("hostedViewerUri")
    @Expose
    private URI hostedViewerUri;
    /**
     * The URIs of the work items associated with this result.
     */
    @SerializedName("workItemUris")
    @Expose
    private Set<URI> workItemUris = new LinkedHashSet<URI>();
    /**
     * Contains information about how and when a result was detected.
     */
    @SerializedName("provenance")
    @Expose
    private ResultProvenance provenance;
    /**
     * An array of 'fix' objects, each of which represents a proposed fix to the problem indicated by the result.
     */
    @SerializedName("fixes")
    @Expose
    private Set<Fix> fixes = new LinkedHashSet<Fix>();
    /**
     * An array of references to taxonomy reporting descriptors that are applicable to the result.
     */
    @SerializedName("taxa")
    @Expose
    private Set<ReportingDescriptorReference> taxa = new LinkedHashSet<ReportingDescriptorReference>();
    /**
     * Describes an HTTP request.
     */
    @SerializedName("webRequest")
    @Expose
    private WebRequest webRequest;
    /**
     * Describes the response to an HTTP request.
     */
    @SerializedName("webResponse")
    @Expose
    private WebResponse webResponse;
    /**
     * Key/value pairs that provide additional information about the object.
     */
    @SerializedName("properties")
    @Expose
    private PropertyBag properties;

    /**
     * No args constructor for use in serialization
     */
    public Result() {
    }

    /**
     * @param attachments
     * @param correlationGuid
     * @param webRequest
     * @param graphTraversals
     * @param rule
     * @param analysisTarget
     * @param fixes
     * @param relatedLocations
     * @param graphs
     * @param provenance
     * @param rank
     * @param ruleId
     * @param taxa
     * @param ruleIndex
     * @param suppressions
     * @param level
     * @param hostedViewerUri
     * @param kind
     * @param stacks
     * @param occurrenceCount
     * @param message
     * @param fingerprints
     * @param codeFlows
     * @param guid
     * @param partialFingerprints
     * @param webResponse
     * @param locations
     * @param baselineState
     * @param workItemUris
     * @param properties
     */
    public Result(String ruleId, int ruleIndex, ReportingDescriptorReference rule, Object kind, Object level, Message message, ArtifactLocation analysisTarget, List<Location> locations, String guid, String correlationGuid, int occurrenceCount, PartialFingerprints partialFingerprints, Fingerprints fingerprints, Set<Stack> stacks, List<CodeFlow> codeFlows, Set<Graph> graphs, Set<GraphTraversal> graphTraversals, Set<Location> relatedLocations, Set<Suppression> suppressions, Result.BaselineState baselineState, double rank, Set<Attachment> attachments, URI hostedViewerUri, Set<URI> workItemUris, ResultProvenance provenance, Set<Fix> fixes, Set<ReportingDescriptorReference> taxa, WebRequest webRequest, WebResponse webResponse, PropertyBag properties) {
        super();
        this.ruleId = ruleId;
        this.ruleIndex = ruleIndex;
        this.rule = rule;
        this.kind = kind;
        this.level = level;
        this.message = message;
        this.analysisTarget = analysisTarget;
        this.locations = locations;
        this.guid = guid;
        this.correlationGuid = correlationGuid;
        this.occurrenceCount = occurrenceCount;
        this.partialFingerprints = partialFingerprints;
        this.fingerprints = fingerprints;
        this.stacks = stacks;
        this.codeFlows = codeFlows;
        this.graphs = graphs;
        this.graphTraversals = graphTraversals;
        this.relatedLocations = relatedLocations;
        this.suppressions = suppressions;
        this.baselineState = baselineState;
        this.rank = rank;
        this.attachments = attachments;
        this.hostedViewerUri = hostedViewerUri;
        this.workItemUris = workItemUris;
        this.provenance = provenance;
        this.fixes = fixes;
        this.taxa = taxa;
        this.webRequest = webRequest;
        this.webResponse = webResponse;
        this.properties = properties;
    }

    /**
     * The stable, unique identifier of the rule, if any, to which this notification is relevant. This member can be used to retrieve rule metadata from the rules dictionary, if it exists.
     */
    public String getRuleId() {
        return ruleId;
    }

    /**
     * The stable, unique identifier of the rule, if any, to which this notification is relevant. This member can be used to retrieve rule metadata from the rules dictionary, if it exists.
     */
    public void setRuleId(String ruleId) {
        this.ruleId = ruleId;
    }

    public Result withRuleId(String ruleId) {
        this.ruleId = ruleId;
        return this;
    }

    /**
     * The index within the tool component rules array of the rule object associated with this result.
     */
    public int getRuleIndex() {
        return ruleIndex;
    }

    /**
     * The index within the tool component rules array of the rule object associated with this result.
     */
    public void setRuleIndex(int ruleIndex) {
        this.ruleIndex = ruleIndex;
    }

    public Result withRuleIndex(int ruleIndex) {
        this.ruleIndex = ruleIndex;
        return this;
    }

    /**
     * Information about how to locate a relevant reporting descriptor.
     */
    public ReportingDescriptorReference getRule() {
        return rule;
    }

    /**
     * Information about how to locate a relevant reporting descriptor.
     */
    public void setRule(ReportingDescriptorReference rule) {
        this.rule = rule;
    }

    public Result withRule(ReportingDescriptorReference rule) {
        this.rule = rule;
        return this;
    }

    /**
     * A value that categorizes results by evaluation state.
     */
    public Object getKind() {
        return kind;
    }

    /**
     * A value that categorizes results by evaluation state.
     */
    public void setKind(Object kind) {
        this.kind = kind;
    }

    public Result withKind(Object kind) {
        this.kind = kind;
        return this;
    }

    /**
     * A value specifying the severity level of the result.
     */
    public Object getLevel() {
        return level;
    }

    /**
     * A value specifying the severity level of the result.
     */
    public void setLevel(Object level) {
        this.level = level;
    }

    public Result withLevel(Object level) {
        this.level = level;
        return this;
    }

    /**
     * Encapsulates a message intended to be read by the end user.
     * (Required)
     */
    public Message getMessage() {
        return message;
    }

    /**
     * Encapsulates a message intended to be read by the end user.
     * (Required)
     */
    public void setMessage(Message message) {
        this.message = message;
    }

    public Result withMessage(Message message) {
        this.message = message;
        return this;
    }

    /**
     * Specifies the location of an artifact.
     */
    public ArtifactLocation getAnalysisTarget() {
        return analysisTarget;
    }

    /**
     * Specifies the location of an artifact.
     */
    public void setAnalysisTarget(ArtifactLocation analysisTarget) {
        this.analysisTarget = analysisTarget;
    }

    public Result withAnalysisTarget(ArtifactLocation analysisTarget) {
        this.analysisTarget = analysisTarget;
        return this;
    }

    /**
     * The set of locations where the result was detected. Specify only one location unless the problem indicated by the result can only be corrected by making a change at every specified location.
     */
    public List<Location> getLocations() {
        return locations;
    }

    /**
     * The set of locations where the result was detected. Specify only one location unless the problem indicated by the result can only be corrected by making a change at every specified location.
     */
    public void setLocations(List<Location> locations) {
        this.locations = locations;
    }

    public Result withLocations(List<Location> locations) {
        this.locations = locations;
        return this;
    }

    /**
     * A stable, unique identifer for the result in the form of a GUID.
     */
    public String getGuid() {
        return guid;
    }

    /**
     * A stable, unique identifer for the result in the form of a GUID.
     */
    public void setGuid(String guid) {
        this.guid = guid;
    }

    public Result withGuid(String guid) {
        this.guid = guid;
        return this;
    }

    /**
     * A stable, unique identifier for the equivalence class of logically identical results to which this result belongs, in the form of a GUID.
     */
    public String getCorrelationGuid() {
        return correlationGuid;
    }

    /**
     * A stable, unique identifier for the equivalence class of logically identical results to which this result belongs, in the form of a GUID.
     */
    public void setCorrelationGuid(String correlationGuid) {
        this.correlationGuid = correlationGuid;
    }

    public Result withCorrelationGuid(String correlationGuid) {
        this.correlationGuid = correlationGuid;
        return this;
    }

    /**
     * A positive integer specifying the number of times this logically unique result was observed in this run.
     */
    public int getOccurrenceCount() {
        return occurrenceCount;
    }

    /**
     * A positive integer specifying the number of times this logically unique result was observed in this run.
     */
    public void setOccurrenceCount(int occurrenceCount) {
        this.occurrenceCount = occurrenceCount;
    }

    public Result withOccurrenceCount(int occurrenceCount) {
        this.occurrenceCount = occurrenceCount;
        return this;
    }

    /**
     * A set of strings that contribute to the stable, unique identity of the result.
     */
    public PartialFingerprints getPartialFingerprints() {
        return partialFingerprints;
    }

    /**
     * A set of strings that contribute to the stable, unique identity of the result.
     */
    public void setPartialFingerprints(PartialFingerprints partialFingerprints) {
        this.partialFingerprints = partialFingerprints;
    }

    public Result withPartialFingerprints(PartialFingerprints partialFingerprints) {
        this.partialFingerprints = partialFingerprints;
        return this;
    }

    /**
     * A set of strings each of which individually defines a stable, unique identity for the result.
     */
    public Fingerprints getFingerprints() {
        return fingerprints;
    }

    /**
     * A set of strings each of which individually defines a stable, unique identity for the result.
     */
    public void setFingerprints(Fingerprints fingerprints) {
        this.fingerprints = fingerprints;
    }

    public Result withFingerprints(Fingerprints fingerprints) {
        this.fingerprints = fingerprints;
        return this;
    }

    /**
     * An array of 'stack' objects relevant to the result.
     */
    public Set<Stack> getStacks() {
        return stacks;
    }

    /**
     * An array of 'stack' objects relevant to the result.
     */
    public void setStacks(Set<Stack> stacks) {
        this.stacks = stacks;
    }

    public Result withStacks(Set<Stack> stacks) {
        this.stacks = stacks;
        return this;
    }

    /**
     * An array of 'codeFlow' objects relevant to the result.
     */
    public List<CodeFlow> getCodeFlows() {
        return codeFlows;
    }

    /**
     * An array of 'codeFlow' objects relevant to the result.
     */
    public void setCodeFlows(List<CodeFlow> codeFlows) {
        this.codeFlows = codeFlows;
    }

    public Result withCodeFlows(List<CodeFlow> codeFlows) {
        this.codeFlows = codeFlows;
        return this;
    }

    /**
     * An array of zero or more unique graph objects associated with the result.
     */
    public Set<Graph> getGraphs() {
        return graphs;
    }

    /**
     * An array of zero or more unique graph objects associated with the result.
     */
    public void setGraphs(Set<Graph> graphs) {
        this.graphs = graphs;
    }

    public Result withGraphs(Set<Graph> graphs) {
        this.graphs = graphs;
        return this;
    }

    /**
     * An array of one or more unique 'graphTraversal' objects.
     */
    public Set<GraphTraversal> getGraphTraversals() {
        return graphTraversals;
    }

    /**
     * An array of one or more unique 'graphTraversal' objects.
     */
    public void setGraphTraversals(Set<GraphTraversal> graphTraversals) {
        this.graphTraversals = graphTraversals;
    }

    public Result withGraphTraversals(Set<GraphTraversal> graphTraversals) {
        this.graphTraversals = graphTraversals;
        return this;
    }

    /**
     * A set of locations relevant to this result.
     */
    public Set<Location> getRelatedLocations() {
        return relatedLocations;
    }

    /**
     * A set of locations relevant to this result.
     */
    public void setRelatedLocations(Set<Location> relatedLocations) {
        this.relatedLocations = relatedLocations;
    }

    public Result withRelatedLocations(Set<Location> relatedLocations) {
        this.relatedLocations = relatedLocations;
        return this;
    }

    /**
     * A set of suppressions relevant to this result.
     */
    public Set<Suppression> getSuppressions() {
        return suppressions;
    }

    /**
     * A set of suppressions relevant to this result.
     */
    public void setSuppressions(Set<Suppression> suppressions) {
        this.suppressions = suppressions;
    }

    public Result withSuppressions(Set<Suppression> suppressions) {
        this.suppressions = suppressions;
        return this;
    }

    /**
     * The state of a result relative to a baseline of a previous run.
     */
    public Result.BaselineState getBaselineState() {
        return baselineState;
    }

    /**
     * The state of a result relative to a baseline of a previous run.
     */
    public void setBaselineState(Result.BaselineState baselineState) {
        this.baselineState = baselineState;
    }

    public Result withBaselineState(Result.BaselineState baselineState) {
        this.baselineState = baselineState;
        return this;
    }

    /**
     * A number representing the priority or importance of the result.
     */
    public double getRank() {
        return rank;
    }

    /**
     * A number representing the priority or importance of the result.
     */
    public void setRank(double rank) {
        this.rank = rank;
    }

    public Result withRank(double rank) {
        this.rank = rank;
        return this;
    }

    /**
     * A set of artifacts relevant to the result.
     */
    public Set<Attachment> getAttachments() {
        return attachments;
    }

    /**
     * A set of artifacts relevant to the result.
     */
    public void setAttachments(Set<Attachment> attachments) {
        this.attachments = attachments;
    }

    public Result withAttachments(Set<Attachment> attachments) {
        this.attachments = attachments;
        return this;
    }

    /**
     * An absolute URI at which the result can be viewed.
     */
    public URI getHostedViewerUri() {
        return hostedViewerUri;
    }

    /**
     * An absolute URI at which the result can be viewed.
     */
    public void setHostedViewerUri(URI hostedViewerUri) {
        this.hostedViewerUri = hostedViewerUri;
    }

    public Result withHostedViewerUri(URI hostedViewerUri) {
        this.hostedViewerUri = hostedViewerUri;
        return this;
    }

    /**
     * The URIs of the work items associated with this result.
     */
    public Set<URI> getWorkItemUris() {
        return workItemUris;
    }

    /**
     * The URIs of the work items associated with this result.
     */
    public void setWorkItemUris(Set<URI> workItemUris) {
        this.workItemUris = workItemUris;
    }

    public Result withWorkItemUris(Set<URI> workItemUris) {
        this.workItemUris = workItemUris;
        return this;
    }

    /**
     * Contains information about how and when a result was detected.
     */
    public ResultProvenance getProvenance() {
        return provenance;
    }

    /**
     * Contains information about how and when a result was detected.
     */
    public void setProvenance(ResultProvenance provenance) {
        this.provenance = provenance;
    }

    public Result withProvenance(ResultProvenance provenance) {
        this.provenance = provenance;
        return this;
    }

    /**
     * An array of 'fix' objects, each of which represents a proposed fix to the problem indicated by the result.
     */
    public Set<Fix> getFixes() {
        return fixes;
    }

    /**
     * An array of 'fix' objects, each of which represents a proposed fix to the problem indicated by the result.
     */
    public void setFixes(Set<Fix> fixes) {
        this.fixes = fixes;
    }

    public Result withFixes(Set<Fix> fixes) {
        this.fixes = fixes;
        return this;
    }

    /**
     * An array of references to taxonomy reporting descriptors that are applicable to the result.
     */
    public Set<ReportingDescriptorReference> getTaxa() {
        return taxa;
    }

    /**
     * An array of references to taxonomy reporting descriptors that are applicable to the result.
     */
    public void setTaxa(Set<ReportingDescriptorReference> taxa) {
        this.taxa = taxa;
    }

    public Result withTaxa(Set<ReportingDescriptorReference> taxa) {
        this.taxa = taxa;
        return this;
    }

    /**
     * Describes an HTTP request.
     */
    public WebRequest getWebRequest() {
        return webRequest;
    }

    /**
     * Describes an HTTP request.
     */
    public void setWebRequest(WebRequest webRequest) {
        this.webRequest = webRequest;
    }

    public Result withWebRequest(WebRequest webRequest) {
        this.webRequest = webRequest;
        return this;
    }

    /**
     * Describes the response to an HTTP request.
     */
    public WebResponse getWebResponse() {
        return webResponse;
    }

    /**
     * Describes the response to an HTTP request.
     */
    public void setWebResponse(WebResponse webResponse) {
        this.webResponse = webResponse;
    }

    public Result withWebResponse(WebResponse webResponse) {
        this.webResponse = webResponse;
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

    public Result withProperties(PropertyBag properties) {
        this.properties = properties;
        return this;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Result.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
        sb.append("ruleId");
        sb.append('=');
        sb.append(((this.ruleId == null) ? "<null>" : this.ruleId));
        sb.append(',');
        sb.append("ruleIndex");
        sb.append('=');
        sb.append(this.ruleIndex);
        sb.append(',');
        sb.append("rule");
        sb.append('=');
        sb.append(((this.rule == null) ? "<null>" : this.rule));
        sb.append(',');
        sb.append("kind");
        sb.append('=');
        sb.append(((this.kind == null) ? "<null>" : this.kind));
        sb.append(',');
        sb.append("level");
        sb.append('=');
        sb.append(((this.level == null) ? "<null>" : this.level));
        sb.append(',');
        sb.append("message");
        sb.append('=');
        sb.append(((this.message == null) ? "<null>" : this.message));
        sb.append(',');
        sb.append("analysisTarget");
        sb.append('=');
        sb.append(((this.analysisTarget == null) ? "<null>" : this.analysisTarget));
        sb.append(',');
        sb.append("locations");
        sb.append('=');
        sb.append(((this.locations == null) ? "<null>" : this.locations));
        sb.append(',');
        sb.append("guid");
        sb.append('=');
        sb.append(((this.guid == null) ? "<null>" : this.guid));
        sb.append(',');
        sb.append("correlationGuid");
        sb.append('=');
        sb.append(((this.correlationGuid == null) ? "<null>" : this.correlationGuid));
        sb.append(',');
        sb.append("occurrenceCount");
        sb.append('=');
        sb.append(this.occurrenceCount);
        sb.append(',');
        sb.append("partialFingerprints");
        sb.append('=');
        sb.append(((this.partialFingerprints == null) ? "<null>" : this.partialFingerprints));
        sb.append(',');
        sb.append("fingerprints");
        sb.append('=');
        sb.append(((this.fingerprints == null) ? "<null>" : this.fingerprints));
        sb.append(',');
        sb.append("stacks");
        sb.append('=');
        sb.append(((this.stacks == null) ? "<null>" : this.stacks));
        sb.append(',');
        sb.append("codeFlows");
        sb.append('=');
        sb.append(((this.codeFlows == null) ? "<null>" : this.codeFlows));
        sb.append(',');
        sb.append("graphs");
        sb.append('=');
        sb.append(((this.graphs == null) ? "<null>" : this.graphs));
        sb.append(',');
        sb.append("graphTraversals");
        sb.append('=');
        sb.append(((this.graphTraversals == null) ? "<null>" : this.graphTraversals));
        sb.append(',');
        sb.append("relatedLocations");
        sb.append('=');
        sb.append(((this.relatedLocations == null) ? "<null>" : this.relatedLocations));
        sb.append(',');
        sb.append("suppressions");
        sb.append('=');
        sb.append(((this.suppressions == null) ? "<null>" : this.suppressions));
        sb.append(',');
        sb.append("baselineState");
        sb.append('=');
        sb.append(((this.baselineState == null) ? "<null>" : this.baselineState));
        sb.append(',');
        sb.append("rank");
        sb.append('=');
        sb.append(this.rank);
        sb.append(',');
        sb.append("attachments");
        sb.append('=');
        sb.append(((this.attachments == null) ? "<null>" : this.attachments));
        sb.append(',');
        sb.append("hostedViewerUri");
        sb.append('=');
        sb.append(((this.hostedViewerUri == null) ? "<null>" : this.hostedViewerUri));
        sb.append(',');
        sb.append("workItemUris");
        sb.append('=');
        sb.append(((this.workItemUris == null) ? "<null>" : this.workItemUris));
        sb.append(',');
        sb.append("provenance");
        sb.append('=');
        sb.append(((this.provenance == null) ? "<null>" : this.provenance));
        sb.append(',');
        sb.append("fixes");
        sb.append('=');
        sb.append(((this.fixes == null) ? "<null>" : this.fixes));
        sb.append(',');
        sb.append("taxa");
        sb.append('=');
        sb.append(((this.taxa == null) ? "<null>" : this.taxa));
        sb.append(',');
        sb.append("webRequest");
        sb.append('=');
        sb.append(((this.webRequest == null) ? "<null>" : this.webRequest));
        sb.append(',');
        sb.append("webResponse");
        sb.append('=');
        sb.append(((this.webResponse == null) ? "<null>" : this.webResponse));
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
        result = ((result * 31) + ((this.attachments == null) ? 0 : this.attachments.hashCode()));
        result = ((result * 31) + ((this.correlationGuid == null) ? 0 : this.correlationGuid.hashCode()));
        result = ((result * 31) + ((this.webRequest == null) ? 0 : this.webRequest.hashCode()));
        result = ((result * 31) + ((this.graphTraversals == null) ? 0 : this.graphTraversals.hashCode()));
        result = ((result * 31) + ((this.rule == null) ? 0 : this.rule.hashCode()));
        result = ((result * 31) + ((this.analysisTarget == null) ? 0 : this.analysisTarget.hashCode()));
        result = ((result * 31) + ((this.fixes == null) ? 0 : this.fixes.hashCode()));
        result = ((result * 31) + ((this.relatedLocations == null) ? 0 : this.relatedLocations.hashCode()));
        result = ((result * 31) + ((this.graphs == null) ? 0 : this.graphs.hashCode()));
        result = ((result * 31) + ((this.provenance == null) ? 0 : this.provenance.hashCode()));
        result = ((result * 31) + ((int) (Double.doubleToLongBits(this.rank) ^ (Double.doubleToLongBits(this.rank) >>> 32))));
        result = ((result * 31) + ((this.ruleId == null) ? 0 : this.ruleId.hashCode()));
        result = ((result * 31) + ((this.taxa == null) ? 0 : this.taxa.hashCode()));
        result = ((result * 31) + this.ruleIndex);
        result = ((result * 31) + ((this.suppressions == null) ? 0 : this.suppressions.hashCode()));
        result = ((result * 31) + ((this.level == null) ? 0 : this.level.hashCode()));
        result = ((result * 31) + ((this.hostedViewerUri == null) ? 0 : this.hostedViewerUri.hashCode()));
        result = ((result * 31) + ((this.kind == null) ? 0 : this.kind.hashCode()));
        result = ((result * 31) + ((this.stacks == null) ? 0 : this.stacks.hashCode()));
        result = ((result * 31) + this.occurrenceCount);
        result = ((result * 31) + ((this.message == null) ? 0 : this.message.hashCode()));
        result = ((result * 31) + ((this.fingerprints == null) ? 0 : this.fingerprints.hashCode()));
        result = ((result * 31) + ((this.codeFlows == null) ? 0 : this.codeFlows.hashCode()));
        result = ((result * 31) + ((this.guid == null) ? 0 : this.guid.hashCode()));
        result = ((result * 31) + ((this.partialFingerprints == null) ? 0 : this.partialFingerprints.hashCode()));
        result = ((result * 31) + ((this.webResponse == null) ? 0 : this.webResponse.hashCode()));
        result = ((result * 31) + ((this.locations == null) ? 0 : this.locations.hashCode()));
        result = ((result * 31) + ((this.baselineState == null) ? 0 : this.baselineState.hashCode()));
        result = ((result * 31) + ((this.workItemUris == null) ? 0 : this.workItemUris.hashCode()));
        result = ((result * 31) + ((this.properties == null) ? 0 : this.properties.hashCode()));
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof Result) == false) {
            return false;
        }
        Result rhs = ((Result) other);
        return (((((((((((((((((((((((((((((((this.attachments == rhs.attachments) || ((this.attachments != null) && this.attachments.equals(rhs.attachments))) && ((this.correlationGuid == rhs.correlationGuid) || ((this.correlationGuid != null) && this.correlationGuid.equals(rhs.correlationGuid)))) && ((this.webRequest == rhs.webRequest) || ((this.webRequest != null) && this.webRequest.equals(rhs.webRequest)))) && ((this.graphTraversals == rhs.graphTraversals) || ((this.graphTraversals != null) && this.graphTraversals.equals(rhs.graphTraversals)))) && ((this.rule == rhs.rule) || ((this.rule != null) && this.rule.equals(rhs.rule)))) && ((this.analysisTarget == rhs.analysisTarget) || ((this.analysisTarget != null) && this.analysisTarget.equals(rhs.analysisTarget)))) && ((this.fixes == rhs.fixes) || ((this.fixes != null) && this.fixes.equals(rhs.fixes)))) && ((this.relatedLocations == rhs.relatedLocations) || ((this.relatedLocations != null) && this.relatedLocations.equals(rhs.relatedLocations)))) && ((this.graphs == rhs.graphs) || ((this.graphs != null) && this.graphs.equals(rhs.graphs)))) && ((this.provenance == rhs.provenance) || ((this.provenance != null) && this.provenance.equals(rhs.provenance)))) && (Double.doubleToLongBits(this.rank) == Double.doubleToLongBits(rhs.rank))) && ((this.ruleId == rhs.ruleId) || ((this.ruleId != null) && this.ruleId.equals(rhs.ruleId)))) && ((this.taxa == rhs.taxa) || ((this.taxa != null) && this.taxa.equals(rhs.taxa)))) && (this.ruleIndex == rhs.ruleIndex)) && ((this.suppressions == rhs.suppressions) || ((this.suppressions != null) && this.suppressions.equals(rhs.suppressions)))) && ((this.level == rhs.level) || ((this.level != null) && this.level.equals(rhs.level)))) && ((this.hostedViewerUri == rhs.hostedViewerUri) || ((this.hostedViewerUri != null) && this.hostedViewerUri.equals(rhs.hostedViewerUri)))) && ((this.kind == rhs.kind) || ((this.kind != null) && this.kind.equals(rhs.kind)))) && ((this.stacks == rhs.stacks) || ((this.stacks != null) && this.stacks.equals(rhs.stacks)))) && (this.occurrenceCount == rhs.occurrenceCount)) && ((this.message == rhs.message) || ((this.message != null) && this.message.equals(rhs.message)))) && ((this.fingerprints == rhs.fingerprints) || ((this.fingerprints != null) && this.fingerprints.equals(rhs.fingerprints)))) && ((this.codeFlows == rhs.codeFlows) || ((this.codeFlows != null) && this.codeFlows.equals(rhs.codeFlows)))) && ((this.guid == rhs.guid) || ((this.guid != null) && this.guid.equals(rhs.guid)))) && ((this.partialFingerprints == rhs.partialFingerprints) || ((this.partialFingerprints != null) && this.partialFingerprints.equals(rhs.partialFingerprints)))) && ((this.webResponse == rhs.webResponse) || ((this.webResponse != null) && this.webResponse.equals(rhs.webResponse)))) && ((this.locations == rhs.locations) || ((this.locations != null) && this.locations.equals(rhs.locations)))) && ((this.baselineState == rhs.baselineState) || ((this.baselineState != null) && this.baselineState.equals(rhs.baselineState)))) && ((this.workItemUris == rhs.workItemUris) || ((this.workItemUris != null) && this.workItemUris.equals(rhs.workItemUris)))) && ((this.properties == rhs.properties) || ((this.properties != null) && this.properties.equals(rhs.properties))));
    }


    /**
     * The state of a result relative to a baseline of a previous run.
     */
    @Generated("jsonschema2pojo")
    public enum BaselineState {

        @SerializedName("new")
        NEW("new"),
        @SerializedName("unchanged")
        UNCHANGED("unchanged"),
        @SerializedName("updated")
        UPDATED("updated"),
        @SerializedName("absent")
        ABSENT("absent");
        private final String value;
        private final static Map<String, Result.BaselineState> CONSTANTS = new HashMap<String, Result.BaselineState>();

        static {
            for (Result.BaselineState c : values()) {
                CONSTANTS.put(c.value, c);
            }
        }

        BaselineState(String value) {
            this.value = value;
        }

        @Override
        public String toString() {
            return this.value;
        }

        public String value() {
            return this.value;
        }

        public static Result.BaselineState fromValue(String value) {
            Result.BaselineState constant = CONSTANTS.get(value);
            if (constant == null) {
                throw new IllegalArgumentException(value);
            } else {
                return constant;
            }
        }

    }

}
