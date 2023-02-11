
package com.github.jmlparser.lint.sarif;

import java.util.HashMap;
import java.util.Map;
import javax.annotation.processing.Generated;

import com.google.gson.annotations.SerializedName;

@Generated("jsonschema2pojo")
public enum Role {

    @SerializedName("analysisTarget")
    ANALYSIS_TARGET("analysisTarget"),
    @SerializedName("attachment")
    ATTACHMENT("attachment"),
    @SerializedName("responseFile")
    RESPONSE_FILE("responseFile"),
    @SerializedName("resultFile")
    RESULT_FILE("resultFile"),
    @SerializedName("standardStream")
    STANDARD_STREAM("standardStream"),
    @SerializedName("tracedFile")
    TRACED_FILE("tracedFile"),
    @SerializedName("unmodified")
    UNMODIFIED("unmodified"),
    @SerializedName("modified")
    MODIFIED("modified"),
    @SerializedName("added")
    ADDED("added"),
    @SerializedName("deleted")
    DELETED("deleted"),
    @SerializedName("renamed")
    RENAMED("renamed"),
    @SerializedName("uncontrolled")
    UNCONTROLLED("uncontrolled"),
    @SerializedName("driver")
    DRIVER("driver"),
    @SerializedName("extension")
    EXTENSION("extension"),
    @SerializedName("translation")
    TRANSLATION("translation"),
    @SerializedName("taxonomy")
    TAXONOMY("taxonomy"),
    @SerializedName("policy")
    POLICY("policy"),
    @SerializedName("referencedOnCommandLine")
    REFERENCED_ON_COMMAND_LINE("referencedOnCommandLine"),
    @SerializedName("memoryContents")
    MEMORY_CONTENTS("memoryContents"),
    @SerializedName("directory")
    DIRECTORY("directory"),
    @SerializedName("userSpecifiedConfiguration")
    USER_SPECIFIED_CONFIGURATION("userSpecifiedConfiguration"),
    @SerializedName("toolSpecifiedConfiguration")
    TOOL_SPECIFIED_CONFIGURATION("toolSpecifiedConfiguration"),
    @SerializedName("debugOutputFile")
    DEBUG_OUTPUT_FILE("debugOutputFile");
    private final String value;
    private final static Map<String, Role> CONSTANTS = new HashMap<String, Role>();

    static {
        for (Role c : values()) {
            CONSTANTS.put(c.value, c);
        }
    }

    Role(String value) {
        this.value = value;
    }

    @Override
    public String toString() {
        return this.value;
    }

    public String value() {
        return this.value;
    }

    public static Role fromValue(String value) {
        Role constant = CONSTANTS.get(value);
        if (constant == null) {
            throw new IllegalArgumentException(value);
        } else {
            return constant;
        }
    }

}
