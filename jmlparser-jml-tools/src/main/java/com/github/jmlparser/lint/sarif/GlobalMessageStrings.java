
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;


/**
 * A dictionary, each of whose keys is a resource identifier and each of whose values is a multiformatMessageString object, which holds message strings in plain text and (optionally) Markdown format. The strings can include placeholders, which can be used to construct a message in combination with an arbitrary number of additional string arguments.
 */
@Generated("jsonschema2pojo")
public class GlobalMessageStrings {


    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(GlobalMessageStrings.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
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
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if ((other instanceof GlobalMessageStrings) == false) {
            return false;
        }
        GlobalMessageStrings rhs = ((GlobalMessageStrings) other);
        return true;
    }

}
