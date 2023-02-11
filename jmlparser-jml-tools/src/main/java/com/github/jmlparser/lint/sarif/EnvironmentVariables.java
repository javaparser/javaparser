
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;


/**
 * The environment variables associated with the analysis tool process, expressed as key/value pairs.
 */
@Generated("jsonschema2pojo")
public class EnvironmentVariables {


    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(EnvironmentVariables.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
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
        if ((other instanceof EnvironmentVariables) == false) {
            return false;
        }
        EnvironmentVariables rhs = ((EnvironmentVariables) other);
        return true;
    }

}
