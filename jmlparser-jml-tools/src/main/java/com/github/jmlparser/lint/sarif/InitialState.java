
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;


/**
 * Values of relevant expressions at the start of the thread flow that may change during thread flow execution.
 */
@Generated("jsonschema2pojo")
public class InitialState {


    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(InitialState.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
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
        if ((other instanceof InitialState) == false) {
            return false;
        }
        InitialState rhs = ((InitialState) other);
        return true;
    }

}
