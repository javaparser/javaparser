
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;


/**
 * Values of relevant expressions at the start of the thread flow that remain constant.
 */
@Generated("jsonschema2pojo")
public class ImmutableState {


    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(ImmutableState.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
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
        if ((other instanceof ImmutableState) == false) {
            return false;
        }
        ImmutableState rhs = ((ImmutableState) other);
        return true;
    }

}
