
package com.github.jmlparser.lint.sarif;

import javax.annotation.processing.Generated;


/**
 * A dictionary, each of whose keys is the name of a hash function and each of whose values is the hashed value of the artifact produced by the specified hash function.
 */
@Generated("jsonschema2pojo")
public class Hashes {


    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Hashes.class.getName()).append('@').append(Integer.toHexString(System.identityHashCode(this))).append('[');
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
        if ((other instanceof Hashes) == false) {
            return false;
        }
        Hashes rhs = ((Hashes) other);
        return true;
    }

}
