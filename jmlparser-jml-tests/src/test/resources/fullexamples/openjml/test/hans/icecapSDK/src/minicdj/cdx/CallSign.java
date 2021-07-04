/**
 *  This file is part of miniCDx benchmark of oSCJ.
 *
 *   miniCDx is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU Lesser General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   miniCDx is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU Lesser General Public License for more details.
 *
 *   You should have received a copy of the GNU Lesser General Public License
 *   along with miniCDx.  If not, see <http://www.gnu.org/licenses/>.
 *
 *
 *   Copyright 2009, 2010 
 *   @authors  Daniel Tang, Ales Plsek
 *
 *   See: http://sss.cs.purdue.edu/projects/oscj/
 */
package minicdj.cdx;

/**
 * CallSign (name) of the plane. Constructor runs and instance lives in the persistent detector scope, so that call
 * signs can be linked in the (persistent) state - StateTable.
 */
/*@javax.safetycritical.annotate.Scope("cdx.Level0Safelet")*/
public class CallSign {

    final private byte[] val;

    public CallSign(final byte[] v) {
        val = v;
    }

    /** Returns a valid hash code for this object. */
    public int hashCode() {
        int h = 0;
        for (int i = 0; i < val.length; i++) {
            h += val[i];
        }
        return h;
    }

    /** Performs a comparison between this object and another. */
    public boolean equals(final Object other) {
        if (other == this) return true;
        else if (other instanceof CallSign) {
            final byte[] cs = ((CallSign) other).val;
            if (cs.length != val.length) return false;
            for (int i = 0; i < cs.length; i++)
                if (cs[i] != val[i]) return false;
            return true;
        } else return false;
    }

    /** Performs comparison with ordering taken into account. */
    public int compareTo(final Object _other) throws ClassCastException {
        final byte[] cs = ((CallSign) _other).val;
        if (cs.length < val.length) return -1;
        if (cs.length > val.length) return +1;
        for (int i = 0; i < cs.length; i++)
            if (cs[i] < val[i]) return -1;
            else if (cs[i] > val[i]) return +1;
        return 0;
    }
}
