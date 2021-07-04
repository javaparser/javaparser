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

// The purpose of this class is to allow printing debug messages with
// callsigns (byte arrays) and floating point data from a no-heap thread.
// With standard Java ways of doing this, we get MemoryAccessError, due to 
// the internal use of ThreadLocal by Sun RTS for character encoders/decoders
// (and possibly other things). With encoders/decoders, the lazy initialization
// leads to uncontrolled allocation wrt to scope. Most likely the problem is that
// the thread locals get allocated on the heap.

// Note that these converters are intentionally incorrect. We have no
// control over the use of thread locals in VM libraries, so these may very
// not work / not be needed on other VMs.

public class ASCIIConverter {
    public static String bytesToString(byte[] bytes) {

        char[] chars = new char[bytes.length];

        for (int i = 0; i < bytes.length; i++) {
            chars[i] = (char) bytes[i];
        }

        return new String(chars);
    }

    public static String floatToString(float f) {

        long intPart = (long) Math.ceil(f);
        long fewDigits = (long) ((f - intPart) * 1000);

        return "" + intPart + "." + fewDigits;
    }
}
