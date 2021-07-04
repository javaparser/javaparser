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

/*@javax.safetycritical.annotate.Scope("immortal")*/
public class RawFrame {
    static private int   MAX_PLANES = 1000;
    static private int   MAX_SIGNS  = 10 * MAX_PLANES;

    public final int[]   lengths    = new int[MAX_PLANES];
    public final byte[]  callsigns  = new byte[MAX_SIGNS];
    public final float[] positions  = new float[3 * MAX_PLANES];
    public int           planeCnt;

    /*@javax.safetycritical.annotate.AllocFree*/
    public void copy(final int[] lengths_, final byte[] signs_, final float[] positions_) {
        for (int i = 0, pos = 0, pos2 = 0, pos3 = 0, pos4 = 0; i < lengths_.length; i++) {
            lengths[pos++] = lengths_[i];
            positions[pos2++] = positions_[3 * i];
            positions[pos2++] = positions_[3 * i + 1];
            positions[pos2++] = positions_[3 * i + 2];
            for (int j = 0; j < lengths_[i]; j++)
                callsigns[pos3++] = signs_[pos4 + j];
            pos4 += lengths_[i];
        }
        planeCnt = lengths_.length;
    }
}