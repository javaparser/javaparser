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
package minicdj.cdx.unannotated;

import javax.realtime.AbsoluteTime;
import javax.realtime.Clock;

import minicdj.cdx.Constants;

public class NanoClock {

    public static long baseMillis = -1;
    public static int  baseNanos  = -1;

    public static AbsoluteTime roundUp(AbsoluteTime t) { // round up to next or second next period

        long tNanos = t.getNanoseconds();
        long tMillis = t.getMilliseconds();

        long periodMillis = Constants.DETECTOR_PERIOD;

        if (tNanos > 0) {
            tNanos = 0;
            tMillis++;
        }

        if (periodMillis > 0) {
            tMillis = ((tMillis + periodMillis - 1) / periodMillis) * periodMillis;
        }

        return new AbsoluteTime(tMillis, (int) tNanos);
    }

    public static void init() {
        if (baseMillis != -1 || baseNanos != -1) { throw new RuntimeException("NanoClock already initialized."); }

        AbsoluteTime rt = roundUp(Clock.getRealtimeClock().getTime());

        baseNanos = rt.getNanoseconds();
        baseMillis = rt.getMilliseconds();
    }

    public static long now() {

        AbsoluteTime t = Clock.getRealtimeClock().getTime();

        return convert(t);
    }

    public static long convert(AbsoluteTime t) {

        long millis = t.getMilliseconds() - baseMillis;
        int nanos = t.getNanoseconds();

        return millis * 1000000 + nanos - baseNanos;
    }

    @SuppressWarnings("unused")
	public static int asMicros(long relativeNanos) {
        if (relativeNanos < 0) {
            if (relativeNanos == -1) { return 0; }
        }

        long millis = baseMillis + relativeNanos / 1000000L;
        int nanos = baseNanos + (int) (relativeNanos % 1000000L);
        millis += nanos / 1000000L;
        nanos = nanos % 1000000;
        return nanos / 1000;
    }

    public static String asString(long relativeNanos) {

        if (relativeNanos < 0) {
            if (relativeNanos == -1) { return "NA"; }
        }

        long millis = baseMillis + relativeNanos / 1000000L;
        int nanos = baseNanos + (int) (relativeNanos % 1000000L);

        millis += nanos / 1000000L;
        nanos = nanos % 1000000;

        String ns = Integer.toString(nanos);
        int zeros = 6 - ns.length();
        StringBuffer result = new StringBuffer(Long.toString(millis));

        while (zeros-- > 0) {
            result = result.append("0");
        }

        result = result.append(ns);

        return result.toString();
    }

}