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

//import com.fiji.fivm.r1.*;

public class Benchmarker {

    /*	@RuntimeImport
    	public static native void set(int what);
    	
    	@RuntimeImport
    	public static native void done(int what);
    	
    	@RuntimeImport
    	public static native void initialize(); */

    public static char      RAPITA_GENERATOR            = 1;
    public static char      RAPITA_ROUNDUP              = 2;
    public static char      RAPITA_PERIOD               = 3;
    public static char      RAPITA_DETECTOR_STEP        = 4;
    public static char      RAPITA_SETFRAME             = 5;
    public static char      RAPITA_REDUCER_INIT         = 6;
    public static char      RAPITA_CREATE_MOTIONS       = 7;
    public static char      RAPITA_DETECTOR_CLEANUP     = 8;
    public static char      RAPITA_REDUCER              = 9;
    public static char      RAPITA_VOXELHASHING         = 10;
    public static char      RAPITA_VOXELHASH_DFS        = 11;
    public static char      RAPITA_ISINVOXEL            = 12;
    public static char      RAPITA_VOXELHASH_EXPANDING  = 13;
    public static char      RAPITA_DETERMINE_COLLISIONS = 14;
    public static char      RAPITA_COLLISION_DUPLICATES = 15;
    public static char      RAPITA_FIND_INTERSECTION    = 16;
    public static char      RAPITA_BENCHMARK            = 255;
    public static char      RAPITA_DONE                 = 128;
    public static char      LOOK_FOR_COLLISIONS         = 17;
    public static char      REDUCE_COLLISIONS           = 18;
    public static char      VOXEL_HASHING               = 19;
    public static char      REDUCE_LOOP                 = 20;

    public static final int TRACE_SIZE                  = 10;
    /*private static int      _tracePtr;
    private static char[]   trace                       = new char[TRACE_SIZE];
    private static int[]    traceTime                   = new int[TRACE_SIZE];
    private static int      _traceStart;*/

    public static void initialize() {
    /*		_tracePtr=0;
    		_traceStart=(int)(System.nanoTime()/1000); */
    }

    public static void set(int what) {
    /*if (_tracePtr>=TRACE_SIZE) return;
    traceTime[_tracePtr]=(int)(System.nanoTime()/1000)-_traceStart;
    trace[_tracePtr]=what;
    _tracePtr++; 
    test(); */
    }

    public static void done(int i) {
    /*if (_tracePtr>=TRACE_SIZE) return;
    traceTime[_tracePtr]=(int)(System.nanoTime()/1000)-_traceStart;
    trace[_tracePtr]=(char)((int)(what)+(int)(RAPITA_DONE));
    _tracePtr++; */
    }

    public static void dump() {
    /*int i=0;
    devices.Console.println("--TRACE BEGIN");
    while (i<_tracePtr) {
    	String line=(int)trace[i]+" "+traceTime[i];
    	devices.Console.println(line);
    	i++;
    }
    devices.Console.println("--TRACE END"); */
    }
}