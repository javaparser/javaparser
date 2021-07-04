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
package minicdj.simulator.immortal;

/*@javax.safetycritical.annotate.Scope("immortal")*/
public abstract class PrecompiledSimulator {

    public static void dumpStats() {}

    protected Object[] positions;
    protected Object[] lengths;
    protected Object[] callsigns;

    // args .. ignored
    public static void generate(final String[] args) {

        (new Simulator()).generate();
    }

    public void generate() {
    /*
    synchronized (ImmortalEntry.initMonitor) {

    /*	if (!immortal.Constants.PRESIMULATE) {
    		ImmortalEntry.simulatorReady = true;
    		ImmortalEntry.initMonitor.notifyAll();
    	}

    	while (!ImmortalEntry.detectorReady) {
    		try {
    			ImmortalEntry.initMonitor.wait();
    		} catch (InterruptedException e) {
    		}
    	} */
    /*}


    if (positions.length < immortal.Constants.MAX_FRAMES) {
    	throw new RuntimeException("Not enough frames in pre-compiled simulator.");
    }

    for(int frameIndex=0; frameIndex<immortal.Constants.MAX_FRAMES;frameIndex++) {

    	immortal.ImmortalEntry.frameBuffer.putFrame( (float[])positions[frameIndex], 
    			(int[])lengths[frameIndex], 
    			(byte[])callsigns[frameIndex]);
    }
    //devices.Console.println("Generated "+immortal.Constants.MAX_FRAMES+" frames.");

    /*		if (immortal.Constants.PRESIMULATE) {
    	synchronized (ImmortalEntry.initMonitor) {
    		ImmortalEntry.simulatorReady = true;
    		ImmortalEntry.initMonitor.notifyAll();
    	}
    } */

    }
}
