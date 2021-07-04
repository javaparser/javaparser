/**************************************************************************
 * File name  : CyclicSchedule.java
 * 
 * This file is part a SCJ Level 0 and Level 1 implementation, 
 * based on SCJ Draft, Version 0.94 25 June 2013.
 *
 * It is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as  
 * published by the Free Software Foundation, either version 3 of the 
 * License, or (at your option) any later version.
 *
 * This SCJ Level 0 and Level 1 implementation is distributed in the hope 
 * that it will be useful, but WITHOUT ANY WARRANTY; without even the  
 * implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this SCJ Level 0 and Level 1 implementation.  
 * If not, see <http://www.gnu.org/licenses/>.
 *
 * Copyright 2012 
 * @authors  Anders P. Ravn, Aalborg University, DK
 *           Stephan E. Korsholm and Hans S&oslash;ndergaard, 
 *             VIA University College, DK
 *************************************************************************/
package javax.safetycritical;

import javax.safetycritical.annotate.SCJAllowed;

/**
 *  A <code>CyclicSchedule</code> object represents a time-driven sequence 
 *  of releases for deterministic scheduling of periodic event handlers.
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 */
@SCJAllowed
public final class CyclicSchedule {
	
	private Frame[] frames;
	
	/**
	 * Constructs a <code>CyclicSchedule</code> by copying the frames array 
	 * into a private array within the same memory area as this newly 
	 * constructed <code>CyclicSchedule</code> object.<br>
	 * The frames array represents the order in which event handlers are to be scheduled.
	 * 
	 * @param frames is the frame array.
	 */
	public CyclicSchedule(Frame[] frames) throws IllegalArgumentException {
		if (frames == null)
			throw new IllegalArgumentException ("frames is null");
		// frames != null:
		for (int i = 0; i < frames.length; i++) {
			if (frames[i] == null)
				throw new IllegalArgumentException ("a frame element is null");
		}
		
		this.frames = new Frame[frames.length];
		for (int i = 0; i < frames.length; i++)
			this.frames[i] = frames[i];
	}

	/**
	 * A method used by infrastructure to access the frame array
	 * @return Frame array.
	 */
	Frame[] getFrames() {
		return frames;
	}

}
