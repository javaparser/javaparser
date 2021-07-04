/**************************************************************************
 * File name: AperiodicParameters.java
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
package javax.realtime;

import javax.safetycritical.annotate.Level;
import javax.safetycritical.annotate.SCJAllowed;

/**
 * SCJ supports no detection of minimum inter-arrival time violations, 
 * therefore only aperiodic parameters are needed. Hence the RTSJ 
 * <code>SporadicParameters</code> class is absent. <br>
 * Deadline miss detection is supported. <br>
 * 
 * The RTSJ supports a queue for storing the arrival of release events in 
 * order to enable bursts of events to be handled. This queue is of length 1 in SCJ. 
 * The RTSJ also enables different responses to the queue overflowing. 
 * In SCJ the overflow behavior is to overwrite the pending release event if there is one.
 * 
 * @version 1.2; - December 2013
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 */
@SCJAllowed(Level.LEVEL_1)
public class AperiodicParameters extends ReleaseParameters {
	/**
	 * Construct a new <code>AperiodicParameters</code> object within the 
	 * current memory area with no deadline detection facility.
	 */
	public AperiodicParameters() {
		super();
	}

	/**
	 * Construct a new <code>AperiodicParameters</code> object within the current memory area.
	 * 
	 * @param deadline is an offset from the release time by which the release 
	 *   should finish. A null deadline indicates that there is no deadline.
	 * 
	 * @param missHandler is the <code>AsynncEventHandler to be released 
	 *   if the handler misses its deadline. 
	 *   A null parameter indicates that no handler should be released.
	 */
	public AperiodicParameters(RelativeTime deadline,
			AsyncEventHandler missHandler) {
		super(deadline, missHandler);
	}
}
