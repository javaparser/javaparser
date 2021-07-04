/**************************************************************************
 * File name  : PriorityScheduler.java
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
import javax.scj.util.Priorities;

/**
 * This class represents the priority-based scheduler for Level 1 and 2. <br>
 * The only access to the priority scheduler is for obtaining the minimum
 * and maximum priorities.
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, <A
 *         HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 *         Hans S&oslash;ndergaard, VIA University College, Denmark, <A
 *         HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 */
@SCJAllowed(Level.LEVEL_1)
public class PriorityScheduler extends Scheduler {

	/**
	 * 
	 * @return The maximum software real-time priority supported by this
	 *         scheduler.
	 */
	@SCJAllowed(Level.LEVEL_1)
	public int getMaxPriority() {
		return Priorities.MAX_PRIORITY;
	}

	/**
	 * 
	 * @return The minimum software real-time priority supported by this
	 *         scheduler.
	 */
	@SCJAllowed(Level.LEVEL_1)
	public int getMinPriority() {
		return Priorities.MIN_PRIORITY;
	}
	
	/**
	 * 
	 * @return The normal software real-time priority supported by this
	 *         scheduler.
	 */
	@SCJAllowed(Level.LEVEL_1)
	public int getNormPriority() {
		return (Priorities.MIN_PRIORITY + Priorities.MAX_PRIORITY)/2;
	}
	
	// used for JML annotation only (not public)
    int getMaxPr() {
		return Priorities.MAX_PRIORITY;
	}
    
    // used for JML annotation only (not public)
    int getMinPr() {
		return Priorities.MIN_PRIORITY;
	}

}
