/**************************************************************************
 * File name  : PriorityParameters.java
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

import javax.safetycritical.annotate.SCJAllowed;
import javax.scj.util.Priorities;

/**
 * This class is restricted relative to the RTSJ so that it allows the 
 * priority to be created and queried, but not changed.<br>
 * In SCJ the range of priorities is separated into software priorities 
 * and hardware priorities (see <code>PriorityScheduler</code>). 
 * Hardware priorities have higher values than software priorities. 
 * Schedulable objects can be assigned only software priorities.<br>
 * Ceiling priorities can be either software or hardware priorities.
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 *  
 * @scjComment
 *   - SCJ issue: The specification of the constructor says: it throws 
 *     <code>IllegalArgumentException</code> if priority is not in range. <br>
 *     And in the <code>PeriodicEventHandler</code> constructors: 
 *     <code>priority</code> - ... Must not be <code>null</code>.<br>
 *     But at Level 0, priorities are not used and a Level 0 application has 
 *     no <code>PriorityScheduler</code> to call <code>getMinPriority()</code> 
 *     and <code>getMaxPriority()</code> to examine the value of the priority. <br>
 *     A solution might be to omit the requirement: throws 
 *     <code>IllegalArgumentException</code> ... in the 
 *     <code>PriorityParameters(int priority)</code> constructor. <br>
 *     
 *     Then the compliance requirements described in SCJ Draft, Section 2.2, 
 *     will still be satisfied.
 *   <p>
 *   - setPriority is not included in SCJ.
 */
@SCJAllowed
public class PriorityParameters extends SchedulingParameters {
	
	private int priority;

	/**
	 * Creates an instance of <code>PriorityParameters</code> 
	 * with the given <code>priority</code>.
	 * @param priority is the integer value of the specified priority.
	 * @throws IllegalArgumentException if <code>priority</code> is not in 
	 *    the range of supported priorities.
	 */
	public PriorityParameters(int priority) {
		// HSO: the if stmt does not work; also see  @scjComment above
		//	if (priority < javax.safetycritical.PriorityScheduler.instance().getMinPriority() || 
		//	    priority > javax.safetycritical.PriorityScheduler.instance().getMaxPriority()) 
		//			throw new IllegalArgumentException("priority not in range");
		this.priority = priority;
	}

	/**
	 * Gets the priority value.
	 * @return The priority.
	 */
	public int getPriority() {
		return priority;
	}
	
	public void setPriority(int value) // not public in SCJ; called in javax.safetycritical.Monitor
	{
		priority = value;
	}
	
	// used for JML annotation only (not public)
    int getPr() {
		return priority;
	}
}
