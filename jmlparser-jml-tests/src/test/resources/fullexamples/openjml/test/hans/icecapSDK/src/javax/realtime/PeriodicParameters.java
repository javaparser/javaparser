/**************************************************************************
 * File name  : PeriodicParameters.java
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
 * This class is restricted relative to RTSJ so that it allows the 
 * start time and the period to be set but not changed or queried.
 * 
 * @version 1.2; - December 2013
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 * 
 * @scjComment     
 *  - implementation issue: 
 *    the following two public methods are not in SCJ: <br>
 *   <ul>
 *    <code>
 *     <li>public RelativeTime getPeriod();<br>
 *     <li>public RelativeTime getStart();
 *    </code>
 *   </ul>
 */
@SCJAllowed
public class PeriodicParameters extends ReleaseParameters {
	
	RelativeTime start;
	RelativeTime period;

	/** 
	 * Constructs a new object within the current memory area.  
	 * The default deadline is the same value as <code>period</code>.<br>
	 * There is no missHandler.
	 *
	 * @param start is the time of the first release relative to start of the mission. 
	 *   A null value defaults to a value of zero milliseconds.
	 * @param period is the is the time between each release of an associated schedulable object. 
	 * 
	 * @throws IllegalArgumentException if <code>period</code> is null.
	 */
	public PeriodicParameters(RelativeTime start, RelativeTime period) {
		this(start, period, null, null);
	}

	/**
	 * Constructs a new object within the current memory area. 
	 * 
	 * @param start is time of the first release of the associated schedulable relative to the start
	 *    of the mission. A null value defaults to zero milliseconds.
	 * @param period is the time between each release of the associated schedulable object.
	 * @param deadline is an offset from the release time by which the release should finish.
	 *    A null <code>deadline</code> indicates the same value as the <code>period</code>.
	 * @param missHandler  is the event handler to be released if the deadline is missed. 
	 *    A null value means that misses are not handled.
	 * 
	 * @throws IllegalArgumentException if <code>period</code> is null.
	 */
	@SCJAllowed(Level.LEVEL_1)
	public PeriodicParameters(RelativeTime start, RelativeTime period,
			RelativeTime deadline, AsyncEventHandler missHandler) {
		super(deadline == null ? period : deadline, missHandler);

		if (start == null)
			this.start = new RelativeTime();
		else
			this.start = new RelativeTime(start);
		
		if (period == null || 
			period.millis < 0 || 
			(period.millis == 0 && period.nanos == 0) || 
			start.clock != period.clock)
				throw new IllegalArgumentException("period is null or not vaild");
		if (deadline != null && 
			(deadline.millis < 0 || 
			  (deadline.millis == 0 && deadline.nanos == 0) || 
			   period.clock != deadline.clock))
				throw new IllegalArgumentException("deadline is null or not vaild");

		this.period = new RelativeTime(period);
	}

	// Not public in SCJ
	public RelativeTime getPeriod() {
		return period;
	}

	// Not public in SCJ
	public RelativeTime getStart() {
		return start;
	}
	
	// used for JML annotation only (not public)
	RelativeTime period() {
    	return period;
    }
    
    // used for JML annotation only (not public)
	RelativeTime start() {
    	return start;
    }
}
