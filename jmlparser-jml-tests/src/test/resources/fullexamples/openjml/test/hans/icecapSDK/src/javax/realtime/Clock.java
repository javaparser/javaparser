/**************************************************************************
 * File name  : Clock.java
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
 *  Copyright 2012 
 *  @authors  Anders P. Ravn, Aalborg University, DK
 *            Stephan E. Korsholm and Hans S&oslash;ndergaard, 
 *              VIA University College, DK
 *************************************************************************/
package javax.realtime;


import javax.safetycritical.annotate.SCJAllowed;

/**
 * A clock marks the passing of time. It has a concept of <i>now</i> that 
 * can be queried through <code>Clock.getTime()</code>. <br>
 * The <code>Clock</code> instance returned by <code>getRealtimeClock()
 * </code> may be used in any context that requires a clock. 
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 * 
 * @scjComment 
 *  - SCJ issue: The semantics of <code>getTime</code> with <code>dest
 *      </code> differs from <code>getTime</code> with no arguments.
 *      It is made consistent below.
 *  <p>
 *  - semantic issue: <code>EpochOffSet</code> must be relative to 
 *      <code>RealTimeClock</code>? 
 *  <p>
 *  - implementation issue:
 *   <ul>
 *   <code>
 *   <li>public abstract boolean drivesEvents();<br>
 *   <li>public abstract void registerCallBack(AbsoluteTime t, ClockCallBack clockEvent);<br>
 *   <li>public abstract boolean resetTargetTime(AbsoluteTime time);
 *   </code>
 *   </ul>
 */
@SCJAllowed
public abstract class Clock {
	
	protected static vm.RealtimeClock nativeClock = 
			vm.RealtimeClock.getRealtimeClock();

	// The nominal interval between ticks.
	protected RelativeTime resolution; 
	
	boolean active;

	/**
	 * This constructor for the abstract class may allocate objects within 
	 * the current allocation context.
	 *
	 * @param active
	 *   when true, indicates that the clock can be used for the event-driven release of handler. 
	 *   When false, indicates that the clock can only be queried for the current time.
	 * 
	 */
	protected Clock(boolean active) {
		this.active = active;
		
		int granularity = nativeClock.getGranularity();

		long millis = granularity / 1000000;
		int nanos = granularity % 1000000;

		resolution = new RelativeTime(millis, nanos);
	}

	/**
	 * Returns the relative time of the offset of the epoch of this clock 
	 * from the Epoch of the <code>RealtimeClock</code>.
	 * 
	 * @return the offset of this clock epoch from the <code>RealtimeClock</code>.
	 *    The returned object is associated with this clock.
	 */
	@SCJAllowed
	public abstract RelativeTime getEpochOffset();

	/**
	 * @return The singleton instance of the default <code>Clock</code>.
	 */
	public static Clock getRealtimeClock() {
		return RealtimeClock.instance();
	}

	/**
	 * Gets the resolution of the clock, the nominal interval between ticks.
	 * 
	 * @return The initially allocated resolution object. The returned object 
	 *    is associated with this clock.
	 */
	@SCJAllowed
	public abstract RelativeTime getResolution();

	/**
	 * Gets the resolution of the clock, the nominal interval between ticks 
	 * and stores the result in <code>dest</code>.
	 * 
	 * @param  dest if <code>dest</code> is null, allocate a new 
	 *   <code>RelativeTime</code> instance to hold the returned value.
	 * 
	 * @return if <code>dest</code> is not null, it is set to the resolution 
	 *    object of <code>this</code>. Otherwise a newly allocated object is 
	 *    returned. The returned object is associated with <code></code>this clock.
	 */
	@SCJAllowed
	public abstract RelativeTime getResolution(RelativeTime dest);

	/**
	 * Creates a new object representing <i>now</i> of this clock. 
	 *
	 * @return A new <code>AbsoluteTime</code> object whose time is <i>now</i> of this clock. 
	 */
	@SCJAllowed
	public abstract AbsoluteTime getTime();

	/**
	 * Stores <i>now</i> of this clock in <code>dest</code>.
	 * 
	 * @param  dest If <code>dest</code> is null, allocate a new 
	 *   <code>AbsoluteTime</code> instance to hold the returned value.
	 * 
	 * @return The resulting value.
	 */
	@SCJAllowed
	public abstract AbsoluteTime getTime(AbsoluteTime dest);
	
	
	// used for JML annotation only (not public)
	boolean getAct()
	{
		return active;
	}
		
	// used for JML annotation only (not public)
	RelativeTime getResol()
	{
		return resolution;
	}

}
