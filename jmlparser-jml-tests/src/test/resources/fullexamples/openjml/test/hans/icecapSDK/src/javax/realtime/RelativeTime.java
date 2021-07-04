/**************************************************************************
 * File name  : RelativeTime.java
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

/**
 * An object that represents a  duration in milliseconds and nanoseconds.
 * The time interval is kept in normalized form. <br>
 * A negative duration relative to now represents time in the past. 
 * For add and subtract negative values behave as they do in arithmetic. <br>
 * <b>Caution</b>: This class is explicitly unsafe in multithreaded situations when it 
 * is being changed. No synchronization is done. 
 *  
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 *  
 */
@SCJAllowed
public class RelativeTime extends HighResolutionTime {
	/**
	 * Equivalent to <code>RelativeTime(0,0)</code>.
	 */
	public RelativeTime() {
		this(0, 0);
	}

	/**
	 * Construct a RelativeTime object representing a duration based on the parameter <code>millis</code>
	 *  plus the parameter <code>nanos</code>. The construction is subject to normalization of these values. 
	 * <br>
	 * The clock association is implicitly made with the real-time clock.
	 * 
	 * @param millis is the milliseconds.
	 * @param nanos is the nanoseconds.
	 */
	public RelativeTime(long millis, int nanos) {
		this(millis, nanos, Clock.getRealtimeClock());
	}

	/**
	 * Constructs a duration of zero milliseconds and zero nanoseconds.
	 * The clock association is made with the <code>clock</code> parameter. 
	 * If <code>clock</code> is null the association is made with the real-time clock.
	 * @param clock is the clock argument.
	 */
	public RelativeTime(Clock clock) {
		this(0, 0, clock == null ? Clock.getRealtimeClock() : clock);
	}

	/**
	 * Constructs a <code>RelativeTime</code> object representing a duration based on the parameters.
	 * If <code>clock </code> is null the association is made with the real-time clock.
	 * @param millis is the milliseconds
	 * @param nanos is the nanoseconds
	 * @param clock is the clock
	 */
	public RelativeTime(long millis, int nanos, Clock clock) {
		super(millis, nanos, clock == null ? Clock.getRealtimeClock() : clock);
	}

	/**
	 * Makes a new <code>RelativeTime</code> object from the given <code>RelativeTime</code> object.
	 * 
	 * @param time is the copied object. 
	 * 
	 * @throws IllegalArgumentException if <code>time</code> is null.
	 */
	public RelativeTime(RelativeTime time) {
		this();
		if (time != null) {
			millis = time.millis;
			nanos = time.nanos;
			clock = time.clock;
		} else
			throw new IllegalArgumentException();
	}

	/**
	 * Creates a new object representing the result of adding <code>millis</code> and <code>nanos</code> to the values
	 * from <code>this</code> and normalizing the result. The result will have the same clock association as <code>this</code>.
	 * @param millis is the milliseconds to be added.
	 * @param nanos is the nanoseconds to be added.
	 * @return the new object with the added durations.
	 */
	public RelativeTime add(long millis, int nanos) {
		return new RelativeTime(this.millis + millis, this.nanos + nanos,
				this.clock);
	}

	/**
	 * Creates a new object representing the result of adding <code>time</code> to the value of <code>this</code>.
	 * @param time is the duration to be added.
	 * @return the new object with the added durations.
	 * @throws IllegalArgumentException if <code>time</code> is null.
	 * @throws IllegalArgumentException if the clock associated with <code>this</code> and the clock associated with 
	 * the <code>time</code> parameter are different.
	 */
	public RelativeTime add(RelativeTime time) {
		if (time == null)
			throw new IllegalArgumentException("time is null");
		if (this.clock != time.clock)
			throw new IllegalArgumentException("clock mismatch");

		return new RelativeTime(this.millis + time.getMilliseconds(),
				this.nanos + time.getNanoseconds(), time.getClock());
	}

	/**
	 * Returns an object containing the value resulting from adding <code>millis</code> and <code>nanos</code>
	 * to <code>this</code> and normalizing the result. If <code>dest</code> is not null, the result is
	 * placed there and returned. Otherwise, a new object is allocated for the result. 
	 * The result will have the same clock association as <code>this</code>, and the clock association
	 * of <code>dest</code> is ignored.
	 *
	 * @param millis is the milliseconds to be added.
	 * @param nanos is the nanoseconds to be added.
	 * @param dest is the destination, if initially null a <code>new RelativeTime()</code> object is created.
	 * @return the the resulting value.
	 */
	public RelativeTime add(long millis, int nanos, RelativeTime dest) {
		if (dest == null) {
			dest = new RelativeTime(this.millis + millis, this.nanos + nanos);
		} else {
			dest.set(this.millis + millis, this.nanos + nanos);
		}
		return dest;
	}

	/**
	 * Returns an object containing the value resulting from adding <code>time</code> to <code>this</code>
	 * and normalizing the result. If <code>dest</code> is not null, the result is placed there
	 * and returned. Otherwise, a new object is allocated for the result. The clock associated with <code>this</code> 
	 * and the clock associated with the <code>time</code> parameter are expected to be the same, and 
	 * it is used for the result. The clock associated with the <code>dest</code> parameter is ignored.
	 * 
	 * @param time is the time to be added
	 * @param dest is the destination, if null a <code>new RelativeTime()</code> object is created
	 * @return the resulting value.
	 * 
	 * @throws IllegalArgumentException if <code>time</code> is null.
	 * @throws IllegalArgumentException if the clock associated with <code>this</code> and the clock associated with 
	 * the <code>time</code> parameter are different.
	 */
	public RelativeTime add(RelativeTime time, RelativeTime dest) {
		if (time == null)
			throw new IllegalArgumentException("time is null");
		if (this.clock != time.clock)
			throw new IllegalArgumentException("clock mismatch");

		return this.add(time.getMilliseconds(), time.getNanoseconds(), dest);
	}

	/**
	 * Creates a new <code>RelativeTime</code> object representing the result 
	 * of subtracting <code>time</code> from the value of <code>this</code>.
	 * @param time the value to be subtracted.
	 * @return the difference between durations.
	 * 
	 * @throws IllegalArgumentException if <code>time</code> is null.
	 * @throws IllegalArgumentException if the clock associated with <code>this</code> and the clock associated with 
	 * the <code>time</code> parameter are different.
	 */
	public RelativeTime subtract(RelativeTime time) {
		if (time == null)
			throw new IllegalArgumentException("time is null");
		if (this.clock != time.clock)
			throw new IllegalArgumentException("clock mismatch");

		return new RelativeTime(this.millis - time.getMilliseconds(),
				this.nanos - time.getNanoseconds(), this.clock);
	}

	/**
	 * Creates a new <code>RelativeTime</code> object representing the result 
	 * of subtracting <code>time</code> from the value of <code>this</code>. 
	 * If <code>dest</code> is not null, the result is placed there and returned. 
	 * Otherwise, a new object is allocated for the result. 
	 * The clock associated with this and the clock associated with the time 
	 * parameter are expected to be the same, and such association is used for the result.
	 * The clock associated with the <code>dest</code> parameter is ignored.
	 * 
	 * @param time is the duration to be subtracted
	 * @param dest is the destination, if  null a <code>new RelativeTime()</code> object is created
	 * @return the <code>dest</code> object with the resulting value.
	 *
	 * @throws IllegalArgumentException if <code>time</code> is null.
	 * @throws IllegalArgumentException if the clock associated with <code>this</code> 
	 *    and the clock associated with the <code>time</code> parameter are different.
	 */
	public RelativeTime subtract(RelativeTime time, RelativeTime dest) {
		if (time == null)
			throw new IllegalArgumentException("time is null");
		if (this.clock != time.clock)
			throw new IllegalArgumentException("clock mismatch");

		if (dest == null) {
			dest = new RelativeTime(this.millis - time.getMilliseconds(),
					this.nanos - time.getNanoseconds(), this.clock);
		} else {
			dest.set(this.millis - time.getMilliseconds(),
					this.nanos - time.getNanoseconds());
		}
		return dest;
	}
}
