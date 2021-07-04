/**************************************************************************
 * File name  : AbsoluteTime.java
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
 * An object that represents a specific point in time given by milliseconds 
 * plus nanoseconds past some point in time fixed by the clock. 
 * For the default real-time clock the fixed point 
 * is the implementation dependent Epoch.<br>
 * 
 * The correctness of the Epoch as a time base depends on the real-time clock synchronization 
 * with an external world time reference. This representation was designed to be compatible with 
 * the standard Java representation of an absolute time in the <code>java.util.Date</code> class. <br>
 * 
 * A time object in normalized form represents negative time if both components are nonzero and 
 * negative, or one is nonzero and negative and the other is zero. For add and subtract negative 
 * values behave as they do in arithmetic.<br>
 * 
 * <b>Caution</b>: This class is explicitly unsafe in multi-threaded situations when it is being 
 * changed. No synchronization is done. It is assumed that users of this class who are mutating 
 * instances will be doing their own synchronization at a higher level.
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 * 
 * @scjComment
 *  - semantic issue: Java arithmetic is assumed for numeric values.
 *      Thus there is no concept of overflow in milliseconds. <br>
 *  - semantic issue: If <code>AbsoluteTime</code> time in subtract is null, 
 *      an <code>IllegalArgumentException</code> is thrown. <br>
 *  - semantic issue: If clocks are different in <code>AbsoluteTime</code> subtract, 
 *      an <code>IllegalArgumentException</code> is thrown.
 */
@SCJAllowed
public class AbsoluteTime extends HighResolutionTime {
	/**
	 * Equivalent to <code>new AbsoluteTime(0,0)</code>. <br>
	 * The clock association is implicitly made with the real-time clock.
	 */
	public AbsoluteTime() {
		this(0L, 0);
	}

	/**
	 * Constructs an <code>AbsoluteTime</code> object with millisecond and 
	 * nanosecond components past the real-time clock's Epoch. <br> 
	 * The actual value is the result of parameter normalization.<br>
	 * 
	 * The clock association is implicitly made with the real-time clock. <br>
	 * 
	 * @param millis is the desired value for the millisecond component. 
	 *    The actual value is the result of parameter normalization.
	 * @param nanos is the desired value for the nanosecond component.
	 *    The actual value is the result of parameter normalization.
	 */
	public AbsoluteTime(long millis, int nanos) {
		super(millis, nanos, Clock.getRealtimeClock());
	}

	/**
	 * Make a new <code>AbsoluteTime</code> object from the given <code>AbsoluteTime</code> object. <br>
	 * 
	 * This constructor requires that the <code>time.getClock()<code> argument 
	 * resides in a scope that encloses the current scope.<br>
	 * 
	 * @param time the object copied
	 * 
	 * @throws IllegalArgumentException if the <code>time</code> parameter is null.
	 */
	public AbsoluteTime(AbsoluteTime time) {
		this();
		if (time == null)
			throw new IllegalArgumentException("null parameter");
		set(time);
	}

	/**
	 * Constructs an <code>AbsoluteTime</code> object with time millisecond 
	 * and nanosecond components past the clock's Epoch. <br>
	 * 
	 * This constructor requires that the <code>>clock</code> object resides 
	 * in a scope that encloses the current scope. <br>
	 * 
	 * @param millis is the desired value for the millisecond component.
	 * 
	 * @param nanos is the desired value for the nanosecond component.
	 * 
	 * @param clock is the desired value for the clock.
	 */
	public AbsoluteTime(long millis, int nanos, Clock clock) {
		super(millis, nanos, clock);
	}

	/**
	 * Equivalent to <code>AbsoluteTime(0,0,clock)</code>.
	 * 
	 * @param clock is the desired value for the clock.
	 */
	public AbsoluteTime(Clock clock) {
		this(0, 0, clock);
	}

	/**
	 * Creates a new object representing the result of adding millis and nanos 
	 * to the values from <code>this</code> and normalizing the result.
	 * The result will have the same clock association as <code>this</code>.
	 * 
	 * @param millis is the number of milliseconds to be added to <code>this</code>.
	 * 
	 * @param nanos is the number of nanoseconds to be added to <code>this</code>.
	 * 
	 * @return a new <code>AbsoluteTime</code> object whose time is the 
	 *    normalization of <code>this </code> plus <code>millis</code> and <code>nanos</code>.
	 */
	public AbsoluteTime add(long millis, int nanos) {
		return new AbsoluteTime(this.millis + millis, this.nanos + nanos,
				this.clock);
	}

	/**
	 * Returns an object containing the value resulting from adding <code>millis</code> and <code>nanos</code> to
	 * the values from <code>this</code> and normalizing the result. If <code>dest</code> is not null, the result is
	 * placed there and returned. Otherwise, a new object is allocated for the result. <br>
	 * 
	 * The result will have the same clock association as <code>this</code>, 
	 * and the clock association with <code>dest</code> is ignored.
	 *  
	 * @param millis is the number of milliseconds to be added to <code>this</code>.
	 * @param nanos is the number of nanoseconds to be added to <code>this</code>.
	 * @param dest if not null, the result is placed there and returned. 
	 *    Otherwise, a new object is allocated for the result.
	 * 
	 * @return the result of the normalization of <code>this</code> plus <code>millis</code> and nanos</code> 
	 *     in <code>dest</code> if it is not null, otherwise the result is returned in a newly allocated object.
	 */
	public AbsoluteTime add(long millis, int nanos, AbsoluteTime dest) {
		if (dest == null)
			dest = new AbsoluteTime(this.clock);
		dest.set(this.millis + millis, this.nanos + nanos);

		return dest;
	}

	/**
	 * Creates a new instance of <code>AbsoluteTime</code> representing the result of 
	 * adding <code>time</code> to the value of <code>this</code> and normalizing the result.<br>
	 * 
	 * @param time the time to add to <code>this</code>.
	 * 
	 * @return a new object whose time is the normalization of <code>this</code> plus the parameter <code>time</code>.
	 * 
	 * @throws IllegalArgumentException if the clock associated with <code>this</code> and the clock associated with the 
	 * <code>time</code> parameter are different, or when the <code>time</code> parameter is null.
	 */	
	public AbsoluteTime add(RelativeTime time) {
		if (time == null)
			throw new IllegalArgumentException("time is null");
		if (time.getClock() != getClock())
			throw new IllegalArgumentException("clock mismatch");

		return new AbsoluteTime(this.millis + time.getMilliseconds(),
				this.nanos + time.getNanoseconds(), this.clock);
	}

	/**
	 * Returns an object containing the value resulting from adding <code>time</code> to the value of 
	 * <code>this</code> and normalizing the result.  If <code>dest</code> is not null, the result 
	 * is placed there and returned. Otherwise, a new object is allocated for the result. 
	 * 
	 * The clock associated with <code>this</code> and the clock associated with the <code>time</code> parameter
	 * must be the same, and it is used for the result. A clock associated with the <code>dest</code> parameter 
	 * is ignored.
	 * 
	 * @param time is the time to add to <code>this</code>.
	 * @param dest is not null, the result is placed there and returned. 
	 *    Otherwise, a new object is allocated for the result.
	 * @return the result in <code>dest</code> if it is not null, 
	 *    otherwise the result is returned in a newly allocated object.
	 * @throws IllegalArgumentException if the clock associated with <code>this</code> and the clock 
	 * associated with the <code>time</code> parameter are different, or when the <code>time</code> parameter is null.
	 */
	public AbsoluteTime add(RelativeTime time, AbsoluteTime dest) {
		if (time == null)
			throw new IllegalArgumentException("time is null");
		if (time.getClock() != getClock())
			throw new IllegalArgumentException("clock mismatch");

		return add(time.getMilliseconds(), time.getNanoseconds(), dest);
	}

	/**
	 * Creates a new instance of <code>RelativeTime</code> representing the result of subtracting <code>time</code>
	 * from the value of <code>this</code> and normalizing the result.
	 * 
	 * The clock associated with <code>this</code> and the clock associated with the <code>time</code> parameter
	 * must be the same, and it is used for the result.
	 * 
	 * @param time is the time to subtract from <code>this.
	 * @return a new object whose time is the normalization of <code>this</code> minus <code>time</code>.
	 * @throws IllegalArgumentException if the clock associated with <code>this</code> and the clock associated 
	 * with the <code>time</code> parameter are different, or when the <code>time</code> parameter is null.
	 */
	public RelativeTime subtract(AbsoluteTime time) {
		if (time == null) {
			throw new IllegalArgumentException("time is null");
		}
		if (this.clock != time.clock) {
			throw new IllegalArgumentException("clock mismatch");
		}		
		return new RelativeTime(this.millis - time.getMilliseconds(),
				this.nanos - time.getNanoseconds(), this.clock);
	}

	/**
	 * Returns an object containing the value resulting from subtracting <code>time</code> from the value
	 * of <code>this</code> and normalizing the result. If <code>dest</code> is not null, the result is placed
	 * there and returned. Otherwise, a new object is allocated for the result. <br>
	 * 
	 * The clock associated with <code>this</code> and the clock associated with the <code>time</code> parameter
	 * must be the same, and it is used for the result. The clock associated with the <code>dest</code> parameter is ignored.
	 * 
	 * @param time is the time to subtract from <code>this</code>.
	 * @param dest if not null, the result is placed there and returned. 
	 * 
	 * @return the result of the normalization of <code>this</code> minus <code>time</code> in <code>dest</code>
	 *  if it is not null, otherwise the result is returned in a newly allocated object. 
	 * @throws IllegalArgumentException if the clock associated with <code>this</code> and the clock associated 
	 * with the <code>time</code> parameter are different, or when the <code>time</code> parameter is null.
	 */
	public RelativeTime subtract(AbsoluteTime time, RelativeTime dest) {
		if (time == null)
			throw new IllegalArgumentException("time is null");
		if (this.clock != time.clock)
			throw new IllegalArgumentException("clock mismatch");

		if (dest != null) {
			dest.set(this.millis - time.getMilliseconds(),
					this.nanos - time.getNanoseconds());
		} else {
			dest = this.subtract(time);
		}

		return dest;
	}

	/**
	 * Creates a new instance of <code>AbsoluteTime</code> representing the result of subtracting <code>time</code>
	 * from the value of <code>this</code> and normalizing the result. <br>
	 * 
	 * The clock associated with <code>this</code> and the clock associated with the <code>time</code> parameter
	 * must be the same, and it is used for the result.
	 * 
	 * @param time is the time to subtract from <code>this</code>.
	 * 
	 * @return a new <code>AbsoluteTime</code> object whose time is the normalization of <code>this</code> minus 
	 * <code>time</code>.
	 * 
	 * @throws IllegalArgumentException  if the clock associated with <code>this</code> and
	 * the clock associated with the <code>time<Code> parameter are different  or when
	 * the <code>time</code> parameter is null.
	 */
	public AbsoluteTime subtract(RelativeTime time) {
		if (time == null)
			throw new IllegalArgumentException("time is null");
		if (time.getClock() != getClock())
			throw new IllegalArgumentException("clock mismatch");

		return new AbsoluteTime(this.millis - time.getMilliseconds(),
				this.nanos - time.getNanoseconds(), this.clock);
	}

	/**
	 * Returns an object containing the value resulting from subtracting <code>time</code> from the value of <code>this</this>
	 * and normalizing the result. If <code>dest</code> is not null, the result is placed
	 * there and returned. Otherwise, a new object is allocated for the result. <br>
	 * 
	 * The clock associated with <code>this</code> and the clock associated with the <code>time</code> parameter
	 * must be the same, and it is used for the result. The clock associated with the <code>dest</code> parameter is ignored.
	 * 
	 * @param time is the time to subtract from <code>this</code>.
	 * @param dest if not null, the result is placed there and returned. 
	 * @return the result of the normalization of <code>this</code> minus <code>time</code> in <code>dest</code>
	 *  if it is not null, otherwise the result is returned in a newly allocated object. 
	 * @throws IllegalArgumentException if the clock associated with <code>this</code> and the clock associated 
	 * with the <code>time</code> parameter are different, or when the <code>time</code> parameter is null.
	 */
	public AbsoluteTime subtract(RelativeTime time, AbsoluteTime dest) {
		if (time == null)
			throw new IllegalArgumentException("time is null");
		if (this.clock != time.clock)
			throw new IllegalArgumentException("clock mismatch");

		if (dest == null) {
			dest = new AbsoluteTime(this.millis - time.getMilliseconds(),
					this.nanos - time.getNanoseconds(), this.clock);
		} else {
			dest.set(this.millis - time.getMilliseconds(),
					this.nanos - time.getNanoseconds());
		}
		return dest;
	}

}
