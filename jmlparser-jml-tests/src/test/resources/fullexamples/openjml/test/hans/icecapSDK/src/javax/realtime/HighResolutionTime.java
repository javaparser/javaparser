/**************************************************************************
 * File name  : HighResolutionTime.java
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

import icecaptools.IcecapCompileMe;

import javax.safetycritical.annotate.SCJAllowed;

/**
 * <code>HighResolutionTime</code> is the base class for time given with nanosecond accuracy.<p>
 * A time object in normalized form represents negative time if both components are
 * nonzero and negative, or one is nonzero and negative and the other is zero. <br>
 * For add and subtract operations, negative values behave as they do in Java arithmetic.
 * <p>
 * Methods of this class are not synchronized by the implementation.
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 * 
 * @scjComment
 *  - semantic issue: clock is only meaningful for <code>AbsoluteTime</code> <br>
 *  - semantic issue: Java arithmetic means no overflow detection <br>
 *  - semantic issue: method <code>set</code>: if parameter null, no Exception? <p>
 *  
 *  - implementation issue: 
 *      <code>public int compareTo (Object arg0)</code> is inherited from 
 *      <code>interface Comparable</code> <br>
 */
@SCJAllowed
public abstract class HighResolutionTime implements
		Comparable<HighResolutionTime> {
	Clock clock;
	long millis;
	int nanos;
	
	HighResolutionTime(long millis, int nanos, Clock clock) {
		if (!isNormalized(millis, nanos)) {
			setNormalized(millis, nanos);			
		}
		else {
			this.millis = millis;
			this.nanos = nanos;
		}
		this.clock = clock;
	}

	private boolean isNormalized(long millis, int nanos) {
		return (millis >= 0L && (0 <= nanos && nanos < 1000000))
				|| (millis <= 0L && (-1000000 < nanos && nanos <= 0));
	}

	/**
	 * 
	 * @return a reference to the clock associated with <code>this</code>.
	 */
	public final Clock getClock() {
		return this.clock;
	}

	/**
	 * 
	 * @return the milliseconds component of the time represented by <code>this</code>.
	 */
	public final long getMilliseconds() {
		return this.millis;
	}

	/**
	 * 
	 * @return the nanoseconds component of the time represented by <code>this</code>.
	 */
	public final int getNanoseconds() {
		return this.nanos;
	}

	/**
	 * Change the value represented by <code>this</code> to that of the given <code>time</code>.
	 * 
	 * @param time is the new value for <code>this</code>. 
	 * 
	 * @throws ClassCastException if the <code>time</code> parameter is not 
	 *    of the same class as <code>this</code>.
	 * @throws IllegalArgumentException if the <code>time</code> parameter is 
	 *    not associated with the same clock as <code>this</code>, or when 
	 *    the <code>time</code> parameter is null.
	 */
	public void set(HighResolutionTime time) {
		if (time == null)
			throw new IllegalArgumentException("null parameter");
		if (this.getClass() != time.getClass())
			throw new ClassCastException("from HighResolutionTime :: set");

		this.millis = time.millis;
		this.nanos = time.nanos;
		this.clock = time.clock;
	}

	/**
	 * Sets the millisecond component of <code>this</code> to the given argument, 
	 * and the nanosecond component of <code>this</code> to 0. 
	 * The clock is unchanged.
	 * 
	 * @param millis is the new value of the millisecond component.
	 */
	public void set(long millis) {
		this.millis = millis;
		this.nanos = 0;
	}

	/**
	 * Sets the millisecond and nanosecond components of <code>this</code> to the given arguments.
	 * The clock is unchanged.
	 * 
	 * @param millis is the new value of the millisecond component.
	 * @param nanos is the new value of the nanosecond component.
	 */
	public void set(long millis, int nanos) {
		if (!isNormalized(millis, nanos))
			setNormalized(millis, nanos);
		else {
			this.millis = millis;
			this.nanos = nanos;
		}
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (int) (millis ^ (millis >>> 32));
		result = prime * result + nanos;
		return result;
	}

	/**
	 * @param time
	 * @return true just when the parameter <code>time</code> is of the same 
	 *   type and has the same values as <code>this</code>.
	 */
	public boolean equals(HighResolutionTime time) {
		if (time == null)
			return false;

		return (this.getClass() == time.getClass())
				&& (this.millis == time.getMilliseconds())
				&& (this.nanos == time.getNanoseconds())
				&& (this.clock == time.getClock());
	}
	
	public boolean equals(Object object) {
		HighResolutionTime time = null;
		if (object instanceof HighResolutionTime)
			time = (HighResolutionTime) object;
		if (object instanceof AbsoluteTime)
			time = (AbsoluteTime) object;
		if (object instanceof RelativeTime)
			time = (RelativeTime) object;
		else
			time = null;
		if (time == null || object == null)
			return false;

		return (this.getClass() == time.getClass()) 
				&& (this.millis == time.getMilliseconds()) 
				&& (this.nanos == time.getNanoseconds())
				&& (this.clock == time.getClock());
	}

	/**
	 * Compares <code>this</code> with the specified <code>HighResolutionTime time</code>.
	 * 
	 * @param time is the second argument to the comparison.
	 * 
	 * @return a negative integer, zero, or a positive integer as <code>this</code> 
	 *    object is less than, equal to, or greater than <code>time</code>.
	 *    
	 * @throws ClassCastException if the <code>time</code> parameter is not 
	 *    of the same class as <code>this</code>.
	 * @throws IllegalArgumentException if the <code>time</code> parameter is 
	 *    not associated with the same clock as <code>this</code>, or when 
	 *    the <code>time</code> parameter is null.
	 */	
	public int compareTo(HighResolutionTime time) {
		if (time == null)
			throw new IllegalArgumentException();
		if (this.getClass() != time.getClass())
			throw new ClassCastException();
		if (this.clock != time.getClock())
			throw new IllegalArgumentException();

		if (this.millis < time.getMilliseconds())
			return -1;
		else if (this.millis > time.getMilliseconds())
			return 1;
		else if (this.nanos < time.getNanoseconds())
			return -1;
		else if (this.nanos > time.getNanoseconds())
			return 1;
		else
			return 0;
	}

	public String toString() {
		return ("(ms,ns) = (" + millis + ", " + nanos + ")");
	}

	static final int NANOS_PER_MILLI = 1000000;

	/**
	 * Sets the normalized values of millis and nanos in this. 
	 */
	@IcecapCompileMe  // Don't remove this CompileMe annotation
	final void setNormalized(final long ms, final int ns) {
		/*
		 * Examples:
		 *   3.12 millis =  3 millis and  120*1000 nanos
		 *   0.12 millis =  0 millis and  120*1000 nanos
		 *   0.00 millis =  0 millis and    0*1000 nanos
		 *  -3.12 millis = -3 millis and -120*1000 nanos 
		 *  -0.12 millis =  0 millis and -120*1000 nanos
		 *  -0.00 millis = -0 millis and -  0*1000 nanos
		 */

		// nanos == nanos/NANOS_PER_MILLI + nanos%NANOS_PER_MILLI

		millis = ms + ns / NANOS_PER_MILLI;
		nanos = ns % NANOS_PER_MILLI;
		if (millis > 0 && nanos < 0) {
			millis--; // millis >= 0
			nanos += NANOS_PER_MILLI;
		} else if (millis < 0 && nanos > 0) {
			millis++; // millis <= 0
			nanos -= NANOS_PER_MILLI;
		}
	}
	
//	public static boolean waitForObject(Object target, HighResolutionTime time) {
//		return javax.safetycritical.PriorityScheduler.waitForObject(target, time);
//	}
	
	// used for JML annotation only (not public)
    long getMillis() {
		return millis;
	}
    
    // used for JML annotation only (not public)
    int getNanos() {
		return nanos;
	}
}
