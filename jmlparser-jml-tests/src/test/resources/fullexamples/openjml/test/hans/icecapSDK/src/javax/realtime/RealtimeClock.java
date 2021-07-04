/**************************************************************************
 * File name  : RealtimeClock.java
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

/**
 * A <code>RealtimeClock</code> implementation. 
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 */
class RealtimeClock extends Clock {
//	private static vm.RealtimeClock nativeClock = 
//		vm.RealtimeClock.getRealtimeClock();

	static Clock rtClock = new RealtimeClock(); 

	RealtimeClock() {
		super(true);
		
//		int granularity = nativeClock.getGranularity();
//
//		long millis = granularity / 1000000;
//		int nanos = granularity % 1000000;
//
//		resolution = new RelativeTime(millis, nanos, rtClock);
		
		resolution.clock = rtClock;
	}

	static Clock instance() {
		return rtClock;
	}

	/*@ 
	  also public behaviour
	    requires true;
	    assignable \nothing;
	    ensures \result.equals(new RelativeTime(0, 0, this));
	  @*/
	@Override
	public RelativeTime getEpochOffset() {
		return new RelativeTime(0, 0, this);
	}

	/**
	 * Returns a newly allocated RelativeTime object that indicates the nominal
	 * interval between ticks. The return value shall be associated with this
	 * clock. All relative time differences measured by this clock are
	 * approximately an integral multiple of the resolution.
	 * 
	 * @return clock resolution.
	 */
	@Override
	public RelativeTime getResolution() {
		return new RelativeTime(resolution);
	}

	@Override
	public RelativeTime getResolution(RelativeTime dest) {
		if (dest == null)
			return getResolution();
		else {
			dest.set(resolution.getMilliseconds(), resolution.getNanoseconds());
			dest.clock = rtClock;
			return dest;
		}
	}

	@Override
	public AbsoluteTime getTime() {
		return getTime(new AbsoluteTime(0, 0, this));
	}

	@Override
	@IcecapCompileMe
	public AbsoluteTime getTime(AbsoluteTime dest) {
		if (dest == null)
			dest = new AbsoluteTime();
		nativeClock.getCurrentTime(dest); // returns Abs time in dest

		// The values in dest are perhaps not normalized:
		// Native values are (x secs, y nanoSecs) which are returned in
		// dest as (1000*x milliSecs, y nanoSecs)

		dest.set(dest.getMilliseconds(), dest.getNanoseconds());
		dest.clock = Clock.getRealtimeClock(); 

		return dest;
	}

}
