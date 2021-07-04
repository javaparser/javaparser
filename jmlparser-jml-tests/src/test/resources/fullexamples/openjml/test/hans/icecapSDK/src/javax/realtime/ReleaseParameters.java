/**************************************************************************
 * File name  : ReleaseParameters.java
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
 *   
 *************************************************************************/
package javax.realtime;

import javax.safetycritical.annotate.Level;
import javax.safetycritical.annotate.SCJAllowed;

/**
 *  All schedulability analysis of safety critical software is performed off line. <br>
 *  Although the RTSJ allows on-line schedulability analysis, SCJ assumes any such analysis is
 *  performed off line and that the on-line environment is predictable. Consequently,
 *  the assumption is that deadlines are not missed. <br>
 *  However, to facilitate fault-tolerant applications, SCJ does support 
 *  a deadline miss detection facility at Levels 1 and 2. <br>
 *  SCJ provides no direct mechanisms for coping with cost overruns. <p>
 *  The <code>ReleaseParameters</code> class is restricted so that the parameters cannot be changed or queried.
 *  
 * @version 1.2; - December 2013
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 * 
 * @scjComment 
 */
@SCJAllowed
public abstract class ReleaseParameters implements Cloneable {
	
	RelativeTime deadline;
	AsyncEventHandler missHandler;

	/**
	 * Constructs an object which has no deadline checking facility. <br>
	 * There is no default for deadline in this class. 
	 * The default is set by the subclasses.
	 */
	protected ReleaseParameters() {
	}

	/**
	 * Constructs an object.  
	 * @param deadline is the deadline to be checked. It is cloned to become immutable.
	 * @param missHandler is the event handler to be released if the deadline is missed.
	 */
	@SCJAllowed(Level.LEVEL_1)
	protected ReleaseParameters(RelativeTime deadline,
			AsyncEventHandler missHandler) {
		this.deadline = (deadline == null ? null : new RelativeTime(deadline));
		this.missHandler = missHandler;
	}
	
	public Object clone() throws CloneNotSupportedException {
		ReleaseParameters clone = (ReleaseParameters) super.clone();
		return clone;
	}

	// Used in JML annotations; also used in JML annotations in CyclicExecutive
	RelativeTime getDeadline() {
		return deadline;
	}

	// Used in JML annotations
	AsyncEventHandler getMissHandler() //  /*@ spec_public @*/
	{
		return missHandler;
	}
}
