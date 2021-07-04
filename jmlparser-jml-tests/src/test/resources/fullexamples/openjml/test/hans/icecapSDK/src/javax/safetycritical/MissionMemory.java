/**************************************************************************
 * File name  : MissionMemory.java
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
package javax.safetycritical;

import javax.safetycritical.annotate.Level;
import javax.safetycritical.annotate.SCJAllowed;

/**
 * Mission memory is a linear-time scoped memory area that remains active
 * through the lifetime of a mission.
 * <p>
 * This class is final. It is instantiated by the infrastructure and 
 * entered by the infrastructure.
 * Hence, non of its constructors are visible.
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 * 
 * @scjComment 
 *  - SCJ issue: This class should not be public.     
 */
@SCJAllowed(Level.INFRASTRUCTURE)
public final class MissionMemory extends ManagedMemory // HSO: not public
{	
	Runnable runInitialize;
	Runnable runExecute;
	Runnable runCleanup;
	Mission m;

	MissionMemory(int size, ManagedMemory backingStoreProvider, String label) {
		super(size, backingStoreProvider.getRemainingBackingstoreSize(), 
			  backingStoreProvider, label);
		
		runInitialize = new Runnable() {
			public void run() {
				m.runInitialize();
			}
		};
		runExecute = new Runnable() {
			public void run() {
				m.runExecute();
			}
		};
		runCleanup = new Runnable() {
			public void run() {
				m.runCleanup(MissionMemory.this);
			}
		};
	}

	void enterToInitialize(final Mission mission) {
		m = mission;
		executeInArea(runInitialize);
	}

	void enterToExecute(final Mission mission) {
		m = mission;
		executeInArea(runExecute);
	}

	void enterToCleanup(final Mission mission) {
		m = mission;
		executeInArea(runCleanup);		
		resetArea();
	}
}
