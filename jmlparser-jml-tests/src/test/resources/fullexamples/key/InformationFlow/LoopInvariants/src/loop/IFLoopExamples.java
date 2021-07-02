package loop;

/**
 * Information flow examples.
 *
 * A collection of several examples showing the usage of information flow
 * loop invariants.
 *
 * @author Christoph Scheben
 */
public class IFLoopExamples {
	int low;

        // This is a secure example from a tutorial by Christian Hammer
        // which was designed to show where approximative analysis usually
        // have to give up.
        //@ normal_behavior
        //@ determines low \by \itself;
        public void hammer(int secret) {
            int x = 0;
            int y = 0;
            //@ loop_invariant 0 <= y && y <= 10;
            //@ determines low, y, (y < 10 ? x : 0) \by \itself;
            //@ assignable low;
            //@ decreases 10 - y;
            while (y < 10) {
                print(x);
                if (y == 5) {
                    x = secret;
                    y = 9;
                }
                x++;
                y++;
            }
        }

        //@ normal_behavior
        //@ determines low, x \by \itself;
        //@ assignable low;
        //@ helper
        public void print(int x) {
            low = x;
        }


	/*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ determines low, x \by \itself;
	  @*/
	public void secure_while(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ determines low, x \by \itself;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
		}
	}

	/*@
	  @ requires   x >= 0;
	  @ assignable low;
	  @ determines low, x \by \itself;
	  @*/
	public void loc_secure_while(int x) {

		int z = 2;
		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ determines low, x, z \by \itself;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
			z = z + x;
		}
	}

	/*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ determines low, x \by \itself;
	  @*/
	public void secure_twoWhile(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ determines low, x \by \itself;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
		}

		/*@
		  @ loop_invariant x >= -1;
		  @ assignable low;
		  @ determines low, x \by \itself;
		  @ decreases x+1;
		  @*/
		while (x == 0) {
			low = low + 1;
			x = x - 1;
		}
	}

	/*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ determines low \by \itself;
	  @*/
	public void insecure_twoWhile_2(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ determines low, x \by \itself;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
		}

		/*@
		  @ loop_invariant x >= -1;
		  @ assignable low;
		  @ determines low, x \by \itself;
		  @ decreases x+1;
		  @*/
		while (x == 0) {
			low = low + 1;
			x = x - 1;
		}
	}

        /*@
	  @ requires   x >= 0;
	  @ assignable low;
	  @ determines low, x \by \itself;
	  @*/
	public void insecure_twoWhile(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ determines low, x \by \itself;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
		}

		/*@
		  @ loop_invariant x >= -1;
		  @ assignable low;
		  @ determines x \by \itself;
		  @ decreases x+1;
		  @*/
		while (x == 0) {
			low = low + 1;
			x = x - 1;
		}
	}


	/*@
	  @ requires   x >= 1;
	  @ assignable low;
	  @ determines low \by \itself;
	  @*/
	public void notSecure_while_wrongInv(int x) {

		/*@
		  @ loop_invariant x >= 1;
		  @ assignable low;
		  @ determines low \by \itself;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
		}
	}

	/*@
	  @ requires   x >= 0;
	  @ assignable low;
	  @ determines low \by \itself;
	  @*/
	public void notSecure_while(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ determines low \by \itself;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
		}
	}

	/*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ determines low, x \by \itself;
	  @*/
	public void secure_nestedWhile(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ determines low, x \by \itself;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
			
			/*@
			  @ loop_invariant x >= 0;
			  @ assignable low;
			  @ determines low, x \by \itself;
			  @ decreases x;
			  @*/
			while (x > 0) {
				low = low + 1;
				x = x - 1;				
			}
		}
	}

	/*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ determines low, x \by \itself;
	  @*/
	public void secure_nestedTwoWhile(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ determines low, x \by \itself;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;

			/*@
			  @ loop_invariant x >= 0;
			  @ assignable low;
			  @ determines low, x \by \itself;
			  @ decreases x;
			  @*/
			while (x > 0) {
				low = low + 1;
				x = x - 1;				
			}

			/*@
			  @ loop_invariant x >= 0;
			  @ assignable low;
			  @ determines low, x \by \itself;
			  @ decreases x;
			  @*/
			while (x > 0) {
				low = low + 1;
				x = x - 1;				
			}
		}
	}

	/*@
	  @ requires   x >= 0;
	  @ assignable low;
	  @ determines low, x \by \itself;
	  @*/
	public void secure_doubleNestedWhile(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ determines low, x \by \itself;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;

                        /*@
			  @ loop_invariant x >= 0;
			  @ assignable low;
			  @ determines low, x \by \itself;
			  @ decreases x;
			  @*/
			while (x > 0) {
				low = low + 1;
				x = x - 1;

				/*@
				  @ loop_invariant x >= 0;
				  @ assignable low;
				  @ determines low, x \by \itself;
				  @ decreases x;
				  @*/
				while (x > 0) {
					low = low + 1;
					x = x - 1;
				}				
			}
		}
	}

        /*@
	  @ requires   x >= 0;
	  @ assignable low;
	  @ determines low \by \itself;
	  @*/
	public void insecure_doubleNestedWhile(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ determines low, x \by \itself;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;

			/*@
			@ loop_invariant x >= 0;
			@ assignable low;
			@ determines low, x \by \itself;
			@ decreases x;
			@*/
			while (x > 0) {
				low = low + 1;
				x = x - 1;

				/*@
				  @ loop_invariant x >= 0;
				  @ assignable low;
				  @ determines low, x \by \itself;
				  @ decreases x;
				  @*/
				while (x > 0) {
					low = low + 1;
					x = x - 1;
				}
			}
		}
	}

        	/*@
	  @ requires   x >= 0;
	  @ assignable low;
	  @ determines low, x \by \itself;
	  @*/
	public void insecure_doubleNestedWhile2(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ determines low, x \by \itself;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;

			/*@
			@ loop_invariant x >= 0;
			@ assignable low;
			@ determines low \by \itself;
			@ decreases x;
			@*/
			while (x > 0) {
				low = low + 1;
				x = x - 1;

				/*@
				  @ loop_invariant x >= 0;
				  @ assignable low;
				  @ determines low, x \by \itself;
				  @ decreases x;
				  @*/
				while (x > 0) {
					low = low + 1;
					x = x - 1;
				}
			}
		}
	}
        
        
                /*@
          @ requires   x >= 0;
          @ assignable low;
          @ determines low, x \by \itself;
          @*/
        public void secure_while_4(int x) {
                low = low + 1;
                /*@
                  @ loop_invariant 0 <= x;
                  @ assignable  low;
                  @ determines  low, x \by \itself;
                  @ decreases   x;
                  @*/
                while (x > 0) {
                        low = low + 1;
                        x = x - 1;
                }
                low = low + 1;
        }

        /*@
          @ requires   x >= 0;
          @ assignable low;
          @ determines low, x \by \itself;
          @*/
        public void secure_while_2(int x) {
                low = low + 1;
                /*@
                  @ loop_invariant 0 <= x;
                  @ assignable  low;
                  @ determines  low, x \by \itself;
                  @ decreases   x;
                  @*/
                while (x > 0) {
                        low = low + 1;
                        x = x - 1;
                }
                low = low + 1;
        }

        /*@
          @ requires   x >= 1;
          @ assignable low;
          @ determines low \by \itself;
          @*/
        public void insecure_while_3(int x) {
                low = low + 1;
                /*@
                  @ loop_invariant 0 <= x;
                  @ assignable  low;
                  @ determines  low \by \itself;
                  @ decreases   x;
                  @*/
                while (x > 0) {
                        low = low + 1;
                        x = x - 1;
                }
                low = low + 1;
        }
}