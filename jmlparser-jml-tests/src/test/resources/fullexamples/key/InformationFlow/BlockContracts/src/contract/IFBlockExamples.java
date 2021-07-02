package contract;

/**
 * Information flow examples.
 *
 * A collection of several examples showing the usage of information flow
 * block contracts.
 *
 * @author Christoph Scheben
 */
public class IFBlockExamples {
        int low;

        //@ determines low, \result \by low, l;
        public int secure_1(int l) {
            int l1 = l;
            low++;

            int l2 = 7;
            int l3 = 8;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ determines l1 \by \itself;
            {   l1++;
                if(l2 == 8) {}
            }

            return l1;
        }

        //@ determines low, \result \by low, l;
        public int secure_4(int l) {
            int l1 = l;
            low++;

            int l2 = 7;
            int l3 = 8;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ determines l1, l2 \by \itself;
            {   l1 += l2;
            }

            return l1;
        }

        //@ determines low, \result \by low;
        public int insecure_1(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ determines l1 \by \itself;
            {   l1++;
            }

            return l1;
        }

        //@ determines \result \by l;
        public int secure_6(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ determines l1 \by \itself;
            {   l1++;
            }

            return l1;
        }

        //@ determines \result \by l;
        public int secure_7(int l) {
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ determines l \by \itself;
            {   l++;
            }

            return l;
        }

        //@ determines low \by \itself;
        public int secure_8(int l) {
            low++;

            //@ normal_behavior
            //@ assignable low;
            //@ determines low \by \itself;
            {   low++;
            }

            return low;
        }


        //@ determines low, \result \by low, l;
        public int secure_2(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ determines l1 \by \itself;
            {   l1++;
                //@ normal_behavior
                //@ assignable \nothing;
                //@ determines l1 \by \itself;
                {   l1++;
                    //@ normal_behavior
                    //@ assignable \nothing;
                    //@ determines l1 \by \itself;
                    {   l1++;
                    }
                }
            }

            return l1;
        }


        //@ determines low, \result \by low, l;
        public int secure_3(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ determines l1 \by \itself;
            {   l1++;
                //@ normal_behavior
                //@ assignable \nothing;
                //@ determines l1 \by \itself;
                {   l1++;
                }
                //@ normal_behavior
                //@ assignable \nothing;
                //@ determines l1 \by \itself;
                {   l1++;
                }
            }

            return l1;
        }

        //@ determines low, \result \by low, l;
        public int insecure_3(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ determines l1 \by \itself;
            {   l1++;
                //@ normal_behavior
                //@ assignable \nothing;
                //@ determines low \by \itself;
                {   l1++;
                }
                //@ normal_behavior
                //@ assignable \nothing;
                //@ determines l1 \by \itself;
                {   l1++;
                }
            }

            return l1;
        }

        //@ determines low, \result \by low;
        public int insecure_4(int l) {
            int l1 = l;
            low++;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ determines l1 \by \itself;
            {   l1++;
                //@ normal_behavior
                //@ assignable \nothing;
                //@ determines l1 \by \itself;
                {   l1++;
                }
                //@ normal_behavior
                //@ assignable \nothing;
                //@ determines l1 \by \itself;
                {   l1++;
                }
            }

            return l1;
        }

        //@ requires l > 0;
        //@ determines low \by low, l;
        public void block_while_secure(int l) {
            int l1 = low;
            //@ normal_behavior
            //@ assignable \nothing;
            //@ determines l1 \by \itself;
            { l1++;
            }

           /*@
             @ loop_invariant l >= 0;
             @ assignable \nothing;
             @ determines l1, l \by \itself;
             @ decreases l;
             @*/
            while (l > 0) {
                l--;
                l1++;
            }

            low = l1;
        }


        //@ requires l > 0;
        //@ determines low \by low, l;
        public void while_block_secure(int l) {
            int l1 = low;
           /*@
             @ loop_invariant l >= 0;
             @ assignable \nothing;
             @ determines l1, l \by \itself;
             @ decreases l;
             @*/
            while (l > 0) {
                l--;
                l1++;
            }

            //@ normal_behavior
            //@ assignable \nothing;
            //@ determines l1 \by \itself;
            { l1++;
            }

            low = l1;
        }

        //@ requires l > 0;
        //@ determines low \by low, l;
        public void while_block_insecure(int l) {
            int l1 = low;
           /*@
             @ loop_invariant l >= 0;
             @ assignable \nothing;
             @ determines l \by \itself;
             @ decreases l;
             @*/
            while (l > 0) {
                l--;
                l1++;
            }

            //@ normal_behavior
            //@ assignable \nothing;
            //@ determines l1 \by \itself;
            { l1++;
            }

            low = l1;
        }

                //@ requires l > 0;
        //@ determines low \by low, l;
        public void block_no_return_secure(int l) {
            int l1 = low;

            //@ normal_behavior
            //@ assignable \nothing;
            //@ determines l1 \by \itself;
            { l1++;
            }

            low = l1;
        }

        //@ determines low \by \itself;
        public void secure_5() {
            //@ normal_behavior
            //@ assignable low;
            //@ determines low \by \itself;
            {   low++;
            }
        }

}
