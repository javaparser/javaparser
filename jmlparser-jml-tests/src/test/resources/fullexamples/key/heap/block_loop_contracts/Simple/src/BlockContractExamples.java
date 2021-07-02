public class BlockContractExamples {

    /*@ normal_behavior
      @ ensures from < 0 ==> \result == (
          \sum int i;
             0 <= i && i < numbers.length;
          numbers[i]
        );
      @ ensures from >= 0 ==> \result == (
          \sum int i;
             from <= i && i < numbers.length;
          numbers[i]
        );
      @ assignable \nothing;
      @*/
    public int sum(int[] numbers, int from)
    {
        /*@ requires numbers != null;
          @ ensures 0 <= from && from < numbers.length
              && (\before(from) < 0 ==> from == 0)
              && (\before(from) >= 0 ==> from == \before(from));
          @ returns \result == 0
              && (\before(from) >= numbers.length
                  || numbers.length == 0);
          @ signals_only \nothing;
          @ assignable \nothing;
          @*/
        {
            if (from < 0) {
                from = 0;
            }
                
            if (from >= numbers.length) {
                return 0;
            }
        }
            
        int result = 0;
            
        /*@ maintaining from <= i && i <= numbers.length
                && result == (\sum int j;
                    from <= j && j < i;
                    numbers[j]);
          @ decreasing numbers.length - i;
          @ assignable \nothing;
          @*/
        for (int i = from; i < numbers.length; i++) {
            result += numbers[i];
        }
        return result;
    }

    /*@ normal_behavior
      @ requires idx <= arr.length && idx >= 0;
      @ ensures \result == arr.length - idx;
      @ measured_by arr.length - idx;
      @*/
    public static int lengthFrom(int[] arr, int idx) {
        if (idx == arr.length) {
            return 0;
        } else {
            ++idx;
            /*@ return_behavior
              @ requires arr != null;
              @ requires \old(arr.length - (idx + 1)) == arr.length - idx;
              @ requires \old(arr.length - idx) > 0;
              @ requires idx <= arr.length && idx >= 0;
              @ returns \result == arr.length - idx + 1;
              @ measured_by arr.length - idx;
              @*/
            {
                return lengthFrom(arr, idx) + 1;
            }
        }
    }
}