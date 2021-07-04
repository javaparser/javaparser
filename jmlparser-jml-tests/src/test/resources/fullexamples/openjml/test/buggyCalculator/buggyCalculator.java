// This was a problem with SMT encoding of characters, now fixed.
public class buggyCalculator {


  //@ requires operator == '+' || operator == '*' || operator == '-' || operator == '/' || operator == '%' || operator == '&' || operator == '|' || operator == '^';
    //@{|
      //@ requires operator == '+';
      //@ requires num1 + num2 <= Integer.MAX_VALUE;
      //@ requires num1 + num2 >= Integer.MIN_VALUE;
      //@ ensures \result == num1 + num2;

      //@ also

      //@ requires operator == '*'; 
      //@ requires num1 * num2 <= Integer.MAX_VALUE;
      //@ requires num1 * num2 >= Integer.MIN_VALUE;
      //@ ensures \result == num1 * num2;

      //@ also

      //@ requires operator == '-'; 
      //@ requires num1 - num2 <= Integer.MAX_VALUE;
      //@ requires num1 - num2 >= Integer.MIN_VALUE;
      //@ ensures \result == num1 - num2;

      //@ also

      //@ requires operator == '/'; 
      //@ requires num2 != 0;
      //@ requires num1 / num2 <= Integer.MAX_VALUE;
      //@ requires num1 / num2 >= Integer.MIN_VALUE;
      //@ ensures \result == (num1 / num2);

      //@ also

      //@ requires operator == '%'; 
      //@ requires num2 != 0;
      //@ requires num1 % num2 <= Integer.MAX_VALUE;
      //@ requires num1 % num2 >= Integer.MIN_VALUE;
      //@ ensures \result == (num1 % num2);
/*
      //@ also

      //@ requires operator == '&';
      //@ ensures \result == (num1 & num2);

      //@ also

      //@ requires operator == '|';
      //@ ensures \result == (num1 | num2);

      //@ also

      //@ requires operator == '^';
      //@ ensures \result == (num1 ^ num2);
*/      //@ |}

      //@ also
      //@ requires operator != '+' && operator != '-' && operator != '*' && operator != '/' && operator != '%' && operator != '&' && operator != '^' && operator != '|';
      //@ ensures \result == -1;


      public int calculate(int num1, int num2, char operator) {

          int output;

      
          switch(operator)
          {
              case '+':
                  output = num1 + num2;
                  break;

              case '-':
                  output = num1 - num2;
                  break;

              case '*':
                  output = num1 * num2;
                  break;

              case '/':
                  output = num1 / num2;
          break;

          case '%':
                  output = num1 % num2;
                  break;

//          case '&':
//                  output = num1 & num2;
//                  break;
//          
//          case '|':
//                  output = num1 | num2;
//                  break;
//           
//              case '^':
//                  output = num1 ^ num2;
//              break;

              default:
                  System.err.println("You entered a not defined operator");
                  return -1;
          }
          return output;
      }
    //@ requires operator == '+' || operator == '*' || operator == '-' || operator == '/' || operator == '%' || operator == '&' || operator == '|' || operator == '^';
      //@{|
        //@ requires operator == '+';
        //@ requires num1 + num2 <= Integer.MAX_VALUE;
        //@ requires num1 + num2 >= Integer.MIN_VALUE;
        //@ ensures \result == num1 + num2;

        //@ also

        //@ requires operator == '*'; 
        //@ requires num1 * num2 <= Integer.MAX_VALUE;
        //@ requires num1 * num2 >= Integer.MIN_VALUE;
        //@ ensures \result == num1 * num2;

        //@ also

        //@ requires operator == '-'; 
        //@ requires num1 - num2 <= Integer.MAX_VALUE;
        //@ requires num1 - num2 >= Integer.MIN_VALUE;
        //@ ensures \result == num1 - num2;

        //@ also

        //@ requires operator == '/'; 
        //@ requires num2 != 0;
        //@ requires num1 / num2 <= Integer.MAX_VALUE;
        //@ requires num1 / num2 >= Integer.MIN_VALUE;
        //@ ensures \result == (num1 / num2);

        //@ also

        //@ requires operator == '%'; 
        //@ requires num2 != 0;
        //@ requires num1 % num2 <= Integer.MAX_VALUE;
        //@ requires num1 % num2 >= Integer.MIN_VALUE;
        //@ ensures \result == (num1 % num2);

        //@ also

        //@ requires operator == '&';
        //@ ensures \result == (num1 & num2);

        //@ also

        //@ requires operator == '|';
        //@ ensures \result == (num1 | num2);

        //@ also

        //@ requires operator == '^';
        //@ ensures \result == (num1 ^ num2);
        //@ |}

        //@ also
        //@ requires operator != '+' && operator != '-' && operator != '*' && operator != '/' && operator != '%' ;
        //@ ensures \result == -1;


        public int calculateBad(int num1, int num2, char operator) {

            int output;

        
            switch(operator)
            {
                case '+':
                    output = num1 - num2;
                    break;

                case '-':
                    output = num1 - num2;
                    break;

                case '*':
                    output = num1 * num2;
                    break;

                case '/':
                    output = num1 / num2;
                    break;

            case '%':
                    output = num1 % num2;
                    break;

            case '&':
                    output = num1 & num2;
                    break;
            
                 case '|':
                    output = num1 | num2;
                    break;
             
                case '^':
                    output = num1 ^ num2;
                break;

                default:
                    System.err.println("You entered a not defined operator");
                    return -1;
            }
            return output;
        }
}
