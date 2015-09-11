public class ma{

    private /*@ spec_public non_null@*/ int[] the_array;
    //@ public invariant the_array != null  && 0 <= the_array.length && (\typeof(the_array) == \type(int[])) ;

   
      
    /*@initially (\forall  int I;
      @ getElementAt(I) == -1 &&
      @ getSize() == 0);
     @*/
   
    //@ assignable the_array;
    //@ ensures the_array != null && the_array.length == 0 && (\typeof(the_array) == \type(int[])) ;
     public ma(){
    	 the_array = new int[0];
     }

        /*@ requires (( (I < the_array.length ) && (I >= 0 )  && (the_array != null) && (the_array[I] != 0)  ));
          @ ensures  \result == the_array[I] ;
          @ also
          @ requires ( !( (I < the_array.length ) && (I >= 0 )  && (the_array != null) && (the_array[I] != 0)  ));
          @ ensures \result == -1; 
          @
         */
        public /*@ pure @*/ int getElementAt(int I){
            if ( (I < the_array.length ) && (I >= 0 ) 
                    && (the_array != null) && (the_array[I] != 0)  )
                return the_array[I] ;
            else return -1 ;
        }
       
        /*@ requires  (the_array != null);
         @ ensures \result == the_array.length ;
         @ also
         @ requires !(the_array != null) ;
         @ ensures \result == 0;
         */
        public /*@ pure @*/ int getSize(){
            if (the_array != null)
                return the_array.length;
            else return 0;
        }

        /*@  normal_behavior
        @ ensures
        @ (J >= 0 && (getSize() == 0)) ==>
        @ \result == true ;
        @ also
        @ ensures
        @ (!(J >= 0 && (getSize() == 0))) ==>
        @ \result == false ;
        @*/
        public /*@ pure @*/  boolean csetSize(int J){
            if((J>=0) && (getSize() == 0))
                return true;
            else return false;
        }

       

        /*@  normal_behavior
        @ ensures
        @  \result ==  (I >= 0 && ((0 < getSize()) &&
        @             (V > 0 && ((getElementAt(I-1) <= V) && ((I + 1 < getSize())
        @                     && ((getElementAt(I+1) >= 0) && ((getElementAt(I+1) > V)
        @                     && (I < getSize())))))))) ;
        @*/
        public/*@ pure @*/  boolean csetElementAt(int I, int V){
            return (I >= 0 && ((0 < getSize()) &&
                     (V > 0 && ((getElementAt(I-1) <= V) && ((I + 1 < getSize())
                             && ((getElementAt(I+1) >= 0) && ((getElementAt(I+1) > V)
                             && (I < getSize()))))))));
           
        }

        /*@ ensures
        @ (csetSize(J) ==>
        @ getSize() == J) &&
        @ (\forall  int I;
        @ (csetSize(J) ==>
        @ getElementAt(I ) == \old(getElementAt(I))));
        @*/
        public void setSize(int J){
            if( csetSize(J)  )
                the_array = new int[J];
        }


        /*@
        @ requires csetElementAt(I, V) ;
        @ ensures  getSize() == \old(getSize());
        @ also
        @ requires csetElementAt(I, V);
        @ ensures
        @ getElementAt(I) == V ;
        @*/
        public void setElementAt(int I, int V){
            if (csetElementAt(I, V)  && the_array!=null){
                the_array[I] = V;
            }//end of if   
        }


       


}