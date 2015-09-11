public class bs_copy {

	private  /*@ spec_public non_null @*/ ma ma ;
	 // public invariant ma.the_array != null   ;
	

	
	//@ public non_null model int pivot_m ;
	//@ represents pivot_m  = pivot();

	//@ public non_null model int left_m ;
	//@ represents left_m  = left();
	
	
	//@ public non_null model int value_m ;
	//@ represents value_m  = value();
	
	//@ public non_null model int right_m ;
	//@ represents right_m  = right();
	
	//@ public non_null model boolean found_m ;
	//@ represents found_m  = found();
	
	//@ public non_null model int return_m ;
	//@ represents return_m  = toRetrun();
	
	//@ public non_null model ma array_m ;
	//@ represents array_m  = ar() ;
		
	
	
	
	public /*@ non_null */ int the_value = -1;
	public /*@ non_null */ int the_left = 0; 
	public /*@ non_null */ int the_right ;; 
	public /*@ non_null */ int the_pivot ; 
	public /*@ non_null */ boolean the_found =false; 
	public /*@ non_null */ int the_return = -1;
	
	
	//@ assignable ma, the_pivot, the_right;
    //@ ensures ma != null && ma.the_array!=null && 0 <= ma.the_array.length ;
	public bs_copy(){
		ma = new ma();
		the_pivot = ma.getSize()/2;
		the_right = ma.getSize();
	}
	
	
	
	/*@ modifies \nothing; 
	  @ ensures
	  @ \result == ma;
	 */
	public /*@ pure non_null @*/ ma ar(){ return ma ;}
	
	/*@ modifies \nothing;
	  @ ensures  
	  @ \result  == the_pivot ;
	  */
	public /*@ pure non_null @*/ int pivot(){return the_pivot; }
	
	/*@ modifies \nothing;
	 @  ensures
	 @  \result == the_value ;
	 */
	public /*@ pure non_null@*/ int value(){return the_value;}
	
	
	/*@ modifies \nothing;
	 @  ensures
	 @  \result == the_left ;
	*/
	public /*@ pure non_null@*/ int left(){return the_left;}
	
	/*@ modifies \nothing;
	 @ ensures
	 @  \result == the_right ;
	*/
	public /*@ pure non_null@*/ int right(){return the_right;}
	
	/*@ modifies \nothing;  
	@ ensures
	@  \result == the_found  ;
	*/
	public /*@ pure non_null@*/ boolean found(){return the_found ;} 
	
	/*@ modifies \nothing;
	@ ensures
	@  \result == the_return   ;
	*/
	public  /*@ pure non_null @*/ int toRetrun(){return the_return;}


	/*@ modifies \nothing;
	@ ensures
	@ \result == ((found()  ==  false)  &&  ((pivot() >= 0)  &&  (!((right()  ==  left()))  &&  ((left() >= 0)  &&  ((right() >= 0)  
	@  ))))) ;
	@*/
	public  /*@ pure non_null@*/ boolean csearchright(){
		return ((the_found  ==  false)  &&  (( the_pivot>= 0))  
				&& (right() != left())  &&  (left() >= 0)  && (right() >= 0) );
	}
	

	
	
	/*@ modifies \nothing;
	@ ensures
	@ \result == ((found()  ==  false)  &&  ((pivot() >= 0)  &&  (!((right()  ==  left()))  &&  ((left() >= 0)  &&  ((right() >= 0)  &&  (ar().getElementAt(pivot()) > value()))))))
	@ && pivot_m == \old(pivot_m) && left_m == \old(left_m) && right_m == \old(right_m)
	@ && value_m == \old(value_m) && return_m == \old(return_m) && found_m == \old(found_m);
	@*/
	public  /*@ pure non_null@*/ boolean csearchleft(){
		return ((found()  ==  false)  &&  ((pivot() >= 0)  &&  (!((right()  ==  left()))  
				&&  ((left() >= 0)  &&  ((right() >= 0)  
				&&  (ar().getElementAt(pivot()) > value()))))));
		
	}








	

	/*@ requires 
	  @ 	(found() == false) && 
	  @		( ar().getElementAt(pivot()) > value()) && 
	  @		( left() != right()) &&
	  @     (pivot()  >= 0) && 
	  @ 	(right() >= 0) && 
	  @ 	(left() >= 0) ;
	  @ ensures  
	  @   left() == left_m && pivot() == pivot_m && value() == value_m && found() == found_m
	  @  && toRetrun() == return_m && array_m == ar() 
	  @  && (\forall int i; ar().getElementAt(i) == array_m.getElementAt(i))==>
	  @		(right() == \old(pivot() -1)) && 
	  @		(left() == \old(left())) && 
	  @ 	(found() == (\old(ar().getElementAt( (pivot() -1 + left()) / 2))  == \old(value())) ) &&  
	  @ 	(pivot() == \old( (pivot() -1 + left()) / 2) ) &&
	  @  	( (\old(ar().getElementAt( (pivot() -1 + left()) / 2)))  == \old(value())  
	  @			==> toRetrun() == \old((pivot() -1 + left()) / 2) ) && 
	  @  	( (\old(ar().getElementAt( (pivot() -1 + left()) / 2)))  != \old(value())  
	  @			==> toRetrun() == -1 ) ;
	@*/ 
	public void  searchLeft(){
		if ( ( the_found == false) && ( ar().getElementAt(the_pivot) > the_value) 
				&& ( the_left != the_right)
				&&(ma != null)  && (the_pivot >= 0) && (the_left >= 0) && (the_right >= 0)	
		){
			the_right = the_pivot -1 ;
			
			
			if ( ar() != null && ar().getElementAt((the_pivot -1 + the_left) / 2) == the_value ){
				the_found = true ;
			}else{the_found = false ;}
			
			if( ar() != null && ar().getElementAt((the_pivot -1 + the_left) / 2) == value() ){
				the_return = (the_pivot -1 + the_left) / 2 ;
			}else{ the_return =  -1;}
			
			the_pivot = (the_pivot -1 + the_left) / 2 ;
		}
	}
	

	
	
	


	
	/*@ requires  csearchright();
	  @ ensures  
	  @   left() == left_m && pivot() == pivot_m && value() == value_m && found() == found_m
	  @  && toRetrun() == return_m && array_m == ar() 
	  @  && (\forall int i; ar().getElementAt(i) == array_m.getElementAt(i))==>
	@( left() == \old((1 + pivot()))) &&
	@( right() == \old(right())) &&
	@( found() == \old((ar().getElementAt((((pivot() + 1) + right())/ 2))  ==  value()))) &&
	@ pivot() == \old((((pivot() + 1) + right())/ 2)) &&
	@( \old((ar().getElementAt((((pivot() + 1) + right())/ 2))  ==  value())) ==> 
	@ toRetrun() == \old(((pivot() + 1) + ((right())/2 ))) ) &&
	@( \old((ar().getElementAt((((pivot() + 1) + right())/ 2))  !=  value())) ==> 
	@ toRetrun() == -1 ) &&
	@ value() == \old(value()) &&
	@( \forall int I;
	@ ar().getElementAt(I) ==\old(ar().getElementAt(I)) ) && 
	@ ar().getSize() ==\old(ar().getSize()) ;
	@*/
	public void searchright(){
		
		if( csearchright() ){
			if(ar().getElementAt((((pivot() + 1) + right())/ 2))  ==  value()){
				the_return = ((pivot() + 1) + ((right())/2 ));
			}else{
				the_return = -1;
			}
			
			the_left = pivot() +1;
			the_found = ar().getElementAt((((pivot() + 1) + right())/ 2))  ==  value();
			the_pivot = ((pivot() + 1) + right())/ 2;
		}//end of requires if
		
		
	}//end of searchRight
	
	
	
	
}



