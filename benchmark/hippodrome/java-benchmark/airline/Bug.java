package airline;

import java.io.FileOutputStream;
import com.facebook.infer.annotation.*;

/**
 * Created by IntelliJ IDEA.
 * User: amit rotstein I.D: 037698867
 * Date: Oct 17, 2003
 * Time: 1:02:13 PM
 * To change this template use Options | File Templates.
 */
@ThreadSafe
public  class Bug implements Runnable{

    static int  Num_Of_Seats_Sold =0;
    int         Maximum_Capacity, Num_of_tickets_issued;
    boolean     StopSales = false;
    Thread      threadArr[] ;
    FileOutputStream output;

    private String fileName;

    public Bug (String fileName, int size, int cushion){
        this.fileName = fileName;
	Num_of_tickets_issued = size;   
        Maximum_Capacity = Num_of_tickets_issued - cushion;
        threadArr = new Thread[Num_of_tickets_issued];
        /**
         * starting the selling of the tickets:
         * "StopSales" indicates to the airline that the max capacity
         * was sold & that they should stop issuing tickets
         */
        for( int i=0; i < Num_of_tickets_issued; i++) {
           threadArr[i] = new Thread (this) ;
           /**
            * first the airline is checking to see if it's agents had
            * sold all the seats:
            */
            if( StopSales ){
                 Num_Of_Seats_Sold--;
                 break;
            }
            /**
             * THE BUG : StopSales is updated by the selling posts 
             * (public void run() ), and by the time it is updated
             * more tickets then are allowed to be are sold by other
             * threads that are still running
             */
            threadArr[i].start();  // "make the sale !!!"
         }

         if (Num_Of_Seats_Sold > Maximum_Capacity)
             throw new RuntimeException("bug found");
     }
   /**
    * the selling post:
    * making the sale & checking if limit was reached (and updating
    * "StopSales" ),
    */
    public void run() {
        Num_Of_Seats_Sold++;                       // making the sale
        if (Num_Of_Seats_Sold > Maximum_Capacity)  // checking
            StopSales = true;                      // updating
    }
}



