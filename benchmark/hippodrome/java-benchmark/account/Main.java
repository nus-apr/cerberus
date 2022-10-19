package account;

import com.facebook.infer.annotation.*;
import java.io.*;

/**
 * Title:        Software Testing course
 * Description:  The goal of the exercise is implementing a  program which demonstrate  a parallel bug.
 * In the exercise we have two accounts.The program enable tranfering  money from one account to the other.Although the functions were defended by locks (synchronize) there exists an interleaving which we'll experience a bug.
 * Copyright:    Copyright (c) 2003
 * Company:      Haifa U.
 * @author Zoya Shaham and  Maya Maimon
 * @version 1.0
 */

public class Main {


  public static void main(String[] args) {

      try{
	ManageAccount.num = 10;
          ManageAccount[] bank=new ManageAccount[ManageAccount.num];
          String[] accountName={new String("A"),new String("B"),new String("C"),new String("D"),new String("E"),
                                                       new String("F"),new String("G"),new String("H"),new String("I"),new String("J"),};
          for (int j=0;j<ManageAccount.num;j++){
              bank[j]=new ManageAccount(accountName[j],100);
              ManageAccount.accounts[j].print();;//print it
              }


 //start the threads
        for (int k=0;k<ManageAccount.num;k++){
              bank[k].start();
              }




 // wait until all are finished
        for (int k=0;k<ManageAccount.num;k++){
              bank[k].join();
              }
        //ManageAccount.printAllAccounts();

        //updating the output file
        boolean bug = false;
	//flags which will indicate the kind of the bug
        for (int k=0;k<ManageAccount.num;k++){
            //System.out.println("account "+k+" has $"+ManageAccount.accounts[k].amount);
            if(ManageAccount.accounts[k].amount<300){
                          bug=true;
                          }
            else if(ManageAccount.accounts[k].amount>300){
                          bug=true;
                          }
        }

        if(bug) 
		throw new RuntimeException("bug found");

        } catch(InterruptedException e){
        }

  }//end of function main
}//end of class Main
