package account;

//import java.lang.*;

import com.facebook.infer.annotation.*;

@ThreadSafe
public class Account {
    double amount;
    String  name;

    //constructor
  public Account(String nm,double amnt ) {
        amount=amnt;
        name=nm;
  }
  //functions
  synchronized  void depsite(double money){
      amount+=money;
      }

  synchronized  void withdraw(double money){
      amount-=money;
      }

  synchronized  void transfer(Account ac,double mn){
      amount-=mn;
      //System.out.println("ac.amount is $"+ac.amount);
      if (name.equals("D")) {
	System.out.println("unprotected");
            ac.amount += mn;//no aquire for the other lock!!
        //+= might cause problem --it is not atomic.
      } else {
	//System.out.println("protected");
	synchronized (ac) { ac.amount+=mn; }
      }
  }

 synchronized void print(){
  }

      }//end of class Acount
