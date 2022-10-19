  package account;
  import com.facebook.infer.annotation.*;  
  /**  
   * Title:        Software Testing course  
   * Description:  The goal of the exercise is implementing a  program which demonstrate  a parallel bug.  
   * In the exercise we have two accounts.The program enable tranfering  money from one account to the other.Although the functions were defended by locks (synchronize) there exists an interleaving which we'll experience a bug.  
   * Copyright:    Copyright (c) 2003  
   * Company:      Haifa U.  
   * @author Maya Maimon  
   * @version 1.0  
   */  
  @ThreadSafe  
  public class ManageAccount extends Thread {
    Account account;  
    static Account[] accounts=new Account[10] ;//we may add more later to increase the parallelism level  
    static int num=2;//the number of the accounts  
    static int accNum=0;//index to insert the next account  
    int i;//the index  
    
    public ManageAccount(String name,double amount) {  
        account=new Account(name,amount);  
        i=accNum;
        accounts[i]=account;
        accNum=(accNum+1)%num; //the next index in a cyclic order
    }  
    
    public void run(){  
    account.depsite(300);  
    account.transfer(accounts[(i+1)%num],10);
    account.depsite(10);
    account.transfer(accounts[(i+2)%num],10);  
    account.withdraw(20);  
    account.depsite(10);  
    account.transfer(accounts[(i+1)%num],10);  
    account.withdraw(100);
    }
    
    public void helper(){
        for (int j=0;j<num;j++){
            if( accounts[j]!=null){
                accounts[j].print();;//print it
            }
        }
    }

    public void printAllAccounts(){
            helper();
          }  
    
  }//end of class ManageAccount
