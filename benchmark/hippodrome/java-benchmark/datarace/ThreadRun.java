package datarace;

public class ThreadRun extends Thread{

	CustomerInfo ci;
	
	public ThreadRun(CustomerInfo ci) {
		this.ci = ci;
	}


	@Override
	public void run() {
		ci.deposit(1, 50);
//		ci.withdraw(1, 20);
	}
	
}
