package datarace;

public class Checker implements Runnable {
	private CustomerInfo ci;
	
	public boolean buggy;
	
	public Checker(CustomerInfo ci) {
		 this.ci = ci;
		 buggy = false;
	}
	
	public void run() {
		if (!ci.check(1, 50 * Main.THREAD_NUMBER)) {
			buggy = true;
		}
	}
}
