package linkedlist;

//BugTester.java
//implements two threads that are building the same list
//and are conflicting each other next pointer in the latency between
//fetch and write back

public class BugTester
{
	public static void main(String[] args)
	{
		int builders = 2;
		int maxsize = 6;

                if (args != null && args.length == 2) {
		  builders = Integer.parseInt(args[0]);
		  maxsize = Integer.parseInt(args[1]);
		}

                int step = maxsize/builders;
		Thread[] threads = new Thread[builders];

		try {
			MyLinkedList mlst = new MyLinkedList(maxsize);
			MyListBuilder mlist = null;

			for (int i = 0; i < builders; i++) {
			  mlist = new MyListBuilder(
					       mlst,i*step,(i+1)*step,true);
			  threads[i] = new Thread(mlist);
			}

			for (int i = 0; i < builders; i++) 
				threads[i].start();

			for (int i = 0; i < builders; i++) 
				threads[i].join();


			mlist.print();			//prints results to output file

			mlist.empty();			//empties list
		} catch (InterruptedException e) {
			throw new RuntimeException("interrupted exception");
		}

	}


}

