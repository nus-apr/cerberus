package sg.edu.nus.comp.cerberus;

import org.junit.Test;
import static org.junit.Assert.assertEquals;

public class Test5{


	@Test
	public void test4(){
		LeapYear a = new LeapYear();
		assertEquals(false, a.LeapChecking(1579559530));
	}
}