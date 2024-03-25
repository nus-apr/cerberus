package sg.edu.nus.comp.cerberus;

import org.junit.Test;
import static org.junit.Assert.assertEquals;

public class Test3{

	@Test
	public void test3(){
		LeapYear a = new LeapYear();
		assertEquals(false, a.LeapChecking(2106384300));
	}

}