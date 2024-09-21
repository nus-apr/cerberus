package sg.edu.nus.comp.cerberus;

import org.junit.Test;
import static org.junit.Assert.assertEquals;

public class Test6{

	@Test
	public void test6(){
		LeapYear a = new LeapYear();
		assertEquals(true, a.LeapChecking(1677721600));
	}
}