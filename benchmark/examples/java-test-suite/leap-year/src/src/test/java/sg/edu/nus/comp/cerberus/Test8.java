package sg.edu.nus.comp.cerberus;

import org.junit.Test;
import static org.junit.Assert.assertEquals;

public class Test8{
	@Test
	public void test8(){
		LeapYear a = new LeapYear();
		assertEquals(false, a.LeapChecking(724249387));
	}
}