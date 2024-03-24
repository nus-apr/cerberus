package sg.edu.nus.comp.evorepair;

import org.junit.Test;
import static org.junit.Assert.assertEquals;

public class Test7{

	@Test
	public void test7(){
		LeapYear a = new LeapYear();
		assertEquals(false, a.LeapChecking(739513900));
	}
}