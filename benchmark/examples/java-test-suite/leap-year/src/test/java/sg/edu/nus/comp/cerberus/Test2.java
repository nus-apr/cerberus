package sg.edu.nus.comp.evorepair;

import org.junit.Test;
import static org.junit.Assert.assertEquals;

public class Test2{

	@Test
	public void test2(){
		LeapYear a = new LeapYear();
		assertEquals(true, a.LeapChecking(100659200));
	}
}