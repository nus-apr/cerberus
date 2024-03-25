package sg.edu.nus.comp.cerberus;

import org.junit.Test;
import static org.junit.Assert.assertEquals;

public class Test1{

	@Test
	public void test1(){
		LeapYear a = new LeapYear();
		assertEquals(true, a.LeapChecking(1694498816));
	}
}