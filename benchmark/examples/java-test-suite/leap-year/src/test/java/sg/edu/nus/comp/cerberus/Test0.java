package sg.edu.nus.comp.evorepair;

import org.junit.Test;
import static org.junit.Assert.assertEquals;

public class Test0{

	@Test
	public void test0(){
		LeapYear a = new LeapYear();
		assertEquals(false, a.LeapChecking(1416128883));
	}

}