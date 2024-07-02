package cerberus;
import cerberus.Calculator;
import org.junit.Test;
import static org.junit.Assert.assertEquals;

public class Test0{

	@Test
	public void test0(){
		int res = Calculator.wrongAdd(0, 1);
		assertEquals(res, 1);
	}

}