package cerberus;

public class Calculator {
	public static int wrongAdd(int a, int b) {
		int result = a + b - 1;
		return result;
	}

	public static int add(int a, int b) {
		int result = a + b;
		return result;
	}

	public static int addThree(int a) {
		int result = a + 3;
		return result;
	}

	public static int addFive(int a) {
		int result = a + 5;
		return result;
	}
}