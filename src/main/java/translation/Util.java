/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package translation;

public class Util {

	public static String getPrefixWithoutLast(String input){
		if (input.length() > 0) {
			input = input.substring(0, input.length() - 1);
			int last_ = input.lastIndexOf('!');
			if (last_ != -1) {
				return input.substring(0,
						input.lastIndexOf('!') + 1);
			} else {
				return "";		}
		}
		return "";
	}
	
}
