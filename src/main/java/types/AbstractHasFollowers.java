package types;

import java.util.ArrayList;
import tla2sany.semantic.SemanticNode;

public abstract class AbstractHasFollowers extends BType {

	public ArrayList<Object> followers;

	public AbstractHasFollowers(int t) {
		super(t);
		followers = new ArrayList<Object>();
	}

	public ArrayList<Object> getFollowers() {
		return followers;
	}

	public void addFollower(Object o) {
		// only (partial) untyped types need follower
		if (this.followers != null) {
			for (int i = 0; i < followers.size(); i++) {
				if (followers.get(i) == o)
					return;
			}
			followers.add(o);
		}

	}

	public void deleteFollower(Object o) {
		followers.remove(o);
	}

	public void deleteFollowers() {
		followers = null;
	}

	public void removeFollower(Object o) {
		followers.remove(o);
	}

	public String followersToString() {
		return followers.toString();
	}

	protected void setFollowersTo(BType o) {
		if (this.followers == null)
			return;
		for (int i = 0; i < this.followers.size(); i++) {

			Object follower = this.followers.get(i);
			if (follower instanceof SemanticNode) {
				((SemanticNode) follower).setToolObject(5, o);
				if (o instanceof AbstractHasFollowers) {
					((AbstractHasFollowers) o).addFollower(follower);
				}
			} else if (follower instanceof AbstractSymbol) {
				((AbstractSymbol) follower).setType(o);
			} else if (follower instanceof PowerSetType) {
				((PowerSetType) follower).setSubType(o);
			} else if (follower instanceof PairType) {
				PairType pair = ((PairType) follower);
				if (pair.getFirst() == this) {
					pair.setFirst(o);
				}
				if (pair.getSecond() == this) {
					pair.setSecond(o);
				}

			} else if (follower instanceof StructType) {
				((StructType) follower).setNewType(this, o);
			} else {
				throw new RuntimeException("Unknown follower type: "
						+ follower.getClass());
			}
		}
	}

}
