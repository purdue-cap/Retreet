import java.util.*;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import java.util.logging.Logger;
import java.util.logging.FileHandler;
import java.util.logging.SimpleFormatter;

public class Block {
	public String id;		// unique block id
	public String text;
	public boolean call = false;	// true when it's a call block, false when it's a noncall block
	public String callname = null;			// contains the function name of the function the call block calls, null if it's not a call block
	public List<String> callseq = new LinkedList<String>();	// the call sequence of the call block, for example, call on n.left.right
	public Set<List<String>> readfield = new HashSet<List<String>>();	// read set of fields for this block
	public Set<List<String>> writefield = new HashSet<List<String>>();	// write set of fields for this block
	public Set<String> readvar = new HashSet<String>();	// read set of variables for this block
	public Set<String> writevar = new HashSet<String>();	// write set of variables for this block

	public Block(String id, String text) {
		this.id = id;
		this.text = text;
	}

	public void setId(String name) {
		this.id = name;
	}

	public void setText(String nodeText) {
		this.text = nodeText;
	}

	public void setCall() {
		this.call = true;
	}

	public void setCallname(String name) {
		this.callname = name;
	}

	public void setNoncall() {
		this.call = false;
	}

	public String getId() {
		return this.id;
	}

	public String getText() {
		return this.text;
	}

	public boolean getCallFlag() {
		return this.call;
	}

	public String getCallname() {
		return this.callname;
	}
}	