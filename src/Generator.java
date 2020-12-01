import java.util.*;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import java.io.*;

public class Generator {
	RetreetExtractor unfused;
	RetreetExtractor fused;
	RetreetExtractor relation;
	PrintWriter writer;
	String filename;
	String currentPath = System.getProperty("user.dir");
	String filepath = currentPath + "//output//";

	public Generator(String filename, RetreetExtractor unfused) {
		this.filename = filename;
		this.unfused = unfused;
	}

	public Generator(String filename, RetreetExtractor unfused, RetreetExtractor fused, RetreetExtractor relation) {
		this.filename = filename;
		this.unfused = unfused;
		this.fused = fused;
		this.relation = relation;
	}

	public String getOr(List<String> store, String tabs, boolean newline) {
		String ret = "";
		for (int i = 0; i < store.size(); i++) {
			if (i == 0) {
				ret = ret + store.get(i);
			} else {
				if (newline) {
					ret = ret + "\n" + tabs + "| " + store.get(i);
				} else {
					ret = ret + tabs + " | " + store.get(i);
				}
			}
		}
		return ret;
	}

	public String getAnd(List<String> store, String tabs, boolean newline) {
		String ret = "";
		for (int i = 0; i < store.size(); i++) {
			if (i == 0) {
				ret = ret + store.get(i);
			} else {
				if (newline) {
					ret = ret + "\n" + tabs + "& " + store.get(i);
				} else {
					ret = ret + tabs + " & " + store.get(i);
				}
			}
		}
		return ret;
	}

	public String l(String prefix, String blockid, String varname) {
		if (blockid.equals("empty_set")) {
			return "empty_set";
		}
		return prefix + blockid + varname;
	}

	// generate argument list for predicates
	public String genarglist(String p, String var, List<String> list, boolean main) {
		// main function should have an unique blockid
		String arglist = "";
		if (main) {
			arglist = l(p, "main", var);
		} 
		for (String blockid : list) {
			if (arglist.equals("")) {
				arglist = l(p, blockid, var);
			} else {
				arglist = arglist + ", " + l(p, blockid, var);
			}
		}
		return arglist;
	}

	// generate mona file that checks the validity of fusion.
	public void genfuse() {
		if (unfused.funcs.size() > 4) {
			// if there are many traversals to be fused, split disjuncts, generate several mona files
			genmultfuse();
		} else {
			// otherwise, generate one file.
			File file = new File(filepath + filename + ".mona");
			try {
				file.createNewFile();
			} catch (Exception fnfe) {
				System.out.println(fnfe);
			}
			try {
				writer = new PrintWriter(file);
			} catch (FileNotFoundException fnfe) {
				System.out.println(fnfe);
			}
			writer.println("ws2s;\n");
			genconfig("Configuration", "C", unfused);
			writer.println();
			genconfig("ConfigurationFused", "D", fused);
			writer.println();
			genordered("Ordered", "Configuration", "C", unfused, null);
			writer.println();
			genordered("OrderedFused", "ConfigurationFused", "D", fused, null);
			writer.println();
			gendependence("Ordered", "C", unfused);
			writer.println();
			genconvert("C", "D", unfused.getRdcdBlocklist(), fused.getRdcdBlocklist(), relation, false);
			writer.println();
			genfuseconstraint("OrderedFused", "C", "D", unfused.getRdcdBlocklist(), fused.getRdcdBlocklist());
			writer.println();
			writer.close();
		}
	}

	public void genpara() {
		File file = new File(filepath + filename + ".mona");
		try {
			file.createNewFile();
		} catch (Exception fnfe) {
			System.out.println(fnfe);
		}
		try {
			writer = new PrintWriter(file);
		} catch (FileNotFoundException fnfe) {
			System.out.println(fnfe);
		}
		writer.println("ws2s;\n");
		genfuncconfig("Configuration_A", "C", unfused, unfused.parallel.get(0));
		writer.println();
		genfuncconfig("Configuration_B", "D", unfused, unfused.parallel.get(1));
		writer.println();
		genParaDependence("C", "D", unfused, unfused.parallel.get(0), unfused.parallel.get(1));
		writer.println();
		genparaconstraint("Configuration_A", "Configuration_B", "C", "D", unfused);
		writer.println();
		writer.close();
	}

	public void genfuncconfig(String configname, String p, RetreetExtractor extractor, String funcid) {
		List<String> funcs = new LinkedList<String>(extractor.getFuncs());
		Map<String, Block> rblocks = new LinkedHashMap<String, Block>(extractor.getRdcdBlocks());
		List<String> rblocklist = new LinkedList<String>(extractor.getRdcdBlocklist());
		Set<String> calls = new HashSet<String>(extractor.getCalls());
		Set<String> rnoncalls = new HashSet<String>(extractor.getRdcdNoncalls());
		Map<String, List<String>> rfuncBlock = new LinkedHashMap<String, List<String>>(extractor.getRdcdFuncBlock());
		List<String> ortmp = new LinkedList<String>();
		List<String> andtmp = new LinkedList<String>();
		List<String> innerandtmp = new LinkedList<String>();

		Map<String, Set<String>> callmap = extractor.getCallMap();
		// calls.removeAll(rfuncBlock.get("main"));
		// calls.add(funcid);
		// rnoncalls.removeAll(rfuncBlock.get("main"));
		// rblocklist.removeAll(rfuncBlock.get("main"));
		// rblocklist.add(funcid);
		// funcs.remove("main");
		for (String func : extractor.getFuncs()) {
			String funcname = rblocks.get(funcid).getCallname();
			if (!callmap.get(funcname).contains(func)) {
				calls.removeAll(rfuncBlock.get(func));
				rnoncalls.removeAll(rfuncBlock.get(func));
				rblocklist.removeAll(rfuncBlock.get(func));
				funcs.remove(func);
			}
		}
		calls.add(funcid);
		rblocklist.add(funcid);

		String v = "x";
		// first the predicate signature
		writer.print("pred " + configname + "(var1 " + v + ", var2 ");
		writer.print(genarglist(p, v, rblocklist, false));
		writer.println(") = ");

		// root should be in main block
		writer.println("\t(root in " + l(p, funcid, v) + ")");

		// other nodes should not in blocks of main function
		writer.println("\t& ~(ex1 v where v ~= root: v in " + l(p, funcid, v) + ")");

		// non-leaf nodes should be calls, first consider the special case: main function, then call in calls
		writer.println("\t& (all1 u where u ~= x: (");
		writer.print("\t\t\t");
		// for (String id : rfuncBlock.get("main")) {
		// 	// for every block b in blocks of func
		// 	if (calls.contains(id)) {
		// 		// check if b is also in calls, which means b is a call block
		// 		List<String> callseq = rblocks.get(id).callseq;
		// 		String seq = "";
		// 		for (int i = 0; i < callseq.size(); i++) {
		// 			if (i == 0) {
		// 				seq = seq + "u";
		// 			} else {
		// 				if (callseq.get(i).equals("left") || callseq.get(i).equals("next")) {
		// 					seq = seq + ".0";
		// 				} else if (callseq.get(i).equals("right")) {
		// 					seq = seq + ".1";
		// 				}
		// 			}
		// 		}
		// 		ortmp.add(seq + " in " + l(p, id, v));
		// 	}
		// }
		// andtmp.add("(u in " + l(p, "main", v) + " => " + "(" + getOr(ortmp, "", false) + ") )");
		// ortmp.clear();
		for (String callid : calls) {
			// node u is in a call block implies that
			// there are nodes (u itself or u.0, u.1 ...) in the blocks of the called function
			String funcname = rblocks.get(callid).getCallname();
			for (String id : rfuncBlock.get(funcname)) {
				// for every block b in blocks of func
				if (calls.contains(id)) {
					// check if b is also in calls, which means b is a call block
					List<String> callseq = rblocks.get(id).callseq;
					String seq = "";
					for (int i = 0; i < callseq.size(); i++) {
						if (i == 0) {
							seq = seq + "u";
						} else {
							if (callseq.get(i).equals("left") || callseq.get(i).equals("next")) {
								seq = seq + ".0";
							} else if (callseq.get(i).equals("right")) {
								seq = seq + ".1";
							}
						}
					}
					ortmp.add(seq + " in " + l(p, id, v));
				}
			}
			andtmp.add("(u in " + l(p, callid, v) + " => " + "(" + getOr(ortmp, "", false) + ") )");
			ortmp.clear();
		}
		writer.print(getAnd(andtmp, "\t\t\t", true));
		andtmp.clear();
		writer.println("\n\t\t\t)\n\t\t)");

		// if x is in a call, then x should be in one and only one of noncall blocks that correspond to that call
		// for every call in calls
		// find out the function that the call belongs to
		// find out the noncalls in that function
		// x should be in one of the noncalls.
		writer.print("\t& (");
		List<String> ncinfunc = new LinkedList<String>();
		for (String id : rfuncBlock.get("main")) {
			if (rnoncalls.contains(id)) {
				ncinfunc.add(id);
			}
		}
		for (int i = 0; i < ncinfunc.size(); i++) {
			innerandtmp.add(v + " in " + l(p, ncinfunc.get(i), v));
			for (int j = 0; j < ncinfunc.size(); j++) {
				if (i != j) {
					innerandtmp.add(v + " notin " + l(p, ncinfunc.get(j), v));
				}
			}
			ortmp.add("(" + getAnd(innerandtmp, "", false) + ")");
			innerandtmp.clear();
		}
		if (ncinfunc.size() > 0) {
			andtmp.add("(" + v + " in " + l(p, "main", v) + " => " + getOr(ortmp, "", false) + ")");
		}
		ncinfunc.clear();
		ortmp.clear();
		for (String callid : calls) {
			String funcname = rblocks.get(callid).getCallname();
			for (String id : rfuncBlock.get(funcname)) {
				if (rnoncalls.contains(id)) {
					ncinfunc.add(id);
				}
			}
			for (int i = 0; i < ncinfunc.size(); i++) {
				innerandtmp.add(v + " in " + l(p, ncinfunc.get(i), v));
				for (int j = 0; j < ncinfunc.size(); j++) {
					if (i != j) {
						innerandtmp.add(v + " notin " + l(p, ncinfunc.get(j), v));
					}
				}
				ortmp.add("(" + getAnd(innerandtmp, "", false) + ")");
				innerandtmp.clear();
			}
			ncinfunc.clear();
			andtmp.add("(" + v + " in " + l(p, callid, v) + " => " + getOr(ortmp, "", false) + ")");
			ortmp.clear();
		}
		writer.print(getAnd(andtmp, "\t\t", true));
		andtmp.clear();
		writer.println("\n\t\t)");

		// for node v which is not x, v should not in any of noncall blocks
		writer.println("\t& (all1 v where v ~= x:");
		for (String noncallid : rnoncalls) {
			andtmp.add("v notin " + l(p, noncallid, v));
		}
		writer.print("\t\t(");
		writer.print(getAnd(andtmp, "", false));
		andtmp.clear();
		writer.print(")");
		writer.println("\n\t\t)");

		// if x is in one of noncall blocks, then x is not in any other noncall block
		if (rnoncalls.size() > 1) {
			writer.print("\t& (");
			for (String i : rnoncalls) {
				for (String j : rnoncalls) {
					if (!i.equals(j)) {
						innerandtmp.add(v + " notin " + l(p, j, v));
					}

				}
				andtmp.add("(" + v + " in " + l(p, i, v) + " => (" + getAnd(innerandtmp, "", false) + "))");
				innerandtmp.clear();
			}
			writer.print(getAnd(andtmp, "\t\t", true));
			andtmp.clear();
			writer.println("\n\t\t)");
		}

		// for node z which is not root, 
		// if z is in call block that is calling on children nodes, 
		// then there exist w where w is the parent of z
		writer.println("\t& (all1 z where z ~= root:");
		// for every call in calls, find out their corresponding block
		// check if the call is calling on child node
		// convert the callseq to "0" or "1" ...
		for (String callid : calls) {
			List<String> callseq = rblocks.get(callid).callseq;
			if (callseq.size() > 1) {
				String seq = "";
				for (int i = 1; i < callseq.size(); i++) {
					if (callseq.get(i).equals("left") || callseq.get(i).equals("next")) {
						seq = seq + ".0";
					} else if (callseq.get(i).equals("right")) {
						seq = seq + ".1";
					}
				}
				String zinLabel = "z in " + l(p, callid, v);
				andtmp.add("(" + zinLabel + " => ex1 w: w" + seq + " = z)");
			}
		}
		writer.print("\t\t");
		writer.print(getAnd(andtmp, "\t\t", true));
		andtmp.clear();
		writer.print("\n\t\t)");

		// configuration comes to an end
		writer.println(";");

	}

	public void genParaDependence(String p1, String p2, RetreetExtractor extractor, String para1, String para2) {
		Map<String, Set<String>> callmap = extractor.getCallMap();

		List<String> p1funcs = new LinkedList<String>(extractor.getFuncs());
		Map<String, Block> p1rblocks = new LinkedHashMap<String, Block>(extractor.getRdcdBlocks());
		List<String> p1rblocklist = new LinkedList<String>(extractor.getRdcdBlocklist());
		Set<String> p1calls = new HashSet<String>(extractor.getCalls());
		Set<String> p1rnoncalls = new HashSet<String>(extractor.getRdcdNoncalls());
		Map<String, List<String>> p1rfuncBlock = new LinkedHashMap<String, List<String>>(extractor.getRdcdFuncBlock());
		for (String func : extractor.getFuncs()) {
			String funcname = p1rblocks.get(para1).getCallname();
			if (!callmap.get(funcname).contains(func)) {
				p1calls.removeAll(p1rfuncBlock.get(func));
				p1rnoncalls.removeAll(p1rfuncBlock.get(func));
				p1rblocklist.removeAll(p1rfuncBlock.get(func));
				p1funcs.remove(func);
			}
		}
		p1calls.add(para1);
		p1rblocklist.add(para1);

		List<String> p2funcs = new LinkedList<String>(extractor.getFuncs());
		Map<String, Block> p2rblocks = new LinkedHashMap<String, Block>(extractor.getRdcdBlocks());
		List<String> p2rblocklist = new LinkedList<String>(extractor.getRdcdBlocklist());
		Set<String> p2calls = new HashSet<String>(extractor.getCalls());
		Set<String> p2rnoncalls = new HashSet<String>(extractor.getRdcdNoncalls());
		Map<String, List<String>> p2rfuncBlock = new LinkedHashMap<String, List<String>>(extractor.getRdcdFuncBlock());
		for (String func : extractor.getFuncs()) {
			String funcname = p2rblocks.get(para2).getCallname();
			if (!callmap.get(funcname).contains(func)) {
				p2calls.removeAll(p2rfuncBlock.get(func));
				p2rnoncalls.removeAll(p2rfuncBlock.get(func));
				p2rblocklist.removeAll(p2rfuncBlock.get(func));
				p2funcs.remove(func);
			}
		}
		p2calls.add(para2);
		p2rblocklist.add(para2);

		List<String> ortmp = new LinkedList<String>();
		List<String> andtmp = new LinkedList<String>();

		String x = "x";
		String y = "y";

		// first the predicate signature
		writer.print("pred Dependence(var1 " + x + ", " + y + ", var2 ");
		writer.print(genarglist(p1, x, p1rblocklist, false));
		writer.print(", ");
		writer.print(genarglist(p2, y, p2rblocklist, false));
		writer.println(") = ");

		// list the dependence
		// for every noncall block, find out the write set
		// for each variable in the write set, find the other noncall block that is reading or writing to that variable
		// for each field in the write set, find out the callseq, find the other noncall block that is reading or writing to that field
		writer.print("\t (");
		for (String ncid : p1rnoncalls) {
			Block nc = p1rblocks.get(ncid);
			for (String otherncid : p2rnoncalls) {
				Block othernc = p2rblocks.get(otherncid);
				// if (!otherncid.equals(ncid)) {
					// for each variable in the write set, find the other noncall block that is reading or writing to that variable
					for (String v : nc.writevar) {
						for (String writev : othernc.writevar) {
							if (v.equals(writev)) {
								andtmp.add(x + " in " + l(p1, ncid, x));
								andtmp.add(y + " in " + l(p2, otherncid, y));
								andtmp.add(x + " = " + y);
								if (!ortmp.contains("(" +  getAnd(andtmp, "", false)  + ")")) {
									ortmp.add("(" +  getAnd(andtmp, "", false)  + ")");
								}
								andtmp.clear();
							}
						}
						for (String readv : othernc.writevar) {
							if (v.equals(readv)) {
								andtmp.add(x + " in " + l(p1, ncid, x));
								andtmp.add(y + " in " + l(p2, otherncid, y));
								andtmp.add(x + " = " + y);
								if (!ortmp.contains("(" +  getAnd(andtmp, "", false)  + ")")) {
									ortmp.add("(" +  getAnd(andtmp, "", false)  + ")");
								}
								andtmp.clear();
							}
						}
					}

					// for each field in the write set, find out the callseq, find the other noncall block that is reading or writing to that field
					for (List<String> field : nc.writefield) {
						String callseq = "";
						for (int i = 1; i < field.size() - 1; i++) {
							if (field.get(i).equals("left") || field.get(i).equals("next")) {
								callseq = callseq + ".0";
							} else if (field.get(i).equals("right")) {
								callseq = callseq + ".1";
							}
						}
						String fieldname = field.get(field.size() - 1);
						for (List<String> otherfield : othernc.writefield) {
							String othercallseq = "";
							for (int i = 1; i < otherfield.size() - 1; i++) {
								if (otherfield.get(i).equals("left") || otherfield.get(i).equals("next")) {
									othercallseq = othercallseq + ".0";
								} else if (otherfield.get(i).equals("right")) {
									othercallseq = othercallseq + ".1";
								}
							}
							String otherfieldname = otherfield.get(otherfield.size() - 1);
							if (fieldname.equals(otherfieldname)) {
								andtmp.add(x + " in " + l(p1, ncid, x));
								andtmp.add(y + " in " + l(p2, otherncid, y));
								andtmp.add(x + callseq + " = " + y + othercallseq);
								if (!ortmp.contains("(" +  getAnd(andtmp, "", false)  + ")")) {
									ortmp.add("(" +  getAnd(andtmp, "", false)  + ")");
								}
								andtmp.clear();
							}
						}
						for (List<String> otherfield : othernc.readfield) {
							String othercallseq = "";
							for (int i = 1; i < otherfield.size() - 1; i++) {
								if (otherfield.get(i).equals("left") || otherfield.get(i).equals("next")) {
									othercallseq = othercallseq + ".0";
								} else if (otherfield.get(i).equals("right")) {
									othercallseq = othercallseq + ".1";
								}
							}
							String otherfieldname = otherfield.get(otherfield.size() - 1);
							if (fieldname.equals(otherfieldname)) {
								andtmp.add(x + " in " + l(p1, ncid, x));
								andtmp.add(y + " in " + l(p2, otherncid, y));
								andtmp.add(x + callseq + " = " + y + othercallseq);
								if (!ortmp.contains("(" +  getAnd(andtmp, "", false)  + ")")) {
									ortmp.add("(" +  getAnd(andtmp, "", false)  + ")");
								}
								andtmp.clear();
							}
						}
					}
				// }
			}
		}
		writer.print(getOr(ortmp, "\t\t", true));
		ortmp.clear();
		writer.print(" )");

		// dependence comes to an end
		writer.println("\n\t;");

	}

	public void genparaconstraint(String config1, String config2, String p1, String p2, RetreetExtractor extractor) {
		Map<String, Set<String>> callmap = extractor.getCallMap();
		List<String> p1rblocklist = new LinkedList<String>(extractor.getRdcdBlocklist());
		List<String> p2rblocklist = new LinkedList<String>(extractor.getRdcdBlocklist());
		for (String func : extractor.getFuncs()) {
			String funcname = extractor.getRdcdBlocks().get(extractor.parallel.get(0)).getCallname();
			if (!callmap.get(funcname).contains(func)) {
				p1rblocklist.removeAll(extractor.getRdcdFuncBlock().get(func));
			}
		}
		p1rblocklist.add(extractor.parallel.get(0));
		for (String func : extractor.getFuncs()) {
			String funcname = extractor.getRdcdBlocks().get(extractor.parallel.get(1)).getCallname();
			if (!callmap.get(funcname).contains(func)) {
				p2rblocklist.removeAll(extractor.getRdcdFuncBlock().get(func));
			}
		}
		p2rblocklist.add(extractor.parallel.get(1));

		String x = "x";
		String y = "y";

		// declare var1 x, y first
		writer.println("var1 " + x + ", " + y + ";");
		writer.println();

		// declare var2
		writer.print("var2 ");
		writer.print(genarglist(p1, x, p1rblocklist, false));
		writer.print(", ");
		writer.print(genarglist(p2, y, p2rblocklist, false));
		writer.println(";");
		writer.println();

		// x is in A's config
		writer.print(config1 + "(" + x + ", ");
		writer.print(genarglist(p1, x, p1rblocklist, false));
		writer.println(");");
		writer.println();

		// y is in B's config
		writer.print(config2 + "(" + y + ", ");
		writer.print(genarglist(p2, y, p2rblocklist, false));
		writer.println(");");
		writer.println();

		// dependence x y
		writer.print("Dependence(" + x + ", " + y + ", ");
		writer.print(genarglist(p1, x, p1rblocklist, false));
		writer.print(", ");
		writer.print(genarglist(p2, y, p2rblocklist, false));
		writer.println(");");
		writer.println();

	}

	// generate configuration predicate 
	public void genconfig(String configname, String p, RetreetExtractor extractor) {
		List<String> funcs = extractor.getFuncs();
		Map<String, Block> rblocks = extractor.getRdcdBlocks();
		List<String> rblocklist = extractor.getRdcdBlocklist();
		Set<String> calls = extractor.getCalls();
		Set<String> rnoncalls = extractor.getRdcdNoncalls();
		Map<String, List<String>> rfuncBlock = extractor.getRdcdFuncBlock();
		List<String> ortmp = new LinkedList<String>();
		List<String> andtmp = new LinkedList<String>();
		List<String> innerandtmp = new LinkedList<String>();

		String v = "x";
		// first the predicate signature
		writer.print("pred " + configname + "(var1 " + v + ", var2 ");
		writer.print(genarglist(p, v, rblocklist, true));
		writer.println(") = ");

		// root should be in main block
		writer.println("\t(root in " + l(p, "main", v) + ")");

		// other nodes should not in blocks of main function
		if(!rfuncBlock.get("main").isEmpty()) {
			List<String> binMain = rfuncBlock.get("main");
			writer.print("\t& ~(ex1 v where v ~= root: ");
			for (int i = 0; i < binMain.size(); i++) {
				if (i == 0) {
					writer.print("v in " + l(p, binMain.get(i), v));
				} else {
					writer.print(" | v in " + l(p, binMain.get(i), v));
				}
			}
			writer.println(")");
		}

		// only one of blocks of main function should in root
		if (rfuncBlock.get("main").size() > 1) {
			// if there are more than one blocks in main function
			List<String> binmain = rfuncBlock.get("main");
			writer.print("\t& (");
			for (int i = 0; i < binmain.size(); i++) {
				if (i > 0) {
					writer.print("\t\t& ");
				}
				writer.print("(root in " + l(p, binmain.get(i), v) + " => (");
				List<String> store = new LinkedList<String>();
				for (int j = 0; j < binmain.size(); j++) {
					if (i != j) {
						store.add("root notin " + l(p, binmain.get(j), v));
					}
				}
				writer.print(getAnd(store, "", false));
				writer.print("))\n");
			}
			writer.println("\t\t)");
		}

		// non-leaf nodes should be calls, first consider the special case: main function, then call in calls
		writer.println("\t& (all1 u where u ~= x: (");
		writer.print("\t\t\t");
		for (String id : rfuncBlock.get("main")) {
			// for every block b in blocks of func
			if (calls.contains(id)) {
				// check if b is also in calls, which means b is a call block
				List<String> callseq = rblocks.get(id).callseq;
				String seq = "";
				for (int i = 0; i < callseq.size(); i++) {
					if (i == 0) {
						seq = seq + "u";
					} else {
						if (callseq.get(i).equals("left") || callseq.get(i).equals("next")) {
							seq = seq + ".0";
						} else if (callseq.get(i).equals("right")) {
							seq = seq + ".1";
						}
					}
				}
				ortmp.add(seq + " in " + l(p, id, v));
			}
		}
		andtmp.add("(u in " + l(p, "main", v) + " => " + "(" + getOr(ortmp, "", false) + ") )");
		ortmp.clear();
		for (String callid : calls) {
			// node u is in a call block implies that
			// there are nodes (u itself or u.0, u.1 ...) in the blocks of the called function
			String funcname = rblocks.get(callid).getCallname();
			for (String id : rfuncBlock.get(funcname)) {
				// for every block b in blocks of func
				if (calls.contains(id)) {
					// check if b is also in calls, which means b is a call block
					List<String> callseq = rblocks.get(id).callseq;
					String seq = "";
					for (int i = 0; i < callseq.size(); i++) {
						if (i == 0) {
							seq = seq + "u";
						} else {
							if (callseq.get(i).equals("left") || callseq.get(i).equals("next")) {
								seq = seq + ".0";
							} else if (callseq.get(i).equals("right")) {
								seq = seq + ".1";
							}
						}
					}
					ortmp.add(seq + " in " + l(p, id, v));
				}
			}
			andtmp.add("(u in " + l(p, callid, v) + " => " + "(" + getOr(ortmp, "", false) + ") )");
			ortmp.clear();
		}
		writer.print(getAnd(andtmp, "\t\t\t", true));
		andtmp.clear();
		writer.println("\n\t\t\t)\n\t\t)");

		// if x is in a call, then x should be in one and only one of noncall blocks that correspond to that call
		// for every call in calls
		// find out the function that the call belongs to
		// find out the noncalls in that function
		// x should be in one of the noncalls.
		writer.print("\t& (");
		List<String> ncinfunc = new LinkedList<String>();
		for (String id : rfuncBlock.get("main")) {
			if (rnoncalls.contains(id)) {
				ncinfunc.add(id);
			}
		}
		for (int i = 0; i < ncinfunc.size(); i++) {
			innerandtmp.add(v + " in " + l(p, ncinfunc.get(i), v));
			for (int j = 0; j < ncinfunc.size(); j++) {
				if (i != j) {
					innerandtmp.add(v + " notin " + l(p, ncinfunc.get(j), v));
				}
			}
			ortmp.add("(" + getAnd(innerandtmp, "", false) + ")");
			innerandtmp.clear();
		}
		if (ncinfunc.size() > 0) {
			andtmp.add("(" + v + " in " + l(p, "main", v) + " => " + getOr(ortmp, "", false) + ")");
		}
		ncinfunc.clear();
		ortmp.clear();
		for (String callid : calls) {
			String funcname = rblocks.get(callid).getCallname();
			for (String id : rfuncBlock.get(funcname)) {
				if (rnoncalls.contains(id)) {
					ncinfunc.add(id);
				}
			}
			for (int i = 0; i < ncinfunc.size(); i++) {
				innerandtmp.add(v + " in " + l(p, ncinfunc.get(i), v));
				for (int j = 0; j < ncinfunc.size(); j++) {
					if (i != j) {
						innerandtmp.add(v + " notin " + l(p, ncinfunc.get(j), v));
					}
				}
				ortmp.add("(" + getAnd(innerandtmp, "", false) + ")");
				innerandtmp.clear();
			}
			ncinfunc.clear();
			andtmp.add("(" + v + " in " + l(p, callid, v) + " => " + getOr(ortmp, "", false) + ")");
			ortmp.clear();
		}
		writer.print(getAnd(andtmp, "\t\t", true));
		andtmp.clear();
		writer.println("\n\t\t)");

		// for node v which is not x, v should not in any of noncall blocks
		writer.println("\t& (all1 v where v ~= x:");
		for (String noncallid : rnoncalls) {
			andtmp.add("v notin " + l(p, noncallid, v));
		}
		writer.print("\t\t(");
		writer.print(getAnd(andtmp, "", false));
		andtmp.clear();
		writer.print(")");
		writer.println("\n\t\t)");

		// if x is in one of noncall blocks, then x is not in any other noncall block
		if (rnoncalls.size() > 1) {
			writer.print("\t& (");
			for (String i : rnoncalls) {
				for (String j : rnoncalls) {
					if (!i.equals(j)) {
						innerandtmp.add(v + " notin " + l(p, j, v));
					}

				}
				andtmp.add("(" + v + " in " + l(p, i, v) + " => (" + getAnd(innerandtmp, "", false) + "))");
				innerandtmp.clear();
			}
			writer.print(getAnd(andtmp, "\t\t", true));
			andtmp.clear();
			writer.println("\n\t\t)");
		}

		// for node z which is not root, 
		// if z is in call block that is calling on children nodes, 
		// then there exist w where w is the parent of z
		writer.println("\t& (all1 z where z ~= root:");
		// for every call in calls, find out their corresponding block
		// check if the call is calling on child node
		// convert the callseq to "0" or "1" ...
		for (String callid : calls) {
			List<String> callseq = rblocks.get(callid).callseq;
			if (callseq.size() > 1) {
				String seq = "";
				for (int i = 1; i < callseq.size(); i++) {
					if (callseq.get(i).equals("left") || callseq.get(i).equals("next")) {
						seq = seq + ".0";
					} else if (callseq.get(i).equals("right")) {
						seq = seq + ".1";
					}
				}
				String zinLabel = "z in " + l(p, callid, v);
				andtmp.add("(" + zinLabel + " => ex1 w: w" + seq + " = z)");
			}
		}
		writer.print("\t\t");
		writer.print(getAnd(andtmp, "\t\t", true));
		andtmp.clear();
		writer.print("\n\t\t)");

		// configuration comes to an end
		writer.println(";");

	}

	public void genordered(String ordername, String configname, String p, RetreetExtractor extractor, List<String> callslist) {
		List<String> funcs = extractor.getFuncs();
		Map<String, Block> rblocks = extractor.getRdcdBlocks();
		List<String> rblocklist = extractor.getRdcdBlocklist();
		Set<String> calls = extractor.getCalls();
		Set<String> rnoncalls = extractor.getRdcdNoncalls();
		Map<String, List<String>> rfuncBlock = extractor.getRdcdFuncBlock();
		Map<String, List<String>> sequential = extractor.getSequential();
		List<String> ortmp = new LinkedList<String>();
		List<String> andtmp = new LinkedList<String>();

		String x = "x";
		String y = "y";

		// first the predicate signature
		writer.print("pred " + ordername + "(var1 " + x + ", " + y + ", var2 ");
		writer.print(genarglist(p, x, rblocklist, true));
		writer.print(", ");
		writer.print(genarglist(p, y, rblocklist, true));
		writer.println(") = ");

		// the labels for x and y should not be exactly the same
		andtmp.add(l(p, "main", x) + " = " + l(p, "main", y));
		for (String id : rblocklist) {
			andtmp.add(l(p, id, x) + " = " + l(p, id, y));
		}
		writer.println("\t~(" + getAnd(andtmp, "", false) + ")");
		andtmp.clear();

		// labels for x and y should be valid configurations
		writer.println("\t& " + configname + "(" + x + ", " + genarglist(p, x, rblocklist, true) + ")");
		writer.println("\t& " + configname + "(" + y + ", " + genarglist(p, y, rblocklist, true) + ")");

		// exists a node z which precede x and y in the tree, such that
			// every node v precede z, v in labels of x <=> v in labels of y
			// but labels of x and labels of y start to differ on z or children of z.
		// first part: every node v precede z, v in labels of x <=> v in labels of y
		writer.println("\t& (ex1 z: (z <= " + x + ") & (z <= " + y + ")");
		writer.println("\t\t& (all1 v:");
		writer.println("\t\t\t(v < z) => ");
		writer.print("\t\t\t(\t");
		andtmp.add("(v in " + l(p, "main", x) + " <=> v in " + l(p, "main", y) + ")");
		for (String id : rblocklist) {
			andtmp.add("(v in " + l(p, id, x) + " <=> v in " + l(p, id, y) + ")");
		}
		writer.print(getAnd(andtmp, "\t\t\t\t", true));
		andtmp.clear();
		writer.println(" )");
		writer.println("\t\t\t)");
		// second part: but labels of x and labels of y start to differ on z or children of z.
		writer.print("\t\t& (");
		// for every call block
		// find out the function which the call block actually calls
		// get the sequential relation corresponding to the function
		// list all possibilities
		List<String> seqmain = sequential.get("main");
		for (int i = 0; i < seqmain.size(); i++) {
			andtmp.add("(z in " + l(p, "main", x) + ")");
			andtmp.add("(z in " + l(p, "main", y) + ")");
			// get the block, check if it's a call
			Block iblock = rblocks.get(seqmain.get(i));
			if (iblock.getCallFlag()) {
				// if it is a call, get the callseq of the call, z.callseq should be in that call block
				List<String> icallseq = iblock.callseq;
				String iseq = "";
				for (int m = 1; m < icallseq.size(); m++) {
					if (icallseq.get(m).equals("left") || icallseq.get(m).equals("next")) {
						iseq = iseq + ".0";
					} else if (icallseq.get(m).equals("right")) {
						iseq = iseq + ".1";
					}
				}
				andtmp.add("(z" + iseq + " in " + l(p, seqmain.get(i), x) + ")");
			} else {
				// if it's noncall, z should be in the noncall block
				andtmp.add("(z in " + l(p, seqmain.get(i), x) + ")");
			}
			for (int j = i + 1; j < seqmain.size(); j++) {
				Block jblock = rblocks.get(seqmain.get(j));
				if (jblock.getCallFlag()) {
					// if it is a call, get the callseq of the call, z.callseq should be in that call block
					List<String> jcallseq = jblock.callseq;
					String jseq = "";
					for (int m = 1; m < jcallseq.size(); m++) {
						if (jcallseq.get(m).equals("left") || jcallseq.get(m).equals("next")) {
							jseq = jseq + ".0";
						} else if (jcallseq.get(m).equals("right")) {
							jseq = jseq + ".1";
						}
					}
					andtmp.add("(z" + jseq + " in " + l(p, seqmain.get(j), y) + ")");
				} else {
					// if it's noncall, z should be in the noncall block
					andtmp.add("(z in " + l(p, seqmain.get(j), y) + ")");
				}
				ortmp.add("(" + getAnd(andtmp, "\t\t\t\t", true) + ")");
				andtmp.remove(andtmp.size() - 1);
			}
			andtmp.clear();
		}
		List<String> iterlist = new LinkedList<String>(calls);
		if (callslist != null) {
			iterlist = new LinkedList<String>(callslist);
		}
		for (String callid : iterlist) {
			String funcname = rblocks.get(callid).getCallname();
			List<String> seqfunc = sequential.get(funcname);
			for (int i = 0; i < seqfunc.size(); i++) {
				andtmp.add("(z in " + l(p, callid, x) + ")");
				andtmp.add("(z in " + l(p, callid, y) + ")");
				// get the block, check if it's a call
				Block iblock = rblocks.get(seqfunc.get(i));
				if (iblock.getCallFlag()) {
					// if it is a call, get the callseq of the call, z.callseq should be in that call block
					List<String> icallseq = iblock.callseq;
					String iseq = "";
					for (int m = 1; m < icallseq.size(); m++) {
						if (icallseq.get(m).equals("left") || icallseq.get(m).equals("next")) {
							iseq = iseq + ".0";
						} else if (icallseq.get(m).equals("right")) {
							iseq = iseq + ".1";
						}
					}
					andtmp.add("(z" + iseq + " in " + l(p, seqfunc.get(i), x) + ")");
				} else {
					// if it's noncall, z should be in the noncall block
					andtmp.add("(z in " + l(p, seqfunc.get(i), x) + ")");
				}
				for (int j = i + 1; j < seqfunc.size(); j++) {
					Block jblock = rblocks.get(seqfunc.get(j));
					if (jblock.getCallFlag()) {
						// if it is a call, get the callseq of the call, z.callseq should be in that call block
						List<String> jcallseq = jblock.callseq;
						String jseq = "";
						for (int m = 1; m < jcallseq.size(); m++) {
							if (jcallseq.get(m).equals("left") || jcallseq.get(m).equals("next")) {
								jseq = jseq + ".0";
							} else if (jcallseq.get(m).equals("right")) {
								jseq = jseq + ".1";
							}
						}
						andtmp.add("(z" + jseq + " in " + l(p, seqfunc.get(j), y) + ")");
					} else {
						// if it's noncall, z should be in the noncall block
						andtmp.add("(z in " + l(p, seqfunc.get(j), y) + ")");
					}
					ortmp.add("(" + getAnd(andtmp, "\t\t\t\t", true) + ")");
					andtmp.remove(andtmp.size() - 1);
				}
				andtmp.clear();
			}
		}
		writer.print(getOr(ortmp, "\t\t\t", true));
		ortmp.clear();
		writer.println("\n\t\t\t)");
		writer.print("\t\t)");

		// ordered comes to an end
		writer.println(";");

	}

	public void gendependence(String ordername, String p, RetreetExtractor extractor) {
		List<String> funcs = extractor.getFuncs();
		Map<String, Block> rblocks = extractor.getRdcdBlocks();
		List<String> rblocklist = extractor.getRdcdBlocklist();
		Set<String> calls = extractor.getCalls();
		Set<String> rnoncalls = extractor.getRdcdNoncalls();
		Map<String, List<String>> rfuncBlock = extractor.getRdcdFuncBlock();
		List<String> ortmp = new LinkedList<String>();
		List<String> andtmp = new LinkedList<String>();

		String x = "x";
		String y = "y";

		// first the predicate signature
		writer.print("pred Dependence(var1 " + x + ", " + y + ", var2 ");
		writer.print(genarglist(p, x, rblocklist, true));
		writer.print(", ");
		writer.print(genarglist(p, y, rblocklist, true));
		writer.println(") = ");

		// x y should be ordered
		writer.println("\t" + ordername + "(" + x + ", " + y + ", " + genarglist(p, x, rblocklist, true) + ", " + genarglist(p, y, rblocklist, true) + ")");

		// list the dependence
		// for every noncall block, find out the write set
		// for each variable in the write set, find the other noncall block that is reading or writing to that variable
		// for each field in the write set, find out the callseq, find the other noncall block that is reading or writing to that field
		writer.print("\t & (");
		for (String ncid : rnoncalls) {
			Block nc = rblocks.get(ncid);
			for (String otherncid : rnoncalls) {
				Block othernc = rblocks.get(otherncid);
				if (!otherncid.equals(ncid)) {
					// for each variable in the write set, find the other noncall block that is reading or writing to that variable
					for (String v : nc.writevar) {
						for (String writev : othernc.writevar) {
							if (v.equals(writev)) {
								andtmp.add(x + " in " + l(p, ncid, x));
								andtmp.add(y + " in " + l(p, otherncid, y));
								andtmp.add(x + " = " + y);
								ortmp.add("(" +  getAnd(andtmp, "", false)  + ")");
								andtmp.clear();
							}
						}
						for (String readv : othernc.writevar) {
							if (v.equals(readv)) {
								andtmp.add(x + " in " + l(p, ncid, x));
								andtmp.add(y + " in " + l(p, otherncid, y));
								andtmp.add(x + " = " + y);
								ortmp.add("(" +  getAnd(andtmp, "", false)  + ")");
								andtmp.clear();
							}
						}
					}

					// for each field in the write set, find out the callseq, find the other noncall block that is reading or writing to that field
					for (List<String> field : nc.writefield) {
						String callseq = "";
						for (int i = 1; i < field.size() - 1; i++) {
							if (field.get(i).equals("left") || field.get(i).equals("next")) {
								callseq = callseq + ".0";
							} else if (field.get(i).equals("right")) {
								callseq = callseq + ".1";
							}
						}
						String fieldname = field.get(field.size() - 1);
						for (List<String> otherfield : othernc.writefield) {
							String othercallseq = "";
							for (int i = 1; i < otherfield.size() - 1; i++) {
								if (otherfield.get(i).equals("left") || otherfield.get(i).equals("next")) {
									othercallseq = othercallseq + ".0";
								} else if (otherfield.get(i).equals("right")) {
									othercallseq = othercallseq + ".1";
								}
							}
							String otherfieldname = otherfield.get(otherfield.size() - 1);
							if (fieldname.equals(otherfieldname)) {
								andtmp.add(x + " in " + l(p, ncid, x));
								andtmp.add(y + " in " + l(p, otherncid, y));
								andtmp.add(x + callseq + " = " + y + othercallseq);
								ortmp.add("(" +  getAnd(andtmp, "", false)  + ")");
								andtmp.clear();
							}
						}
						for (List<String> otherfield : othernc.readfield) {
							String othercallseq = "";
							for (int i = 1; i < otherfield.size() - 1; i++) {
								if (otherfield.get(i).equals("left") || otherfield.get(i).equals("next")) {
									othercallseq = othercallseq + ".0";
								} else if (otherfield.get(i).equals("right")) {
									othercallseq = othercallseq + ".1";
								}
							}
							String otherfieldname = otherfield.get(otherfield.size() - 1);
							if (fieldname.equals(otherfieldname)) {
								andtmp.add(x + " in " + l(p, ncid, x));
								andtmp.add(y + " in " + l(p, otherncid, y));
								andtmp.add(x + callseq + " = " + y + othercallseq);
								ortmp.add("(" +  getAnd(andtmp, "", false)  + ")");
								andtmp.clear();
							}
						}
					}
				}
			}
		}
		writer.print(getOr(ortmp, "\t\t", true));
		ortmp.clear();
		writer.print(" )");

		// dependence comes to an end
		writer.println("\t;");

	}

	public void genconvert(String pu, String pf, List<String> ufblck, List<String> fblck, RetreetExtractor extractor, boolean funcFlag) {
		Map<String, List<String>> unfused2fused = extractor.getUnfused2fused();
    	Map<String, List<String>> fused2unfused = extractor.getFused2unfused();
    	List<String> ortmp = new LinkedList<String>();
		List<String> andtmp = new LinkedList<String>();

		String x = "x";

		// first the predicate signature
		writer.print("pred Convert(var2 ");
		if (funcFlag) {
			writer.print(genarglist(pu, x, ufblck, false));
		} else {
			writer.print(genarglist(pu, x, ufblck, true));
		}
		writer.print(", ");
		if (funcFlag) {
			writer.print(genarglist(pf, x, fblck, false));
		} else {
			writer.print(genarglist(pf, x, fblck, true));
		}
		writer.println(") = ");

		// then for all node u, if u is in an unfused block, u should be in the corresponding fused block, and vice versa
		writer.println("\t(all1 u:");
		writer.print("\t\t( ");
		if (!funcFlag) {
			andtmp.add("(u in " + l(pu, "main", x) + " <=> u in " + l(pf, "main", x) + ")");
		}
		for (String unfusedid : ufblck) {
			List<String> fusedlist = unfused2fused.get(unfusedid);
			for (String fusedid : fusedlist) {
				if (fblck.contains(fusedid)) {
					ortmp.add("u in " + l(pf, fusedid, x));
				}
			}
			if (!ortmp.isEmpty()) {
				andtmp.add("(u in " + l(pu, unfusedid, x) + " => (" + getOr(ortmp, "", false) + "))");
			} else {
				andtmp.add("~(u in " + l(pu, unfusedid, x) + ")");
			}
			ortmp.clear();
		}
		for (String fusedid : fblck) {
			List<String> unfusedlist = fused2unfused.get(fusedid);
			for (String unfusedid : unfusedlist) {
				if (ufblck.contains(unfusedid)) {
					ortmp.add("u in " + l(pu, unfusedid, x));
				}
			}
			if (!ortmp.isEmpty()) {
				andtmp.add("(u in " + l(pf, fusedid, x) + " => (" + getOr(ortmp, "", false) + "))");
			} else {
				andtmp.add("~(u in " + l(pf, fusedid, x) + ")");
			}
			ortmp.clear();
		}
		writer.print(getAnd(andtmp, "\t\t", true));
		andtmp.clear();
		writer.print(" )");

		// convert comes to an end
		writer.println("\n\t);");

	}

	public void genfuseconstraint(String fusedorder, String pu, String pf, List<String> ufblck, List<String> fblck) {
		String x = "x";
		String y = "y";

		// declare var1 x, y first
		writer.println("var1 " + x + ", " + y + ";");
		writer.println();

		// declare var2
		writer.print("var2 ");
		writer.print(genarglist(pu, x, ufblck, true));
		writer.print(", ");
		writer.print(genarglist(pu, y, ufblck, true));
		writer.print(", ");
		writer.print(genarglist(pf, x, fblck, true));
		writer.print(", ");
		writer.print(genarglist(pf, y, fblck, true));
		writer.println(";");
		writer.println();

		// fusedordered y x
		writer.print(fusedorder + "(" + y + ", " + x + ", ");
		writer.print(genarglist(pf, y, fblck, true));
		writer.print(", ");
		writer.print(genarglist(pf, x, fblck, true));
		writer.println(");");
		writer.println();

		// dependence x y
		writer.print("Dependence(" + x + ", " + y + ", ");
		writer.print(genarglist(pu, x, ufblck, true));
		writer.print(", ");
		writer.print(genarglist(pu, y, ufblck, true));
		writer.println(");");
		writer.println();

		// convert labels of x from unfused to fused blocks
		writer.print("Convert(");
		writer.print(genarglist(pu, x, ufblck, true));
		writer.print(", ");
		writer.print(genarglist(pf, x, fblck, true));
		writer.println(");");
		writer.println();

		// convert labels of x from unfused to fused blocks
		writer.print("Convert(");
		writer.print(genarglist(pu, y, ufblck, true));
		writer.print(", ");
		writer.print(genarglist(pf, y, fblck, true));
		writer.println(");");
		writer.println();

	}

	public List<String> getFuncblocklist(String blockid, RetreetExtractor extractor) {
		// blocks that will be used when calling this function
		Map<String, Set<String>> callmap = extractor.getCallMap();
		List<String> p1rblocklist = new LinkedList<String>(extractor.getRdcdBlocklist());
		for (String func : extractor.getFuncs()) {
			String funcname = extractor.getRdcdBlocks().get(blockid).getCallname();
			if (!callmap.get(funcname).contains(func)) {
				p1rblocklist.removeAll(extractor.getRdcdFuncBlock().get(func));
			}
		}
		p1rblocklist.add(blockid);
		return p1rblocklist;
	}

	public List<String> getFuncNCblocklist(String funcname, RetreetExtractor extractor) {
		List<String> nclist = new LinkedList<String>();
		Map<String, Set<String>> callmap = extractor.getCallMap();
		for(String func : callmap.get(funcname)) {
			for (String block : extractor.rfuncBlock.get(func)) {
				if (extractor.rnoncalls.contains(block)) {
					nclist.add(block);
				}
			}
		}
		return nclist;
	}

	public List<String> genNCCrrspList(List<String> blocklist, RetreetExtractor relation, boolean uf2f) {
		List<String> crrlist = new LinkedList<String>();
		if (uf2f) {
			Map<String, List<String>> unfused2fused = relation.getUnfused2fused();
			for (String blockid : blocklist) {
				crrlist.addAll(unfused2fused.get(blockid));
			}
		} else {
			Map<String, List<String>> fused2unfused = relation.getFused2unfused();
			for (String blockid : blocklist) {
				crrlist.addAll(fused2unfused.get(blockid));
			}
		}
		return crrlist;
	}

	public List<String> genRplist(List<String> original, List<String> replace) {
		List<String> newlist = new LinkedList<String>(original);
		for (int i = 0; i < newlist.size(); i++) {
			if (replace.contains(newlist.get(i))) {
				newlist.set(i, "empty_set");
			}
		}
		return newlist;
	}

	public void gendiffordered(String ordered, String config1, String config2, String p, RetreetExtractor extractor, String func1, String func2) {
		String x = "x";
		String y = "y";

		// pred signature
		writer.print("pred " + ordered + "(var1 " + x + ", " + y + ", var2 ");
		writer.print(genarglist(p, x, getFuncblocklist(func1, extractor), false));
		writer.print(", ");
		writer.print(genarglist(p, y, getFuncblocklist(func2, extractor), false));
		writer.println(") = ");

		// x in func1
		writer.print("\t" + config1 + "(" + x + ", ");
		writer.print(genarglist(p, x, getFuncblocklist(func1, extractor), false));
		writer.println(")");

		// y in func2
		writer.print("\t& " + config2 + "(" + y + ", ");
		writer.print(genarglist(p, y, getFuncblocklist(func2, extractor), false));
		writer.println(")");

		writer.println("\t;");
	}

	public void gendifffuseconstr(String fusedorder, String ordered, String pu, String pf, String func1, String func2) {
		String x = "x";
		String y = "y";
		List<String> f1blck = getFuncblocklist(func1, unfused);
		List<String> f2blck = getFuncblocklist(func2, unfused);
		List<String> fblck = new LinkedList<String>(fused.rblocklist);
		List<String> f1nclist = getFuncNCblocklist(unfused.rblocks.get(func1).getCallname(), unfused);
		List<String> f2nclist = getFuncNCblocklist(unfused.rblocks.get(func2).getCallname(), unfused);
		List<String> f1ncCrrsplist = genNCCrrspList(f1nclist, relation, true);
		List<String> f2ncCrrsplist = genNCCrrspList(f2nclist, relation, true);

		// declare var1 x, y first
		writer.println("var1 " + x + ", " + y + ";");
		writer.println();

		// declare var2
		writer.print("var2 empty_set, ");
		writer.print(genarglist(pu, x, f1blck, false));
		writer.print(", ");
		writer.print(genarglist(pu, y, f2blck, false));
		writer.print(", ");
		List<String> fvars = new LinkedList<String>(fblck);
		fvars.removeAll(f1ncCrrsplist);
		writer.print(genarglist(pf, y, fvars, true));
		writer.print(", " + l(pu, "main", x));
		writer.println(";");
		writer.println();

		// define empty_set
		writer.println("all1 u: ~(u in empty_set);");
		writer.println();

		// fusedordered y x
		writer.print(fusedorder + "(" + y + ", " + x + ", ");
		fvars = genRplist(fblck, f1ncCrrsplist);
		writer.print(genarglist(pf, y, fvars, true));
		writer.print(", ");
		fvars = new LinkedList<String>(fblck);
		for (int i = 0; i < fvars.size(); i++) {
			List<String> tmplist = new LinkedList<String>();
			tmplist.add(fvars.get(i));
			fvars.set(i, genNCCrrspList(tmplist, relation, false).get(0));
		}
		fvars = genRplist(fvars, f2nclist);
		writer.print(genarglist(pu, x, fvars, true));
		writer.println(");");
		writer.println();

		// ordered x y
		writer.print(ordered + "(" + x + ", " + y + ", ");
		writer.print(genarglist(pu, x, f1blck, false));
		writer.print(", ");
		writer.print(genarglist(pu, y, f2blck, false));
		writer.println(");");
		writer.println();

		// dependence x y
		writer.print("Dependence(" + x + ", " + y + ", ");
		writer.print(genarglist(pu, x, f1blck, false));
		writer.print(", ");
		writer.print(genarglist(pu, y, f2blck, false));
		writer.println(");");
		writer.println();

		// convert
		writer.print("Convert(");
		writer.print(genarglist(pu, y, f2blck, false));
		writer.print(", ");
		fvars = genRplist(fblck, f1ncCrrsplist);
		writer.print(genarglist(pf, y, fvars, false));
		writer.println(");");
		writer.println();

	}

	public void genfuncordered(String ordername, String configname, String p, RetreetExtractor extractor, String funcid) {
		List<String> funcs = new LinkedList<String>(extractor.getFuncs());
		Map<String, Block> rblocks = new LinkedHashMap<String, Block>(extractor.getRdcdBlocks());
		List<String> rblocklist = new LinkedList<String>(extractor.getRdcdBlocklist());
		Set<String> calls = new HashSet<String>(extractor.getCalls());
		Set<String> rnoncalls = new HashSet<String>(extractor.getRdcdNoncalls());
		Map<String, List<String>> rfuncBlock = new LinkedHashMap<String, List<String>>(extractor.getRdcdFuncBlock());
		Map<String, List<String>> sequential = extractor.getSequential();
		List<String> ortmp = new LinkedList<String>();
		List<String> andtmp = new LinkedList<String>();

		Map<String, Set<String>> callmap = extractor.getCallMap();
		for (String func : extractor.getFuncs()) {
			String funcname = rblocks.get(funcid).getCallname();
			if (!callmap.get(funcname).contains(func)) {
				calls.removeAll(rfuncBlock.get(func));
				rnoncalls.removeAll(rfuncBlock.get(func));
				rblocklist.removeAll(rfuncBlock.get(func));
				funcs.remove(func);
				// sequential.remove(func);
			}
		}
		calls.add(funcid);
		rblocklist.add(funcid);

		String x = "x";
		String y = "y";

		// first the predicate signature
		writer.print("pred " + ordername + "(var1 " + x + ", " + y + ", var2 ");
		writer.print(genarglist(p, x, rblocklist, false));
		writer.print(", ");
		writer.print(genarglist(p, y, rblocklist, false));
		writer.println(") = ");

		// the labels for x and y should not be exactly the same
		// andtmp.add(l(p, "main", x) + " = " + l(p, "main", y));
		for (String id : rblocklist) {
			andtmp.add(l(p, id, x) + " = " + l(p, id, y));
		}
		writer.println("\t~(" + getAnd(andtmp, "", false) + ")");
		andtmp.clear();

		// labels for x and y should be valid configurations
		writer.println("\t& " + configname + "(" + x + ", " + genarglist(p, x, rblocklist, false) + ")");
		writer.println("\t& " + configname + "(" + y + ", " + genarglist(p, y, rblocklist, false) + ")");

		// exists a node z which precede x and y in the tree, such that
			// every node v precede z, v in labels of x <=> v in labels of y
			// but labels of x and labels of y start to differ on z or children of z.
		// first part: every node v precede z, v in labels of x <=> v in labels of y
		writer.println("\t& (ex1 z: (z <= " + x + ") & (z <= " + y + ")");
		writer.println("\t\t& (all1 v:");
		writer.println("\t\t\t(v < z) => ");
		writer.print("\t\t\t(\t");
		// andtmp.add("(v in " + l(p, "main", x) + " <=> v in " + l(p, "main", y) + ")");
		for (String id : rblocklist) {
			andtmp.add("(v in " + l(p, id, x) + " <=> v in " + l(p, id, y) + ")");
		}
		writer.print(getAnd(andtmp, "\t\t\t\t", true));
		andtmp.clear();
		writer.println(" )");
		writer.println("\t\t\t)");
		// second part: but labels of x and labels of y start to differ on z or children of z.
		writer.print("\t\t& (");
		// for every call block
		// find out the function which the call block actually calls
		// get the sequential relation corresponding to the function
		// list all possibilities
		// List<String> seqmain = sequential.get("main");
		// for (int i = 0; i < seqmain.size(); i++) {
		// 	andtmp.add("(z in " + l(p, "main", x) + ")");
		// 	andtmp.add("(z in " + l(p, "main", y) + ")");
		// 	// get the block, check if it's a call
		// 	Block iblock = rblocks.get(seqmain.get(i));
		// 	if (iblock.getCallFlag()) {
		// 		// if it is a call, get the callseq of the call, z.callseq should be in that call block
		// 		List<String> icallseq = iblock.callseq;
		// 		String iseq = "";
		// 		for (int m = 1; m < icallseq.size(); m++) {
		// 			if (icallseq.get(m).equals("left") || icallseq.get(m).equals("next")) {
		// 				iseq = iseq + ".0";
		// 			} else if (icallseq.get(m).equals("right")) {
		// 				iseq = iseq + ".1";
		// 			}
		// 		}
		// 		andtmp.add("(z" + iseq + " in " + l(p, seqmain.get(i), x) + ")");
		// 	} else {
		// 		// if it's noncall, z should be in the noncall block
		// 		andtmp.add("(z in " + l(p, seqmain.get(i), x) + ")");
		// 	}
		// 	for (int j = i + 1; j < seqmain.size(); j++) {
		// 		Block jblock = rblocks.get(seqmain.get(j));
		// 		if (jblock.getCallFlag()) {
		// 			// if it is a call, get the callseq of the call, z.callseq should be in that call block
		// 			List<String> jcallseq = jblock.callseq;
		// 			String jseq = "";
		// 			for (int m = 1; m < jcallseq.size(); m++) {
		// 				if (jcallseq.get(m).equals("left" || jcallseq.get(m).equals("next")) {
		// 					jseq = jseq + ".0";
		// 				} else if (jcallseq.get(m).equals("right")) {
		// 					jseq = jseq + ".1";
		// 				}
		// 			}
		// 			andtmp.add("(z" + jseq + " in " + l(p, seqmain.get(j), y) + ")");
		// 		} else {
		// 			// if it's noncall, z should be in the noncall block
		// 			andtmp.add("(z in " + l(p, seqmain.get(j), y) + ")");
		// 		}
		// 		ortmp.add("(" + getAnd(andtmp, "\t\t\t\t", true) + ")");
		// 		andtmp.remove(andtmp.size() - 1);
		// 	}
		// 	andtmp.clear();
		// }
		for (String callid : calls) {
			String funcname = rblocks.get(callid).getCallname();
			List<String> seqfunc = sequential.get(funcname);
			for (int i = 0; i < seqfunc.size(); i++) {
				andtmp.add("(z in " + l(p, callid, x) + ")");
				andtmp.add("(z in " + l(p, callid, y) + ")");
				// get the block, check if it's a call
				Block iblock = rblocks.get(seqfunc.get(i));
				if (iblock.getCallFlag()) {
					// if it is a call, get the callseq of the call, z.callseq should be in that call block
					List<String> icallseq = iblock.callseq;
					String iseq = "";
					for (int m = 1; m < icallseq.size(); m++) {
						if (icallseq.get(m).equals("left") || icallseq.get(m).equals("next")) {
							iseq = iseq + ".0";
						} else if (icallseq.get(m).equals("right")) {
							iseq = iseq + ".1";
						}
					}
					andtmp.add("(z" + iseq + " in " + l(p, seqfunc.get(i), x) + ")");
				} else {
					// if it's noncall, z should be in the noncall block
					andtmp.add("(z in " + l(p, seqfunc.get(i), x) + ")");
				}
				for (int j = i + 1; j < seqfunc.size(); j++) {
					Block jblock = rblocks.get(seqfunc.get(j));
					if (jblock.getCallFlag()) {
						// if it is a call, get the callseq of the call, z.callseq should be in that call block
						List<String> jcallseq = jblock.callseq;
						String jseq = "";
						for (int m = 1; m < jcallseq.size(); m++) {
							if (jcallseq.get(m).equals("left") || jcallseq.get(m).equals("next")) {
								jseq = jseq + ".0";
							} else if (jcallseq.get(m).equals("right")) {
								jseq = jseq + ".1";
							}
						}
						andtmp.add("(z" + jseq + " in " + l(p, seqfunc.get(j), y) + ")");
					} else {
						// if it's noncall, z should be in the noncall block
						andtmp.add("(z in " + l(p, seqfunc.get(j), y) + ")");
					}
					ortmp.add("(" + getAnd(andtmp, "\t\t\t\t", true) + ")");
					andtmp.remove(andtmp.size() - 1);
				}
				andtmp.clear();
			}
		}
		writer.print(getOr(ortmp, "\t\t\t", true));
		ortmp.clear();
		writer.println("\n\t\t\t)");
		writer.print("\t\t)");

		// ordered comes to an end
		writer.println(";");

	}

	public void genxxfuseconstr(String fusedorder, String ordered, String pu, String pf, String func1, String func2) {
		String x = "x";
		String y = "y";
		List<String> f1blck = getFuncblocklist(func1, unfused);
		List<String> fblck = new LinkedList<String>(fused.rblocklist);
		List<String> f2nclist = getFuncNCblocklist(unfused.rblocks.get(func2).getCallname(), unfused);

		// declare var1 x, y first
		writer.println("var1 " + x + ", " + y + ";");
		writer.println();

		// declare var2
		writer.print("var2 empty_set, ");
		writer.print(genarglist(pu, x, f1blck, true));
		writer.print(", ");
		writer.print(genarglist(pu, y, f1blck, true));
		writer.println(";");
		writer.println();

		// define empty_set
		writer.println("all1 u: ~(u in empty_set);");
		writer.println();

		// fusedordered y x
		writer.print(fusedorder + "(" + y + ", " + x + ", ");
		List<String> fvars = new LinkedList<String>(fblck);
		for (int i = 0; i < fvars.size(); i++) {
			List<String> tmplist = new LinkedList<String>();
			tmplist.add(fvars.get(i));
			fvars.set(i, genNCCrrspList(tmplist, relation, false).get(0));
		}
		fvars = genRplist(fvars, f2nclist);
		writer.print(genarglist(pu, y, fvars, true));
		writer.print(", ");
		writer.print(genarglist(pu, x, fvars, true));
		writer.println(");");
		writer.println();

		// ordered x y
		writer.print(ordered + "(" + x + ", " + y + ", ");
		writer.print(genarglist(pu, x, f1blck, false));
		writer.print(", ");
		writer.print(genarglist(pu, y, f1blck, false));
		writer.println(");");
		writer.println();

		// dependence x y
		writer.print("Dependence(" + x + ", " + y + ", ");
		writer.print(genarglist(pu, x, f1blck, false));
		writer.print(", ");
		writer.print(genarglist(pu, y, f1blck, false));
		writer.println(");");
		writer.println();

	}

	public void genyyfuseconstr(String fusedorder, String ordered, String pu, String pf, String func1, String func2) {
		String x = "x";
		String y = "y";
		List<String> f1blck = getFuncblocklist(func1, unfused);
		List<String> f2blck = getFuncblocklist(func2, unfused);
		List<String> fblck = new LinkedList<String>(fused.rblocklist);
		List<String> f1nclist = getFuncNCblocklist(unfused.rblocks.get(func1).getCallname(), unfused);
		List<String> f2nclist = getFuncNCblocklist(unfused.rblocks.get(func2).getCallname(), unfused);
		List<String> f1ncCrrsplist = genNCCrrspList(f1nclist, relation, true);
		List<String> f2ncCrrsplist = genNCCrrspList(f2nclist, relation, true);

		// declare var1 x, y first
		writer.println("var1 " + x + ", " + y + ";");
		writer.println();

		// declare var2
		writer.print("var2 empty_set, ");
		writer.print(genarglist(pu, x, f2blck, false));
		writer.print(", ");
		writer.print(genarglist(pu, y, f2blck, false));
		writer.print(", ");
		List<String> fvars = new LinkedList<String>(fblck);
		fvars.removeAll(f1ncCrrsplist);
		writer.print(genarglist(pf, x, fvars, true));
		writer.print(", ");
		writer.print(genarglist(pf, y, fvars, true));
		writer.println(";");
		writer.println();

		// define empty_set
		writer.println("all1 u: ~(u in empty_set);");
		writer.println();

		// fusedordered y x
		writer.print(fusedorder + "(" + y + ", " + x + ", ");
		fvars = genRplist(fblck, f1ncCrrsplist);
		writer.print(genarglist(pf, y, fvars, true));
		writer.print(", ");
		// fvars = new LinkedList<String>(fblck);
		// for (int i = 0; i < fvars.size(); i++) {
		// 	List<String> tmplist = new LinkedList<String>();
		// 	tmplist.add(fvars.get(i));
		// 	fvars.set(i, genNCCrrspList(tmplist, relation, false).get(0));
		// }
		// fvars = genRplist(fvars, f2nclist);
		// writer.print(genarglist(pu, x, fvars, true));
		writer.print(genarglist(pf, x, fvars, true));
		writer.println(");");
		writer.println();


		// ordered x y
		writer.print(ordered + "(" + x + ", " + y + ", ");
		writer.print(genarglist(pu, x, f2blck, false));
		writer.print(", ");
		writer.print(genarglist(pu, y, f2blck, false));
		writer.println(");");
		writer.println();

		// dependence x y
		writer.print("Dependence(" + x + ", " + y + ", ");
		writer.print(genarglist(pu, x, f2blck, false));
		writer.print(", ");
		writer.print(genarglist(pu, y, f2blck, false));
		writer.println(");");
		writer.println();

		// convert x
		writer.print("Convert(");
		writer.print(genarglist(pu, x, f2blck, false));
		writer.print(", ");
		fvars = genRplist(fblck, f1ncCrrsplist);
		writer.print(genarglist(pf, x, fvars, false));
		writer.println(");");
		writer.println();

		// convert y
		writer.print("Convert(");
		writer.print(genarglist(pu, y, f2blck, false));
		writer.print(", ");
		fvars = genRplist(fblck, f1ncCrrsplist);
		writer.print(genarglist(pf, y, fvars, false));
		writer.println(");");
		writer.println();

	}

	public void genmultfuse() {
		// there are 3 cases
		String func1 = unfused.rfuncBlock.get("main").get(0);	// block id
		String func2 = unfused.rfuncBlock.get("main").get(1);
		String func1config = "Configuration_" + unfused.rblocks.get(func1).getCallname();
		String func2config = "Configuration_" + unfused.rblocks.get(func2).getCallname();

		// x and y in different traversal
		File file = new File(filepath + filename + "_1.mona");
		try {
			file.createNewFile();
		} catch (Exception fnfe) {
			System.out.println(fnfe);
		}
		try {
			writer = new PrintWriter(file);
		} catch (FileNotFoundException fnfe) {
			System.out.println(fnfe);
		}
		writer.println("ws2s;\n");
		genfuncconfig(func1config, "C", unfused, func1);
		writer.println();
		genfuncconfig(func2config, "C", unfused, func2);
		writer.println();
		genconfig("ConfigurationFused", "D", fused);
		writer.println();
		gendiffordered("Ordered", func1config, func2config, "C", unfused, func1, func2);
		writer.println();
		genordered("OrderedFused", "ConfigurationFused", "D", fused, null);
		writer.println();
		genParaDependence("C", "C", unfused, func1, func2);
		writer.println();
		genconvert("C", "D", getFuncblocklist(func2, unfused), fused.getRdcdBlocklist(), relation, true);
		writer.println();
		gendifffuseconstr("OrderedFused", "Ordered", "C", "D", func1, func2);
		writer.println();
		writer.close();

		// both x and y in the fisrt traversal
		int index = fused.calls.size() / 2;
		List<String> call = new LinkedList<String>(fused.calls);
		List<String> call1 = new LinkedList<String>(call.subList(0, index));
		List<String> call2 = new LinkedList<String>(call.subList(index, call.size()));

		file = new File(filepath + filename + "_2.mona");
		try {
			file.createNewFile();
		} catch (Exception fnfe) {
			System.out.println(fnfe);
		}
		try {
			writer = new PrintWriter(file);
		} catch (FileNotFoundException fnfe) {
			System.out.println(fnfe);
		}
		writer.println("ws2s;\n");
		genfuncconfig(func1config, "C", unfused, func1);
		writer.println();
		genconfig("ConfigurationFused", "D", fused);
		writer.println();
		genfuncordered("Ordered", func1config, "C", unfused, func1);
		writer.println();
		genordered("OrderedFused", "ConfigurationFused", "D", fused, call1);
		writer.println();
		genParaDependence("C", "C", unfused, func1, func1);
		writer.println();
		genxxfuseconstr("OrderedFused", "Ordered", "C", "D", func1, func2);
		writer.println();
		writer.close();

		file = new File(filepath + filename + "_3.mona");
		try {
			file.createNewFile();
		} catch (Exception fnfe) {
			System.out.println(fnfe);
		}
		try {
			writer = new PrintWriter(file);
		} catch (FileNotFoundException fnfe) {
			System.out.println(fnfe);
		}
		writer.println("ws2s;\n");
		genfuncconfig(func1config, "C", unfused, func1);
		writer.println();
		genconfig("ConfigurationFused", "D", fused);
		writer.println();
		genfuncordered("Ordered", func1config, "C", unfused, func1);
		writer.println();
		genordered("OrderedFused", "ConfigurationFused", "D", fused, call2);
		writer.println();
		genParaDependence("C", "C", unfused, func1, func1);
		writer.println();
		genxxfuseconstr("OrderedFused", "Ordered", "C", "D", func1, func2);
		writer.println();
		writer.close();

		// both x and y in the second traversal
		file = new File(filepath + filename + "_4.mona");
		try {
			file.createNewFile();
		} catch (Exception fnfe) {
			System.out.println(fnfe);
		}
		try {
			writer = new PrintWriter(file);
		} catch (FileNotFoundException fnfe) {
			System.out.println(fnfe);
		}
		writer.println("ws2s;\n");
		genfuncconfig(func2config, "C", unfused, func2);
		writer.println();
		genconfig("ConfigurationFused", "D", fused);
		writer.println();
		genfuncordered("Ordered", func2config, "C", unfused, func2);
		writer.println();
		genordered("OrderedFused", "ConfigurationFused", "D", fused, call1);
		writer.println();
		genParaDependence("C", "C", unfused, func2, func2);
		writer.println();
		genconvert("C", "D", getFuncblocklist(func2, unfused), fused.getRdcdBlocklist(), relation, true);
		writer.println();
		genyyfuseconstr("OrderedFused", "Ordered", "C", "D", func1, func2);
		writer.println();
		writer.close();

		file = new File(filepath + filename + "_5.mona");
		try {
			file.createNewFile();
		} catch (Exception fnfe) {
			System.out.println(fnfe);
		}
		try {
			writer = new PrintWriter(file);
		} catch (FileNotFoundException fnfe) {
			System.out.println(fnfe);
		}
		writer.println("ws2s;\n");
		genfuncconfig(func2config, "C", unfused, func2);
		writer.println();
		genconfig("ConfigurationFused", "D", fused);
		writer.println();
		genfuncordered("Ordered", func2config, "C", unfused, func2);
		writer.println();
		genordered("OrderedFused", "ConfigurationFused", "D", fused, call2);
		writer.println();
		genParaDependence("C", "C", unfused, func2, func2);
		writer.println();
		genconvert("C", "D", getFuncblocklist(func2, unfused), fused.getRdcdBlocklist(), relation, true);
		writer.println();
		genyyfuseconstr("OrderedFused", "Ordered", "C", "D", func1, func2);
		writer.println();
		writer.close();

	}


}	