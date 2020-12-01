import java.util.*;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;

public class RetreetExtractor extends RetreetBaseListener {

    List<String> funcs = new LinkedList<String>();		// AllFuncs
    List<String> params = new LinkedList<String>();		// 
    Map<String, Block> blocks = new LinkedHashMap<String, Block>();		// AllBlocks
    List<String> blocklist = new LinkedList<String>();     // AllBlocks
    Set<String> calls = new HashSet<String>();		// AllCalls: a set of ids of the call block
    Set<String> noncalls = new HashSet<String>();	// AllNonCalls: a set of ids of the noncall block

    Map<String, List<String>> funcBlock = new LinkedHashMap<String, List<String>>();		// Blocks(f)
    Map<String, List<String>> funcParam = new LinkedHashMap<String, List<String>>();		// Params(f) 

    String currFunc;
    String currBlock;

    Map<String, List<String>> sequential = new LinkedHashMap<String, List<String>>();
    List<String> parallel = new LinkedList<String>(); // parallelization only happens in main function
    Map<String, List<String>> funcsInFunc = new LinkedHashMap<String, List<String>>(); //

    List<String> locseq = new LinkedList<String>();		// the location sequence of a lexpr, the first element is the node, the rest of elements are pointers

    Set<String> currReadVar = new HashSet<String>();	// read set of variables for this block
	Set<String> currWriteVar = new HashSet<String>();	// write set of variables for this block
    Set<List<String>> currReadField = new HashSet<List<String>>();   // read set of fields for this block
    Set<List<String>> currWriteField = new HashSet<List<String>>();  // write set of fields for this block

    Map<String, List<String>> unfused2fused = new LinkedHashMap<String, List<String>>();
    Map<String, List<String>> fused2unfused = new LinkedHashMap<String, List<String>>();

    Map<String, Block> rblocks = new LinkedHashMap<String, Block>();       // reduced AllBlocks
    List<String> rblocklist = new LinkedList<String>();
    Set<String> rnoncalls = new HashSet<String>();   // reduced AllNonCalls: a set of ids of the noncall block
    Map<String, List<String>> rfuncBlock = new LinkedHashMap<String, List<String>>();        // reduced Blocks(f)

    public List<String> getFuncs() {
    	return this.funcs;
    }

    public Map<String, Block> getBlocks() {
    	return this.blocks;
    }

    public List<String> getBlocklist() {
        return this.blocklist;
    }

    public Set<String> getCalls() {
    	return this.calls;
    }

    public Set<String> getNoncalls() {
    	return this.noncalls;
    }

    public Map<String, List<String>> getFuncBlock() {
    	return this.funcBlock;
    }

    public Map<String, List<String>> getSequential() {
        return this.sequential;
    }

    public List<String> getParallel() {
        return this.parallel;
    }

    public Map<String, Block> getRdcdBlocks() {
        return this.rblocks;
    }

    public List<String> getRdcdBlocklist() {
        return this.rblocklist;
    }

    public Set<String> getRdcdNoncalls() {
        return this.rnoncalls;
    }

    public Map<String, List<String>> getRdcdFuncBlock() {
        return this.rfuncBlock;
    }

    public Map<String, List<String>> getUnfused2fused() {
        return this.unfused2fused;
    }

    public Map<String, List<String>> getFused2unfused() {
        return this.fused2unfused;
    }

    public void exitRelation(RetreetParser.RelationContext ctx) {
        String unfusedid = ctx.getChild(2).getText();
        String fusedid = ctx.getChild(6).getText();
        // add unfused to fused mapping to unfused2fused
        if (unfused2fused.get(unfusedid) == null) {
            List<String> fusedlist = new LinkedList<String>();
            fusedlist.add(fusedid);
            unfused2fused.put(unfusedid, fusedlist);
        } else {
            List<String> fusedlist = unfused2fused.get(unfusedid);
            fusedlist.add(fusedid);
            unfused2fused.put(unfusedid, fusedlist);
        }
        // add fused to unfused mapping to fused2unfused
        if (fused2unfused.get(fusedid) == null) {
            List<String> unfusedlist = new LinkedList<String>();
            unfusedlist.add(unfusedid);
            fused2unfused.put(fusedid, unfusedlist);
        } else {
            List<String> unfusedlist = fused2unfused.get(fusedid);
            unfusedlist.add(unfusedid);
            fused2unfused.put(fusedid, unfusedlist);
        }
    }

    public void exitProg(RetreetParser.ProgContext ctx) {
        for (String func : funcs) {
            List<String> blocksInFunc = new LinkedList<String>();
            for (String blockid : sequential.get(func)) {
                rblocks.put(blockid, blocks.get(blockid));
                rblocklist.add(blockid);
                blocksInFunc.add(blockid);
                if (noncalls.contains(blockid)) {
                    rnoncalls.add(blockid);
                }
            }
            rfuncBlock.put(func, blocksInFunc);
        }
        // for every function, collect the functions that this function call inside
        for (String func : funcs) {
            List<String> blocksInFunc = funcBlock.get(func);
            List<String> funcInFunc = new LinkedList<String>();
            for (String blockid : blocksInFunc) {
                Block block = blocks.get(blockid);
                if (block.getCallFlag()) {
                    funcInFunc.add(block.getCallname());
                }
            }
            funcsInFunc.put(func, funcInFunc); 
        }
    }

    public Map<String, Set<String>> getCallMap() {
        Map<String, Set<String>> callmap = new LinkedHashMap<String, Set<String>>();
        for (String func : funcs) {
            Set<String> called = new HashSet<String>();
            called.addAll(funcsInFunc.get(func));
            int oldlength = called.size();
            int newlength = 0;
            while(oldlength != newlength) {
                oldlength = called.size();
                Set<String> calledcopy = new HashSet<String>();
                calledcopy.addAll(called);
                for (String f : calledcopy) {
                    for (String c : funcsInFunc.get(f)) {
                        if (!called.contains(c)) {
                            called.add(c);
                        }
                    }

                }
                newlength = called.size();
            }
            // include itself
            called.add(func);
            callmap.put(func, called);
        }
        return callmap;
    }

    public void enterMain(RetreetParser.MainContext ctx) {
    	String name = ctx.getChild(0).getText();
    	funcs.add(name);
    	currFunc = name;
    	List<String> blocksInFunc = new LinkedList<String>();
    	funcBlock.put(currFunc, blocksInFunc);
        List<String> seqInFunc = new LinkedList<String>();
        sequential.put(currFunc, seqInFunc);
    }

    public void enterFunc(RetreetParser.FuncContext ctx) {
    	String name = ctx.getChild(0).getText();
    	funcs.add(name);
    	currFunc = name;
    	List<String> blocksInFunc = new LinkedList<String>();
    	funcBlock.put(currFunc, blocksInFunc);
        List<String> seqInFunc = new LinkedList<String>();
        sequential.put(currFunc, seqInFunc);
    }

    public void enterBlock(RetreetParser.BlockContext ctx) {
    	String blockid = ctx.getParent().getChild(2).getText();
    	Block newblock = new Block(blockid, ctx.getText());
    	if (ctx.call() != null) {
    		newblock.setCall();
    		newblock.setCallname(ctx.call().getChild(0).getText());
    		calls.add(blockid);
    	}
    	if (ctx.assgn_list() != null || ctx.single_if_stmt() != null) {
    		newblock.setNoncall();
    		noncalls.add(blockid);
    	}
    	blocks.put(blockid, newblock);
        blocklist.add(blockid);
        currBlock = blockid;
    	// add this block id to the current function-block mapping
    	List<String> blocksInFunc = funcBlock.get(currFunc);
    	blocksInFunc.add(blockid);
    	funcBlock.put(currFunc, blocksInFunc);
    	// reset the read set and write set
    	currReadVar.clear();
		currWriteVar.clear();
        currReadField.clear();
        currWriteField.clear();
        // add this block id to current sequential
        List<String> seqInFunc = sequential.get(currFunc);
        seqInFunc.add(blockid);
        sequential.put(currFunc, seqInFunc);
    }

    public void exitLexpr(RetreetParser.LexprContext ctx) {
    	if (ctx.id() != null) {
            locseq.clear();
    		locseq.add(ctx.id().getText());
    	} else {
    		locseq.add(ctx.getChild(2).getText());
    	}
    }

    public void exitArg_list(RetreetParser.Arg_listContext ctx) {
    	Block block = blocks.get(currBlock);
    	block.callseq.clear();
    	block.callseq.addAll(locseq);
    	blocks.put(currBlock, block);
    }

    public void exitBlock(RetreetParser.BlockContext ctx) {
    	Block block = blocks.get(currBlock);
    	block.readvar.addAll(currReadVar);
    	block.writevar.addAll(currWriteVar);
        block.readfield.addAll(currReadField);
        block.writefield.addAll(currWriteField);
    	blocks.put(currBlock, block);
    }

    // public void exitCall(RetreetParser.CallContext ctx) {
    // 	currWrite.add(ctx.getChild(0).getText());
    // }

    public void exitAssgn(RetreetParser.AssgnContext ctx) {
    	if (ctx.id() != null) {
    		currWriteVar.add(ctx.id().getText());
    	}
    }

    public void exitField(RetreetParser.FieldContext ctx) {
        if (ctx.getParent().getChildCount() == 4) {
            // field written in assgn
            List<String> field = new LinkedList<String>();
            field.addAll(locseq);
            field.add(ctx.getChild(2).getText());
            currWriteField.add(field);
        } else if (ctx.getParent().getChildCount() == 1) {
            // field read in aexpr
            List<String> field = new LinkedList<String>();
            field.addAll(locseq);
            field.add(ctx.getChild(2).getText());
            currReadField.add(field);
        }
    }

    public void exitAexpr(RetreetParser.AexprContext ctx) {
    	if (ctx.id() != null) {
    		currReadVar.add(ctx.getChild(0).getText());
    	}
    }

    public void exitIf_part(RetreetParser.If_partContext ctx) {
        List<String> seqInFunc = sequential.get(currFunc);
        seqInFunc.clear();
        sequential.put(currFunc, seqInFunc);
    }

    public void enterStmt(RetreetParser.StmtContext ctx) {
        if (ctx.getChildCount() == 5) {
            parallel.add(ctx.getChild(1).getChild(2).getText());
            parallel.add(ctx.getChild(3).getChild(2).getText());
        }
    }

}