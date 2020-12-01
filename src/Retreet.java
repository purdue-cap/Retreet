import java.util.*;
import java.io.File;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import java.util.logging.Logger;
import java.util.logging.FileHandler;
import java.util.logging.SimpleFormatter;

public class Retreet {
	public static void main( String[] args) throws Exception {

        if (args[0].equals("fuse")) {
            if (args.length != 4) {
                System.out.println("For 'fuse' option, the arg length should be 4.");
                System.exit(1);
            }
            ANTLRFileStream unfusedinput = new ANTLRFileStream(args[1]);
            RetreetLexer unfusedlexer = new RetreetLexer(unfusedinput);
            CommonTokenStream unfusedtokens = new CommonTokenStream(unfusedlexer);
            RetreetParser unfusedparser = new RetreetParser(unfusedtokens);

            ANTLRErrorStrategy unfusedes = new CustomErrorStrategy();
            unfusedparser.setErrorHandler(unfusedes);

            ParseTree unfusedtree = null;
            try{
                unfusedtree = unfusedparser.prog();
                // System.out.println("Unfused Accepted");
            } catch(Exception ex) {
                System.out.println("Unfused Not Accepted");
                return;
            }

            ParseTreeWalker unfusedwalker = new ParseTreeWalker();
            RetreetExtractor unfusedlistener = new RetreetExtractor();
            unfusedwalker.walk(unfusedlistener, unfusedtree);

            ANTLRFileStream fusedinput = new ANTLRFileStream(args[2]);
            RetreetLexer fusedlexer = new RetreetLexer(fusedinput);
            CommonTokenStream fusedtokens = new CommonTokenStream(fusedlexer);
            RetreetParser fusedparser = new RetreetParser(fusedtokens);

            ANTLRErrorStrategy fusedes = new CustomErrorStrategy();
            fusedparser.setErrorHandler(fusedes);

            ParseTree fusedtree = null;
            try{
                fusedtree = fusedparser.prog();
                // System.out.println("Fused Accepted");
            } catch(Exception ex) {
                System.out.println("Fused Not Accepted");
                return;
            }

            ParseTreeWalker fusedwalker = new ParseTreeWalker();
            RetreetExtractor fusedlistener = new RetreetExtractor();
            fusedwalker.walk(fusedlistener, fusedtree);

            ANTLRFileStream relationinput = new ANTLRFileStream(args[3]);
            RetreetLexer relationlexer = new RetreetLexer(relationinput);
            CommonTokenStream relationtokens = new CommonTokenStream(relationlexer);
            RetreetParser relationparser = new RetreetParser(relationtokens);

            ANTLRErrorStrategy relationes = new CustomErrorStrategy();
            relationparser.setErrorHandler(relationes);

            ParseTree relationtree = null;
            try{
                relationtree = relationparser.prog();
                // System.out.println("Relation Accepted");
            } catch(Exception ex) {
                System.out.println("Relation Not Accepted");
                return;
            }

            ParseTreeWalker relationwalker = new ParseTreeWalker();
            RetreetExtractor relationlistener = new RetreetExtractor();
            relationwalker.walk(relationlistener, relationtree);

            File file = new File(args[1]);
            String filename = file.getName();
            filename = filename.substring(0, filename.indexOf("."));
            Generator generator = new Generator("fuse_" + filename, unfusedlistener, fusedlistener, relationlistener);
            generator.genfuse();

        } else if (args[0].equals("parallel")) {
            if (args.length != 2) {
                System.out.println("For 'parallel' option, the arg length should be 2.");
                System.exit(1);
            }

            ANTLRFileStream input = new ANTLRFileStream(args[1]);
            RetreetLexer lexer = new RetreetLexer(input);
            CommonTokenStream tokens = new CommonTokenStream(lexer);
            RetreetParser parser = new RetreetParser(tokens);

            ANTLRErrorStrategy es = new CustomErrorStrategy();
            parser.setErrorHandler(es);

            ParseTree tree = null;
            try{
                tree = parser.prog();
                // System.out.println("Accepted");
            } catch(Exception ex) {
                System.out.println("Not Accepted");
                return;
            }

            ParseTreeWalker walker = new ParseTreeWalker();
            RetreetExtractor listener = new RetreetExtractor();
            walker.walk(listener, tree);

            File file = new File(args[1]);
            String filename = file.getName();
            filename = filename.substring(0, filename.indexOf("."));
            Generator generator = new Generator(filename, listener);
            generator.genpara();

        } else {
            // debug area
            File file = new File(args[0]);
            String filename = file.getName();
            System.out.println("Filename: " + filename.substring(0, filename.indexOf(".")));

            ANTLRFileStream input = new ANTLRFileStream(args[0]);
            RetreetLexer lexer = new RetreetLexer(input);
            CommonTokenStream tokens = new CommonTokenStream(lexer);
            RetreetParser parser = new RetreetParser(tokens);

            Logger logger = Logger.getLogger("main");

            ANTLRErrorStrategy es = new CustomErrorStrategy();
            parser.setErrorHandler(es);

            ParseTree tree = null;
            try{
                tree = parser.prog();
                logger.info("Accepted");
            } catch(Exception ex) {
                logger.info("Not Accepted");
                return;
            }

            ParseTreeWalker walker = new ParseTreeWalker();
            RetreetExtractor listener = new RetreetExtractor();
            walker.walk(listener, tree);

            List<String> funcs = listener.getFuncs();
            Map<String, Block> blocks = listener.getBlocks();
            Set<String> calls = listener.getCalls();
            Set<String> noncalls = listener.getNoncalls();
            Map<String, List<String>> funcBlock = listener.getFuncBlock();
            Map<String, List<String>> sequential = listener.getSequential();
            List<String> parallel = listener.getParallel();

            System.out.println("Print out AllFuncs:");
            for (String func : funcs) {
             System.out.println("Function: " + func);
            }
            System.out.println();

            System.out.println("Print out AllBlocks:");
            for (String blockid : listener.getBlocklist()) {
                Block block = blocks.get(blockid);
             System.out.println("Block id: " + block.getId() + " Text: " + block.getText());
                if (block.getCallFlag()) {
                    System.out.println("It's a call block. It calls function: " + block.getCallname());
                }
                if (!block.callseq.isEmpty()) {
                    System.out.println("The call sequence is: ");
                    for (String s : block.callseq) {
                        System.out.println("  " + s);
                    }
                }
                if (!block.readvar.isEmpty()) {
                    System.out.println("The read set of variables: ");
                    for (String s : block.readvar) {
                        System.out.println("     " + s);
                    }
                }
                if (!block.readfield.isEmpty()) {
                    System.out.println("The read set of fields: ");
                    for (List<String> field : block.readfield) {
                        System.out.println("     field:");
                        for (String s : field) {
                            System.out.println("          " + s);
                        }
                    }
                }
                if (!block.writevar.isEmpty()) {
                    System.out.println("The write set of variables: ");
                    for (String s : block.writevar) {
                        System.out.println("     " + s);
                    }
                }
                if (!block.writefield.isEmpty()) {
                    System.out.println("The write set of fields: ");
                    for (List<String> field : block.writefield) {
                        System.out.println("     field:");
                        for (String s : field) {
                            System.out.println("          " + s);
                        }
                    }
                }
            }
            System.out.println();

            System.out.println("Print out AllCalls:");
            for (String call : calls) {
             System.out.println("Call block id: " + call);
            }
            System.out.println();

            System.out.println("Print out AllNoncalls:");
            for (String noncall : noncalls) {
             System.out.println("Noncall block id: " + noncall);
            }
            System.out.println();

            System.out.println("Print out mapping of functions to blocks:");
            for (String func : funcBlock.keySet()) {
             List<String> blockList = funcBlock.get(func);
             System.out.println("Current function: " + func);
             for (String b : blockList) {
                 System.out.println("    block: " + b);
             }
            }
            System.out.println();

            System.out.println("Print out sequential relations in functions:");
            for (String func : sequential.keySet()) {
                List<String> seq = sequential.get(func);
                System.out.println("Current function: " + func);
                for (String b : seq) {
                    System.out.println("    block: " + b);
                }
            }
            System.out.println();



            System.out.println("Print out reduced AllBlocks:");
            Map<String, Block> rblocks = listener.getRdcdBlocks();
            for (String blockid : listener.getRdcdBlocklist()) {
                Block block = rblocks.get(blockid);
                System.out.println("Block id: " + block.getId() + " Text: " + block.getText());
                if (block.getCallFlag()) {
                    System.out.println("It's a call block. It calls function: " + block.getCallname());
                }
                if (!block.callseq.isEmpty()) {
                    System.out.println("The call sequence is: ");
                    for (String s : block.callseq) {
                        System.out.println("  " + s);
                    }
                }
                if (!block.readvar.isEmpty()) {
                    System.out.println("The read set of variables: ");
                    for (String s : block.readvar) {
                        System.out.println("     " + s);
                    }
                }
                if (!block.readfield.isEmpty()) {
                    System.out.println("The read set of fields: ");
                    for (List<String> field : block.readfield) {
                        System.out.println("     field:");
                        for (String s : field) {
                            System.out.println("          " + s);
                        }
                    }
                }
                if (!block.writevar.isEmpty()) {
                    System.out.println("The write set of variables: ");
                    for (String s : block.writevar) {
                        System.out.println("     " + s);
                    }
                }
                if (!block.writefield.isEmpty()) {
                    System.out.println("The write set of fields: ");
                    for (List<String> field : block.writefield) {
                        System.out.println("     field:");
                        for (String s : field) {
                            System.out.println("          " + s);
                        }
                    }
                }
            }
            System.out.println();

            System.out.println("Print out reduced AllNoncalls:");
            for (String noncall : listener.getRdcdNoncalls()) {
                System.out.println("Noncall block id: " + noncall);
            }
            System.out.println();

            System.out.println("Print out reduced mapping of functions to blocks:");
            Map<String, List<String>> rfuncBlock = listener.getRdcdFuncBlock();
            for (String func : rfuncBlock.keySet()) {
                List<String> blockList = rfuncBlock.get(func);
                System.out.println("Current function: " + func);
                for (String b : blockList) {
                    System.out.println("    block: " + b);
                }
            }
            System.out.println();


            System.out.println("Print out parallel relations in functions:");
            for (String p : parallel) {
                System.out.println("    block: " + p);
            }
            System.out.println();

            System.out.println("Print out callmap:");
            Map<String, Set<String>> callmap = listener.getCallMap();
            for (String func : funcs) {
                System.out.println("  function: " + func);
                for (String f : callmap.get(func)) {
                    System.out.println("    called: " + f);
                }
            }
            System.out.println();

        }

	}
}

class CustomErrorStrategy extends DefaultErrorStrategy{
	@Override
	public void reportError(Parser recognizer, RecognitionException err){
		throw err;
	}	
}	