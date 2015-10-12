import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import soot.Unit;
import soot.Local;
import soot.Value;
import soot.ValueBox;
import soot.SootMethod;
import soot.jimple.IfStmt;
import soot.jimple.Constant;
import soot.jimple.LookupSwitchStmt;
import soot.jimple.TableSwitchStmt;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JLookupSwitchStmt;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JStaticInvokeExpr;
import soot.jimple.internal.JTableSwitchStmt;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.BriefBlockGraph;
import soot.toolkits.graph.pdg.HashMutablePDG;
import soot.toolkits.graph.pdg.PDGNode;
import soot.toolkits.graph.pdg.IRegion;

/** Here you need to implement your intra-procedural t_ analysis.
 * In this dummy program, I just traverse the entire cfg and print out all the stmts in Jimple format 
 * as well as the associated information (e.g., predecessors, succ, defined and used variables).
 * 
 * @author z_zhiqiang
 *
 */
public class IntraTaintAnalysis {
	
	//New data members
	private String[] inputmtds = 
		{"<java.io.BufferedReader: java.lang.String readLine()>", 
			"<java.util.Scanner: java.lang.String next()>",
			"<java.io.InputStreamReader: java.lang.String read()>",
			"<java.util.Scanner: java.lang.String nextLine()>",
			"<java.util.Scanner: java.lang.BigDecimal nextBigDecimal()>",
			"<java.util.Scanner: java.lang.BigInteger nextBigInteger()>",
			"<java.util.Scanner: java.lang.boolean nextBoolean()>",
			"<java.util.Scanner: java.lang.byte nextByte()>",
			"<java.util.Scanner: java.lang.double nextDouble()>",
			"<java.util.Scanner: java.lang.float nextFloat()>",
			"<java.util.Scanner: java.lang.int nextInt()>",
			"<java.util.Scanner: java.lang.long nextLong()>",
			"<java.util.Scanner: java.lang.short nextShort()>"}; //user input mtds
	private BriefBlockGraph bfg;
	private Block currentBlock;  //stores the currently analysed block
	private LinkedHashMap<Object, Unit> stmtMap; 	//to store each stmt as per the sequence number
	private ArrayList<Block> blockProcessList; 	// to stroe the list of blocks which need to be processed
	private LinkedHashMap<Unit, LinkedHashSet<String>> entrySetMap; //unit and it's entry-set
	private LinkedHashMap<Unit, LinkedHashSet<String>> exitSetMap; //unit and entry-set
	private ArrayList<Block> controllingBlocks; //to store the control dependency blocks 
	private LinkedHashMap<Unit, Unit> directCdg; //Units and their direct controlling Unit
	private LinkedHashMap<Unit, LinkedHashSet<Unit>> indirectCdg; //Units and their indirect controlling Unit
	private boolean isInvokedByt_edExpr; // current block is t_ed or not
	private InterTaintAnalysis interAna; //inter-procedural t_ analyser
	private SootMethod mtd;
	//control flow graph in Jimple format
	private BriefUnitGraph cfg;
	

	public IntraTaintAnalysis(SootMethod mtd) {
		this.mtd = mtd;
		this.cfg = new BriefUnitGraph(mtd.getActiveBody());
		this.printOut();
	}
	
	public IntraTaintAnalysis(SootMethod mtd, InterTaintAnalysis interProcAna) {
		this.interAna = interProcAna;
		this.mtd = mtd;
		this.cfg = new BriefUnitGraph(mtd.getActiveBody());
		//initialize all new data members
		stmtMap = new LinkedHashMap<Object, Unit>();		
		blockProcessList = new ArrayList<Block>();
		entrySetMap = new LinkedHashMap<Unit, LinkedHashSet<String>>();
		exitSetMap = new LinkedHashMap<Unit, LinkedHashSet<String>>();
		controllingBlocks = new ArrayList<Block>();	
		directCdg = new LinkedHashMap<Unit, Unit>();
		indirectCdg = new LinkedHashMap<Unit, LinkedHashSet<Unit>>();
		isInvokedByt_edExpr = false;		

		Iterator<Unit> itrState = cfg.iterator();
		int unitNo = 0;
		while(itrState.hasNext()) {
			Unit stmt = itrState.next();
			stmtMap.put(unitNo, stmt);	
			LinkedHashSet<String> blankentrySet = new LinkedHashSet<String>();
			entrySetMap.put(stmt, blankentrySet);
			LinkedHashSet<String> blankexitSet = new LinkedHashSet<String>();
			exitSetMap.put(stmt, blankexitSet);
			unitNo++;
		}
		//direct, indirect cdg for the mtd
		HashMutablePDG pdg = new HashMutablePDG((BriefUnitGraph) cfg);
		List<Object> pdgnodes = pdg.getNodes(); //pdg node list
	
		for(Iterator<PDGNode> itrPdg = pdg.iterator(); itrPdg.hasNext();) {
			PDGNode controllingNode = itrPdg.next();
			//handing of cfg nodes - if, while, switch
			if((PDGNode.Type.CFGNODE) == (controllingNode.getType())) {
				Block blk1 = (Block) controllingNode.getNode();
				Unit blkTail = blk1.getTail();
				if(blkTail instanceof TableSwitchStmt || blkTail instanceof LookupSwitchStmt || blkTail instanceof IfStmt) {
					for(Object obj1: pdgnodes) {
						PDGNode node1 = (PDGNode) obj1;
						if(pdg.dependentOn(node1, controllingNode)) {		
							IRegion region = (IRegion) node1.getNode();
							for(Unit un1: region.getUnits()) {
								directCdg.put(un1, blkTail);
							}							
						}
					}
				}
			}
		}
		for(Unit u2: directCdg.keySet())
		{
			LinkedHashSet<Unit> tempu = new LinkedHashSet<Unit>();
			indirectCdg.put(u2, tempu );
			Unit u3 = u2;
			while(directCdg.containsKey(u3)) {
				u3 = directCdg.get(u3);
				indirectCdg.get(u2).add(u3);
			}
		}		
	}

	//fixed point analysis
	//exitSet of last unit will be merged to in of the current's 1st one
	public void stmtAnalysis() {
		this.bfg = new BriefBlockGraph(mtd.getActiveBody());
		Iterator<Block> itrBlk = bfg.getBlocks().iterator();
		currentBlock = itrBlk.next();
		blockProcessList.add(currentBlock);
		SootMethod mtd = currentBlock.getBody().getMethod();
		if (mtd.isMain()) {
			interAna.PreMapCreation("@parameter0: java.lang.String[]", mtd);
		}
		while(!blockProcessList.isEmpty()) {
			ListIterator<Block> itrBlkProc = blockProcessList.listIterator();			
			currentBlock = itrBlkProc.next();
			isInvokedByt_edExpr = false;
			List<Block> predecessors = currentBlock.getPreds();
			LinkedHashSet<String> entrySet = entrySetMap.get(currentBlock.getHead());
			Iterator<Block> itrPred = predecessors.iterator();
			while(itrPred.hasNext()) {
				Block pred = itrPred.next();
				Unit predTail = pred.getTail();
				LinkedHashSet<String> exitSet = exitSetMap.get(predTail);
				setCopyFn(exitSet, entrySet);				
			}
			entrySetMap.put(currentBlock.getHead(),entrySet);
			LinkedHashSet<String> newexitSet = exitSetMap.get(currentBlock.getTail());
			LinkedHashSet<String> oldexitSet = new LinkedHashSet<String>();
			setCopyFn(newexitSet, oldexitSet);
			itrPred = predecessors.iterator();
			if(itrPred.hasNext()) {
				Block controlBlock = itrPred.next(); 
				if(controllingBlocks.contains(controlBlock) && indirectCdg.containsKey(currentBlock.getHead())) {
					LinkedHashSet<Unit> ctrlUnits = indirectCdg.get(currentBlock.getHead());
					if(ctrlUnits.contains(controlBlock.getTail())) {
						isInvokedByt_edExpr = true;
					}
				}
			}
			Iterator<Unit> itrUnit = currentBlock.iterator();
			Unit stmt = null, prevStnt = null;
			LinkedHashSet<String> prevExit = null;
			while(itrUnit.hasNext()) {
				if(stmt != null) {
					prevStnt = stmt;
					prevExit = exitSetMap.get(prevStnt);
				}
				stmt = itrUnit.next();
				LinkedHashSet<String> entrySet1 = entrySetMap.get(stmt);
				LinkedHashSet<String> exitSet1 = exitSetMap.get(stmt);
				if(prevExit != null) {
					setCopyFn(prevExit, entrySet1);
				}
				kill(entrySet1, exitSet1,stmt);
				gen(entrySet1, exitSet1, stmt);
				entrySetMap.put(stmt, entrySet1);
				exitSetMap.put(stmt, exitSet1);
			}
			blockProcessList.remove(currentBlock);
			if(!setComparison(newexitSet, oldexitSet)) {
				List<Block> succ = currentBlock.getSuccs();
				Iterator<Block> itrsucc = succ.iterator();
				while(itrsucc.hasNext())	{
					blockProcessList.add(itrsucc.next());
				}
			}
		}
	}

	//kill Set 
	private void kill(LinkedHashSet<String> entrySet, LinkedHashSet<String> exitSet, Unit stmt) {
		setCopyFn(entrySet, exitSet);
		if(!isInvokedByt_edExpr) {
			if(stmt instanceof JAssignStmt) {
				JAssignStmt assignS = (JAssignStmt)stmt;	
				String lhsv = assignS.leftBox.getValue().toString();		
				boolean t_Chk = false;
				if(!lhsv.contains("[")) {						
					Value rightv = assignS.rightBox.getValue();
					if (rightv instanceof JStaticInvokeExpr) {
						JStaticInvokeExpr expr = (JStaticInvokeExpr) rightv;
						List args = expr.getArgs();
						Iterator itrag = args.iterator();
						while (itrag.hasNext()) {
							Value arg = (Value) itrag.next();
							if (entrySet.contains(arg.toString())) {
								t_Chk = true;
								break;
							}
						}
						if(!t_Chk) {
							exitSet.remove(lhsv);
						}
					}			
					else {
						if(assignS.rightBox.getValue() instanceof Constant) {
							exitSet.remove(lhsv);
							interAna.KillMapCreation(lhsv, assignS.rightBox.getValue().toString(), currentBlock.getBody().getMethod());
						}
						else {					
							Iterator itsUse = assignS.getUseBoxes().iterator();
							Value v = assignS.rightBox.getValue();
							if(v instanceof Local) {
								if (!entrySet.contains(v.toString())) {
									exitSet.remove(lhsv);
									interAna.KillMapCreation(lhsv, v.toString(),  currentBlock.getBody().getMethod());
								}
							}
							else {
								while (itsUse.hasNext()) {
									ValueBox useBox = (ValueBox) itsUse.next();
									if (useBox.getValue() instanceof Local) {
										if (!entrySet.contains(useBox.getValue().toString()) && !lhsv.equals(useBox.getValue().toString())) {
											exitSet.remove(lhsv);
											interAna.KillMapCreation(lhsv, useBox.getValue().toString(), currentBlock.getBody().getMethod());
										}
									}					
								}
							}
						}
					}
				}
			}					
			else if(stmt instanceof JReturnStmt) {
				JReturnStmt retStmt = (JReturnStmt)stmt;
				SootMethod mtd = currentBlock.getBody().getMethod();
				String retVal = retStmt.getOp().toString();
				LinkedHashSet<String> genSet = interAna.getGenSet(mtd);
				if(!entrySet.contains(retVal) && genSet.contains("@return")) {
					interAna.KillMapCreation("@return", retVal, mtd);
				}
			}
		}
	}
	
	//gen set
	private void gen(LinkedHashSet<String> entrySet, LinkedHashSet<String> exitSet, Unit stmt) {				
		if(stmt instanceof JIdentityStmt) {
			JIdentityStmt idStmt = (JIdentityStmt)stmt;
			Value lhs = idStmt.leftBox.getValue();
			Value rhs = idStmt.rightBox.getValue();
			String rhsv = rhs.toString();
			String lhsv = lhs.toString();
			LinkedHashSet<String> t_par = interAna.getPreSet(currentBlock.getBody().getMethod());
			LinkedHashSet<String> genSet = interAna.getGenSet(currentBlock.getBody().getMethod());
			setCopyFn(genSet, t_par);
			if(t_par.contains(rhsv) && !exitSet.contains(lhsv)) {
				exitSet.add(lhsv);
			}
			else if(lhsv.equals("this")) {
				Iterator<String> itrPar = t_par.iterator();
				while(itrPar.hasNext()) {
					String param = itrPar.next();
					if(param.contains("@this")) {
						String t_Obj = param.substring(1, param.length());
						if(!exitSet.contains(t_Obj)) {
							exitSet.add(t_Obj);
						}
					}
				}
			}
			else {	
				String rhsType = rhs.getType().toString();
				Iterator<String> itrPar = t_par.iterator();
				String UDcls = interAna.getClassList();
				while(itrPar.hasNext()) {
					String param = itrPar.next();				
					if(param.contains(rhsType) && UDcls.contains(rhsType)) {
						String[] fields = param.split("\\.");
						String t_fld = lhsv + "." + fields[1];
						if(!exitSet.contains(t_fld)) {
							exitSet.add(t_fld);
						}
					}
				}
			}
		}
		else if(stmt instanceof JAssignStmt) {
			JAssignStmt assignS = (JAssignStmt)stmt;
			String lhsv = assignS.leftBox.getValue().toString();				
			if(lhsv.contains("[")) {
				String[] lhs = lhsv.split("\\[");
				lhsv = lhs[0];
			}		
			Value rightv = assignS.rightBox.getValue(); 
			if(rightv instanceof JStaticInvokeExpr)	{
				JStaticInvokeExpr expr = (JStaticInvokeExpr)rightv;
				List args = expr.getArgs();
				Iterator itrag = args.iterator();			
				while(itrag.hasNext()) {
					Value arg = (Value) itrag.next();
					if((entrySet.contains(arg.toString()) || isInvokedByt_edExpr) && !exitSet.contains(lhsv)) {
						exitSet.add(lhsv);
					}
				}
			}
			else if(rightv instanceof JVirtualInvokeExpr) {
				JVirtualInvokeExpr expr = (JVirtualInvokeExpr)rightv;		
				String mtdRef = expr.getMethodRef().toString();			
				if(isInvokedByt_edExpr && !exitSet.contains(lhsv)) {
					exitSet.add(lhsv);
				}
				else {
					if(mtdRef.equals(inputmtds[0]) || mtdRef.equals(inputmtds[1]) ||
							mtdRef.equals(inputmtds[2]) || mtdRef.equals(inputmtds[3]) ||
							mtdRef.equals(inputmtds[4]) || mtdRef.equals(inputmtds[5]) ||
							mtdRef.equals(inputmtds[6]) || mtdRef.equals(inputmtds[7]) ||
							mtdRef.equals(inputmtds[8]) || mtdRef.equals(inputmtds[9]) ||
							mtdRef.equals(inputmtds[10]) || mtdRef.equals(inputmtds[11]) ||
							mtdRef.equals(inputmtds[12]) && !exitSet.contains(lhsv)) {						
						exitSet.add(lhsv);
					}
					else {					
						Value base = expr.getBase();					
						Iterator itrag = expr.getArgs().iterator();
						ArrayList<Value> params = new ArrayList<>();
						params.add(base);
						while(itrag.hasNext()) {
							params.add((Value) itrag.next());
						}
						SootMethod mtd = expr.getMethod();
						if(interAna.ifUDmtd(mtd)) {
							//t_ParGen(entrySet, exitSet, params, mtd, base);
							t_ParGen(entrySet, exitSet, params, mtd);
							LinkedHashSet<String> genSet = interAna.getGenSet(mtd);
							Iterator<String> itGenSet = genSet.iterator();
							while(itGenSet.hasNext()) {
								String val = itGenSet.next();
								if(val.contains("@return.")) {
									String[] objField = val.split("\\.");
									String lhsField = lhsv + "." + objField[1];
									if(!exitSet.contains(lhsField)) {
										exitSet.add(lhsField);
									}
								}
								else if(val.contains("@return") && !exitSet.contains(lhsv)) {
									exitSet.add(lhsv);						
								}
								else if(val.contains("@this.") && !exitSet.contains(lhsv)) {
									exitSet.add(lhsv);							
								}
							}
						}
						else {
							Iterator<Value> itrPar = params.iterator();
							while(itrPar.hasNext()) {
								Value arg = itrPar.next();	
								if(entrySet.contains(arg.toString()) && !exitSet.contains(lhsv)) {
									exitSet.add(lhsv);								
								}
							}						
						}										
					}
				}
			}
			else if(rightv instanceof JSpecialInvokeExpr) {
				JSpecialInvokeExpr expr = (JSpecialInvokeExpr)rightv;
				ArrayList<Value> params = new ArrayList<>();
				Value base = expr.getBase();
				params.add(base);	
				Iterator itrag = expr.getArgs().iterator();
				while(itrag.hasNext()) {
					params.add((Value)itrag.next());
				}
				SootMethod mtd = expr.getMethod();
				if (interAna.ifUDmtd(mtd)) {
					t_ParGen(entrySet, exitSet, params, mtd);
					LinkedHashSet<String> genSet = interAna.getGenSet(mtd);
					Iterator<String> itGenSet = genSet.iterator();
					while (itGenSet.hasNext()) {				
						String val = itGenSet.next();
						if(val.contains("@return.")) {
							String[] objField = val.split("\\.");
							String lhsField = lhsv + "." + objField[1];
							if(!exitSet.contains(lhsField)) {
								exitSet.add(lhsField);
							}					
						}
						else if(val.contains("@return") && !exitSet.contains(lhsv)) {
							exitSet.add(lhsv);						
						}
						else if(val.contains("@this.") && !exitSet.contains(lhsv)) {
							exitSet.add(lhsv);					
						}
					}			
				}
			}	
			else {	
				if(isInvokedByt_edExpr && !exitSet.contains(lhsv)) {
					exitSet.add(lhsv);
				}
				else {
					Iterator itsUse = assignS.getUseBoxes().iterator();
					while (itsUse.hasNext()) {
						ValueBox useBox = (ValueBox)itsUse.next();
						if (useBox.getValue() instanceof Local) {
							if(entrySet.contains(useBox.getValue().toString()) && !exitSet.contains(lhsv) && !lhsv.equals(useBox.getValue().toString())) {
								exitSet.add(lhsv);							
							}
						}
						else if(entrySet.contains(useBox.getValue().toString()) && !exitSet.contains(lhsv)) {
							exitSet.add(lhsv);
						}
					}
				}
			}
		}
		else if (stmt instanceof JInvokeStmt) {
			JInvokeStmt invokeStmt = (JInvokeStmt)stmt;
			Value value = invokeStmt.getInvokeExprBox().getValue();
			ArrayList<Value> params = new ArrayList<>();		
			SootMethod mtd = null;
			Value base = null;
			if(value instanceof JSpecialInvokeExpr) {			
				JSpecialInvokeExpr expr = (JSpecialInvokeExpr)value;
				base = expr.getBase();
				params.add(base);
				Iterator itrag = expr.getArgs().iterator();
				while(itrag.hasNext()) {
					params.add((Value)itrag.next());
				}
				mtd = expr.getMethod();
			}
			else if(value instanceof JVirtualInvokeExpr) {
				JVirtualInvokeExpr expr = (JVirtualInvokeExpr)value;
				base = expr.getBase();
				params.add(base);
				Iterator itrag = expr.getArgs().iterator();
				while(itrag.hasNext()) {
					params.add((Value)itrag.next());
				}
				mtd = expr.getMethod();
			}
			if (interAna.ifUDmtd(mtd)) {
				t_ParGen(entrySet, exitSet, params, mtd);
				LinkedHashSet<String> genSet = interAna.getGenSet(mtd);
				Iterator<String> itGenSet = genSet.iterator();
				while(itGenSet.hasNext()) {
					String val = itGenSet.next();
					if(val.contains("@this.") && !exitSet.contains(base.toString())) {
						String t_Obj = base.toString() + val.substring(5, val.length());										
						if(!exitSet.contains(t_Obj)) {
							exitSet.add(t_Obj);
						}
					}
				}
			}
		}
		else if(stmt instanceof JIfStmt) {
			JIfStmt ifStmt = (JIfStmt)stmt;
			Value condition = ifStmt.getCondition();
			if(ctrlExpCheck(entrySet, exitSet, condition)) {				
				controllingBlocks.add(currentBlock);
			}
		}	
		else if(stmt instanceof JTableSwitchStmt) {
			JTableSwitchStmt switchStmt = (JTableSwitchStmt)stmt;
			Value key = switchStmt.getKey();
			if(ctrlExpCheck(entrySet, exitSet, key)) {
				controllingBlocks.add(currentBlock);
			}
		}
		else if(stmt instanceof JLookupSwitchStmt) {
			JLookupSwitchStmt switchStmt = (JLookupSwitchStmt)stmt;
			Value key = switchStmt.getKey();
			if(ctrlExpCheck(entrySet, exitSet, key)) {
				controllingBlocks.add(currentBlock);
			}
		}
		else if(stmt instanceof JReturnStmt) {
			JReturnStmt retStmt = (JReturnStmt)stmt;
			String retVal = retStmt.getOp().toString();
			if(entrySet.contains(retVal)) {
				interAna.GenMapCreation("@return", currentBlock.getBody().getMethod());
			}
			Iterator<String> itentrySet = entrySet.iterator();
			while(itentrySet.hasNext()) {
				String value = itentrySet.next();
				if(value.contains("this.")) {
					String genValue = "@" + value;
					interAna.GenMapCreation(genValue, currentBlock.getBody().getMethod());
				}				
				else if(value.contains(retVal + ".")) {
					String[] retField = value.split("\\.");
					interAna.GenMapCreation("@return." + retField[1], currentBlock.getBody().getMethod());
				}
			}
		}		
		else 
		{
			Iterator<String> itentrySet = entrySet.iterator();
			while(itentrySet.hasNext()) {
				String value = itentrySet.next();
				if(value.contains("this.")) {
					String genValue = "@" + value;
					interAna.GenMapCreation(genValue, 
							currentBlock.getBody().getMethod());
				}
			}
		}
	}

	//taint parameter set
	private void t_ParGen(LinkedHashSet<String> entrySet, LinkedHashSet<String> exitSet, ArrayList<Value> params, SootMethod mtd) {
		interAna.calleeCallerMapCreation(mtd, currentBlock.getBody().getMethod());
		Iterator<Value> itrPar = params.iterator();		
		int index = 0;
		String callingObj = "@this: ";			
		String inParam = "@parameter";
		String param;
		while(itrPar.hasNext()) {
			Value arg = itrPar.next();
			if(entrySet.contains(arg.toString())) {
				if(index == 0) {
					param = callingObj + arg.getType().toString();
				}
				else {
					param = inParam + Integer.toString(index - 1) +  ": " + arg.getType().toString();
				}
				interAna.PreMapCreation(param, mtd);							
			}
			else {
				Iterator<String> itentrySet = entrySet.iterator();
				while(itentrySet.hasNext()) {
					String knownt_Var = itentrySet.next();
					String t_fld;
					if(knownt_Var.contains(arg.toString() + ".")) {
						String[] split = knownt_Var.split("\\.");
						if(index == 0) {							
							t_fld = "@this." + split[1];
						}
						else {
							t_fld = inParam + Integer.toString(index - 1) +
									"." + split[1];
						}
						interAna.PreMapCreation(t_fld, mtd);
					}
				}
			}
			index++;
		}		
	}

	//if control exp check
	private boolean ctrlExpCheck(LinkedHashSet<String> entrySet, LinkedHashSet<String> exitSet, Value condition) {	
		Iterator itr1 = condition.getUseBoxes().iterator();
		boolean ctrlexpAns = false;
		if(condition instanceof Local && entrySet.contains(condition.toString())) {
			ctrlexpAns = true;
		}
		else {
			while(itr1.hasNext()) {
				ValueBox useBox = (ValueBox) itr1.next();
				Value var = useBox.getValue();
				if(var instanceof Local && entrySet.contains(var.toString())) {				
					ctrlexpAns = true;
					break;
				}
			}
		}		
		return ctrlexpAns;
	}

	private void setCopyFn(LinkedHashSet<String> src, LinkedHashSet<String> dest)  {
		if(src != null) {
			Iterator<String> itrsrc = src.iterator();
			while(itrsrc.hasNext()) {
				String val = itrsrc.next();
				if(!dest.contains(val)) {
					dest.add(val);
				}
			}
		}
	}

	private boolean setComparison(LinkedHashSet<String> newSet, LinkedHashSet<String> oldSet)  {
		boolean setEqual = true;
		Iterator<String> itrOld = oldSet.iterator();
		Iterator<String> itrNew = newSet.iterator();
		while(itrOld.hasNext()) {
			String value = itrOld.next();
			if(!newSet.contains(value)) {
				setEqual = false;
				break;
			}
		}
		while(itrNew.hasNext()) {
			String value = itrNew.next();
			if(!oldSet.contains(value)) {
				setEqual = false;
				break;
			}
		}
		return setEqual;
	}

	public void printOut1() {
		int stmtnum = 0;
		while(stmtMap.containsKey(stmtnum)) {
			Unit stmt = stmtMap.get(stmtnum);
			LinkedHashSet<String> entrySet = entrySetMap.get(stmt);
			LinkedHashSet<String> exitSet = exitSetMap.get(stmt);
			System.out.println(entrySet);
			System.out.println(stmt);
			System.out.println(exitSet + "\n");
			stmtnum++;
		}
	}

	public void printOut(){
		//System.out.println("\n" + this.method.getName());
		System.out.println("----------------------------------------------------");
//		System.out.println(this.cfg.toString());
		
		for(Iterator<Unit> it = this.cfg.iterator(); it.hasNext();){
			Unit stmt = it.next();
			
			//print out the current stmt
			System.out.println(stmt.toString());
			
			//print out the defined variables of this current stmt
			System.out.print("// defined: ");
			String defined_var = null;
			for(ValueBox vb: stmt.getDefBoxes()){
				Value value = vb.getValue();
				//array reference
				if(value instanceof soot.jimple.ArrayRef){
					defined_var = ((soot.jimple.ArrayRef) value).getBase().toString();
				}
				//instance field reference
				else if(value instanceof soot.jimple.InstanceFieldRef){
					defined_var = ((soot.jimple.InstanceFieldRef) value).getBase().toString() + ((soot.jimple.InstanceFieldRef) value).getField().toString();
				}
				//static field reference
				else if(value instanceof soot.jimple.StaticFieldRef){
					defined_var = ((soot.jimple.StaticFieldRef) value).getField().getDeclaringClass().toString() + ((soot.jimple.StaticFieldRef) value).getField().toString();
				}
				//local variable
				else if(value instanceof soot.Local){
					defined_var = value.toString();
				}
				else{
					continue;
				}
				System.out.print(defined_var + "  ");
			}
			System.out.println();
			
			//print out the used variables of the current stmt
			System.out.print("// used: ");
			String used_var = null;
			for(ValueBox vb: stmt.getUseBoxes()){
				Value value = vb.getValue();
				//array reference
				if(value instanceof soot.jimple.ArrayRef){
					used_var = ((soot.jimple.ArrayRef) value).getBase().toString();
				}
				//instance field reference
				else if(value instanceof soot.jimple.InstanceFieldRef){
					used_var = ((soot.jimple.InstanceFieldRef) value).getBase().toString() + ((soot.jimple.InstanceFieldRef) value).getField().toString();
				}
				//static field reference
				else if(value instanceof soot.jimple.StaticFieldRef){
					used_var = ((soot.jimple.StaticFieldRef) value).getField().getDeclaringClass().toString() + ((soot.jimple.StaticFieldRef) value).getField().toString();
				}
				//local variable
				else if(value instanceof soot.Local){
					used_var = value.toString();
				}
				else{
					continue;
				}
				System.out.print(used_var + "  ");
			}
			System.out.println();
			
			//print out the predecessors of the current stmt
			System.out.println("<- preds: " + this.cfg.getPredsOf(stmt));
			
			//print out the succ of the current stmt
			System.out.println("-> succs: " + this.cfg.getSuccsOf(stmt));
			
			System.out.println();
		}
		
		System.out.println();
	}
	
}
