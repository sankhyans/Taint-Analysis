import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Iterator;
import java.util.concurrent.LinkedBlockingQueue;

//import soot.Body;
import soot.SootClass;
import soot.SootMethod;
import soot.util.Chain;

/** Here you need to implement your inter-procedural taint analysis.
 * This dummy program just examines all the mtds in each class under analysis 
 * while invoking IntraTaintAnalysis to analyze each mtd.
 * 
 * @author z_zhiqiang
 *
 */
public class InterTaintAnalysis {
	
	final Chain<SootClass> classes;
	//new member variables
	private ArrayList<SootClass> classList; //list of classes 
	private ArrayList<SootMethod> udmtdList; 	//mtd and its bbg
	private LinkedHashMap<SootMethod, LinkedHashSet<String>> genMap; //mtd and gen set
	private LinkedHashMap<SootMethod, LinkedHashSet<String>> killMap; //mtd and kill set
	private LinkedHashMap<SootMethod, LinkedHashSet<String>> preMap; //mtd and tainted para
	private LinkedHashMap<SootMethod, IntraTaintAnalysis> mtdIntraProcMap; //// mtd and intra proc analyser
	private ArrayList<SootMethod> mtdList; //all the mtds
	private LinkedHashMap<SootMethod, ArrayList<SootMethod>> callingmtdMap; //mtds calling a specific mtd
	private LinkedBlockingQueue<SootMethod> pendingBlocks; //pending mtds
	private SootMethod currentmtd; 	//current mtd

	public InterTaintAnalysis(Chain<SootClass> classes1) {
		// TODO Auto-generated constructor stub
		this.classes = classes1;
		classList = new ArrayList<>();
		udmtdList = new ArrayList<>();
		genMap = new LinkedHashMap<>();
		killMap = new LinkedHashMap<>();
		preMap = new LinkedHashMap<>();
		mtdIntraProcMap = new LinkedHashMap<>();
		callingmtdMap = new LinkedHashMap<>();
		mtdList = new ArrayList<>();
		pendingBlocks = new LinkedBlockingQueue<>(); 
		
		//add all mtds from all classes
		Iterator<SootClass> itrClass = classes.iterator();
		while(itrClass.hasNext()) {
			SootClass sootClass = itrClass.next();
			classList.add(sootClass);
			Iterator<SootMethod> itrMtd = sootClass.methodIterator();
			
			while(itrMtd.hasNext()) {
				SootMethod mtd = itrMtd.next();		
				udmtdList.add(mtd);
				//init gen,kill,taint para
				LinkedHashSet<String> genSet1 = new LinkedHashSet<>();
				genMap.put(mtd, genSet1);
				LinkedHashSet<String> killSet1 = new LinkedHashSet<>();
				killMap.put(mtd, killSet1);
				LinkedHashSet<String> taintParSet1 = new LinkedHashSet<>();
				preMap.put(mtd, taintParSet1);
				
				//intra-proc analysis
				IntraTaintAnalysis analyser = new IntraTaintAnalysis(mtd,this);
				mtdIntraProcMap.put(mtd, analyser);
				mtdList.add(mtd);
				//1st mtd should be main as it will contain the info about the tainted variables
				if(mtd.isMain()) {
					pendingBlocks.add(mtd);
				}	
			}
		}
		//analysis start - all mtds in pendingBlocks and mtdList list
		while(!pendingBlocks.isEmpty() || !mtdList.isEmpty()) {
			//add the mtd that has never been analysed - 1st time
			if(pendingBlocks.isEmpty()) {
				Iterator<SootMethod> itrMet = mtdList.iterator();
				pendingBlocks.add(itrMet.next());
			}
			currentmtd = pendingBlocks.remove();			
			//get the intra-proc analyser created in constructor and call its analyzer to get data
			IntraTaintAnalysis intraprocana = mtdIntraProcMap.get(currentmtd);
			intraprocana.stmtAnalysis();
			mtdList.remove(currentmtd);		
		}
		//display the resultst
		this.printOut();
	}

	//check if its a user defined mtd - if entered in the constructor in beginning
	public boolean ifUDmtd(SootMethod SootMethod) {
		//return udmtdList.containsKey(SootMethod);
		return udmtdList.contains(SootMethod);
	}

	//taint par set for each mtd
	public void PreMapCreation(String arg, SootMethod mtd) {
		LinkedHashSet<String> preSet = preMap.get(mtd);
		if(!preSet.contains(arg)) {
			preSet.add(arg);
			preMap.put(mtd, preSet);
			if(!pendingBlocks.contains(mtd)) {
				pendingBlocks.add(mtd);
			}
			if(!pendingBlocks.contains(currentmtd)) {
				pendingBlocks.add(currentmtd);
			}
		}
	}

	//gen set for each mtd - add the non-duplicate info to it, if its not alredy there
	// context insensitive analysis so all callers should all be analysed
	public void GenMapCreation(String retValue, SootMethod mtd)  {
		LinkedHashSet<String> genSet = genMap.get(mtd);
		LinkedHashSet<String> taintParamsSet = preMap.get(mtd);
		if(!genSet.contains(retValue) && !taintParamsSet.contains(retValue)) {
			genSet.add(retValue);
			genMap.put(mtd, genSet);
			ArrayList<SootMethod> callerList = callingmtdMap.get(mtd);
			if(callerList != null) {
				Iterator<SootMethod> itrClr = callerList.iterator();
				while(itrClr.hasNext()) {
					SootMethod caller = itrClr.next();
					if(!pendingBlocks.contains(caller)) {
						pendingBlocks.add(caller);
					}
				}
			}
		}
	}

	//kill set for each mtd - add based on if it's an old tainted filed or this obj's
	// context insensitive analysis so all callers should all be analysed
	public void KillMapCreation(String lhs, String rhs, SootMethod mtd) {
		LinkedHashSet<String> killSet = killMap.get(mtd);		
		LinkedHashSet<String> taintParSet = preMap.get(mtd);	
		if((!killSet.contains(lhs)) && (!lhs.equals(rhs))) {
			boolean isParKilled = false;
			StringBuilder killVal = new StringBuilder();
			if(lhs.contains(".")) {
				String[] lhs1 = lhs.split("\\.");
				Iterator<String> itrPar = taintParSet.iterator();
				while(itrPar.hasNext()) {
					String taintedPar1 = itrPar.next();
					if(taintedPar1.contains(lhs1[1])) {
						isParKilled = true;
						if(lhs1[0].equals("this")) {
							killVal.append("@" + lhs);
						}
						else {
							killVal.append(taintedPar1);
						}
					}
				}
			}
			if(isParKilled) {
				killSet.add(killVal.toString());
				killMap.put(mtd, killSet);
				ArrayList<SootMethod> callerList1 = callingmtdMap.get(mtd);
				if(callerList1 != null) {
					Iterator<SootMethod> itrClrs = callerList1.iterator();
					while(itrClrs.hasNext()) {
						SootMethod caller = itrClrs.next();
						if(!pendingBlocks.contains(caller)) {
							pendingBlocks.add(caller);
						}
					}
				}
			}
		}
	}
	
	//callee-caller map
	public void calleeCallerMapCreation(SootMethod calleeMet, SootMethod callerMet) {
		ArrayList<SootMethod> clrList = callingmtdMap.get(calleeMet);
		if(clrList == null) {
			clrList = new ArrayList<>();
		}
		if(!clrList.contains(callerMet)) {
			clrList.add(callerMet);
			callingmtdMap.put(calleeMet, clrList);
		}
	}

	public String getClassList() {
		return classList.toString();
	}
	

	public LinkedHashSet<String> getPreSet(SootMethod mtd) {
		return preMap.get(mtd);
	}

	public LinkedHashSet<String> getGenSet(SootMethod mtd) {		
		return genMap.get(mtd);
	}

	public LinkedHashSet<String> getKillSet(SootMethod mtd) {		
		return killMap.get(mtd);
	}

	public LinkedHashSet<String> getUpdatedPreSet(LinkedHashSet<String> preSet) {
		LinkedHashSet<String> preSet1 =  new LinkedHashSet<>();
		ArrayList<String> temp = new ArrayList<>(preSet);
		for (String val : temp) {
			if(val.contains("@parameter0")) {
				preSet1.add("@para0");
			}
		    else if (val.contains("@parameter")) {
		    	int temp1 = val.indexOf(".");
		    	if(temp1 !=-1)
		    	{
		    		String temp2 = "@para"+val.substring(temp1-1);
		    		preSet1.add(temp2);
		    	}
		    }
		    else
		    {
		    	preSet1.add(val);
		    }
		}
		return preSet1;

	}

	public void printOut(){
		Iterator<SootClass> itrCls = classes.iterator();
		System.out.println("\n\nThe fixed signatures for each method are as follows:");
		System.out.println("========================================================\n");
		// print the kill,gen info 
		while (itrCls.hasNext()) {
			SootClass sootClass = itrCls.next();
			Iterator<SootMethod> itrMtd = sootClass.methodIterator();							
			while (itrMtd.hasNext()) {			
				SootMethod mtd = itrMtd.next();
				System.out.println(mtd.toString());
				LinkedHashSet<String> preSet = preMap.get(mtd);
				LinkedHashSet<String> preSet1 =getUpdatedPreSet(preSet);
				LinkedHashSet<String> genSet = genMap.get(mtd);
				LinkedHashSet<String> killSet = killMap.get(mtd);
				System.out.println("preSet: " + preSet1);
				System.out.println("genSet: " + genSet);
				System.out.println("killSet: " + killSet + "\n");
			}
		}
		System.out.println("========================================================");
		//taint info for each method
		System.out.println("\n\n\n\nThe taint information within each method is as follows:");
		System.out.println("========================================================\n");
		itrCls = classList.iterator();
		while (itrCls.hasNext()) {
			SootClass sootClass = itrCls.next();
			Iterator<SootMethod> itmtd = sootClass.methodIterator();						
			while (itmtd.hasNext()) {
				SootMethod mtd = itmtd.next();
				System.out.println(mtd.toString());
				System.out.println("--------------------------------------");
				mtdIntraProcMap.get(mtd).printOut1();
				System.out.println("\n\n\n");
			}
		}
		System.out.println("\n\n\n========================================================\n\n");
	}
}
