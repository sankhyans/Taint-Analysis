import java.util.Map;

import soot.PackManager;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.Transform;
import soot.options.Options;
import soot.util.Chain;

/** This is a wrapper class. You do NOT need to change it at all.
 * 
 * Feb 13, 2015
 * @author Zuo Zhiqiang
 */
public class InterMainDriver {
	public static void main(String[] args) {
		PackManager.v().getPack("wjtp").add(new Transform("wjtp.myTransform", new SceneTransformer(){

			@Override
			protected void internalTransform(String phaseName, Map options) {
				// TODO Auto-generated method stub
				Chain<SootClass> classes = Scene.v().getApplicationClasses();
				System.out.println("Application classes analyzed: " + classes.toString());
				//you should implement the inter-procedural taint analysis as class InterTaintAnalysis
				InterTaintAnalysis analysis = new InterTaintAnalysis(classes);
			}
			
		}));
		
		Options.v().set_whole_program(true);
		Options.v().setPhaseOption("cg", "enabled:false");
		Options.v().setPhaseOption("wjpp", "enabled:false");
		Options.v().setPhaseOption("wjap", "enabled:false");
		
		Options.v().setPhaseOption("jap", "enabled:false");
		Options.v().setPhaseOption("jb", "use-original-names:true");
		
		Options.v().set_keep_line_number(true);
		Options.v().set_output_format(Options.output_format_jimple);
		
		//Important: you need to add rt.jar of jre to your CLASSPATH
		Options.v().set_prepend_classpath(true);
		
		/**args should be in the following format: "-cp path_of_classes_analyzed class_names"
		 * e.g., -cp E:\Workspace\ws_program\taintanalysis\bin\ InterTest HelloWorld
		 */
		soot.Main.main(args);
	}

}
