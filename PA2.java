
import soot.*;
import soot.options.Options;

public class PA2 {

    public static void main(String[] args) {

        String classPath = "./testcases/" + args[0];  // do not change this, as evaluation would have testcases under this dir
        String outPath = "./optimized/" + args[0];


        // Set up arguments for Soot
        String[] sootArgs = {
            "-cp", classPath,
            "-pp",
            "-w",
            "-f", "c",          // output .class files
            "-d", outPath,      // where to write optimized binaries
            "-t", "1",
            "-main-class", "Test",
            "-process-dir", classPath
        };

        // Create transformer for analysis
        AnalysisTransformer analysisTransformer = new AnalysisTransformer();

        // Add transformer to appropriate pack in PackManager; PackManager will run all packs when soot.Main.main is called
        PackManager.v().getPack("wjtp")
                .add(new Transform("wjtp.dfa", analysisTransformer));

        // Set Soot options (Used to maintain line numbers from source code)
        Options.v().set_keep_line_number(true);

        // Call Soot's main method with arguments
        soot.Main.main(sootArgs);
    }
}
