# Taint-Analysis

CS 5218  Assignment 1

Static context-insensitive taint analysis on an intermediate representation of Java Programs.


1. The property space for “taint” information contains the details of the variables or user-input data that is flagged as tainted. So code will be run to ensure that security critical code is not being used using the tainted data. Initially there are no tainted variables, until  user input is started. After that all the values directly or indirectly in contact with it are marked as tainted. 

Information about such tainted variables is represented as:

1.1 Fixed Signature for each Method : 

	(a) Pre - Set: It will contain the information about the tainted parameters passed to the function as the input parameters. Hence, the name pre-set.

	(b) Gen - Set: It will contain the information about the variables that are still alive when the method returns back to the caller and these were tainted during method execution. It is basically the generated variable set obtained from an untrusted source.

	(c) Kill - Set: It will contain the information about the variables that are still alive when the method returns back to the caller but these were untainted during method execution. It is basically the killed tainted variable set. This was validated to ensure that the value is proper and untainted.
Example - variable obtained after re-assignment with untainted variable.


1.2 Taint information within each method is given as:
	(a) Entry - Set: It will contain the information about the tainted variables before the statement was executed. 
	(b) Exit - Set: It will contain the information about the tainted variables after the statement was executed.



2. A description of the strategy taken to perform context-insensitivity of the taint analysis.

Context insensitivity refers to the analysis in which we are not worried about how calling a method ‘a’ from ‘b’ is different from calling method ‘a’ from ‘c’.
It can be of two types :
Intra-procedural : Within a single method or procedure.
Inter-procedural : Across various methods/classes/procedures. 

Hence, first intra-procedural was done and then inter was done which used intra for  further analysis. This was also required because the fixed signature of a method can only be found out after all the statements in the method have been analysed. 

2.1 Intra-procedural Analysis: 
Only the variables that were tainted were tracked. Two separate sets/maps were maintained to store the in and exit-set, i.e. the variables flowing into and out from a statement. So, the exit-set of 1st statement will be the entry-set of 2nd statement. If we generalise it, exit-set of k-th statement will be the entry-set of ‘k+1’-th statement. Map were maintained to store the information related to each statement and its corresponding in and exit-sets. Initially all the sets are empty and then as processing is done, the information related to each statement is updated. Soot was used for converting the method body into ‘Jimple’ code and then get the control flow graphs. Control flow graphs are required to store the information related to a block. It stores the successor and predecessor  of any block. A block can be any bunch of statements. 

2.1.1 Maps/Arrays Used:
  a) ‘methodLIst’ and ‘pendingBlocks’  - to maintain a list to hold the list of blocks. methodList contains the information about all the methods. 
  b) ‘pendingBlocks’ - initially it will be empty and it will hold only the current block. But as the processing is done, the entry-set and exit-set of all the statements are merged as they were supposed to,  if the exit-set of the last statement is changed, add them to this.
  c) ‘currentMethod’ - to store the information about the method being currently processed. 

2.1.2. Statement Analysis:
There are different type of statements for analysis.
	- Assignment statements - these can generate or destroy the taint information. Hence, these are used for both gen() and kill(). Only assignment can un-taint a variable so that’s the only statement required for kill() function.
	- If, switch, lookup, while statements - these affect the program flow and can be used for tracking it. These are used only for gen() to check whether the controlling expression is tainted or not.

2.1.3. Fixed Point Analysis Iteration Algorithm:
All entry-set and exit-sets are empty.
While (there are blocks in the pendingBlocks)
{
	Take the first block and start processing
	while( there are statements in the current block)
	{
		merge exit-set of the previous statement with entry-set of current statement
		analyze the statement
		build the exit-set based on analysis
	}
	if(exit-set of last statement has changed)
	{	
		add all successors to the pendingBlocks for processing 
	}
	remove the block from the list
}


2.2. Inter-procedural Analysis :

Fixed Signatures of all the methods are calculated as part of the inter-proc, i.e. we need to find the pre-set, gen-set and kill-set of the method. An assumption here is that the main method is tainted. 
The pre-set of a function is equivalent to the entry-set of a statement. kill and gen set stores the information of generated or killed tainted variables and hence similar to the exit-set of a statement.
Similar to intra-proc, Soot was used to transform each class into ‘Jimple’ code and to generate the control flow graphs for each method in the analyzed classes.
A list is maintained to see the methods that need to be analyzed. It is started with the ‘main’ method since that one is definitely tainted. 

2.2.1 Maps/Arrays Used:
	- taintMap: to store the information related to the tainted variables.
	- killMap: to store the information related to kill variables and corresponding method.
	- genMap: to store the information related to the gen set and corresponding method.
	- methodIntraProcMap - we need to call an intra-proc for every method. So, this map to store intra and its corresponding method.

2.2.2 Chaotic Fixed Point Analysis Iteration Algorithm:
All pre-set, gen-set and kill-sets are empty.
While (there are methods in the List)
{
	if (list is empty but there are some methods that were not called and hence have not analyzed)
	{	
		add them to the list of pending methods for processing 
	}
	if (the list is not empty) 
	{
		get the method
		perform the intra-proc analysis
		remove the method from list
	}
}

2.2.3. Method Analysis :
There are different type of statements for analysis.
	- Assignment statements: these can generate or destroy the taint information. Hence, these are used for both gen() and kill(). Only assignment can un-taint a variable so that’s the only statement required for kill() function.
	- If, switch, lookup, while statements: these affect the program flow and can be used for tracking it. These are used only for gen() to check whether the controlling expression is tainted or not.
	- Function call statement: If newly tainted paramaters are being passed then they are added to pre-set. method is added to the list which shows the methods that are supposed to be analysed.
	- Return statement: If the method has newly generated taint information, then it is added to the gen-set and all callers to the list of methods that are to be analyzed. Similarly, if a method returns the value that is not tainted, then it is added to kills-set and again all the callers are added to the ‘to be analysed method list’.
