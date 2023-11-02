/tag <h2> Commands /tag </h2>


In langauges such as C a function main provides the single entry point into a program. In Tau there can be many entry points and are specified by including the word /em COMMAND
in a comment of a function that meets the following conditions:
/br Is a  valid function 
 /br Define with Function
 /br Has parameter types of seq.word ,seq.file, or boolean. 
 /br Has a return type of seq.word
 /br the word COMMAND is in comment immediately following the return type.
 
Tau documentation of the commands provided in the release is given by  the
command tau?.  This command was defined with 
<* block Function tau? /tag (cmd:seq.word, out:seq.word) seq.word
{COMMAND ... } ... *>
Typing <* block tau? out: full *> on the command line will give 
 /tag <a /sp href ="../documentation/cmddoc.html" > Result /tag </a> /sp
 
Taking <* block tau? /tag (cmd:seq.word, out:seq.word) *> from the definition,
removing the paraenthesis and commas,and 
replacing the types of the arguments actual values will give the   syntax for calling the function on the command line.
<* block tau? /tag cmd: out:full  *>
The order the parameters are specified does not matter. An ommitted parameter of type
seq.word is given an empty value.

"Tau? cmd usegraph out full" only gives the documentation for the usegraph command.  Since cmd is both the the first argument  given and the first argumentin the defining procedure  ,  the -cmd can be omitted. Hence "Tau usegraph -out full" will give the same results.

 For parameters of boolean type the value is false if the parameter is ommited or if the value  /em false.  Any other value for a boolean parameter
 is interpreted as /em true.  
 
Parameters of type seq.file  also are replaced with a string.
 "+ directory.ls file1 file2 file3"

the value is processed as filenames and the file from the filing system is fetched. 
