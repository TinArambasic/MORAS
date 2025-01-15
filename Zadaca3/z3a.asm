@R0
D=M
@CURRENT
M=D

@0
D=A
@R2
M=D

(LOOP)
@CURRENT
D=M
@R2
D=M+D
@R2
M=D
@CURRENT
M=M+1
@R1
D=M
@CURRENT
D=D-M
@END
D;JGT
@LOOP
0;JMP

(END)
@END
0;JMP
