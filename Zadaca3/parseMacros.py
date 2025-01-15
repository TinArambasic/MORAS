def _parsemacros(self):
    self._iter_lines(self._parce_macro)

def _mv(self, A, B):
    s = ["@"+A, "D=M", "@"+B, "M=D"]
    return s

def _swp(self, A, B):
    s = ["@temp", "M=0", "@"+A, "D=M", "@temp", "M=D", "@"+B, "D=M", "@"+A, "M=D", "@temp", "D=M", "@"+B, "M=D"]
    return s

def _add(self, A, B, D):
    s = ["@"+A, "D=M", "@"+B, "D=M+D", "@"+D, "M=D"]
    return s

def _while(self, A):
    self.counter += 1
    s = ["(WHILE" + str(self._counter) + ")" + "\n@" + A + "\nD=M\n" + "@END" + str(self._counter) + "\nD;JEQ\n"]
    return s

def _parse_macro(self, line, p, o):
    if line[0] == "$":
        lines = line[1:].split("(")
        macro = lines[0]


        if len(lines) > 1:
            args = lines[1]
            argl = args.replace(")", "".split(","))

            if macro == "MV":
                s = self._mv()
                return s
            
            elif macro == "SWP":
                s = self._swp
                return s
            
            elif macro == "ADD":
                s = self._add
                return s
            
            elif macro == "WHIlE":
                s = self._while(argl[0])
                return s
            
            else:
                self._flag = False
                self._line = o
                self._errm = "Invalid macro"
            
    else:
        return s