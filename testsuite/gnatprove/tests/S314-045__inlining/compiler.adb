--
-- Implementation of PL/0 Compiler written in Ada
-- by John Perry, 2018
--

pragma Profile(Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

-- for text and integer I/O
with Ada.Text_IO;
with Ada.Integer_Text_IO;
with Text_IO_Wrapper; use Text_IO_Wrapper;

-- gives us some cool tools for manipulating characters
with Ada.Characters.Handling; use Ada.Characters.Handling;
-- gives us access to cool constants like CR, HT (carriage return, horizontal tab)
with Ada.Characters.Latin_1; use Ada.Characters.Latin_1;

-- concurrency tools
with Ada.Synchronous_Task_Control; use Ada.Synchronous_Task_Control;
with Ada.Real_Time; use Ada.Real_Time;

package body Compiler with SPARK_Mode is

Empty_String80: String80 := ( others => ' ' );

  procedure Hang(Message: String) with Global => null is
  begin
    Put(Message); New_Line(1);
    Put("The program or interpreter hung. Terminate, fix the problem, and restart.");
    New_Line(1);
    loop
      null;
    end loop;
  end Hang;

----
-- Displaying p-code
----

-- @summary prints the p-codes stored in code between start and stop
-- @param code table of p-codes to show
-- @param start index of where to start showing p-codes
-- @param stop index of where to stop showing p-codes
procedure Show_PCode(code: in PCode_Table; start, stop: Table_Range)
    with Global => null
is
begin
  for i in start..stop loop
    Put(Positive(i), 4); Put(' ');
    -- Image attribute creates a string representation of enum object
    Put(code(i).instruction'Image); Put(' ');
    Put(code(i).level, 4);
    Put(code(i).data, 4);
    Put("    ");
    Put(code(i).comment);
    New_Line(1);
  end loop;
end Show_PCode;

----
-- Error Handling
----

-- enumeration of errors; see Error_Messages for elaboration
type Errors is (
  NO_ERROR,
  SEMICOLON,
  IDENT,
  UNKNOWN,
  ASSIGN,
  ASSIGN_PROC,
  CALL_PROC,
  END_SYM,
  DO_SYM,
  THEN_SYM,
  VARIABLE,
  RPAREN,
  LPAREN,
  PROG_SIZE,
  NUMBER_EXPECTED,
  REL,
  NUMBER_IDENT,
  NOPROCEDURE,
  END_PROG,
  IS_PROCEDURE,
  BAD_SYMBOL,
  BAD_KIND,
  UNRECOGNIZED_PUNCTUATION,
  END_OF_FILE,
  EXPECT_UNTIL,
  TO_OR_DOWNTO,
  EXPECT_OF,
  COLON,
  CASE_NEEDS_CONSTANT,
  FOR_NEEDS_VARIABLE,
  TOO_MANY_THREADS,
  ARRAY_EXPECTS_SIZE,
  ARRAY_EXPECTS_INDEX,
  ARRAY_REQUIRES_BRACKETS
);

function To_String80(S: String) return String80 is
    Result: String80 := ( others => ' ' );
    J: Integer := String80'First;
begin
    --Move(S, Result);
    for I in S'First .. S'Last loop
      Result(J) := S(I);
      J := J + 1;
      if J > Result'Last then exit; end if;
    end loop;
  return Result;
end To_String80;

-- mapping errors to strings without if statements!
error_strings: constant array(Errors) of String80 := (
  NO_ERROR => To_String80("No error -- strange..."),
  SEMICOLON                => To_String80("Semicolon Expected"),
  IDENT                    => To_String80("Identifier Expected"),
  UNKNOWN                  => To_String80("Unknown Identifier"),
  ASSIGN                   => To_String80("Assignment operator expected"),
  ASSIGN_PROC              => To_String80("Assignment to PROCEDURE not allowed"),
  CALL_PROC                => To_String80("Can only call a procedure"),
  END_SYM                  => To_String80("END symbol Expected"),
  DO_SYM                   => To_String80("DO symbol Expected"),
  THEN_SYM                 => To_String80("THEN symbol Expected"),
  VARIABLE                 => To_String80("Variable or Expression Expected"),
  RPAREN                   => To_String80("RIGHT Parenthesis Expected"),
  LPAREN                   => To_String80("LEFT Parenthesis Expected"),
  PROG_SIZE                => To_String80("Program size is too large..."),
  NUMBER_EXPECTED          => To_String80("A number was Expected"),
  REL                      => To_String80("Relational operator expected"),
  NUMBER_IDENT             => To_String80("number or ident expected"),
  NOPROCEDURE              => To_String80("Procedure not accepted here"),
  END_PROG                 => To_String80("Premature end of program"),
  IS_PROCEDURE             => To_String80("Assignment not allowed here"),
  BAD_SYMBOL               => To_String80("Internal error: bad symbol encountered"),
  BAD_KIND                 => To_String80("Internal error: bad object kind encountered"),
  UNRECOGNIZED_PUNCTUATION => To_String80("Unrecognized punctuation"),
  END_OF_FILE              => To_String80("Unexpected end of file"),
  EXPECT_UNTIL             => To_String80("UNTIL symbol expected"),
  TO_OR_DOWNTO             => To_String80("TO or DOWNTO symbol expected"),
  EXPECT_OF                => To_String80("OF symbol expected"),
  COLON                    => To_String80("Colon expected"),
  CASE_NEEDS_CONSTANT      => To_String80("Cases must be constants"),
  FOR_NEEDS_VARIABLE       => To_String80("For loops require a declared variable"),
  TOO_MANY_THREADS         =>
      To_String80("Too many threads open already cannot start a new one"),
  ARRAY_EXPECTS_SIZE       => To_String80("Must specify a size for an array"),
  ARRAY_EXPECTS_INDEX      => To_String80("Can only access arrays through indices"),
  ARRAY_REQUIRES_BRACKETS  =>
          To_String80("Specify array size with a number in brackets [...] after name")
);

-- @summary raises an informative exception
-- @description Program will halt!
-- @param num which error was selected
  procedure Error(Num: Errors)
  is
    Compile_Error: exception;
  begin
    if Num /= NO_ERROR then
      New_Line(1);
      Hang(Error_Strings(Num));
    end if;
  end Error;

----
-- Symbol recognition and coordination
----

-- symbols/tokens the compiler understands
type Symbol is (
	VARSYM,
	CONSTSYM,
	BEGINSYM,
	ENDSYM,
	PERIOD,
	SEMICOLON,
	COLON,
	LPAREN,
	RPAREN,
	EQL,        -- keep
	NOTEQL,     -- these
	LSTHEN,     -- six
	GREQL,      -- symbols
	GRTHEN,     -- in
	LSEQL,      -- order
	ASSIGN,
	IFSYM,
	IDENT,
	NUM,
	PROCSYM,
	MINUS,
	PLUS,
	DIV,
	MULT,
	COMMA,
	ODDSYM,
	CALL,
	THENSYM,
	WHILESYM,
	DOSYM,
	-- added by John Perry
	ELSESYM,
	REPEATSYM,
	UNTILSYM,
	WRITESYM,
	WRITELNSYM,
	FORSYM,
	TOSYM,
	DOWNTOSYM,
	CASESYM,
	OFSYM,
	CENDSYM,
	ORSYM,
	ANDSYM,
	NOTSYM,
	COBEGINSYM,  -- concurrency
	COENDSYM,    -- concurrency
	THREADSYM,   -- concurrency
	ARRAYSYM,    -- arrays
	LBRACKET,    -- arrays
	RBRACKET,    -- arrays
	-- this last one is not strictly necessary but definitely useful
	MAX_SYMBOL
);

-- helps avoid if statements when processing OPR 0,?
subtype Relation_Symbol is Symbol range EQL..LSEQL;
-- these go with OPR 0,?
relation_operands: constant array(Relation_Symbol) of Integer := (
  EQL    =>  8,
  NOTEQL =>  9,
  LSTHEN => 10,
  GREQL  => 11,
  GRTHEN => 12,
  LSEQL  => 13
);
-- comment strings for OPR 0,?
relation_comments: constant array(Relation_Symbol) of String(1..3) := (
  EQL    => "=?=",
  NOTEQL => "=/=",
  LSTHEN => "<? ",
  GREQL  => ">=?",
  GRTHEN => ">? ",
  LSEQL  => "<=?"
);

----
-- Identifiers
----

-- types of identifiers
type Identifier_Type is (
  NONE,   -- unrecognized (probably an error)
  CONST,  -- constant (but "constant" is a keyword and Ada is case-insensitive)
  VAR,    -- variable
  PROC,   -- procedure (but "procedure" is a keyword)
  ARR     -- array (but "array" is a keyword)
);

-- classification of characters read from input
type Input_Type is ( ALPHA, DIGIT, EOL, NONE, PUNCT, WHITESPACE );
-- things we recognize as characters
subtype Punct_Range is Character range Exclamation..Low_Line;

----
-- Reading input
----

-- @summary determine the character type of ch
-- @param ch character read from input
-- @return what sort of character ch is
function Char_Type(ch: Character) return Input_Type is
begin
  return (
          if ch = LF or ch = CR then EOL               -- end of line
          elsif Is_Letter(Ch) then ALPHA               -- letter
          elsif Is_Digit(Ch)  then DIGIT               -- digit
          elsif Ch = Space or Ch = HT then WHITESPACE  -- space
          elsif Ch in Punct_Range then PUNCT           -- punctuation
          else NONE
         );
end Char_Type;

line:      String80; -- last word processed from input
punc:      String80; -- last puncuation processed from input
read_line: String80; -- full line read from input (please be <80 chars!)
number:    Integer;        -- last number processed from input

linelength: Length_Range := 0; -- length of line read
char_pos:   Length_Range := 1; -- position of next character to process (>= 1!)

-- @summary read a character from input
-- @description If we have already read in an entire line,
-- and have not exhausted it, reads the next unprocessed character in the line.
-- Otherwise, it attempts to read a new line from the input.
procedure Get_Char(ch: out Character)
with
  Global => (Input => Error_Strings,
             In_Out => (Char_Pos, Linelength, Read_Line)
            )
is
begin
  if char_pos > linelength then
    if End_Of_File then Error(END_OF_FILE); end if;
    loop
      declare Inline: String := Get_Line;
      begin
        Read_Line := To_String80(Inline);
        Linelength := Inline'Length;
        if linelength = 0 then New_Line(1);
        else Put(inline); end if;
      end;              
      exit when linelength > 0;
    end loop;
    New_Line(1);
    char_pos := 1; -- reset character count
    Ch := CR;
  else
    ch := Read_Line(Integer(char_pos));
    char_pos := char_pos + 1; -- count characters
  end if;
end Get_Char;

-- used for converting characters to digits
subtype Digit_Range is Natural range 0..9;

-- @summary Converts ch to the corresponding digit.
-- @param ch character from input
-- @return a digit corresponding to this character ('0'->0, '1'->1, etc.)
function Ordinal(ch: Character) return Digit_Range is
  result: Digit_Range;
begin
  case ch is
    when '0'..'9' => result := Character'Pos(ch) - Character'Pos('0');
    when others =>
      Hang("Program error: tried to make a digit from a non-digit");
      Result := 0;
  end case;
  return result;
end Ordinal;

function Identify_Symbol(Line: in String) return Symbol is
  begin
    return (case Line(Line'First) is
            when 'A' => (if Line = "ARRAY" then ARRAYSYM else IDENT),
            when 'B' => (if Line = "BEGIN" then BEGINSYM else IDENT),
               when 'C' => (if Line = "CONST" then CONSTSYM
                            elsif Line = "CALL" then CALL
                            elsif Line = "CASE" then CASESYM
                            elsif Line = "CEND" then CENDSYM
                            elsif Line = "COBEGIN" then COBEGINSYM
                            elsif Line = "COEND" then COENDSYM
                            else IDENT),
            when 'D' => (if Line = "DO" then DOSYM
                         elsif Line = "DOWNTO" then DOWNTOSYM
                         else IDENT),
            when 'E' => (if Line = "ELSE" then ELSESYM
                         elsif Line = "END" then ENDSYM
                         else IDENT),
            when 'F' => (if Line = "FOR" then FORSYM else IDENT),
            when 'I' => (if Line = "IF" then IFSYM else IDENT),
            when 'N' => (if Line = "NOT" then NOTSYM else IDENT),
            when 'O' => (if Line = "OF" then OFSYM
                         elsif Line = "OR" then ORSYM
                         elsif Line = "ODD" then ODDSYM
                         else IDENT),
            when 'P' => (if Line = "PROCEDURE" then PROCSYM else IDENT),
            when 'R' => (if Line = "REPEAT" then REPEATSYM else IDENT),
            when 'T' => (if Line = "TO" then TOSYM
                         elsif Line = "THEN" then THENSYM
                         elsif Line = "THREAD" then THREADSYM
                         else IDENT),
            when 'U' => (if Line = "UNTIL" then UNTILSYM else IDENT),
            when 'V' => (if Line = "VAR" then VARSYM else IDENT),
            when 'W' => (if Line = "WHILE" then WHILESYM
                         elsif Line = "WRITE" then WRITESYM
                         elsif Line = "WRITELN" then WRITELNSYM
                         else IDENT),
            when others => IDENT
           );
  end Identify_Symbol;

function Identify_Punctuation(Punc: in String) return Symbol is
   begin
      return (case Punc(Punc'First) is
                 when ';' => (if Punc = ";" then SEMICOLON else MAX_SYMBOL),
                 when ',' => (if Punc = "," then COMMA else MAX_SYMBOL),
                 when '.' => (if Punc = "." then PERIOD else MAX_SYMBOL),
                 when ':' => (if Punc = ":" then COLON
                              elsif Punc = ":=" then ASSIGN
                              else MAX_SYMBOL),
                 when '/' => (if Punc = "/" then DIV else MAX_SYMBOL),
                 when '-' => (if Punc = "-" then MINUS else MAX_SYMBOL),
                 when '*' => (if Punc = "*" then MULT else MAX_SYMBOL),
                 when '+' => (if Punc = "+" then PLUS else MAX_SYMBOL),
                 when '=' => (if Punc = "=" then EQL else MAX_SYMBOL),
                 when '<' => (if Punc = "<" then LSTHEN
                              elsif Punc = "<=" then LSEQL
                              elsif Punc = "<>" then NOTEQL
                              else MAX_SYMBOL),
                 when '>' => (if Punc = ">" then GRTHEN
                              elsif Punc = ">=" then GREQL
                              else MAX_SYMBOL),
                 when '(' => (if Punc = "(" then LPAREN else MAX_SYMBOL),
                 when ')' => (if Punc = ")" then RPAREN else MAX_SYMBOL),
                 when '[' => (if Punc = "[" then LBRACKET else MAX_SYMBOL),
                 when ']' => (if Punc = "]" then RBRACKET else MAX_SYMBOL),
                 when others => MAX_SYMBOL
              );
   end Identify_Punctuation;

-- @summary gets the next symbol from the input
-- @param sym where to store the symbol
procedure Get_Symbol(sym: out Symbol) is
  ch:       Character;    -- character to be read
  ch_type:  Input_Type;   -- what ch turns out to be
  start_Index, stop_index: Integer;
  i: Natural;
begin
  -- skip whitespace
  loop
    Get_Char(ch);
    ch_type := Char_Type(ch);
    exit when ch_type /= WHITESPACE and ch_type /= EOL;
  end loop;
  -- if it's an alphabetic character, finish reading a full word
  if Char_Type(ch) = ALPHA then
    --Start_Index := Integer(Char_Pos - 1);
    Line(Line'First) := Ch;
    I := Line'First + 1;
    loop
      Get_Char(ch);
      exit when (Char_Type(ch) /= ALPHA and Char_Type(ch) /= DIGIT and ch /= '_');
      Line(I) := Ch;
      I := I + 1;
    end loop;
    I := I - 1;
    if ch /= CR then char_pos := char_pos - 1; end if;
    Sym := Identify_Symbol(To_Upper(Line(Line'First..I)));
    if Sym = IDENT then
      for J in I + 1 .. Line'Last loop Line(J) := ' '; end loop;
    end if;
  -- if it's a digit, finish reading the full number
  elsif Char_Type(ch) = DIGIT then
    sym := NUM;
    number := 0;
    loop
      number := 10 * number + Ordinal(ch);
      Get_Char(ch);
      exit when Char_Type(ch) /= DIGIT;
    end loop;
    if ch /= CR then char_pos := char_pos - 1; end if;
  -- if it's a punctuation...
  elsif Char_Type(ch) = PUNCT then
    Start_Index := Integer(Char_Pos - 1);
    Stop_Index := Start_Index;
    -- check if it's something that might get more than one character
    if ch = ':' or ch = '<' or ch = '>' then
      -- try reading if so
      Get_Char(ch);
      if Char_Type(ch) = PUNCT and (ch = '=' or ch = '>') then
        Stop_Index := Start_Index + 1;
      else
        if ch /= CR then char_pos := char_pos - 1; end if;
      end if;
    end if;
    -- is it something we recognize?
    -- Move(Read_Line(Start_Index..Stop_Index), Punc);
    Punc(Punc'First) := Read_Line(Start_Index);
    if Stop_Index = Start_Index then
      Punc(Punc'First + 1) := ' ';
    else
      Punc(Punc'First + 1) := Read_Line(Stop_Index);
    end if;
    sym := Identify_Punctuation(Punc(Punc'First .. Punc'First + Stop_Index - start_Index));
    if Sym = MAX_SYMBOL then Error(UNRECOGNIZED_PUNCTUATION); end if;
  else
    sym := MAX_SYMBOL;
  end if;
end Get_Symbol;

----
-- Accessing or modifying the symbol table
----

-- Symbol Table structure
type Symbol_Table_Entry is record
  name:   String80;  -- name of the variable/procedure/etc.
  kind:   Identifier_Type; -- whether it's a variable/procedure/etc.
  value:  Integer;         -- for constants
  level:  Integer;         -- relation to the current stack frame
  adr:    Table_Range;     -- where to find it
end record;

-- now set up the symbol table
max_symbols: constant := 499;
type Symbol_Table_Range is range 0..max_symbols;
symbol_table: array(Symbol_Table_Range) of Symbol_Table_Entry;

-- @summary insert block identifier
-- @description Enters an identifier into the symbol table.
procedure Enter(
  kind:        Identifier_Type;           -- whether it's VAR, PROC, etc.
  name:        String80;                  -- the identifier in the source code
  sym:         in out Symbol;             -- the current symbol;
                                          -- modified with value of next symbol
  varcount:    in out Table_Range;        -- number of variables in current frame
  level:       Integer;                   -- current level of the table
  table_index: in out Symbol_Table_Range; -- number of entries in the table
  size:        Table_Range := 0           -- (for arrays) size of object on stack
) is
begin
  table_index := table_index + 1;
  symbol_table(table_index).name := name;
  symbol_table(table_index).kind := kind;

  if kind = CONST then
    if sym /= IDENT then Error(IDENT); end if;
    Get_Symbol(sym);
    if sym /= EQL then Error(ASSIGN); end if;
    Get_Symbol(sym);
    if sym /= NUM then Error(NUMBER_EXPECTED); end if;
    symbol_table(table_index).value := number;
  elsif kind = VAR then
    if sym /= IDENT then Error(IDENT); end if;
    symbol_table(table_index).level := level;
    symbol_table(table_index).adr   := varcount;
    varcount := varcount + 1;
  elsif kind = ARR then
    symbol_table(table_index).level := level;
    symbol_table(table_index).adr   := varcount;
    varcount := varcount + size;
  elsif kind = PROC then
    symbol_table(table_index).level := level;
  end if;
  Get_Symbol(sym);
end Enter;

-- @summary locate position
-- @description Finds the position in the symbol table of the string stored
-- in package variable line.
-- @param table_index where to start looking
-- @return zero if the string stored in line does not appear in the table;
-- otherwise, it returns the index where that string appears
function Position(table_index: Symbol_Table_Range) return Symbol_Table_Range is
  i: Symbol_Table_Range := table_index;
begin
  loop
    exit when i = 0 or line = symbol_table(i).name;
    i := i - 1;
  end loop;
  return i;
end Position;

----
-- Generation of p-code
----

-- where we are in the code
code_index: Table_Range := 0;
-- where the code started
start_code_index: Table_Range := 0;

-- @summary generate a p-code instruction in the program
procedure Gen(
  code: in out PCode_Table; -- list of p-code instructions
  instruction: PCode;       -- new p-code instruction to add
  level: Integer;           -- level of data relative to current stack frame
  data: Integer;            -- data for the instruction
  comment: String80 := Empty_String80
                            -- optional comment for printing p-code
) with Post => (
                    Code(Code_Index).Instruction = Instruction and
                    Code(Code_Index).Level = Level and
                    Code(Code_Index).Data = Data and
                    Code(Code_Index).Comment = Comment and
                    Code_Index = Code_Index'Old + 1
               )
      
is begin
  if code_index > max_table_size then Error(PROG_SIZE); end if;
  code(code_index).instruction := instruction;
  code(code_index).level       := level;
  code(code_index).data        := data;
  code(code_index).comment     := comment;
  code_index := code_index + 1;
end Gen;

----
-- Parsing the code: Statement, Expression, etc.
----

-- @summary process a statement of the input file
-- @param code list of p-code instructions
-- @param sym the current symbol; modified with value of next symbol
-- @param level current stack frame
-- @param table_index number of identifiers currently in the stack
procedure Statement(
    code: in out PCode_Table;
    sym: in out Symbol;
    level: Integer;
    table_index: Symbol_Table_Range
);

-- @summary process an expression of the input file
-- @param code list of p-code instructions
-- @param sym the current symbol; modified with value of next symbol
-- @param level current stack frame
-- @param table_index number of identifiers currently in the stack
procedure Expression(
    code: in out PCode_Table;
    sym: in out Symbol;
    level: Integer;
    table_index: Symbol_Table_Range
);

-- @summary process a general expression in the input file
-- @param code list of p-code instructions
-- @param sym the current symbol; modified with value of next symbol
-- @param level current stack frame
-- @param table_index number of identifiers currently in the stack
procedure General_Expression(
  code: in out PCode_Table;
  sym: in out Symbol;
  level: Integer;
  table_index: Symbol_Table_Range
) is
  saved_sym: Symbol;
begin

  if sym = ODDSYM then -- ODD ...

    Get_Symbol(sym);
    Expression(code, sym, level, table_index);
    Gen(code, OPR, 0, 6, To_String80("odd?"));

  else

    Expression(code, sym, level, table_index);
    if sym in Relation_Symbol then
      saved_sym := sym;
      Get_Symbol(sym);
      Expression(code, sym, level, table_index);
      Gen(
          code,
          OPR,
          0,
          relation_operands(saved_sym),
          To_String80(relation_comments(saved_sym))
      );
    end if;

  end if;

end General_Expression;

-- @summary process a factor in the input file
-- @param code list of p-code instructions
-- @param sym the current symbol; modified with value of next symbol
-- @param level current stack frame
-- @param table_index number of identifiers currently in the stack
procedure Factor(
  code: in out PCode_Table;
  sym: in out Symbol;
  level: Integer;
  table_index: Symbol_Table_Range
) is
  i: Symbol_Table_Range;
begin

  case sym is

    when THREADSYM => -- print the current thread number

      Gen(code, THN, 0, 0, To_String80("thread number"));
      Get_Symbol(sym);

    when NUM => -- number

      Gen(code, LIT, 0, Number);
      Get_Symbol(sym);

    when LPAREN => -- opening a new expression

      Get_Symbol(sym);
      General_Expression(code, sym, level, table_index);
      if sym /= RPAREN then Error(RPAREN); end if;
      Get_Symbol(sym);

    when NOTSYM => -- NOT ...

      Get_Symbol(sym);
      Factor(code, sym, level, table_index);
      Gen(code, LIT, 0, 0, To_String80("not"));
      Gen(code, OPR, 0, 8, To_String80("eq?"));

    when IDENT => -- identifier

      i := Position(table_index);
      if i = 0 then Error(UNKNOWN); end if;
      if symbol_table(i).kind = PROC then Error(IS_PROCEDURE); end if;

      case symbol_table(i).kind is

        when CONST => -- constant

          Gen(code, LIT, 0, symbol_table(i).value, symbol_table(i).name);

        when VAR => -- load variable

          Gen(
            code,
            LOD,
            level - symbol_table(i).level,
            symbol_table(i).adr,
            symbol_table(i).name
          );

        when ARR => -- load array with offset

          Get_Symbol(sym);
          if sym /= LBRACKET then Error(ARRAY_EXPECTS_INDEX); end if;
          Get_Symbol(sym);
          Expression(code, sym, level, table_index);
          if sym /= RBRACKET then Error(ARRAY_EXPECTS_INDEX); end if;
          Gen(
            code,
            LDX,
            level - symbol_table(i).level,
            symbol_table(i).adr,
            symbol_table(i).name
          );

        when others => Error(BAD_KIND);

      end case;

      Get_Symbol(sym);

    when others => Error(VARIABLE);

  end case;

end Factor;

-- @summary process a term in the input file
-- @param code list of p-code instructions
-- @param sym the current symbol; modified with value of next symbol
-- @param level current stack frame
-- @param table_index number of identifiers currently in the stack
procedure Term(
  code: in out PCode_Table;
  sym: in out Symbol;
  level: Integer;
  table_index: Symbol_Table_Range
) is
  prev_sym: Symbol;
begin
  Factor(code, sym, level, table_index);
  while sym = MULT or sym = DIV or sym = ANDSYM loop
    prev_sym := sym;
    Get_Symbol(sym);
    Factor(code, sym, level, table_index);
    if prev_sym = DIV then Gen(code, OPR, 0, 5, To_String80("div"));
    elsif prev_sym = MULT then Gen(code, OPR, 0, 4, To_String80("mul"));
    else gen(code, OPR, 0, 4, To_String80("and"));
    end if;
  end loop;
end Term;

procedure Expression(
  code: in out PCode_Table;
  sym: in out Symbol;
  level: Integer;
  table_index: Symbol_Table_Range
) is
  prev_sym: Symbol;
begin
  if sym = PLUS or sym = MINUS then
    prev_sym := sym;
    Get_Symbol(sym);
    Term(code, sym, level, table_index);
    if prev_sym = MINUS then
      Gen(code, OPR, 0, 1, To_String80("negate"));
    end if;
  else
    Term(code, sym, level, table_index);
  end if;
  while sym = PLUS or sym = MINUS or sym = ORSYM loop
    prev_sym := sym;
    Get_Symbol(sym);
    Term(code, sym, level, table_index);
    if prev_sym = MINUS then Gen(code, OPR, 0, 3, To_String80("sub"));
    elsif prev_sym = PLUS then Gen(code, OPR, 0, 2, To_String80("add"));
    else Gen(code, OPR, 0, 2, To_String80("or"));
    end if;
  end loop;
end Expression;

-- @summary process an if statement
-- @param code list of p-code instructions
-- @param sym the current symbol; modified with value of next symbol
-- @param level current stack frame
-- @param table_index number of identifiers currently in the stack
procedure Process_If(
  code: in out PCode_Table;
  sym: out Symbol;
  level: Integer;
  table_index: Symbol_Table_Range
) is
  cx1, cx2: Table_Range;
begin
  Gen(code, OPR, 0, 7, To_String80("IF"));
  Get_Symbol(sym);
  General_Expression(code, sym, level, table_index);
  cx1 := code_index;
  Gen(code, JPC, 0, 0);
  if sym /= THENSYM then Error(THEN_SYM); end if;
  Get_Symbol(sym);
  Statement(code, sym, level, table_index);
  cx2 := code_index;
  Gen(code, JMP, 0, 0);
  code(cx1).data := Code_index;
  if sym = ELSESYM then
    Get_Symbol(sym);
    Statement(code, sym, level, table_index);
  end if;
  code(cx2).data := Code_index;
end Process_If;

-- @summary process a repeat statement
-- @param code list of p-code instructions
-- @param sym the current symbol; modified with value of next symbol
-- @param level current stack frame
-- @param table_index number of identifiers currently in the stack
procedure Process_Repeat(
  code: in out PCode_Table;
  sym: out Symbol;
  level: Integer;
  table_index: Symbol_Table_Range
) is
  cx1: Table_Range;
begin
  cx1 := code_index;
  Gen(code, OPR, 0, 7, To_String80("REPEAT"));
  loop
    Get_Symbol(sym);
    Statement(code, sym, level, table_index);
    exit when sym /= SEMICOLON;
  end loop;
  if sym /= UNTILSYM then Error(EXPECT_UNTIL); end if;
  Gen(code, OPR, 0, 7, To_String80("UNTIL"));
  Get_Symbol(sym);
  General_Expression(code, sym, level, table_index);
  Gen(code, JPC, 0, Cx1);
end Process_Repeat;

-- @summary process a for statement
-- @param code list of p-code instructions
-- @param sym the current symbol; modified with value of next symbol
-- @param level current stack frame
-- @param table_index number of identifiers currently in the stack
procedure Process_For(
  code: in out PCode_Table;
  sym: out Symbol;
  level: Integer;
  table_index: Symbol_Table_Range
) is
  i: Symbol_Table_Range;
  cx1, cx2: Table_Range;
  upwards: Boolean;
begin
  Gen(code, OPR, 0, 7, To_String80("FOR"));
  Get_Symbol(sym);
  if sym /= IDENT then Error(IDENT); end if;
  i := Position(table_index);
  if symbol_table(i).kind /= VAR then Error(FOR_NEEDS_VARIABLE); end if;
  Get_Symbol(sym);
  if sym /= ASSIGN then Error(ASSIGN); end if;
  Get_Symbol(sym);
  Expression(code, sym, level, table_index);
  Gen(
      code,
      STO,
      level - symbol_table(i).level,
      Symbol_table(i).adr,
      symbol_table(i).name
  );
  if sym /= TOSYM and sym /= DOWNTOSYM then Error(TO_OR_DOWNTO); end if;
  upwards := sym = TOSYM;
  Get_Symbol(sym);
  Expression(code, sym, level, table_index);
  cx1 := code_index;
  -- duplicate top of stack
  Gen(code, CTS, 0, 0);
  Gen(
      code,
      LOD,
      level - symbol_table(i).level,
      Symbol_table(i).adr,
      symbol_table(i).name
  );
  if upwards then Gen(code, OPR, 0, 11, To_String80("geq?"));
  else Gen(code, OPR, 0, 13, To_String80("leq?"));
  end if;
  cx2 := code_index;
  Gen(code, JPC, 0, 0);
  if sym /= DOSYM then Error(DO_SYM); end if;
  Get_Symbol(sym);
  Statement(code, sym, level, table_index);
  if upwards then Gen(code, LIT, 0, 1, To_String80("up"));
  else Gen(code, LIT, 0, -1, To_String80("down"));
  end if;
  Gen(
      code,
      LOD,
      level - symbol_table(i).level,
      Symbol_table(i).adr,
      symbol_table(i).name
  );
  Gen(code, OPR, 0, 2, To_String80("step"));
  Gen(
      code,
      STO,
      level - symbol_table(i).level,
      Symbol_table(i).adr,
      symbol_table(i).name
  );
  Gen(code, JMP, 0, Cx1);
  code(cx2).data := Code_index;
  Gen(code, INT, 0, -1);
end Process_For;

-- @summary process a case statement
-- @param code list of p-code instructions
-- @param sym the current symbol; modified with value of next symbol
-- @param level current stack frame
-- @param table_index number of identifiers currently in the stack
procedure Process_Case(
  code: in out PCode_Table;
  sym: out Symbol;
  level: Integer;
  table_index: Symbol_Table_Range
) is
  i: Symbol_Table_Range;
  cx0, cx1: Table_Range;
begin
  Gen(code, JMP, 0, code_index + 2, To_String80("CASE"));
  cx0 := code_index;
  Gen(code, JMP, 0, 0);
  Get_Symbol(sym);
  Expression(code, sym, level, table_index);
  if sym /= OFSYM then Error(EXPECT_OF); end if;
  Get_Symbol(sym);
  while sym /= CENDSYM loop
    -- duplicate top of stack
    Gen(code, CTS, 0, 0);
    if sym /= IDENT and sym /= NUM then Error(NUMBER_IDENT); end if;
    if sym = IDENT then
      i := Position(table_index);
      if symbol_table(i).kind /= CONST then Error(CASE_NEEDS_CONSTANT); end if;
      Gen(
          code,
          LIT,
          0,
          symbol_table(i).value,
          To_String80("case " & symbol_table(i).name)
      );
    else
      Gen(
          code,
          LIT,
          0,
          number,
          To_String80("case " & Integer'Image(number))
      );
    end if;
    Gen(code, OPR, 0, 8, To_String80("equal?"));
    Get_Symbol(sym);
    if sym /= COLON then Error(COLON); end if;
    cx1 := code_index;
    Gen(code, JPC, 0, 0);
    Get_Symbol(sym);
    Statement(code, sym, level, table_index);
    code(cx1).data := code_index + 1;
    if sym /= SEMICOLON then Error(SEMICOLON); end if;
    Get_Symbol(sym);
    Gen(code, JMP, 0, Cx0);
  end loop;
  code(cx0).data := Code_index;
  Gen(code, INT, 0, -1, To_String80("CEND"));
  Get_Symbol(sym);
end Process_Case;

-- @summary process a cobegin statement
-- @param code list of p-code instructions
-- @param sym the current symbol; modified with value of next symbol
-- @param level current stack frame
-- @param table_index number of identifiers currently in the stack
procedure Process_Cobegin(
  code: in out PCode_Table;
  sym: out Symbol;
  level: Integer;
  table_index: Symbol_Table_Range
) is
  num_to_spawn: Natural := 0;
  cx1: Table_Range;
begin
  Gen(code, OPR, 0, 7, To_String80("COBEGIN"));
  Get_Symbol(sym);
  while sym /= COENDSYM loop
    num_to_spawn := num_to_spawn + 1;
    cx1 := code_index;
    Gen(
        code,
        SNT,
        0,
        0,
        To_String80("spawn " & Integer'Image(num_to_spawn))
    );
    Statement(code, sym, level, table_index);
    Gen(
        code,
        RFT,
        0,
        0,
        To_String80("join " & Integer'Image(num_to_spawn))
    );
    code(cx1).data := code_index;
    if sym /= SEMICOLON then Error(SEMICOLON); end if;
    Get_Symbol(sym);
  end loop;
  Gen(code, WFT, 0, 0, To_String80("COEND"));
  Get_Symbol(sym);
end Process_Cobegin;

procedure Statement( -- documented above
  code: in out PCode_Table;
  sym: in out Symbol;
  level: Integer;
  table_index: Symbol_Table_Range
) is
  i: Symbol_Table_Range;
  cx1, cx2: Table_Range;
begin

  case sym is

    when IDENT => -- identifier

      i := Position(table_index);
      if i = 0 then Error(UNKNOWN); end if;

      case symbol_table(i).kind is

        when VAR => -- variables start assignment statements

          Get_Symbol(sym);
          if sym /= ASSIGN then Error(ASSIGN); end if;
          Get_Symbol(sym);
          Expression(code, sym, level, table_index);
          Gen(
              code,
              STO,
              level - symbol_table(i).level,
              Symbol_table(i).adr,
              symbol_table(i).name
          );

        when ARR => -- arrays can also start assignment statements

          Get_Symbol(sym);
          if sym /= LBRACKET then Error(ARRAY_EXPECTS_INDEX); end if;
          Get_Symbol(sym);
          Expression(code, sym, level, table_index);
          if sym /= RBRACKET then Error(ARRAY_EXPECTS_INDEX); end if;
          Get_Symbol(sym);
          if sym /= ASSIGN then Error(ASSIGN); end if;
          Get_Symbol(sym);
          Expression(code, sym, level, table_index);
          Gen(
              code,
              STX,
              level - symbol_table(i).level,
              Symbol_table(i).adr,
              symbol_table(i).name
          );

        when others => Error(ASSIGN_PROC); -- can't assign to anything else

      end case;

    when CALL => -- procedure call

      Get_Symbol(sym);
      if sym /= IDENT then Error(IDENT); end if;
      i := Position(table_index);
      if i = 0 then Error(UNKNOWN); end if;
      if symbol_table(i).kind /= PROC then Error(CALL_PROC); end if;
      Get_Symbol(sym);
      Gen(
          code,
          CAL,
          level - symbol_table(i).level,
          Symbol_table(i).adr,
          symbol_table(i).name
      );

    when BEGINSYM => -- BEGIN...END block

      Get_Symbol(sym);
      Statement(code, sym, level, table_index);
      while sym = SEMICOLON loop
        Get_Symbol(sym);
        Statement(code, sym, level, table_index);
      end loop;
      if sym /= ENDSYM then Error(END_SYM); end if;
      Get_Symbol(sym);

    when WHILESYM => -- WHILE block

      Gen(code, OPR, 0, 7, To_String80("WHILE"));
      Get_Symbol(sym);
      cx1 := code_index;
      General_Expression(code, sym, level, table_index);
      cx2 := code_index;
      Gen(code, JPC, 0, 0);
      if sym /= DOSYM then Error(DO_SYM); end if;
      Get_Symbol(sym);
      Statement(code, sym, level, table_index);
      Gen(code, JMP, 0, Cx1);
      code(cx2).data := Code_index;

    when IFSYM => Process_If(code, sym, level, table_index);

    when WRITESYM | WRITELNSYM => -- output

      declare newln: Boolean := sym = WRITELNSYM;
      begin
        Get_Symbol(sym);
        if sym /= LPAREN then Error(LPAREN); end if;
        loop
          Get_Symbol(sym);
          Expression(code, sym, level, table_index);
          Gen(code, OPR, 0, 14, To_String80("WRITE"));
          exit when sym /= COMMA;
        end loop;
        if sym /= RPAREN then Error(RPAREN); end if;
        Get_Symbol(sym);
        if newln then Gen(code, OPR, 0, 15, To_String80("WRITELN")); end if;
      end;

    when REPEATSYM  => Process_Repeat(code, sym, level, table_index);

    when FORSYM     => Process_For(code, sym, level, table_index);

    when CASESYM    => Process_Case(code, sym, level, table_index);

    when COBEGINSYM => Process_Cobegin(code, sym, level, table_index);
 
    when others     => null;

  end case;

end Statement;

-- @summary process a block of the input file
-- @param code list of p-code instructions
-- @param sym the current symbol; modified with value of next symbol
-- @param level current stack frame
-- @param table_index number of identifiers currently in the stack
procedure Block(
  code: in out PCode_Table;
  sym: in out Symbol;
  level: Integer;
  table_index_initial: Symbol_Table_Range
) is
  varcount: Table_Range;
  size: Table_Range;
  start_table_index: Symbol_Table_Range;
  table_index: Symbol_Table_Range := table_index_initial;
begin
  varcount := 5;
  start_table_index := table_index;
  symbol_table(table_index).adr := code_index;
  Gen(code, JMP, 0, 0);

  -- restricted globals loop
  while sym = CONSTSYM or sym = VARSYM or sym = PROCSYM or sym = ARRAYSYM loop
    if sym = CONSTSYM then
      -- CONST
      Get_Symbol(sym);
      Enter(CONST, line, sym, varcount, level, table_index);
      while sym = COMMA loop
        Get_Symbol(sym);
        Enter(CONST, line, sym, varcount, level, table_index);
      end loop;
      if sym /= SEMICOLON then Error(SEMICOLON); end if;
      Get_Symbol(sym);
    elsif sym = VARSYM then
      -- VAR
      Get_Symbol(sym);
      Enter(VAR, line, sym, varcount, level, table_index);
      while sym = COMMA loop
        Get_Symbol(sym);
        Enter(VAR, line, sym, varcount, level, table_index);
      end loop;
      if sym /= SEMICOLON then Error(SEMICOLON); end if;
      Get_Symbol(sym);
    end if;
    while sym = PROCSYM loop
      -- PROCEDURE
      Get_Symbol(sym);
      if sym /= IDENT then Error(IDENT); end if;
      Enter(PROC, line, sym, varcount, level, table_index);
      Get_Symbol(sym);
      Block(code, sym, level + 1, table_index);
      if sym /= SEMICOLON then Error(SEMICOLON); end if;
      Get_Symbol(sym);
    end loop;
    while sym = ARRAYSYM loop
      -- ARRAY
      loop
        Get_Symbol(sym);
        if sym /= IDENT then Error(IDENT); end if;
        Get_Symbol(sym);
        if sym /= LBRACKET then Error(ARRAY_REQUIRES_BRACKETS); end if;
        Get_Symbol(sym);
        if sym /= NUM then Error(NUMBER_EXPECTED); end if;
        size := Table_Range(number);
        Get_Symbol(sym);
        if sym /= RBRACKET then Error(ARRAY_REQUIRES_BRACKETS); end if;
        Enter(ARR, line, sym, varcount, level, table_index, size);
        exit when sym /= COMMA;
      end loop;
      if sym /= SEMICOLON then Error(SEMICOLON); end if;
      Get_Symbol(sym);
    end loop;
  end loop;
  
  code(symbol_table(start_table_index).adr).data := Code_index;
  symbol_table(start_table_index).adr:= code_index;
  start_code_index := code_index;
  Gen(code, INT, 0, varcount, To_String80("BEGIN"));
  Statement(code, sym, level, table_index);
  Gen(code, OPR, 0, 0, To_String80("END"));

  New_Line(1);
  Show_PCode(code, start_code_index, code_index - 1);
end Block;

----
-- Entry for compilation
----

-- @summary compile using standard input
-- @param code list of p-code instructions to write to
procedure Compile(code: in out PCode_Table) is
  sym: Symbol := MAX_SYMBOL;
  level: Integer := 0;
  table_index: Symbol_Table_Range := 0;
begin
  Get_Symbol(sym);
  Block(code, sym, level, table_index);
  New_Line(1);
  Put("Successful compilation!");
  New_Line(1);
end Compile;

----
-- The Interpreter, Part I: the Stack Machine
----

-- stack constants and types
max_stack: constant := 1000;
type Stack_Type is array(Table_Range) of Integer;

-- for multitasking/multiprocessing:
-- minimum number of threads
first_thread: constant := 0;
-- maximum number of threads
max_threads: constant := 15;
-- fnumber/range of stacks
subtype Thread_Range is Natural range first_thread..max_threads;

subtype Stack_Range is Natural range 0..Max_Stack;

-- information on who called a procedure or function
type Caller_Data is record
  stack:    Thread_Range := 0; -- which stack called it
  location: Table_Range := 0;  -- where to return in the program code
end record;

----
-- The Interpreter, Part II: concurrency
----

-- "protected" types are useful for concurrency;
-- only one task can access an entry at a time
-- we can also place regular procedures or functions in a protected type,
-- and any task can access them at any time, even simultaneously,
-- but we have no need for that in this case

type Thread_Array is array(Thread_Range) of Natural;

-- threads that are available for usage
protected type Threads_Avail_Lock is

  -- @summary acquire a thread for concurrent operation
  -- @description The new thread is stored in new_thread.
  procedure Acquire(new_thread: out Thread_Range);

  -- @summary release a thread from concurrent operation
  procedure Release(old_thread: in Thread_Range);

private

  -- threads currently available
  threads_avail: Thread_Array :=
        ( others => Thread_Range'First );
  Threads_Avail_Length: Thread_Range := Thread_Range'First;
  locked:      Boolean := false;  -- make it thread-safe
  initialized: Boolean := false;  -- whether we've initialized threads_avail

end Threads_Avail_Lock;

protected body Threads_Avail_Lock is

  -- @summary make all threads available (except the first)
  -- @description Ends as the set { 1, 2, 3, ..., 15 } (so long as
  -- first_thread is 0).
  procedure Initialize is
  begin
    -- Threads_Avail(Threads_Avail'Last) := First_Thread;
    for i in (first_thread + 1)..max_threads loop
      threads_avail(i - 1) := i;
    end loop;
    Threads_Avail_Length := Threads_Avail'First;
    initialized := true;
  end Initialize;

  -- @summary acquire a new thread
  -- @description Initializes threads_avail if not already initialized.
  procedure Acquire(new_thread: out Thread_Range) is
  begin
    if not initialized then Initialize; end if;
    New_Thread := Threads_Avail(Threads_Avail_Length);
    Threads_Avail_Length := Threads_Avail_Length + 1;
  end Acquire;

  -- @summary returns old_thread to the set of available threads
  procedure Release(old_thread: in Thread_Range) is
  begin
    Threads_Avail_Length := Threads_Avail_Length - 1;
    Threads_Avail(Threads_Avail_Length) := Old_Thread;
  end Release;

end Threads_Avail_Lock;

threads_avail: Threads_Avail_Lock; -- threads available for concurrency

  type Stack_Array is array(Stack_Range) of Integer;
  
-- "tasks" are the Ada mechanism for concurrent threads

  type New_Thread_Requirements is
      (
       CALLER_LOCATION, CALLER_BASE_REG, CALLER_PROG_REG,
       PARENT_STACK, GRANDPARENT_STACK,
       NEW_TOP, NEW_BASE_REG, NEW_PROG_REG
      );
  
  type New_Thread_Data is array(New_Thread_Requirements) of Integer;
  
-- this runs the actual stack machine
protected type Processor is
    -- @summary notifies the processor to start and sets up
    procedure Start
        (Program: PCode_Table; Which_Stack: Thread_Range; Data: New_Thread_Data
        );
    procedure Child_Finished(Child_Stack: Thread_Range);
    procedure Set_Monitor(Success: out Boolean);
    function Read_Stack(Location: Stack_Range) return Integer;
    procedure Write_Stack(Location: Stack_Range; Value: Integer);
    function Program return PCode_Table;
    function Program_Register return Table_Range;
    function Top_Of_Stack return Stack_Range;
    function Base_Register return Stack_Range;
    procedure Add_Child(Which: Thread_Range);
    function Is_Ready return Boolean;
    procedure Set_Unready;
    
  private
    
    Ready: Boolean := False;
    Stack: Stack_Array := ( others => 0 );
    Monitored: Boolean := False;
    Codes: PCode_Table;           -- the program
    Current_Stack: Thread_Range := 0;  -- which thread is running
    progreg:   Table_Range := 0;       -- program register
    Top:       Stack_Range := 0;       -- top of the stack
    Basereg:   Stack_Range := 0;       -- base register
    Code: PCode_Entry;            -- most recently read p-code
    Child_Threads: Thread_Array := ( others => 0 ); -- set of new threads spawned
    Last_Child_Index: Thread_Range := Thread_Array'First;

  end Processor;

  Processors: array(Thread_Range) of Processor; -- think of these as the "threads"
  -- Processors_Ready: array(Thread_Range) of Suspension_Object;
  
  procedure Run_Stack(Which_Stack: Thread_Range);

  task type Core;
  
  task body Core is
    Which: Integer := -1;
    Success: Boolean;
    Time: Ada.Real_Time.Time;
    Period: constant Ada.Real_Time.Time_Span := Ada.Real_Time.Milliseconds(10);
    Ready: Boolean;
  begin
    -- Which := Monitors.Get_Next_Processor;
    for I in Thread_Range loop
      Processors(I).Set_Monitor(success);
      if Success then
        Which := I;
        exit;
      end if;
    end loop;
    if Which /= -1 then
    loop
      --Put('(' & Trim(Integer'Image(Which), Ada.Strings.Left) & " going to sleep)" & CR & LF);
      -- Suspend_Until_True(Processors_Ready(Which));
      --Put('(' & Trim(Integer'Image(Which), Ada.Strings.Left) & " woke up to work)" & CR & LF);
      Ready := Processors(Which).Is_Ready;
      if Ready then
          Run_Stack(Which);
      else
          Time := Ada.Real_Time.Clock;
          Time := Time + Period;
          delay until Time;
      end if;
      -- Set_False(Processors_Ready(Which));
      --Done := true;
      --for I in Thread_Range loop
      --  declare
      --    Pi_In_Use: Boolean := Current_State(Processors_Ready(I));
      --  begin
      --    Done := Done and Pi_In_Use;
      --    end;
      --  end loop;
      --if Done
      --then
      --  Time_To_Quit := True;
      --  for I in Thread_Range loop
      --    Set_True(Processors_Ready(Which));
      --  end loop;
      --  exit;
      --end if;
      end loop;
    end if;
    declare
      S: String := Integer'Image(Which);
    begin
      Put("Quit " & S(S'Last - 1) & S(S'Last) & CR & LF);
    end;
  end Core;
  
  Cores: array(Thread_Range) of Core;

-- @summary finds the "base" frame that contains "global" data for a procedure or function
-- @param level how far down in the stack to go, relative to current
--    (this may involve switching stacks, so see other parameters)
-- @param basereg current base register
-- @param which_stack stack belonging to the current thread
-- @param stacks all the stacks, needed sometimes to find global data
-- @return the stack that called this function,
--     and the next p-code location to execute
procedure Base(
  level: Integer;
  basereg: Table_Range;
  which_stack: Thread_Range;
  result: out Caller_Data
) is
  lev: Integer := level;
  new_stack: Thread_Range := which_stack;
  new_base: Table_Range;
  base1: Table_Range := basereg;
begin
    if (Base1 = 0 and Which_Stack /= First_Thread) then
      Lev := Lev + 1;
    end if;
    while lev > 0 loop
      New_Base := Table_Range(Processors(New_Stack)
                              .Read_Stack(Stack_Range(Base1)));
      New_Stack := Thread_Range(Processors(New_Stack)
                                .Read_Stack(Stack_Range(Base1 + 4)));
      Base1 := New_Base;
      if Base1 = 0 and New_Stack /= First_Thread then
        Lev := Lev + 1;
      end if;
      Lev := Lev - 1;
    end loop;
    Result := (New_Stack, Base1);
end Base;

-- @summary runs an indicated thread (which_stack) on the given p-codes
-- @description The stack's bottom 5 entries must already be set up as:
-- (0) base register of global variables;
-- (1)current base register;
-- (2)program register to return to;
-- (3)stack calling this one;
-- (4)stack that called the calling stack.
-- @param program table of p-codes to execute
-- @param which_stack which stack to use
procedure Dispatch
      (
       program: PCode_Table; which_stack: Thread_Range; Data: New_Thread_Data
      ) is
begin
    New_Line(1);
    Put("Start PL/0 #"); Put(which_stack, 2);
    New_Line(1);
    Processors(Which_Stack).Start(Program, Which_Stack, Data);
end Dispatch;

----
-- The Interpreter, part III: the stack machine
----

  protected body Processor is
    
    function Read_Stack(Location: Stack_Range) return Integer is
        (Stack(Location));
    
    function Program return PCode_Table is (Codes);
    
    function Program_Register return Table_Range is (progreg);
    
    function Top_Of_Stack return Stack_Range is (Top);
    
    function Base_Register return Stack_Range is (Basereg);
    
    function Is_Ready return Boolean is (Ready);
    
    procedure Set_Unready is begin Ready := False; end Set_Unready;
    
    procedure Write_Stack(Location: Stack_Range; Value: Integer) is
    begin
      Stack(Location) := Value;
    end Write_Stack;
    
    procedure Set_Monitor(Success: out Boolean) is
      begin
        Success := not Monitored;
        if Success then Monitored := True; end if;
    end;
    
    procedure Add_Child(Which: Thread_Range) is
    begin
      Child_Threads(Last_Child_Index) := which;
      Last_Child_Index := Last_Child_Index + 1;
    end Add_Child;
    
    procedure Start
        (
         Program: PCode_Table; Which_Stack: Thread_Range; Data: New_Thread_Data
        ) is
    begin

      -- set up for execution
      Current_Stack := Which_Stack;
      Stack(0) := Data(CALLER_LOCATION);
      Stack(1) := Data(CALLER_BASE_REG);
      Stack(2) := Data(CALLER_PROG_REG);
      Stack(3) := Data(PARENT_STACK);
      Stack(4) := Data(GRANDPARENT_STACK);
      Top := Data(NEW_TOP);
      Progreg := Data(NEW_PROG_REG);
      Basereg := Data(NEW_BASE_REG);
      
      Codes := Program;
      
      -- Set_True(Processors_Ready(Which_Stack));
      Ready := True;

    end Start;


      -- this should occur only after a WFT

      procedure Child_Finished(child_stack: Thread_Range) is begin

        -- child has finished; return to set of available threads
        threads_avail.Release(child_stack);
        Last_Child_Index := Last_Child_Index - 1;

      -- if we still have children, we have to wait;
      -- otherwise we return to executions
      if Last_Child_Index = Child_Threads'First then
        --Run_Stack(Current_Stack);
        -- Set_True(Processors_Ready(Current_Stack));
        Ready := True;
      end if;

      end Child_Finished;

end Processor;

  -- @summary runs the p-codes on the stack; needs to be set up by Start
  procedure Run_Stack(Which_stack: Thread_Range) is
      
    Spawn_Data: New_Thread_Data;
    Code: PCode_Entry;
    Codes: PCode_Table := Processors(Which_stack).Program;
    Progreg: Table_Range := Processors(Which_stack).Program_Register;
    Top: Stack_Range := Processors(Which_Stack).Top_Of_Stack;
    Basereg: Stack_Range := Processors(Which_Stack).Base_Register;
    Caller: Caller_Data;          -- result of call to Base()
    New_Thread: Thread_Range;     -- for spawning a new task
    Tmp_Data: Integer;
    Ready: Boolean;

  begin

    Processors(Which_Stack).Set_Unready;
    
    loop

      -- get next instruction and increase program register
      Code := Codes(Progreg);
      Progreg := Progreg + 1;

      -- examine instruciton
      case Code.Instruction is

        when LIT => -- place literal on stack

          Top := Top + 1;
          Processors(Which_Stack).write_stack(Top, Code.Data);

        when OPR => -- operation, see cases

          case Code.Data is

          when 0 => -- return from subroutine

            Top           := (if Basereg = 0 then 0 else Basereg - 1);
            Basereg       := Stack_Range(Processors(Which_Stack).Read_Stack(Top + 2));
            Progreg       := Stack_Range(Processors(Which_Stack).Read_Stack(Top + 3));

          when 1 =>
            Processors(Which_Stack)
                .Write_Stack(Top, -Processors(Which_Stack).Read_Stack(Top)); -- negate

          when 2 => -- add

            Top := Top - 1;
            Processors(Which_Stack)
                .Write_Stack(Top, Processors(Which_Stack).Read_Stack(Top)
                       + Processors(Which_Stack).Read_Stack(Top + 1));

          when 3 => -- subtract

            Top := Top - 1;
            Processors(Which_Stack)
                .Write_Stack(Top,
                             Processors(Which_Stack).Read_Stack(Top)
                             - Processors(Which_Stack).Read_Stack(Top + 1));

          when 4 => -- multiply

            Top := Top - 1;
            Processors(Which_Stack)
                .Write_Stack(Top, Processors(Which_Stack).Read_Stack(Top)
                             * Processors(Which_Stack).Read_Stack(Top + 1));

          when 5 => -- divide

            Top := Top - 1;
            Processors(Which_Stack)
                .Write_Stack(Top,
                             Processors(Which_Stack).Read_Stack(Top)
                             / Processors(Which_Stack).Read_Stack(Top + 1));

          when 6 => -- odd
            
            Processors(Which_Stack)
                .Write_Stack(Top, Processors(Which_Stack).Read_Stack(Top) mod 2);

          when 8 => -- eq

            Top := Top - 1;
            Processors(Which_Stack)
                .Write_Stack(Top,
                             (
                              if
                                  Processors(Which_Stack).Read_Stack(Top)
                                  = Processors(Which_Stack).Read_Stack(Top + 1)
                              then 1 else 0
                             ));

          when 9 => -- not eq

            Top := Top - 1;
            Processors(Which_Stack)
                .Write_Stack(Top,
                             (
                              if
                                  Processors(Which_Stack).Read_Stack(Top)
                                  /= Processors(Which_Stack).Read_Stack(Top + 1)
                              then 1 else 0
                             ));

          when 10 => -- less

            Top := Top - 1;
            Processors(Which_Stack)
                .Write_Stack(Top,
                             (
                              if
                                  Processors(Which_Stack).Read_Stack(Top)
                                  < Processors(Which_Stack).Read_Stack(Top + 1)
                              then 1 else 0
                             ));

          when 11 => -- greater or eq

            Top := Top - 1;
            Processors(Which_Stack).
                Write_Stack(Top,
                            (
                             if
                                 Processors(Which_Stack).Read_Stack(Top)
                             >= Processors(Which_Stack).Read_Stack(Top + 1)
                             then 1 else 0
                            ));

          when 12 => -- greater

            Top := Top - 1;
            Processors(Which_Stack)
                .Write_Stack(Top,
                             (
                              if Processors(Which_Stack).Read_Stack(Top)
                              > Processors(Which_Stack).Read_Stack(Top + 1)
                              then 1 else 0
                          ));

          when 13 => -- less or eq

            Top := Top - 1;
            Processors(Which_Stack)
                .Write_Stack(Top,
                             (
                              if Processors(Which_Stack).Read_Stack(Top)
                              <= Processors(Which_Stack).Read_Stack(Top + 1)
                              then 1 else 0
                          ));

          when 14 => -- WriteLn

            Tmp_Data := Processors(Which_Stack).Read_Stack(Top);
            Put(Tmp_Data, 0); Put(' ');
            Top := Top - 1;

          when 15 => New_Line(1); -- WriteLn

          when others => null;

          end case;

        when LOD => -- load

          Top := Top + 1;
          Base(Code.Level, Basereg, Which_Stack, Caller);
          Tmp_Data := Processors(Caller.Stack)
              .Read_Stack(Caller.Location + Table_Range(Code.Data));
          Processors(Which_Stack).Write_Stack(Top, Tmp_Data);

        when LDX => -- load with offset, added by John Perry for arrays

          Base(Code.Level, Basereg, Which_Stack, Caller);
          Tmp_Data := Processors(Caller.Stack)
              .Read_Stack(Caller.Location + Table_Range(Code.Data)
                          + Table_Range(Processors(Which_Stack).Read_Stack(Top))
                         );
          Processors(Which_Stack).Write_Stack(Top, Tmp_Data);
        when STO => -- store

          Base(Code.Level, Basereg, Which_Stack, Caller);
          Tmp_Data := Processors(Which_Stack).Read_Stack(Top);
          Processors(Caller.Stack)
              .Write_Stack(Caller.Location + Table_Range(Code.Data), Tmp_Data);
          Top := Top - 1;

        when STX => -- store with offset, added by John Perry for arrays

          Base(Code.Level, Basereg, Which_Stack, Caller);
          Tmp_Data := Processors(Which_Stack).Read_Stack(Top);
          Processors(Caller.Stack)
              .Write_Stack(Caller.Location + Table_Range(Code.Data)
                           + Table_Range(Processors(Which_Stack).Read_Stack(Top - 1)),
                             Tmp_Data
                          );
          Top := Top - 2;

        when CAL => -- call a subroutine

          Base(Code.Level, Basereg, Which_Stack, Caller);
          Processors(Which_Stack).Write_Stack(Top + 1, Caller.Location);
          Processors(Which_Stack).Write_Stack(Top + 2, Basereg);
          Processors(Which_Stack).Write_Stack(Top + 3, Progreg);
          Processors(Which_Stack).Write_Stack(Top + 4, Which_Stack);
          Processors(Which_Stack).Write_Stack(Top + 5, Caller.Stack);
          Basereg := Top + 1;
          Progreg := Table_Range(Code.Data);

        when INT => -- increase top of stack

          Top := Table_Range(Integer(Top) + Code.Data);

        when JMP => -- jump always

          Progreg := Table_Range(Code.Data);

        when JPC => -- conditional jump

          Tmp_Data := Processors(Which_Stack).Read_Stack(Top);
          if Tmp_Data = 0 then
            Progreg := Table_Range(Code.Data);
          end if;
          Top := Top - 1;

          -- the following were added by John Perry

        when CTS => -- copy top of stack

          Top := Top + 1;
          Tmp_Data := Processors(Which_Stack).Read_Stack(Top - 1);
          Processors(Which_Stack).Write_Stack(Top, Tmp_Data);

        when SNT => -- spawn new thread

          -- obtain available thread
          Threads_Avail.Acquire(New_Thread);
          -- set up new thread's stacks
          Base(Code.Level, Basereg, Which_Stack, Caller);
          Spawn_Data := (
                         Caller.Location, Basereg, Progreg,
                         Which_stack, Caller.Stack,
                         5, 0, Progreg
                        );
          Progreg := Code.Data;
          Processors(Which_Stack).Add_Child(New_Thread);
          Dispatch(Codes, New_Thread, Spawn_Data);

        when RFT => -- return from thread

          Put("End PL/0 #"); Put(Which_stack, 2);
          New_Line(1);
          Progreg := 0;
          -- signal parent
          Processors(Processors(Which_Stack).Read_Stack(4))
              .Child_Finished(Which_stack);

        when WFT => -- wait for child threads

          -- jump out of the loop and wait for Child_Finished signal
          -- Set_False(Processors_Ready(Which_stack));
          -- Suspend_Until_True(Processors_Ready(Which_Stack));
          declare
            Time: Ada.Real_Time.Time := Ada.Real_Time.Clock;
            Period: Ada.Real_Time.Time_Span := Ada.Real_Time.Milliseconds(10);
          begin
            loop
              Time := Time + Period;
              delay until Time;
              Ready := Processors(Which_Stack).Is_Ready;
              if Ready then exit; end if;
            end loop;
          end;
          Processors(Which_Stack).Set_Unready;

          when THN => -- push thread number to top of stack

          Top := Top + 1;
          Processors(Which_Stack).Write_Stack(Top, Which_stack);

      end case;

      exit when Progreg = 0;

    end loop;

  end Run_Stack;

-- @summary interpret the compiled program
-- @param codes table of p-codes
  procedure Interpret(codes: PCode_Table) is
    Spawn_Data: New_Thread_Data;
  begin
    Spawn_Data := ( others => 0 );
    New_Line(1);
    Put("Start PL/0 #"); Put(first_thread, 2);
    New_Line(1);
    Processors(First_Thread).Start(Codes, First_Thread, Spawn_Data);
    Put("End PL/0 # "); Put(First_Thread, 2); New_Line(1);
  end Interpret;

end Compiler;
