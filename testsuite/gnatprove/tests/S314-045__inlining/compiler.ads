--
-- Interface for PL/0 Compiler written in Ada
-- by John Perry, 2018
--

-- import this package
with Ada.Strings.Bounded;

package Compiler with SPARK_Mode is

-- we must pre-declare this type, but that doesn't mean we have to expose it
type PCode_Table is private;

-- @summary call this to compile from standard input
-- @description Generated p-codes will automatically be shown during compilation.
-- ("out" means that the parameter will be modified)
-- @param code where to store the generated p-code
procedure Compile(code: in out PCode_Table);

-- @summary call this to interpret the generated p-codes
-- @description("in" means the parameter will be read but not modified;
-- this is strictly enforced)
-- @param codes where the p-code is stored
procedure Interpret(codes: in PCode_Table);

private

-- enumeration of all pcodes
-- @value OPR some operation
-- @value CAL call a subroutine
-- @value INT increase the top of stack
-- @value JPC conditional jump
-- @value JMP unconditional jump
-- @value LIT place literal onto top of stack
-- @value LOD load onto top of stack value found elsewhere
-- @value STO store top of stack somewhere
-- @value CTS copy top of stack onto top of stack
-- @value SNT spawn new thread
-- @value RFT return from thread
-- @value WFT wait for thread
-- @value THN thread number
-- @value STX store at offset
-- @value LDX load from offset
type PCode is (
  OPR, CAL, INT, JPC, JMP, LIT, LOD, STO,
  CTS, SNT, RFT, WFT, THN, STX, LDX
);

-- maximum string length
strlen: constant := 80;
type Length_Range is new Integer range 0..Strlen;
subtype String80 is String(1..Strlen);

-- entry to the table of p-codes
type PCode_Entry is record
  instruction: PCode := OPR;          -- an appropriate p-code instruction
  level:       Integer := 0;
  -- the relation of the data with respect to the current stack frame
  data:        Integer := 0;        -- data 
  comment:     String80 := ( others => ' ' ); -- an optional string explaining what is going on
end record;

-- How large the program is allowed to be (in terms of p-codes)
max_table_size: constant := 999;
-- defining this subtype helps the compiler check for errors
subtype Table_Range is Natural range 0..max_table_size;
-- the list of p-codes
type PCode_Table is array(Table_Range) of PCode_Entry;

end Compiler;
