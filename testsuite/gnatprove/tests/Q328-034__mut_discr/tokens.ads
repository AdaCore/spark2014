--  This package defines the notion of a token. In general terms a token is
--  the smallest lexical entity known to SDC.

with Instructions;
with Types;
with Values;
with Values.Operations;
with Stack;

package Tokens
with SPARK_Mode => On
is

   type Token_Kind is (Val, Op, Instr);

   type Token (Kind : Token_Kind := Val) is private;
   --  The actual token type.

   procedure Next (V : out Token);
   --  Reads the input characters typed by the user
   --  and converts them into tokens.

   procedure Process (T : Token)
     with Pre => (if T.Kind = Val then not Stack.Full
     and then (if T.Kind = Op then Stack.Size >= 2));
   --  Process token T, ie undertake the actions corresponding to token T.

private

   type Token (Kind  : Token_Kind := Val) is record
      case Kind is
         when Val =>
            Val   : Types.Value;
         when Op =>
            Op    : Values.Operations.Operation;
         when Instr =>
            Instr : Instructions.Instruction;
      end case;
   end record;

end Tokens;


