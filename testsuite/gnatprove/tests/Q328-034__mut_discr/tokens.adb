with Except;
with Input;
with Screen_Output;

package body Tokens
with SPARK_Mode => On
is

   ----------
   -- Next --
   ----------

   procedure Next (V : out Token) is
      Word_Buffer : String (1 .. Input.Line_Size);
      Word_Size : Integer;
   begin
      loop --  until we have read a valid token.

         --  Open block to catch exceptions raised for user errors.

         Input.Next_Word (Word_Buffer, Word_Size);

         Read_A_Valid_Token : declare
            Word : String := Word_Buffer (1 .. Word_Size);

         begin
            --  Figure out which kind of token we have from the first
            --  character and delegate the full token recognition to
            --  the Read routine in the appropriate Instruction, Values
            --  or Values.Operations package.
            if Word'Length >= 1 then
               case Word (Word'First) is

               when '0' .. '9' | '.' =>
                  V := Token'(Kind => Val, Val => Values.Read (Word)); --@DISCRIMINANT_CHECK:FAIL
                  return;

               when '+' | '*' | '/' =>
                  V := Token'(Kind => Op, Op => Values.Operations.Read (Word)); --@DISCRIMINANT_CHECK:FAIL
                  return;

               when '-' =>
                  if Word'Length > 1 then
                     V := Token'(Kind => Val, Val => Values.Read (Word)); --@DISCRIMINANT_CHECK:FAIL
                     return;
                  else
                     V := Token' --@DISCRIMINANT_CHECK:FAIL
                       (Kind => Op, Op => Values.Operations.Read (Word));
                     return;
                  end if;

               when 'a' .. 'z'
                  |  'A' .. 'Z' =>
                  V := Token' --@DISCRIMINANT_CHECK:FAIL
                    (Kind => Instr, Instr => Instructions.Read (Word));
                  return;

               when others =>
                  raise Except.User_Error;
               end case;
            end if;
         end Read_A_Valid_Token;
      end loop;
   end Next;

   -------------
   -- Process --
   -------------

   procedure Process (T : Token) is
   begin
      case T.Kind is
         when Val =>
            Values.Process (T.Val);

         when Op =>
            Values.Operations.Process (T.Op);

         when Instr =>
            Instructions.Process (T.Instr);
      end case;
   end Process;

end Tokens;

