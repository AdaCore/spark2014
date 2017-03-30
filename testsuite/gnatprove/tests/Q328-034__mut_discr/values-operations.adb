with Except;
with Screen_Output;
with Stack;

package body Values.Operations
with SPARK_Mode => On
is

   ----------
   -- Read --
   ----------

   function Read (Op : String) return Operation is
   begin
      if Op = "+" then
         return Add;

      elsif Op = "-" then
         return Sub;

      elsif Op = "*" then
         return Mul;

      elsif Op = "/" then
         return Div;

      else
         raise Except.User_Error;
      end if;
   end Read;

   -------------
   -- Process --
   -------------

   procedure Process (Op : Operation) is
      V2 : Value;
      V1 : Value;

      Result : Integer;

   begin
      Stack.Pop (V2);
      Stack.Pop (V1);

      if Op in Add | Sub then
         if V1.E not in Integer'First / 2 + 1 .. Integer'Last / 2 - 1 then
            return;
         end if;

         if V2.E not in Integer'First / 2 + 1 .. Integer'Last / 2 - 1 then
            return;
         end if;
      elsif Op in Div then
         if V2.E = 0 then
            return;
         end if;
      end if;


      case Op is
         when Add =>
            Result := V1.E + V2.E;

         when Div =>
            Result := V1.E / V2.E;

         when Mul =>
            Result := V1.E * V2.E;

         when Sub =>
            Result := V1.E - V2.E;
      end case;

      --  Create an integer Value by setting the field "E" of the record
      --  to Result.

      Stack.Push (Value'(E => Result));

   end Process;

end Values.Operations;


