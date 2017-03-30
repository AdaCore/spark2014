with Except;
with Screen_Output;

with Values; use Values;

package body Stack
with SPARK_Mode => On
is


   Tab  : array (1 .. Max_Size) of Value;
   --  The stack. We push and pop pointers to Values.


   -----------
   -- Clear --
   -----------

   procedure Clear is
   begin
      Last := Tab'First - 1;
   end Clear;

   ----------
   -- Push --
   ----------

   procedure Push (V : Value) is
   begin
      if Last = Tab'Last then
         raise Overflow;
      end if;

      Screen_Output.Debug_Msg ("Pushing -> " & Values.To_String (V));

      Last := Last + 1;
      Tab (Last) := V;
   end Push;

   ---------
   -- Pop --
   ---------

   procedure Pop (V : out Value) is
   begin
      if Empty then
         raise Underflow;
      end if;

      V := Tab (Last);
      Last := Last - 1;

      Screen_Output.Debug_Msg ("Popping <- " & Values.To_String (V));
   end Pop;

   ---------
   -- Top --
   ---------

   function Top return Value is
   begin
      if Empty then
         raise Underflow;
      end if;

      return Tab (Last);
   end Top;

   ----------
   -- View --
   ----------

   procedure View is
   begin
      for I in Tab'First .. Last loop
         Screen_Output.Msg (Values.To_String (Tab (I)));
      end loop;

      Screen_Output.Msg ("");
   end View;

end Stack;
