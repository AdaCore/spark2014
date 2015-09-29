with Ada.Real_Time;

package body Blocking_Contract is

   function Blocking return Boolean
     with Volatile_Function
   is
   begin
      delay until Ada.Real_Time.Clock;
      return True;
   end;

   procedure Proc with Pre => Blocking;

   procedure Proc is
   begin
      null;
   end;

   protected PO is
      entry Dummy;
   end;

   protected body PO is
      entry Dummy when True is
      begin
         Proc;
      end;
   end;
end;
