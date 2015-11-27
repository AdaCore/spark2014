with Ada.Real_Time, Ada.Dispatching;

package body Blocking_Contract is

   function Blocking return Boolean

   is
   begin
      Ada.Dispatching.Yield;
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
