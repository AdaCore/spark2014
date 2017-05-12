with Ada.Dispatching;

package body P is

   function Blocking return Boolean is
   begin
      Ada.Dispatching.Yield;
      return True;
   end;

   protected body PT is
      procedure Dummy is
         X : T := 0;
         pragma Unreferenced (X);
      begin
         null;
      end;
   end;

end;
