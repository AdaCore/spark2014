with Parent_05.Private_Child_B_05;
package body Parent_05.Public_Child_B_05
is
   function H (X : Integer) return Integer is
   begin
      return Parent_05.Private_Child_B_05.H (X);
   end H;
end Parent_05.Public_Child_B_05;
