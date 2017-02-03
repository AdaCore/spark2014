with Extension_Pkg;
package body Root_Pkg is
   function Op (X : Root) return Boolean is
   begin
      return True;
   end;

   function Op_Wrapper (Y : Root'Class) return Boolean is
   begin
      return Op (Y);
   end;
end;
