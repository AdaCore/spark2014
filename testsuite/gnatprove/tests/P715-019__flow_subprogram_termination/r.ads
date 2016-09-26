with GNAT.OS_Lib;            use GNAT.OS_Lib;
package R
is
   subtype My_Integer is Integer range 1 .. 5;

   procedure Proc2 with No_Return;
   function Proc3 return Boolean;

end R;
