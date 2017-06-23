generic

   type T_E is private;

package Lib.Cont.G_B is

   type T (C : T_C) is tagged private;

private

   subtype Index is T_Count range 1 .. T_Count'Last;

   type T_T is array (Index range <>) of T_E;

   type T (C : T_C) is tagged
      record
         E : T_T (1 .. C);
      end record;

end Lib.Cont.G_B;
