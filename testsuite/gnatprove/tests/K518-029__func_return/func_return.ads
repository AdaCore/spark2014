package Func_Return is

   type T is range -20 .. 20;
   type NT is new T range 0 .. 20;
   subtype S is T range 0 .. 20;

   function FI return Integer;
   function FN return Natural;
   function FT return T;
   function FNT return NT;
   function FS return S;

   procedure Call;

end Func_Return;
