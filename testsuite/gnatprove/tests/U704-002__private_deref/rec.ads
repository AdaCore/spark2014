package Rec
is
   type T is private;
private
   type T_Data;
   type T is access T_Data;

   type T_Data is
   record
      N : T;
   end record;
   function F (E : T) return T is (E.all.N);
end Rec;
