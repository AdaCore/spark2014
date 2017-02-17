with Ada.Iterator_Interfaces;

package Test_Iterable is pragma SPARK_Mode (On);

   type T is new Natural;
   type T_Array is array (Integer range <>) of T;
   type T_List (C : Natural) is record
      Content : T_Array (1 .. C);
   end record
     with Iterable => (First       => My_First,
                       Has_Element => My_Has_Element,
                       Next        => My_Next);
   function My_First (Cont : T_List) return Natural is
     (if Cont.C > 0 then 1 else 0);
   function My_Has_Element (Cont : T_List; P : Natural) return Boolean is
     (P in Cont.Content'Range);
   function My_Next (Cont : T_List; Position : Natural) return Natural is
     (if Position in 1 .. Cont.C - 1 then Position + 1 else 0);
   function All_Zeros (Cont : T_List) return Boolean is
     (for all C in Cont => Cont.Content (C) = 0);
end Test_Iterable;
