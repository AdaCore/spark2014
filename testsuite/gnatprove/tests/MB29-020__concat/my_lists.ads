package My_Lists is
   pragma SPARK_Mode (On);

   type Int_Array is array (Positive range <>) of Integer;

   type My_List is private;

   function Singleton (I : Integer) return My_List
   with Post => Get_Model (Singleton'Result) = (1 => I);

   function Head (L : My_List) return Integer
   with Post => Get_Model (L) (1) = Head'Result;

   function Cons (I : Integer; L : My_List) return My_List
   with Pre  => Get_Model (L)'Last < Natural'Last,
        Post => Get_Model (Cons'Result) = I & Get_Model (L);

   function Get_Model (L : My_List) return Int_Array;

private
   pragma SPARK_Mode (Off);

   type My_List_Record is record
      Head : Integer;
      Tail : My_List;
   end Record;

   type My_List is access My_List_Record;
end;
